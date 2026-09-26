# Kickoff: baseline fast paths (B5), lane renaming, then MIR

This is the starting brief for the next session on branch `cfallin/mir`.
Read it first, then the documents it points to. Where this brief and a
design doc disagree, the design doc wins; if implementation shows the
design is wrong, stop and raise it rather than quietly diverging, and
record the outcome in that doc's decision log.

## 1. Where things stand

Read in this order:
1. `docs/BASELINE.md`: the baseline tier's design, plan (§8), the
   B0–B4 status and deviations, and the Octane numbers.
2. `docs/MIR.md` (rev 6): the MIR design on top of baseline. §5 is the
   MIR/baseline boundary, and §13 is the plan from M0b on.
3. `docs/DESIGN.md`: the rest of the system.

What's done:
- **M0, the MIR IR core** (`compiler/src/mir/`): types, ops and
  effects, the text format, and the validator. It predates rev 6; M0b
  (below) brings it up to date.
- **B0–B4, the baseline tier** (`compiler/src/wasm/baseline/`):
  - `layout.rs` defines the frame format, which is the inter-tier
    contract: per-pc stack depths, the resume word, the `argc` flags and
    `ERR_DEOPT`.
  - `codegen.rs` lowers every JSOp except `ForceInterpreter`.
  - `mod.rs` holds `translate_script` and the gates.
  - The new C++ helpers are at the end of `runtime/NightRuntime.cpp`.
    The direct-eval kernel is in `runtime/NightOpsInterp.cpp` (MPL).
- **Options** (`compiler/src/options.rs`): `--pipeline legacy|baseline|mir`,
  `--strict-coverage` and `--dump-tiers`, parsed by `Options::apply_flag`
  for both the CLI and the in-process option string (`NIGHT_OPTIONS`).
  `--pipeline mir` exists, but the MIR builder doesn't yet, so every
  script falls through to baseline.

## 2. Building and testing

- **Build:**
  - `cmake --build build -j16` builds the wasm shell, `build/bin/nightmonkey`
    (with the `wizen` feature that `--shell` needs; a plain `cargo build`
    lacks it) and the in-process runner.
  - SpiderMonkey is prebuilt at `~/work/firefox/obj-nightmonkey-sm/dist`.
  - `cargo test -p night-compiler` runs the unit tests.
- **Lanes** (`scripts/run-jit-tests.sh ~/work/firefox build -- -j24`):
  - Default: legacy BBV.
  - `NIGHT_OPTIONS="--pipeline baseline --strict-coverage"`: the
    baseline-tier lane. Every script in the batch must compile, or the
    test aborts. It also skips `tests/jit-test-excludes-baseline.txt`.
  - `NIGHT_INPROCESS_OFF=1`: interpreter only (to be renamed; §3).
  - Both compiled lanes must pass before each commit that touches
    codegen or the runtime.
- **Census.** Run every jit-test file with `--dump-tiers` and group the
  `night: tier <sid> interp [...]` lines by reason; this finds declines
  and in-process batch failures (`night: inprocess: ...`). The last
  session's command lines are in its transcript. The pattern is
  `find ... | xargs -P 24 -I{} sh -c 'timeout 30 build/bin/inproc-shell.sh -f $0 ...'`.
- **Octane:** the sources are in `~/work/firefox-scratch/octane/*.js`.
  - Run each through `build/bin/inproc-shell.sh` with the lane's env
    vars, best of 2, pinned with `taskset -c N`.
  - Parse the final `Score (version 9): N`, not the first number.
  - For compile-time profiling, snapshot once with
    `build/bin/nightmonkey --shell build/bin/js bench.js --keep-snapshot s.wasm -o /dev/null`
    (the source minus its trailing `main();`). Then time or `perf` just
    `build/bin/nightmonkey s.wasm -o out.wasm --pipeline baseline --stats`.

Pitfalls from the last session:
- **Waiting on a background run:** don't write `while pgrep -f "jit_test.py"`,
  because it matches its own command line and never exits. Start runs as
  tracked background tasks instead.
- **In-process build errors print only their first line.** When a batch
  fails with "serialize in-process batch", reproduce with the native
  `nightmonkey` on a snapshot, or bisect by script.
- **Git stash is shared with other worktrees and sessions.** Prefer a WIP
  commit to set work aside. If you must stash, tag the entry and apply it
  by SHA.
- **waffle's `validate()` is quadratic on long block chains**
  (`dominates` walks the idom chain once per value use), and its backend
  runs it on every function. Avoid shapes with huge fan-in into one
  block, and mind body size.

## 3. Task A: rename the interpreter-only lane

"Baseline" now names a tier (the SpiderMonkey sense), so the
interpreter-only lane becomes **interpreter-only**, or **interp** for
short.
- **Docs and comments:** update every mention in `README.md` ("the
  baseline lane", "the differential baseline"), `scripts/run-jit-tests.sh`,
  `scripts/run-jstests.sh`, `scripts/run-night-tests.sh`,
  `scripts/inproc-shell.sh.in`, `docs/DESIGN.md` and the other docs.
- **Code:** check the `--night-inprocess` help text and the source
  comments for the same usage (`git grep -i "baseline lane"`,
  `git grep -in "baseline" -- README.md scripts docs/DESIGN.md`).
- **The switch itself:** keep `NIGHT_INPROCESS_OFF=1` as the mechanism
  unless a rename is clearly better. It says what it does. If you rename
  it, keep the old name as an alias.
- This is one commit.

## 4. Task B: inline int32 fast paths (B5)

**Goal:** stop baseline from losing to the interpreter on
arithmetic-heavy code (crypto 0.51×, navier-stokes 0.41× the
interpreter) without making it speculative.
- A fast path is **pure** inline code that decides from the operands'
  tags alone, and falls back to the same helper call as today for
  everything else.
- No analysis facts, no state carried between ops: values stay in the
  frame. This is the baseline analogue of what the interpreter does, so
  it keeps the tier's character. Record the decision (it amends
  BASELINE.md §3.1 "nothing else is special-cased") in BASELINE.md's
  decision list.

Candidates, in expected order of payoff. Measure after each group.

1. **`ToBoolean` for conditional jumps and `Not`**
   (`JumpIfFalse`/`JumpIfTrue`/`And`/`Or`/`Not`). Handle the boolean,
   int32, undefined and null tags inline; call `to_boolean` for the
   rest.
2. **Relational and equality compares** on two int32s: `Lt Le Gt Ge`,
   and `Eq Ne StrictEq StrictNe` (int32 against int32 are equal exactly
   when the payloads are). For `StrictEq`/`StrictNe`, identical raw bits
   are also equal for every tag except double: `NaN !== NaN`, and
   `+0 === -0` has different bits. So a bitwise shortcut must exclude
   doubles.
3. **`Add`/`Sub` on two int32s**, with an overflow check (i64
   arithmetic, then range-check). On overflow, call the helper rather
   than boxing a double inline; it's simpler and rare.
4. **`BitAnd BitOr BitXor Lsh Rsh`** on two int32s (shift counts masked
   to 5 bits, as JS does), and `Ursh` when the result fits in int32
   (else the helper). **`Inc`/`Dec`** on an int32, with the overflow
   check.
5. **`Mul`** on two int32s: a checked product, and the helper when it
   overflows *or* when the result is 0 with a negative operand (−0).
   Leave `Div`/`Mod` to the helper at first; add a `Mod` fast path only
   if the numbers show it (a non-negative dividend and a positive
   divisor are the easy case).
6. Then look at the profile again. Plausible next targets are `GetElem`
   on a dense array with an int32 index, and `GetLocal`/`SetLocal` of
   values already in the frame (which are already just a load and a
   store). Only do what the numbers justify.

**Constraints:**
- Each fast path adds a diamond to the body. Measure body size (the
  `--stats` line `night: baseline body ... blocks/values`) along with
  speed, and keep the fallback block per op, not shared, for the
  fan-in reason above.
- The slow path must see the same frame state as today: operands in
  their slots, `top` at the op's entry depth.
- No new helper ABI.

**Tests:**
- Unit tests that validate the emitted module for each fast-pathed op.
- A small differential JS file under `tests/jit-test/` exercising the
  edges: int32 overflow, −0 from `Mul` and from `Sub` (`0 - 0` is +0,
  but `-0 - 0` arrives as a double), `NaN` compares, `Ursh` over 2³¹,
  shift counts ≥ 32, and mixed int32/double operands.
  `scripts/run-night-tests.sh` runs it in both lanes.

**Gate:**
- The strict baseline-tier lane and the legacy lane pass.
- The Octane table in BASELINE.md is updated (interp, baseline before
  and after, legacy), with body-size deltas.
- Arithmetic-heavy benchmarks should at least reach parity with the
  interpreter.

## 5. Task C: back to MIR

Continue with MIR.md §13 and BASELINE.md §8, in order:

- **M0b.** Bring the committed M0 code up to rev 6:
  - `TagSet` gains `magic`. `Val(⊤)` includes it, nothing unboxes it,
    and `guard.tags` can remove it.
  - `exit`/`exit.throw` and onramp roots carry the rval.
  - Loops are declared (header, preheader). The validator's
    "irreducible" structure error goes, and the preheader check keys off
    the declared loops.
  - Update the fixtures and tests.
- **M1.** MIR lowers to its own waffle function, with exits and throws
  into baseline, and forced-exit tests on hand-written MIR. Two pieces
  of infrastructure don't exist yet and belong to M1:
  - **Baseline's `ARGC_RESUME_BIT` entry.** Baseline has the resume
    dispatch machinery (loop-header dispatch blocks driven by the
    frame's resume word, and landing blocks), but only the generator
    entry drives it today. Add an entry fork on `ARGC_RESUME_BIT` that
    reads the resume word and routes as `resume_route` does. Mode
    `Throw` lands on that pc's exception landing: add landing blocks
    for throw targets, reached the same way. MIR's exit and throw pcs
    have to be passed to the baseline compile as extra `resume_targets`,
    so MIR builds first.
  - **Two functions per script.** `Outcome::Compiled` grows a list of
    extra bodies, called directly and never through the table. The
    in-process blob carving and its position check
    (`wasm/inprocess.rs`) and the snapshot placement must account for
    them. The MIR body is the table entry.
- **M2.** The JSOps-to-MIR builder under `--pipeline mir`, with the
  guard-failure stress mode.
- **M3.** Onramps, and the onramp-root policy of BASELINE.md §7.
- **W.** Only after M3: measure waffle's reducifier on real onramp-shaped
  MIR, and change waffle only if the numbers call for it.
- **M4 onward**, as in MIR.md.

## 6. Known limitations to keep in view

- **Module scripts never reach either tier.** The shell compiles a
  module root through the module loader, which doesn't call the
  `scriptCompiled` extension hook, so neither the in-process batch nor
  snapshot registration sees them. This is a pre-existing pipeline
  limitation, not something baseline introduced. It is tracked in
  `docs/TODO`, and matters for full AOT under MIR too.
- **Scripts over 1 MiB of bytecode stay interpreted** under baseline,
  because of the waffle validate cost above.
- **Frame introspection doesn't see compiled frames**
  (`tests/jit-test-excludes-baseline.txt`). This is designed out, as for
  legacy.
