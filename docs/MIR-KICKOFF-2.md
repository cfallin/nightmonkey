# MIR tier: kickoff for the next session

Branch `cfallin/mir`, head `4e84435`. Read docs/MIR.md (§4.3, §4.6, §5) and
docs/MIR-PARITY.md first. Working rules (from the user, also in memory):

- Build to the design and to legacy parity. No hill-climbing: never gate
  or retreat from a design element because a run moved a few percent
  (noise is 2-4%). Measure, then find the real cause.
- Two tracks: MIR = OPT, baseline = GEN. Facts are fixed; a kill exits
  (OPT -> GEN is natural). No general multiversioning.
- Use every analysis fact legacy uses; finish the designed ops.
- Commit and push as you go; commits end with the Co-Authored-By line.
  Never use the shared git stash. Do not commit docs/MIR-KICKOFF.md,
  mir-tier.md, prompt.md, reply.md.
- Lanes run `build/bin/js-inproc`: `make -C build js-inproc` after
  compiler changes (runtime changes: `make -C build js js-inproc`). Never
  rebuild build/ while lanes run. Host benchmark binary: a hostbuild
  (`CARGO_TARGET_DIR=build/cargo ... --features ff147 --features wizen`).

## First: the state at `4e84435` is not lane-tested

The last commit passed the night tests (all four configurations) and the
MIR unit tests, but the full lanes (mir, mir-stress 3, baseline, legacy)
were interrupted. Run them first; fix anything they find.

## Priority 1: deltablue runs in baseline. Find out why, and fix it.

Legacy ran deltablue at high-90% occupancy in OPT. Under MIR, a
significant share runs in baseline, and since TYPES landed that is
catastrophic (deltablue ~3300 vs ~7200 before, legacy ~6200):

- Method-entry `this` guards now prove TYPES (`guard_this_layout`,
  docs/MIR.md: identity and TYPES are what OPT means). deltablue's
  constraint objects are published *without* TYPES, so e.g. sid#254's
  entry guard (`L3 types`) exits ~9.8M times per run (exit census:
  `--mir-exit-census`, scratch script `ec3.sh` pattern: AOT with
  `--pipeline mir --mir-exit-census --stats --dump-tiers`, run, join
  `census kind 90` ids with `night: mir exit` lines).
- Current hypothesis: the delegating constructors
  (`BinaryConstraint.superConstructor.call(this, ...)`, then
  `this.addConstraint()` inside the delegate) call methods on the
  object while it is still under construction; those methods' entry
  guards fail on the CONSTRUCTING sentinel, so they run in baseline, and
  baseline's (engine-path) stores to `this` (e.g. `this.direction = ...`
  in `addToGraph`) clear TYPES. The object is then published without it.
  Verify this; do not assume it.
- Questions to answer with data, not guesses:
  1. Which deltablue scripts are not MIR at all? Run with `--dump-tiers`
     and collect every `night: tier N baseline [mir: <reason>]` line
     (whole-script declines). Any decline in a hot script is a
     completeness bug (see priority 2).
  2. Of the MIR scripts, how much time is spent in their baseline
     bodies (exits, onramps)? Profile with `WJR_PERFMAP=1 perf record`,
     and map `wasm[0]::function[N]` to scripts with `--stats`
     (`night: body sid#S func F`); baseline bodies are the `extra_bodies`.
  3. Why exactly does construction leave OPT (which guard, which pc)?
- Candidate fixes, once the cause is confirmed:
  - Methods called on a partially constructed object should run in OPT.
    The object's early key (the "partially constructed type") is known;
    a callee inlined at such a site could be built knowing its `this` is
    that constructing object (context-sensitive callee builds, like
    `formal_fns`), skipping the published-layout guard and storing with
    per-class checks (`field_types`, which already dispatch on the early
    key).
  - Alternatively or additionally: validate field types when an object is
    stamped (ctor exit, restamp), setting TYPES iff every typed field
    conforms, so construction outside OPT does not leave a published
    object permanently without TYPES. This is a design change; propose it
    to the user before building it.
- Also watch raytrace: ~760K engine-path value-store demotions of layout
  12 (`IntersectionInfo`) remain (epoch-bump census `census kind 66`,
  id = (bump site << 16) | idx; site 7 = StoredValue). Find which stores
  still take the engine path.

## Priority 2: MIR completeness

We should be able to compile almost any function to MIR, apart from
temporary macro-scale carve-outs (e.g. async/generator resume). Today
whole scripts decline (docs/MIR-PARITY.md §1.6): `typeof globalName`,
class constructors, for-of/iterators, `??`, spread (call and array),
`super`, `new.target`, `Hole`, `InitElemInc`, singleton `Object`,
getter/setter element inits, lexical environments (`PushLexicalEnv`
etc.), non-global `GetName`/`SetName`, eval, try/catch bodies (catch is
never built: throws exit). Plan:

1. Census every decline reason across jit-tests and Octane
   (`--dump-tiers`; scratch `census.sh` pattern), rank by frequency and
   by hot-script impact.
2. Implement the ops (lowering can call the same helpers baseline uses;
   correctness first, fast paths after). Add night tests per op family.
3. Keep `--strict-coverage` lanes meaningful: anything that declines is
   visible there.

## Priority 3: the rest of the parity arc

See docs/MIR-PARITY.md §2 for the ranked list. Not yet done:

- TYPES object component (JSClass kind, function script, singleton) for
  object-typed fields (docs/MIR.md §4.6 point 1).
- Designed ops never built: LoadGName/StoreGName/CheckBinding,
  NewObject(K)/InitField/PublishLayout, NewArray, CallDirect,
  CallNative, GuardSingleton, LengthArray/LengthString, IntArith.
- Ranges (interval propagation, overflow-check removal); the array read
  fold with element ranges; the typed-entry SEL bit (callee skips entry
  claims its caller proved).
- Effect summaries (`script_effects`) for proven callees, to keep loads
  available across calls (needs a proven callee: guarded direct call
  whose miss exits).
- Element misses in loops: their generic arms keep LICM from hoisting
  env reads (navier-stokes `width`).
- apply-forward wrappers, accessor arms, hasOwn/parseInt arms.
- `push` arm owes the array stamp's RANGES/TYPES duty (now clears
  conservatively).

## What landed this session (for orientation)

Stamps (literal, array, restamps; MIR and baseline); fixed facts (kills
exit; `exit.inline` clean/dirty); narrowing from tag tests; direct and
polymorphic call arms, lean callees, known closures through inlining;
typed Math, `length.ta`; load CSE, fuse-check folding, LICM; SLOTS in
layout guards; append arm, polymorphic typed-array probes, string
equality, native call route; advisory class hints; entry-param store
forwarding fix; TYPES as designed (M5b: any-type field claims,
`layout_field_types_in`, engine clears TYPES on every store, per-class
store checks).

Last full Octane (MIR, AOT) before the TYPES work, vs legacy:
crypto 17340/15322, deltablue 7180/6175, earley-boyer 11416/13209,
navier-stokes 19453/22979, pdfjs 18462/21115, raytrace 10687/11793,
regexp 2277/2293, richards 9401/11844, splay 8022/8258. After TYPES +
per-class stores (partial runs): raytrace ~8500, richards ~9050,
deltablue ~3300.
