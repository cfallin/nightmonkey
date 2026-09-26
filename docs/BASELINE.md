# NightMonkey baseline tier: design and plan (draft)

Status: **draft for review**. Nothing here is implemented. This replaces
the "GEN is today's `Dirty`-track BBV lowering" premise of `docs/MIR.md`
(§0, §5, §9) and makes `docs/MIR-GEN-SEAM.md` obsolete. §9 lists the
MIR.md changes that follow.

## 0. Summary

- **A new, deliberately simple compiled tier.** Each JSOp is lowered
  straight to Wasm. The only inline ops are trivial ones: constants,
  stack manipulation, local/arg/rval access, jumps and return.
  Everything else is one direct call to a runtime helper, with no ICs
  and no speculation.
- **The whole frame lives in NightStack memory**: callee, this, args,
  locals, env, arguments object, new.target, rval, and the operand stack.
  No JS value is carried in SSA between ops. GC rooting is therefore
  trivial, and the program state at any pc is just "the frame, plus the
  static operand depth at that pc".
- **It uses the existing AOT stack and ABI.** Frames are built in place
  on the NightStack, bodies have the `night_abi_sig2` signature, and
  interpreter entry, calls, exceptions and generator resume follow
  today's protocols. A baseline body can call, and be called by, legacy
  BBV bodies and the interpreter.
- **The frame format is the contract between tiers.** A MIR exit
  writes a baseline frame and resumes baseline at a pc. A MIR onramp
  reads a baseline frame at a loop header. MIR and baseline are
  separate Wasm functions, so there are no loop tokens, no peel
  funnels, and no combined-CFG reducibility problem. The MIR function's
  own CFG may be irreducible because of onramps into nested loops;
  waffle's reducifier handles that (§7).
- **Two gates, but only one lasting.** A script runs the MIR pipeline
  only if baseline supports every op in it and the MIR builder does too.
  Baseline is total: it supports every JSOp except `ForceInterpreter`
  (§6), including scripts that call eval (the eval'd code itself is
  interpreted). After that its gate is vacuous and the MIR
  builder's gate is the only real one.

## 1. What exists and what we reuse

Verified in code; see the investigation notes for file references.

- **NightStack**: a 2 MiB static array of boxed Values. `[base, top)` is
  traced as roots on every GC. Any helper that may GC takes `top` as its
  second argument, installs it with `SetNightTop`, and writes a boxed
  result to `*top` (`NightRuntime.h:32-44`, `NightStack.h`).
- **Helper ABI**: the manifest is `runtime/NightHelperList.h`, with 139
  `extern "C"` helpers whose signature strings are derived from their C++
  types. The Rust mirror is `Helpers` (`translate.rs:31`), resolved by
  name (`wasm/mod.rs:794`). A throwing helper returns 1 on success and 0
  with the exception pending on `cx`.
- **Helper coverage**: nearly every JSOp already has a generic lowering
  on the Dirty/GEN track that makes a single `rt_call` to a thin wrapper.
  Most wrappers call SpiderMonkey's own `*Operation`/`*Values`
  functions:
  - arithmetic, compares, typeof and instanceof;
  - property and element access, including super;
  - names and globals, env push/pop, calls, construct and spread;
  - literals, closures, class ops, iteration;
  - throw and catch/finally, generators/async, arguments and rest.

  Some helpers are resolved but never called by BBV, and fit a baseline
  well: `get_property`, `set_property`, `get_aliased`, `set_aliased`,
  `string`.
- **Body ABI**: `(cx, sp, argc, retval_out, script, new_target: i64) ->
  (err, eff)`.
  - Bodies sit in one contiguous block of the table; their sig1
    adapters sit exactly `n_bodies` slots above
    (`wasm/mod.rs:2020-2102`), and BBV callers rely on that offset. **A
    baseline body must be sig2 and placed in that block.**
  - `eff = FLAGS_ALL` is always safe.
  - The `script` parameter must be ignored; it is re-derived from the
    callee at `sp+0`, because a raw script pointer does not survive a
    compacting GC.
- **Entry**: the script's `externalTierWord` holds its adapter's table
  index. `EnterNight`, `EnterNightGlobal` and `EnterNightResume` build
  `[callee, this, args…]` at `frameBase()`. A word of 0 means the script
  is interpreted.
- **No deopt exists today.** Compilation is all-or-nothing per script,
  and no compiled frame is ever converted into an interpreter frame.
- **Decline set today.**
  - 17 opcodes: `BigInt`, `NonSyntacticGlobalThis`, `SetIntrinsic`,
    `EnvCallee`, the four eval ops, `DynamicImport`, `ImportMeta`,
    `GetImport`, the three explicit-resource-management ops,
    `ForceInterpreter`, `DebugCheckSelfHosted` and `Resume`.
  - Script gates:
    - size (128 KiB of bytecode);
    - generator combined with `arguments`/actuals;
    - `env_unsupported`: a non-Function/Global body scope, or a
      named-lambda environment;
    - an unmarked back edge.
- **waffle** reducifies an irreducible CFG by code duplication, with an
  explicit warning about exponential blowup (`backend/reducify.rs`).
  Baseline must be reducible by construction (§4) and asserts it.

## 2. The frame format (the inter-tier contract)

One layout, computed from the script alone (`FrameLayout::of(script)`),
shared by baseline, the MIR lowering, and the resume/exit protocols.
Unlike BBV's layout, **no slot is conditional on what the codegen
decided**, so every tier agrees on it by construction.

| Offset | Slot | Notes |
|---|---|---|
| `sp+0` | callee | global script: `PrivateGCThingValue(script)` (as today) |
| `sp+8` | this | |
| `sp+16+8i` | actuals, `i < max(argc, nargs)` | the caller builds these; the body pads formals with `undefined` |
| `vp` | `sp + 8·max(0, argc−nargs)` if the script needs actuals (arguments, rest, mapped args), else `sp` | today's rule |
| `vp+L+8j` | locals `j < nlocals` | `L = 16 + 8·nargs` |
| `vp+E` | env chain | always present (`undefined` if the script has no env ops) |
| `vp+E+8` | arguments object | always present |
| `vp+E+16` | new.target | always present |
| `vp+E+24` | rval | always present |
| `vp+E+32` | resume word | int32 Value; §4 |
| `vp+O+8k` | operand stack `k < depth(pc)` | `O = E + 40` |

**State at pc.** The frame together with `depth(pc)`, the static operand
depth computed by a forward pass over `nuses`/`ndefs`, fully describes
execution at a bytecode boundary:
- every slot below `vp+O+8·depth(pc)` holds a valid boxed Value;
- the env slot holds the env chain in effect at `pc`;
- the rval slot holds the current rval.

This is what a MIR exit writes and what a MIR onramp reads. Magic values
(TDZ, element holes, generator-closing) are ordinary Values here, so the
frame has no trouble with them. MIR's *types* still need a way to say
"may be magic" (§9).

**GC invariant.** At every may-GC call the published `top` is at least
`vp+O+8·d`, where `d` is the current depth including the op's inputs
(they stay rooted until the result is stored). The prologue initializes
every slot before the first helper call, as today.

## 3. Codegen

### 3.1 Per-op shape

For each bytecode basic block there is one waffle block, with no block
params except the entry's and the loop headers' resume word (§4). Each
op:
1. loads its inputs as i64 from the operand slots it consumes;
2. calls its helper as `helper(cx, top = vp+O+8·depth_before, inputs…,
   immediates…)`;
3. on a zero return, branches to its pc's exception landing (§3.3);
4. copies the result from `*top` into slot `depth_before − nuses`.

Only these are inline: constants (boxed immediates), `Pop`/`Dup`/`Swap`/
`Pick`/`Unpick`/`DupAt`/`PopN`, `Get`/`Set` for locals, args and rval,
`Goto`/`TableSwitch`, `Return`/`RetRval`, and the no-ops. Conditional
jumps call the leaf `to_boolean` helper and branch on its result.
**Nothing else is special-cased: not int32 add, not ToBoolean tag tests.**
Fast paths are a later, measured decision (§8, B5), not part of the
design.

### 3.2 Immediates and helpers

- **Reuse the existing `night_runtime_*` helpers as they are.** They take
  values by value and AtomTable ids resolved at compile time, the same
  AOT environment BBV uses.
- **Where a helper wants a cache or cell index**, pass the documented
  "none" value (`init_prop` takes `u32::MAX`, `new_object`/`new_array`
  take `cell = 0`) or add an IC-free variant. The `*_ic_miss`
  property helpers are replaced by the plain `get_property`/
  `set_property`.
- **Every JSOp lowers to a direct call to one NightMonkey helper.** There
  is no dispatch table, no function-pointer indirection, and no decoding
  at runtime. The compiler decodes immediates (atom ids, gcthing
  indices, scope indices, counts) and passes them as constants.
- **Ops with no helper yet get a new one** that takes decoded immediates
  and calls the same engine function the interpreter case calls:
  env setup for every scope kind, explicit resource management,
  modules, `Resume`, `BigInt`, and so on. A helper that needs the
  script (for a gcthing index, for example) derives it from the callee
  at `sp+0`, never from a raw script pointer.

### 3.3 Exceptions

The handler for each throwing pc is static, found by the try-note walk
BBV already does (`frame.rs:39-118`). Each throwing op's error edge goes
to a per-pc landing that:
1. calls `unwind_to(cx, top, sp, from_pc, handler_pc)`, a new helper
   modeled on the interpreter's `HandleError` path. It closes for-in and
   destructuring iterators and unwinds the env slot using the scope
   notes, so the compiler no longer computes env pops statically;
2. for a catch, jumps to the handler block, whose depth is the try
   note's `stack_depth`;
3. for a finally, pushes `[exception, stack, true]` via
   `get_exception_for_finally`, then jumps to the handler;
4. with no handler, returns `(1, FLAGS_ALL)`.

Error edges only go from inside a try range to its handler, so they
stay reducible.

### 3.4 Calls

- **Initially:** `Call`/`New`/spread go through `night_runtime_call` /
  `construct` / `spread_call`, with the callee frame built in place at
  the operand slots (`frame_base = vp+O+8·(depth−need)`), as BBV's
  generic path does. That is correct for every callee, whether
  interpreted, baseline, BBV, native or proxy, but each call re-enters
  through C++ (`JS::Call` → hooks → `EnterNight`).
- **Later (B5, measured):** a compiled-callee path. A classify helper
  (not an IC) returns the callee's body funcidx, which is then called
  with `call_indirect` sig2 at `funcidx − N`, the same path BBV's
  generic call uses.

### 3.5 Generators and async

A generator resumes through the same mechanism as a MIR deopt (§4).
- **Suspend:** `gen_suspend` copies locals and operands, as today. The
  saved layout is extended with the arguments-object and actuals slots,
  which lifts the "generator using arguments" gate.
- **Resume:** baseline keeps the existing `EnterNightResume` protocol:
  `this == JS_GENERATOR_CLOSING`, a descriptor staged at the locals, and
  `gen_restore`. It then resumes at the yield's successor pc.

The C++ side is unchanged.

## 4. Resume at a pc, reducibly

Three things need to enter a baseline body at a pc other than 0:
generator resume, MIR deopt, and a MIR throw-exit. A direct edge from
the entry to a pc inside a loop is a side entrance, which makes the CFG
irreducible. Instead, **resume dispatch goes through the loop headers.**
- Every loop header `H` gets a dispatch block `H_d`, which becomes the
  loop's header. The loop's entry and every back edge go to `H_d`. It
  takes one i32 param, the resume target: back edges pass `NONE` and
  outside entries pass the target.
- `H_d` branches (`br_table`) on the target:
  - `NONE` goes to `H`;
  - a target directly in `H`'s loop body goes to that pc's block;
  - a target inside a child loop `H'` goes to `H'_d`, still passing the
    target.
- The function entry does the same at the top level: fresh entry goes
  to the prologue; a resume goes to the target's block, or to the
  outermost enclosing loop's `H_d`.

Every added edge runs from a loop header to a block its loop already
contains, so the header still dominates its loop and every retreating
edge still targets a header. **The CFG stays reducible by construction.**
The cost is one compare per loop iteration in baseline code.

- **The resume set is static input.** Baseline-only compiles need only
  the generator resume points. A MIR-pipeline compile adds every MIR
  exit pc and throw pc: MIR is built first, and its exit set is passed
  to the baseline compiler.
- **The resume signal.** The signal fits within the sig2 ABI:
  - `argc` carries `ARGC_RESUME_BIT` (`0x4000_0000`); `ARGC_SEL_BIT`
    is already taken;
  - the frame's resume word holds the target and a mode, either
    `continue` or `throw`;
  - `throw` means "an exception is pending: land on this pc's
    exception landing";
  - generator resume keeps its own `this`-magic protocol (§3.5).

## 5. Integration

- **Code**: `compiler/src/wasm/baseline/`, containing `layout.rs`
  (`FrameLayout`, `depth(pc)`), `mod.rs` (the per-script driver),
  `ops.rs` (one exhaustive `match` over `JSOp`), `exc.rs` and
  `resume.rs`. It shares `Helpers`, `AtomTable` and the try-note walk
  with BBV but none of BBV's version or ctx machinery.
- **Driver**: the `translate_all` loop (`wasm/mod.rs:1979`) picks a tier
  per script. Baseline returns an ordinary
  `Outcome::Compiled { sig: night_abi_sig2, … }` with mostly empty patch
  lists, so table placement, adapters and `externalTierWord` patching
  are unchanged, and mixed calls between baseline and BBV bodies work.
- **Pipeline option** (replacing `MirMode`, which is not yet useful):
  `Options::pipeline`, one of:
  - `Legacy`: BBV, as today;
  - `Baseline`: baseline only;
  - `Mir`: MIR plus baseline. It falls back to baseline alone when the
    MIR builder declines, and to BBV or the interpreter per
    `--baseline-fallback` when baseline declines.
- **Coverage**:
  - Per-script diagnostics say which tier compiled each script, and
    which gate declined it with what reason.
  - A `--strict-coverage` option makes any decline outside an allowlist
    a compile error. That is how a jit-test lane *proves* it ran
    compiled code; `DESIGN.md` §12 notes that nothing enforces this
    today.
- **In-process option channel** (needed for the jit-test lane):
  - `night_inproc_build` gains an options string, parsed by the same
    Rust flag parser the `nightmonkey` CLI uses (moved into
    `options.rs`).
  - The shell gains `--night-options=…`, and `inproc-shell.sh` passes
    `$NIGHT_OPTIONS` through.
  - Today in-process hard-codes `Options::default()`.
- **Two functions per MIR script (MIR phase only)**:
  - `Outcome::Compiled` grows a list of extra bodies that are called
    directly and never through the table. The in-process blob carving
    and its position check must account for them.
  - The script's table entry is the MIR body's adapter.

## 6. Covering every JSOp

Baseline is **total**: it supports all 242 JSOps except
`ForceInterpreter`, which by definition means "run in the interpreter".
A script that calls eval is compiled like any other; the code eval
produces at runtime is interpreted, since the compiler is AOT only.

Beyond what BBV's GEN path already covers:

| Currently declined | Baseline plan |
|---|---|
| `BigInt` | helper: `script->getBigInt(pc)` |
| `NonSyntacticGlobalThis`, `EnvCallee`, `SetIntrinsic` | new helpers |
| `Eval`, `StrictEval`, `SpreadEval`, `StrictSpreadEval` | helper around the engine's JIT-facing direct-eval entry. The frame supplies the env chain, `this` and new.target, and the caller script comes from the callee. The eval'd script runs in the interpreter. A non-strict direct eval can add bindings, but only to the environment object, which baseline keeps in its frame slot, so no baseline invariant is at stake |
| `DynamicImport`, `ImportMeta`, `GetImport` | new helpers; module scripts are in scope (B4) |
| `AddDisposable`, `TakeDisposeCapability`, `CreateSuppressedError` | new helpers |
| `DebugCheckSelfHosted` | no-op |
| `Resume` | helper around the engine's generator-resume entry |
| gate: `env_unsupported` | env setup through one helper that mirrors the interpreter's function-environment initialization, for every body-scope kind and named lambdas |
| gate: generator + arguments | save the arguments object and actuals in the generator state (§3.5) |
| gate: size | lifted; baseline code is linear in bytecode size |

Tests are required to fail on an unclassified opcode (the capability
table `DESIGN.md` §12 asks for). For baseline this is simply the
exhaustive `match` with no wildcard.

## 7. What MIR looks like on top

- **Separate Wasm functions.** The MIR body and the baseline body are
  independent functions sharing the frame format (§2). The MIR body is
  the script's table entry.
- **Exit.** The MIR exit stores `this`, args, locals, rval and the
  operand stack into the frame (all `Val(⊤)`), writes the resume word,
  and then does one of two things:
  - if MIR was entered at function entry, it calls the baseline body
    with `ARGC_RESUME_BIT` and returns its result;
  - if MIR was entered by an onramp from baseline, it returns a DEOPT
    status to that baseline caller, which resumes itself.

  So a JS frame never uses more than three native frames, and there is
  no livelock (MIR.md §5.2's progress rule).
- **`exit.throw`** is the same, with resume mode `throw`.
- **Onramp.**
  - At a loop header's `H_d`, baseline may call the MIR body's onramp
    root for `H`, with backoff so failing guards don't cost a call per
    iteration.
  - If MIR returns normally, baseline returns the value. If it returns
    DEOPT, baseline resumes at the pc in the resume word.
  - The call uses the ordinary sig2 signature with baseline's own `sp`,
    so both tiers share one frame. `argc` carries `ARGC_ONRAMP_BIT`,
    and the resume word names the header.
  - A MIR body returns `err = 2` for DEOPT, next to 0 (ok) and 1
    (exception). Only baseline's onramp call sites can see a 2: a MIR
    body entered normally resumes baseline itself.
  - There is one MIR Wasm function per script, however many roots it
    has. Its entry block tests `ARGC_ONRAMP_BIT` and dispatches with one
    `br_table` to the onramp roots, or falls through to the entry root.
    Each root `O_H` runs its guard chain and jumps to the preheader
    `P_H`.
- **Reducibility.** MIR has no reducibility invariant.
  - An onramp into a nested loop is a side entrance into every
    enclosing loop: the inner preheader `P_H2` lies inside the outer
    loop's body.
  - The lowering emits the MIR CFG as-is. waffle's backend reducifier
    then duplicates the partial first iteration from the side entry to
    the enclosing loop's header, where the copy rejoins the original.
  - Whichever block the reducifier picks as header, the steady-state
    loop exists once. The choice only decides which fragment of one
    iteration is duplicated, which is a code-size question.
  - MIR still declares its loops (header, preheader, from the bytecode
    loops) for LICM, guard hoisting and the validator's preheader rule.
    A loop body is every block that reaches a latch without passing
    through the header, which is well-defined even with side entries.
  - Which headers get onramp roots is policy. Every outermost loop gets
    one, since no duplication is needed there. Inner loops get one
    subject to a code-size limit, informed by the measurements in
    step W (§8).

## 8. Plan

Each step builds, passes `cargo test`, and leaves `Legacy` codegen
byte-identical.

- **B0. Contract and plumbing.**
  - `FrameLayout` and `depth(pc)`, with unit tests (depth at every try
    handler matches the try note's `stack_depth`).
  - `Options::pipeline`, the per-tier coverage diagnostics and
    `--strict-coverage`.
  - The in-process options channel (FFI string, shell flag,
    `inproc-shell.sh`).
  - Write down the frame format and resume protocol in this document as
    final.
  - **Done** (`wasm/baseline/layout.rs`, `wasm/tier.rs`):
    - The flags are `--pipeline legacy|baseline|mir`,
      `--strict-coverage` and `--dump-tiers`, parsed by
      `Options::apply_flag` for both the CLI and the in-process option
      string.
    - The in-process channel is `NIGHT_OPTIONS`, passed through
      `inproc-shell.sh` to the shell's `--night-options` and on to
      `night_inproc_build`. Under strict coverage, a failed in-process
      build aborts.
    - `baseline::translate_script` checks the frame contract on every
      script (layout, depths, try-note agreement) and then declines
      with "not implemented" until B1.
- **B1. Straight-line baseline.**
  - Ops: prologue, constants, stack ops, locals/args/rval, arithmetic
    and compares via helpers, `to_boolean` branches, loops, return,
    generic calls and construct.
  - Scripts using any other op decline.
  - Gate: jit-tests with `pipeline=baseline` pass (declines fall back
    to the interpreter), and the coverage census shows real scripts
    compiled.
- **B2. Exceptions.** `unwind_to`, catch/finally landings and throw.
  Gate: try/catch/finally jit-tests pass under strict coverage for the
  scripts that use them.
- **B3. Parity with GEN coverage.** Properties, elements, names, env,
  closures, literals, classes, iteration, spread, arguments/rest,
  generators/async (resume dispatch, §4). Gate: baseline declines only
  the §6 set.
- **B4. Every JSOp.** The §6 table: new helpers, then lifting the
  env/generator/size gates. Gate: the full jit-test lane under
  `pipeline=baseline --strict-coverage`, whose allowlist is only
  scripts containing `ForceInterpreter`. Record the performance
  datapoint against the interpreter-only lane and legacy BBV.
- **B5 (optional, measured).** The compiled-callee call path (§3.4),
  then any inline fast path whose win shows up in the numbers.
- **Then MIR, revised (§9):**
  - M0b: the small M0 follow-ups of §9 (the `magic` tag, the rval
    operand, declared loops);
  - M1: MIR → its own waffle function, exits and throws into baseline
    via resume, with forced-exit tests;
  - M2: the builder, under `pipeline=mir`, with a stress mode that fails
    guards;
  - M3: onramps from baseline loop headers, with the onramp-root policy
    of §7;
  - M4 onward: as in MIR.md.
- **W. waffle's reducifier, driven by M3 data.** Nothing here starts
  before M3 has produced real onramp-shaped MIR.
  - Measure the reducifier on that output: duplicated blocks against the
    minimal partial iteration, the max-SSA cut's added params, and
    compile time.
  - Only if the numbers call for it, change waffle, which is currently
    consumed from crates.io; use a path or git dependency until a
    release. Candidate changes known today:
    - loop bodies from a loop-nesting forest instead of RPO intervals,
      which over-approximate loops so that non-loop blocks get copied
      instead of shared;
    - a duplication budget that fails cleanly, so MIR can drop onramp
      roots and retry;
    - CFG-shape tests and differential checks with waffle's interpreter.

## 9. Consequences for MIR.md and M0

- **§0, §5, §9: GEN becomes baseline.**
  - Exits land by resume (§4), not by jumping to a GEN version.
  - §5.4 (loop tokens and reducibility) is replaced by §7's
    reducibility rule: no invariant in MIR, and reducification in
    waffle.
  - The GEN seam is gone, and `docs/MIR-GEN-SEAM.md` is retired.
- **The three open seam problems resolve:**
  1. *Magic values:* the frame holds them. MIR's `TagSet` still needs
     a `magic` tag so that `Val(⊤)` includes TDZ values. Nothing
     unboxes it, and `guard.tags` removes it. This is a small M0
     change.
  2. *rval:* it is a frame slot. `exit`/`exit.throw` and onramp roots
     gain an `rval` operand (a small M0 change). The env slot is fixed
     in v1, since MIR declines env ops.
  3. *Throw-block params after rooting:* each exit lowering stores its
     own current waffle values into the frame, so no shared waffle
     block needs params.
- **The validator.** The "irreducible" structure error goes. Loops
  become declared, and the preheader check keys off the declared loops
  instead of dominance-inferred back edges. Dominance over multiple
  roots does not need reducibility and stays as it is.
- **Nothing else in M0 changes.** The types, ops and text format
  stand.
- **§11 (v1 scope):** "declined" now means baseline alone, not legacy.
- **§13:** replaced by §8 above.

## 10. Decisions

1. **Separate Wasm functions** for MIR and baseline, with resume through
   loop-header dispatch (§4, §7), rather than one combined body. MIR's
   own irreducibility, from onramps into nested loops, is left to
   waffle's reducifier and measured in step W.
2. **The resume signal** is an argc bit (`ARGC_RESUME_BIT`, and
   `ARGC_ONRAMP_BIT` for onramps into MIR) plus the frame's resume
   word.
3. **Baseline frame slots are unconditional**: env, arguments object,
   new.target and the resume word are always present. The layout is a
   function of the script alone. This is for baseline's sake: the
   optimizing tier still uses the AOT stack only for GC rooting, and
   only when necessary. A MIR body does not initialize a baseline frame
   in its prologue; it writes the complete frame only when it exits
   (MIR.md §5.1).
4. **Each JSOp lowers to a direct call to one helper**, with immediates
   decoded at compile time (§3.2). There is no interpreter-like
   indirection.
5. **A script declined in `Baseline` mode is interpreted**, not
   compiled by BBV, so the lane measures baseline alone.
6. **Baseline is total** except for `ForceInterpreter` (§6). Scripts
   that call eval are compiled, and the eval'd code is interpreted.
   Module ops are in B4.
