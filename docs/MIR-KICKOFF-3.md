# MIR tier: kickoff for the next session (3)

Branch `cfallin/mir`. Read docs/MIR.md (§2.3 and §4.6 status blocks),
docs/MIR-AUDIT.md (the design as specified vs as built) and
docs/MIR-PARITY.md first. The working rules of docs/MIR-KICKOFF-2.md still
hold (build to the design and to legacy parity, no hill-climbing, facts
fixed / kills exit, commit and push as you go, never the shared stash, lanes
on a fresh `js-inproc`), plus: there is no "pre-existing" failure; every
TEST-UNEXPECTED line in a lane is ours to fix (`run-jit-tests.sh` now counts
them, including the expected-error mismatches jit_test.py itself ignores).

## Where things stand

Octane (MIR, AOT, best of 2; legacy in brackets):

| | MIR | legacy |
|---|---|---|
| crypto | 17765 | 15235 |
| deltablue | 8397 | 6222 |
| earley-boyer | 12108 | 13278 |
| navier-stokes | 20357 | 23299 |
| pdfjs | 17956 | 21010 |
| raytrace | 10804 | 12321 |
| regexp | 2239 | 2262 |
| richards | 9253 | 11819 |
| splay | 8063 | 8434 |

After the completeness batch (4c92af5, 278c691, cde41f6; same method):
crypto 17216, deltablue 8205, earley-boyer 12014, navier-stokes 19866,
pdfjs 17903, raytrace 10887, regexp 2262, richards 9274, splay 8086, all
within noise of the table above. An A/B against the build before the
batch shows crypto and navier-stokes equal under the same conditions.

At the start of the last session deltablue was 3438, crypto ~10200, pdfjs
~12600, raytrace ~8900: those were TYPES losses (objects reaching OPT
without the bit, so entry guards failed and methods ran in baseline). The
exit and guard censuses of richards, deltablue, crypto, earley-boyer, splay
and navier-stokes are now essentially empty; the remaining gaps to legacy
are code quality, not deopts.

What landed (see the commit messages for detail):

- TYPES maintenance: early publish before calls in construction
  (`ctor_publish`), 4-hop add replay, vouched helper stores (MIR's
  `field_types`, baseline's `field_classes`, and the helper's own check of
  the field's claim, `NightStoreConforms`, carried in the layout table),
  plain slot writes and plain adds keep TYPES (`PlainStore`,
  `AutoVouchedStore`), snapshot objects stamped with any row of their clump
  and TYPES validated from the image, baseline's stamps share MIR's any-type
  rule, element stores owe the array stamp's duty only on arrays.
- The constructing type (MIR.md §2.3), for inlined constructs: `guard.ctor`,
  `init_field`, `publish_layout`, callee builds keyed by a constructing
  `this` (`callee_ctx`), `this_out`/`ctor_hint` re-guards.
- `T.call(thisArg, ...)` inlined (`call_forward`).
- Completeness: `typeof globalName`, `new.target`, for-in, try/finally.
- Diagnostics: `--mir-exit-census` also counts guard failures by guard
  (kind 92) with a layout guard's miss reason (93), TYPES drops under
  construction (94), stamps without TYPES (95); `NIGHT_CENSUS_TRACE=N`
  prints exits, guard failures (with the failing object's word and fields),
  epoch bumps, unvouched helper stores and constructing demotions in
  order; `--dump-tiers` names each script.

## Next

1. **Code quality vs legacy** (richards -22%, pdfjs -15%, navier -13%,
   raytrace -12%, earley -9%). No exits to blame: profile (cache the module
   with `wasm-jit-runner --cache-dir`, else wasmtime's compile dominates the
   profile; `WJR_PERFMAP=1 perf record`; map `function[N]` via `--stats`
   `night: body sid#S func N` and `--dump-tiers` names) and compare against
   legacy's code for the same scripts. Candidates from the audit
   (docs/MIR-AUDIT.md ranked table): `length` ops as generic `js.getprop`,
   globals as generic ops (no `load_gname`/binding facts), guard hoisting
   (§10.2) for layout guards in loops, `load_field` as a terminator (never
   hoisted), facts dying at calls (effect summaries), polymorphic call
   dispatch cost (guard.script chains), numeric ranges (overflow checks,
   int-first speculation exits such as crypto's `Mul` in bnpInvDigit).
2. **Completeness**: done except generators and async functions (MIR.md
   M5i): class constructors (base and derived), for-of and spread, lexical
   and `with` scopes, names through the chain, direct eval, and the long
   tail all compile. Re-census with the scratch pattern (`--dump-tiers`
   over every jit-test, first decline per script) after changes.
3. **The constructing type beyond inlined constructs**: a constructor body
   compiled standalone still sees an untyped `this` (the dynamic early
   publish covers methods called after completion). An entry
   `guard.ctor K, 0` where the analysis says every caller constructs is the
   next step; `new_object K` for literals is the audit's item 4.
4. **Engine hook**: `JS::ExternalObjectStore` passes no slot, so a store to
   a slot outside the object's layout (defineProperty's accessor slots, an
   extra property) drops TYPES; the hook needs the slot (a change to the
   firefox fork's ExternalCompilerHooks) to keep it there.

### Generators and async functions: a design extension to decide

They are the one decline left from the jit-test census (476 scripts),
and the current design cannot take them without an extension:

- A resumed generator enters its body at a `yield`'s landing, through
  baseline's resume dispatch (`EnterNightResume`, `gen_restore`, the
  landing's `[sent value, generator, resume kind]`). MIR has entries
  only at the function entry and at loop-header onramps (§5.2).
- Within the design as written, MIR could compile a generator by making
  every `InitialYield`/`Yield`/`Await` an exit to its own pc (baseline
  suspends) and letting baseline onramp back at loop headers. Each
  iteration of a `for (…) yield x` loop would then pay an exit, a
  baseline resume and an onramp. The onramp backoff after exits would
  soon turn the onramp off, so the loop would run in baseline anyway.
  This buys nothing, and I did not build it.
- **The extension I would propose:**
  - (a) `gen.suspend k` in MIR: write the frame through, as an exit's hub
    does, then baseline's `gen_suspend` over the frame's locals and the
    operand stack at the yield's depth, then return the yielded value.
  - (b) Resume landings become onramp roots. Their operands are the
    frame (restored by `gen_restore`) plus the resume protocol's three
    stack values, guarded like any onramp's.
  - (c) The MIR body gets a resume entry, as baseline's: `EnterNightResume`
    enters the script's table entry, which is the MIR body, and a resume
    word selects the landing's root.

  (a) and (b) reuse the exit and onramp machinery. (c) is the new part:
  a generator's MIR body takes the resume fork that baseline's has today.
- **Decision needed:** whether generator bodies are worth an entry kind
  beyond §5.2's function entry and loop headers. Octane has none (its
  async code is in the harness only); the jit-tests have many.

### Richards: where the gap is

A profile of AOT richards under MIR puts 38% in `Scheduler.schedule`
(sid 218), then the task `run` methods (sids 154, 173, 177, 167). The
two tiers split the call chain schedule → `TaskControlBlock.run` (sid
189) → `this.task.run(packet)` (four task scripts) at different places:

- bbv declines `TCB.run` into schedule (its site cap), and compiles
  `TCB.run` standalone with all four task `run`s spliced in
  (`--dump-bbv`: `inline-splice sid#189 pc 171 target#154/167/173/177`).
- MIR inlines `TCB.run` into schedule and then cannot afford the four
  tasks under its per-function budget (`MAX_INLINE_TOTAL_INSTS`, 6000
  spliced MIR instructions), so every task run is a call.

Both take one call per schedule iteration; the difference is where. bbv's
task bodies are spliced under `TCB.run`'s dispatch, with its facts about
the task. MIR's are separate bodies entered through a four-way script
guard chain and a real call, with their own entry guards. Pricing
the budget as bbv does (bytecode bytes per target,
`MAX_INLINE_POLY_BYTES` for a poly site, transitive closure cost), or
preferring the inner poly site to the outer mono one, is the parity
question. It changes §5.5's policy, so it wants a decision. The method
loads in that loop (`isHeldOrSuspended`, `run`, `link`) are
`js.getprop`s with their IC inline, each a fence for layout facts.
