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
2. **Completeness**: census the declines across jit-tests (`census.sh`
   pattern from the previous kickoff) and implement the frequent ones:
   class constructors, for-of / iterator protocol, spread, `super`, lexical
   environments, non-global names, eval.
3. **The constructing type beyond inlined constructs**: a constructor body
   compiled standalone still sees an untyped `this` (the dynamic early
   publish covers methods called after completion). An entry
   `guard.ctor K, 0` where the analysis says every caller constructs is the
   next step; `new_object K` for literals is the audit's item 4.
4. **Engine hook**: `JS::ExternalObjectStore` passes no slot, so a store to
   a slot outside the object's layout (defineProperty's accessor slots, an
   extra property) drops TYPES; the hook needs the slot (a change to the
   firefox fork's ExternalCompilerHooks) to keep it there.
