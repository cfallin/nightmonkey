# MIR tier: kickoff for the next session (6)

Branch `cfallin/mir`. Read docs/MIR.md, docs/MIR-AUDIT.md, docs/MIR-PARITY.md
and docs/MIR-KICKOFF-5.md first; their working rules still hold. Two
measurement rules added this session (details in the placement-sweeps
memory note; the tooling is `~/work/nm-mir-scratch/prof6/ab2.sh` and
`robust.py`):

- **Shuffle which core each run lands on.** An A/B that dealt runs to
  cores round-robin in variant order pinned each variant to the same
  cores, and the core bias read as +3-9% everywhere. That run's numbers
  went into f2d250c's message; they are wrong (the change is neutral).
- **Drop interference outliers.** The machine has sporadic outside slow
  periods that halve whole runs, longer than one job; best-of-2 does not
  remove them. Drop scores under 80% of the benchmark's all-variant
  median, and say how many were dropped. Compile everything first, then
  run.

## Landed

- **The analysis reaches its fixpoint** (f2d250c). The debug-assertion
  failure (likelier/engine.rs:685, MAX_CELL_CHANGES on crypto, pdfjs and
  react) was a no-op raise counted as growth. Behind it, the solve was
  not a fixpoint: re-evaluating every constraint afterwards changed 173k
  cells on crypto, 19k on react. Four causes, all fixed: a
  non-idempotent array join (`One(a)` met itself as `ClassAny`), a
  region's element writes not reaching members' `One` readers, the
  context budget checked before the memo in `Ctxs::push`, and
  region membership / dispatch-table state read without subscribing.
  `--verify-fixpoint` checks it, and debug-assertion builds always do
  (fatal). All thirteen Octane sources are exact fixpoints now. Octane
  neutral within noise.
- **Onramp backoff** (29fcbc3). An onramp attempt that exits at the
  header it entered made no progress; baseline now doubles the wait
  (to 1024x). The overflowing-accumulator micro (KICKOFF-4 item 6):
  1301 -> 666 ms; legacy 109 ms.
- **No IC receiver tag test on an object-typed receiver** (c4ba052), as
  bbv's `is_object_only`. Neutral.
- **Vouched defineProperty** (35f5821): the canvas context's accessor
  defines no longer drop its TYPES. pdfjs exits 322k -> 196k, pdfjs
  +1.5%.

## Open

1. **Overflowing int32 accumulators (KICKOFF-4 item 6): a design
   question.** MIR.md §8 has int32 ops exit on overflow, and block entry
   types come from a fixpoint that never sees the F64 an overflow would
   make, so such a loop leaves MIR for good and finishes in baseline,
   which runs it at about 16 ns/iteration against legacy's 3.6 (legacy
   also leaves OPT here, but its GEN track is itself versioned). Either
   an overflow continues in f64 (legacy's side arm, a change to the
   documented rule), or baseline's double arithmetic gets faster
   (operand stack in frame memory, boxing, the element read). Owner's
   call.
2. **pdfjs Font (L53) loses SLOTS on every main-path instance**: about
   58k exits (the `{types, slots}` entry guards of Font methods). Font's
   constructor has early returns; the `properties.ignore` path writes
   `loadedName, loading` right after `type`, the main path `differences,
   widths, ...`. The layout row is one list in bytecode first-write
   order, so every main-path object puts `differences` where the row
   says `loadedName` (runtime `SlotsAddMismatch4`). The runtime already
   has clumps (a shared prefix, extension rows, the prefix-advance
   restamp); the analysis would need per-path rows from the
   constructor's CFG (`CtorRowExpander` walks a linear event list
   today).
3. **pdfjs: methods reached only by computed-name dispatch get no
   argument evidence.** A computed read whose key may be a name now
   reads the receiver's named fields and escapes the arguments of the
   functions among them (`KeyedRead`, landed). It does not reach
   pdfjs's dispatch yet: `executeOperatorList`'s key `fnName` is Empty,
   because `fnArray` arrives through pdfjs's message handler and promise
   callbacks and the analysis carries no value across them. So
   `setHScale`'s formal is still Empty and `textHScale` still int32-only
   (about 15k int32-unbox exits each in the context's `scale`/
   `translate` and the `ctx*` wrappers). The next step is that upstream
   gap: values delivered through callbacks read as Empty rather than
   unresolved.
4. **`instanceof` narrowing.** Neither backend narrows an operand to
   object on the true branch; only the ordinary-function arm of
   `instanceof_arms` could (a custom `Symbol.hasInstance` may answer
   true for a primitive).
5. KICKOFF-4 item 4 (splay GC) and KICKOFF-5 item 1 (earley-boyer frame
   traffic) stand.
