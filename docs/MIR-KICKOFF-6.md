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
- **Truncation demand over SSA** (e490c14, `opt::trunc_demand`): an
  int32 add or sub whose result only reaches ToInt32 (bit ops, shifts,
  other such sums, through locals and block params) is rewritten in the
  MIR from `.ovf` to `.wrap`. A magnitude bound (units of 2^31, cap
  2^53) and exit/entry-state uses keep it exact. code-load's
  jenkinsHash micro 200 -> 27 ms.
- **Computed-name reads** (726983c, `KeyedRead`): `obj[k]` with a key
  that may be a name reads the receiver's named fields and escapes the
  arguments (not `this`) of the functions among them.

Int32 overflow in practice (the old item 1, withdrawn): across all
thirteen Octane sources MIR takes overflow exits only in code-load's
jenkinsHash, a hash mix whose sums go out of range and come back
through bit ops. Truncation demand removes the in-loop ones; the last
(a returned sum) is a real double. The 2.6x/12x accumulator slowdowns
were synthetic micros. The analysis's intervals cannot tell an
overflowing accumulator from one that stays in range (both
`int32|double`, I53), so they are no help there; they would help the
other way (dropping checks on bounded counters), which needs
post-compare refinement first.

## Next: analysis-chosen slot layouts (the main task)

Designed with the owner at the end of session 6; build it with fresh
context. It serves both backends (the layouts are analysis facts).

### Problem

A constructor with branchy field writes (pdfjs's `Font`: an early-return
path writes `loadedName, loading` right after `type`, the main path
`differences, widths, ...`) gets one layout row in bytecode first-write
order, and every object whose path differs puts a field in another slot
than the row says: SLOTS clears (`SlotsAddMismatch4`), and every
`{types, slots}` guard on it after that exits (about 58k exits in pdfjs).
The engine assigns slots in insertion order, so no single row can serve
every path. Instead, let the analysis choose each field's slot, and put
the value there whatever the insertion order. The semantically visible
property order is unchanged (the shape records insertion order); only
physical slots differ: adding `x y z` and `x z y` both map x->0, y->1,
z->2.

### Principle

Build the SpiderMonkey side the way the external-compiler hooks were
built: generic in principle, usable by any external tier that manages
object layouts itself, with the choices delegated to the embedder's
runtime and none of NightMonkey's specifics (classes, layout tables,
stamps) encoded in the engine. Done right, it could go upstream. So the
engine offers mechanism -- a shape with a chosen slot, a flag that says
slot order is not insertion order, a correct span -- and NightMonkey's
runtime supplies the policy.

### Design (owner's)

- **Slot choice is a function of (parent shape, key).** The analysis
  emits a per-class table name -> slot (a field on no path gets no slot).
  The NightMonkey runtime memoizes (parent shape, key) -> new shape in its
  own table, keyed by class ID too only if the implementation shows two
  classes can pick different slots from one shared parent (point 7);
  SpiderMonkey knows nothing about classes.
- **SpiderMonkey interface** (in the firefox fork, as APIs/hooks):
  - create a "custom-slot shape" from a parent shape, a new property
    (key, flags) and a slot number; then install it on an existing object
    or allocate a new object with it;
  - a **PERMUTED** bit in the shape header, set on every shape so created
    and inherited by every shape added on top of one: it turns off engine
    fast paths that assume shape order == slot order;
  - the shape's true slot span (max slot + 1) stored at creation
    (point 1).
- **Generic adds** (SpiderMonkey's own path, not NightMonkey's) on a
  PERMUTED shape allocate the stored span, O(1). (The owner's first
  design had a PERMUTED_PREFIX bit to get generic adds back to O(1) after
  an O(n) walk for the max slot; with the span stored, it is likely
  unnecessary. Keep it only if some consumer turns out to need "the last
  property holds the top slot".)
- **ICs:** SpiderMonkey's own JIT add stubs simply do not attach on a
  PERMUTED shape (no native Baseline/Ion in Wasm, and no plan to run
  Portable Baseline or a native NightMonkey backend alongside other
  tiers). Keep the check anyway, for safety.

### Points to settle while building

1. **Store the slot span; don't recompute it.** `slotSpan` for a shared
   shape is last property's slot + 1 (`vm/PropMap.h:670-692`), cached in
   10 bits of `immutableFlags` (`vm/Shape.h:538-586`; above 1023,
   `slotSpanSlow` recomputes it the same way). GC marking and tenuring
   trace `[0, slotSpan)` constantly (`gc/Marking.cpp:1412-1417,1655`,
   `gc/Tenuring.cpp:843`), so a PERMUTED shape needs its true span
   (max slot + 1) at creation, in that cache and in `slotSpanSlow`.
   The generic add then takes the stored span (the max is computed once
   per shape, at creation). `SharedPropMap::addProperty` computes the next
   slot from the map's last property (`vm/PropMap.cpp:250`): give it the
   shape's span instead. That also covers hole fills, where a NightMonkey
   add puts a property below the span and the last property is then not
   the top slot.
2. **Skipped slots must hold valid values.** Raising the span past
   skipped slots must initialize them to undefined (the GC traces them):
   `setShapeAndAddNewSlots(newShape, oldSpan, newSpan)`
   (`vm/NativeObject-inl.h:541-579`) does exactly that; the single-slot
   `setShapeAndAddNewSlot` asserts span+1 and must not be used. A hole fill
   writes an existing, initialized slot. New objects allocated with a
   permuted shape get every slot below the span initialized.
3. **A slot must be free before NightMonkey claims it.** The generic path
   appends at the span, which may be a slot the table reserves for a name
   not yet added. A generic add clears only SLOTS (`NightAddPropCheck`,
   and only when a predicted name lands elsewhere; the class word stays),
   and that is all that is needed, since the slot correspondence is what
   breaks. So: a generic add onto a PERMUTED shape clears SLOTS, and
   NightMonkey's custom add checks that its target slot is a hole in the
   object's current shape, else falls back to the generic add (SLOTS then
   clears).
4. **Caches keyed by (key, flags) only.** Property maps are already keyed
   by the full `PropertyInfo` (slot included: `vm/PropertyInfo.h:173`,
   `SharedChildrenHasher`, `InitialPropMapHasher`), so x->1 and x->2 from
   one parent are distinct maps and shapes. But the per-shape add cache
   (`ShapeCachePtr`, `ShapeForAddHasher` in `vm/Shape.h:143-157,555-570`,
   filled at `vm/Shape.cpp:426-439`) and the megamorphic set cache
   (`vm/Caches.h:346-376`) are keyed by key and flags only: custom-slot
   shapes must never be entered in them (NightMonkey memoizes its own), and
   the megamorphic cache must not be filled for a PERMUTED shape.
5. **Fast paths that copy slot i to slot i, to refuse on PERMUTED** (only
   debug asserts guard them today, so a miss corrupts values silently in
   release):
   - `Object.assign`'s fast path and `PlainObjectAssignCache`
     (`builtin/Object.cpp:860,895-1036`; it also sets `newSpan =
     props.length()`);
   - `NewPlainObjectWithPropsCache` (`vm/PlainObject.cpp:210-256`,
     JSON.parse and friends): slot i must be property i;
   - `CompactPropMap` holds slots <= 255 in 8 bits and truncates silently
     in release (`vm/PropertyInfo.h:97-133`): fall back to a normal map for
     larger slots;
   - remove-last / `setShapeAndRemoveLastSlot` (`vm/Shape.cpp:842-860,
     945-956`) assume the removed property had the top slot;
   - the monotonic-slot debug check (`vm/PropMap.cpp:1314-1321`) and the
     `slot == slotSpan` asserts in `addPropertyWithKnownSlot`
     (`PropMap.cpp:295`) and `setShapeAndAddNewSlot`.
   Safe as they are: dictionary conversion (keeps each slot and the span),
   `delete` of a non-last property (goes dictionary), lookups and iteration
   (by `prop.slot()`), swap and object-state recovery (copy `[0, span)`
   with the same map).
6. **Hook placement.** The natural point is `NativeObject::addProperty`
   after `maybeConvertToDictionaryForAdd` (`vm/Shape.cpp:343`), before the
   add-cache lookup; `propertyAdded` already fires after the slot is
   chosen (`Shape.cpp:351-355,406-410`). But NightMonkey's own adds (the
   compiled set ICs' add-transition replay, `night_runtime_set_property`,
   construct paths, baseline's helpers) should call the custom-shape API
   directly with the table's slot, so objects built partly in baseline get
   the same layout. Object literals take template shapes built outside
   `addProperty` (`frontend/ObjLiteral.cpp:328-365`); leave them
   sequential unless the analysis wants literal layouts permuted too.
7. **Classes that share shapes.** Constructor instances of different
   classes differ in prototype, so in BaseShape, so they never share a
   shape; literal sites (same `Object.prototype`) do. NightMonkey's own
   add-transition caches (`gSetAdd`, the site rows, the megamorphic
   table) are keyed by (old shape, key). Let the implementation decide:
   if no two classes' tables can choose different slots from one shared
   parent, (parent shape, key) is enough; otherwise key the memo and
   those caches by class too.

### Plan

1. SpiderMonkey (generic, per the principle above): the stored span for
   PERMUTED shapes; the PERMUTED bit; the custom-slot-shape API (with hole
   check and undefined-fill); the generic add on PERMUTED; refusals in the fast paths and caches of
   point 5 and in `tryAttachAddSlotStub` (`jit/CacheIR.cpp:5566-5695`).
   Engine-level tests: add orders `x y z` / `x z y` / generic adds on top /
   delete / dictionary conversion / Object.assign / JSON round trips / a
   GC with holes present.
2. Analysis: a per-class slot table (the union of the constructor's
   fields over its paths; a field's slot is fixed for the class), in the
   facts next to the layout rows; the stamping and SLOTS logic read slots
   from it.
3. Runtime: the (parent shape, key) -> shape memo; NightMonkey's add
   paths call the custom-shape API; `NightAddPropCheck` checks against
   the table; point 3's SLOTS clears.
4. Both backends consume the table's slots; measure pdfjs's Font exits
   (58k now) and the suite on both backends with the prof6 tooling.

## Open

1. **pdfjs: methods reached only by computed-name dispatch get no
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
2. **`instanceof` narrowing.** Neither backend narrows an operand to
   object on the true branch; only the ordinary-function arm of
   `instanceof_arms` could (a custom `Symbol.hasInstance` may answer
   true for a primitive).
3. KICKOFF-4 item 4 (splay GC) and KICKOFF-5 item 1 (earley-boyer frame
   traffic) stand.
