# NightMonkey MIR: draft design (rev 6)

Status: **draft for iteration**. M0 (the IR core) is implemented in
`compiler/src/mir/`. See `mir-tier.md` for the motivation. Rev 6
replaces GEN (the BBV `Dirty` track) with the baseline tier of
`docs/BASELINE.md` as the deopt destination and onramp source.
Optimizations that must work are in §10, decisions are logged in §12,
and the implementation plan is `docs/BASELINE.md` §8.

## 0. Summary

- **MIR represents OPT only.** The *baseline* tier (`docs/BASELINE.md`)
  is the deopt destination and the source of onramps back into MIR.
  Baseline keeps the whole JS frame in NightStack memory, and that
  frame format is the whole interface between the tiers. MIR and
  baseline are separate Wasm functions.
- **The IR is SSA over a CFG with typed blockparams.** There are no
  frame slots in MIR. Locals, args, `this`, and the JS operand stack are
  all SSA values. The only NightStack traffic MIR code produces is GC
  rooting across may-GC ops, and argument frames for calls. Both are
  introduced while lowering, not in MIR.
- **Invariants are structural.**
  - Per-object facts live in the type of the object reference.
  - Global facts (fuses and the like) are *ghost values*. Checking ops
    produce them, and the ops that rely on them consume them.
  - *Invalidation fences* say which types may not be live across them.
    *Weakening ops* (or edge subtyping) are used to comply.
  - A validator checks all of this. There is no implicit flow typing.
  - Every kill is either predicted by likelier or dynamic (a dirty
    edge). This is asserted through validator-only prediction witnesses
    (§4.5).
  - The builder guards killable components locally at each use. Guard
    folding and hoisting (§10) merge those guards afterwards.
- **A type is (representation × refinement).** "NaN-boxed, known int32"
  and "raw i32" are different types. Unboxing the former is infallible;
  unboxing an arbitrary Value is a fallible guard.
- **A fallible op is a two-target terminator.** The failure target
  usually exits to baseline, but may instead run an inline slowpath and
  merge back.
- **Everything crossing the MIR/baseline boundary is `Val(⊤)`:** boxed,
  with no other known type.
  - **An exit is a variadic op** carrying the resume PC plus every
    `this`/arg/local/rval/operand-stack value. Each value is first
    upcast to `Val(⊤)` (infallible boxing and forgetting).
  - **Every loop header can accept an onramp.** An onramp enters through
    an *onramp entry block* that takes the same full state as `Val(⊤)`.
    The block runs ordinary MIR guards, then either re-deopts or jumps
    into the loop's preheader.
  - Deopt writes the baseline frame and resumes baseline at the pc. An
    onramp reads the frame back into SSA.
- **MIR is the sole input to the backend.** Everything a lowering needs
  is attached to the op, or lives in MIR-level tables the ops reference.
- **Loads and stores carry access descriptors** (field or element, and
  an alias region). This supports classical load/store optimization
  without a functional memory model.
- **The effect-flags word is implicit, flow-carried state.** It is
  derived from op effects and threaded during lowering.
- **Lowering handles GC rooting.** An MIR-value-to-waffle-value map is
  spilled and reloaded around may-GC ops. It does not appear in MIR.
- **MIR has no reducibility invariant.** An onramp into a nested loop
  side-enters every enclosing loop. MIR declares its loops explicitly,
  and waffle's backend reducifier makes the lowered function reducible
  (§5.4).

## 1. IR structure

The MIR lives in `compiler/src/mir/`. It is a separate IR from waffle's
Wasm-level ops, and we lower *into* waffle.

- **Module-level tables** (part of the MIR input, referenced by id):
  - layouts: key to fields, slot, prims, range;
  - snapshot objects;
  - atoms;
  - fuses and bindings;
  - scripts.
- **A `Func`** holds blocks, values, types and per-op attachments, in
  entity arenas.
- **Blocks** have typed params, and terminator targets carry args. A
  value is a blockparam, an instruction result, or a ghost value.
- **Per-op attachments** hold everything the lowering needs that is
  neither an operand nor derivable from operand types:
  - IC cell and accessor-cache addresses;
  - call-cell addresses;
  - candidate call targets (for later inlining);
  - the typed-site field mask;
  - the originating `Site`, for diagnostics only.

  The builder extracts these from `LikelyFacts` and the translator's
  site tables. After that, nothing downstream reads `LikelyFacts`.
- **The textual printer and parser** are part of the first milestone.
  They are used for hand-written pass tests.
- **The validator** checks:
  - SSA dominance;
  - arity and subtyping on edges;
  - operand types for each op;
  - fences (§4), and the predicted-or-dynamic kill rule (§4.5);
  - raw pointers not crossing may-GC ops (§4.3);
  - exit and entry arity against the script's frame shape (§5).

## 2. Type lattice

### 2.1 Types

```
Type := Val(VSet)          boxed JS::Value, wasm i64
      | I32(IRange)        raw i32: JS number, int32-valued, never -0
      | Int(IRange)        raw i64: JS number, integral, |x| <= 2^53, never -0
      | F64(NumInfo)       raw f64: any JS number
      | Bool               raw i32 0/1
      | Obj(ObjInfo)       managed ref to JSObject     (GC-safe across may-GC ops; rooted by lowering)
      | Str(StrInfo)       managed ref to JSString
      | Raw(RawKind)       RAW POINTER: interior/derived pointer (elements, slots vector, TA data);
                           must not be live across a may-GC op
      | W32 | W64          machine words (lengths, indices, stamp words); not JS values
      | Fact(FactKind)     ghost value: no runtime representation (§3)
```

```
VSet     := { tags: TagSet, num: NumInfo, obj: ObjInfo, str: StrInfo }
TagSet   ⊆ { undefined, null, boolean, int32, double, string, symbol, bigint, object }
NumInfo  := { range: Option<[lo,hi]>, integral, may_neg_zero, may_nan }
ObjInfo  := { kind: ObjKind, singleton: Option<SnapObj>, layout: Option<LayoutClaim> }
ObjKind  := Any > Native > { Plain, Array, Function(Option<ScriptId>), TypedArray(TaKind), Arguments, Env, … }
LayoutClaim := { keys: [lo,hi], types: bool, constructing: Option<…> }   (§2.3)
               -- `types` covers TYPES and, where the layout claims ranges,
               -- RANGES. SLOTS is never in a type: it is tested locally per op (§4.3).
```

- **`int32` and `double` in `TagSet` are tags.** An integral double can
  be double-tagged. "Is a number" is `{int32, double}`.
- **Holes are not in the lattice.** A dense element load is fallible
  on a hole.
- **Some components are invariant for the object's lifetime**:
  - `kind` (JSClass never changes);
  - `singleton`;
  - `Function(script)`.

  **Others are heap-dependent**: `layout`, and `Fact` values. These are
  the ones fences kill.

### 2.2 Subtyping and conversions

- **Subtyping** is within one representation only, and pointwise.
  Passing an arg to a blockparam of a supertype is an implicit weakening
  (§4.2).
- **Conversions are explicit:**
  - `box`;
  - infallible `unbox.*`, where the type proves the tag;
  - widening (`i32→int→f64`);
  - fallible `guard.unbox.*` (a terminator).

### 2.3 Constructors

**Status (2026-09-28): built for inlined constructs.**

- **Producer.** An inlined `new` whose allocation word carries the
  constructor's own early key restates `create_this`'s result as
  `guard.ctor K, 0` (an assertion: `create_this` wrote that word; its
  fail edge is unreachable), and splices a callee built for a `this` of
  type `Obj{K constructing(0)}` (`Ty::Ctor` in the builder). A
  constructing `this` is part of a callee build's context, like the
  closures it receives (`callee_ctx`), so the body has no entry guard.
- **In the body.** The add of K's next field is `init_field` (the value
  guarded to the field's claim, exiting on a miss); a field already
  added is a typed `load_field`/`store_field`; once every field is
  there, `publish_layout` stamps K and `this` is a published `Obj{K}`
  (its prediction witness: `constructing`). A builder run's only
  constructing object is its own `this`, so an add replaces every slot
  of K's constructing type (a join may have made a second value of it).
- **Methods.** A method called on the constructing `this` is spliced
  built for it (receiver or a `.call`'s `thisArg`), with no entry guard,
  reading the fields added so far typed. The caller continues with a
  boxed copy, hinted (`ctor_hint`) with the state the callee's returns
  leave `this` in (`Callee::this_out`) where they agree; its next add or
  method call guards that state back (`guard.ctor K, n`: sentinel, early
  key, SLOTS/TYPES, exactly `n` slots), exiting on a miss.
- **Fences.** A fence demotes a `Ctor` to a boxed, hinted object (a
  published-layout `ObjHint` would be wrong); the next use re-guards.
- **`init_field`'s slow path** is `night_runtime_init_field`: the plain
  add (`PlainStore`: runs no JS), vouched (TYPES kept), filling the
  site's add-transition row; `fail` (exit) unless the object is then
  `constructing(n+1)`. Cold sites therefore stay in MIR.
- **Standalone.** A stamping constructor compiled on its own (called by a
  `new` that was not inlined) hints its `this` as `create_this` makes it,
  `constructing(0)` for its own layout: the first add guards that state
  (`guard.ctor K, 0`, exiting on a miss, which is a call without `new` or
  an object made elsewhere), and the adds are `init_field`s, as in an
  inlined construct. (Added 2026-09-29: earley-boyer +4.2%, splay +5.9%.)
- **Everywhere else** (a delegate reached without a constructing `this`),
  `this` is an untyped object, and the dynamic early publish of
  `ctor_publish` stamps it before calls once all its fields are there.

The design as written:

Constructors are in scope for v1. `this` in a constructor is `Obj{layout: {keys: K, constructing: n}}`.
The object carries the CONSTRUCTING sentinel and has had the first `n`
predicted fields added. A compiled stamp guard would fail on it, so this
is not the same claim as "is a published K". The claim it does support
is K's first `n` slots, so field access on it is typed like a K prefix.
Its operations:

- `init_field` transitions `n` to `n+1`. It is a fallible terminator if
  the add can mispredict.
- `publish_layout` at constructor exit gives a published `Obj{layout K}`.

**Subtyping:** `Obj{constructing K, n}` ≤ `Obj{K-prefix(n)}`, where a
K-prefix claim supports exactly K's first `n` slots. It is **not** ≤ the
published `Obj{K}`: a published-K stamp guard would fail on it, and
slots `n` and beyond don't exist yet. `init_field` is how a
constructing type advances, and `publish_layout` is how it becomes a
published K.

## 3. Global facts (ghost values)

`Fact(kind)` values have no runtime representation. They are produced by
checking ops and consumed as extra operands by ops that rely on them. The
lowering drops them. Initial kinds:

- `Fuse(id)`: produced by `check.fuse id` (a terminator). Consumed by
  `load_gname.fused` and similar, so that a fused literal becomes a
  constant.
- `Binding(id)`: the global binding slot is resolved and the global
  shape matches. Consumed by the global get/set fast paths.
- `NativeIntact(which)`: for example, the string-method fuse behind the
  `charCodeAt` fast path.

Because facts are values, CSE, hoisting and dominance come for free.
Fences kill them like any other type (§4).

## 4. Invalidation, weakening, and GC

### 4.1 Fences

- **Each effectful op carries a kill pattern**, computed from its
  opcode and operand types, over:
  - `LayoutClaims`: any type with `ObjInfo.layout`, inside `Obj` or
    `Val`;
  - `Fact(Fuse(id))`, `Fact(Binding(id))`, …;
  - `All`.
- **The rule:** no value whose type matches the pattern may be live
  across the fence.
- **Single-successor ops:** "across" means live both before and after.
- **Terminators:** a fence can sit on individual *edges*, per §4.2.

### 4.2 Weakening and the clean/dirty rejoin

- Before a fence op, the builder inserts `weaken v : T → T'`, which
  produces a new SSA value. Uses after the fence refer to the weakened
  value.
- On a **fence edge**, weakening is done by passing the value as a
  blockparam of the weaker type. A value of a killed type may not flow
  into the successor except through such a param.
- A call, or a generic op with a dynamic effect report, is a terminator
  of the form:

  ```
  call ... -> ok_clean: b1(r), ok_dirty: b2(r), err: b3
  ```

  - `ok_clean` is not a fence edge, so every per-object and global fact
    survives. This is the rejoin.
  - `ok_dirty` is a fence edge with the op's static kill pattern.
    `b2` weakens by parameter typing, then exits to baseline or
    re-guards and merges.
  - `err` goes to a throw exit (§5.3).
- An op with no dynamic effect report has a single `ok` edge carrying
  its kill pattern.

### 4.3 Layout claims, stamp bits, and ICs

**What today's backend does:**
- **Sites with a class/slot prediction:** a fused identity (+`SLOTS`,
  +`TYPES`/`RANGES` for typed sites) stamp guard (`property.rs:541–800`).
  On a miss, a side arm runs the inline IC, then continues at the next
  PC in GEN (`Side` folds to `Dirty`).
- **Sites without a prediction:** the IC runs inline in OPT. A hit, or a
  clean miss (the "second chance" bit, `object.rs:10`), rejoins. Only a
  dirty miss leaves OPT.

**MIR: the three stamp components are treated differently.**

| Component | Meaning | In the type? | On failure |
|---|---|---|---|
| identity (`keys`) | object has layout K | yes, killable | exit to baseline at the op's PC |
| `TYPES` (+`RANGES`) | K's protected fields hold their predicted types (and ranges) | **yes, killable** | exit to baseline at the op's PC |
| `SLOTS` | K's fields sit in their predicted fixed slots | **no**: local to each op | the IC, staying in OPT |

- **Identity and `TYPES` are part of what OPT means.**
  - `load_field` and `store_field` require a receiver of type
    `Obj{layout K, types}`. With local-first guarding (§8), the builder
    emits one `guard.layout K {types}` before each such op. Lowering
    fuses it into a single masked stamp compare, as today.
  - **On failure, including a class-key miss, it exits to baseline** at the
    op's own PC, before anything observable has happened. Staying in
    OPT with an unexpected class would give up the type specialization
    that follows from it.
  - **Loads feed the predicted type out.** The result has the field's
    claimed type (`Val{int32}`, `Val{int32,double}` with a range, a
    string, an object of a known kind, …). This is the value-type
    specialization we get from the analysis's knowledge of the object.
    Exactly what `TYPES` guarantees, and therefore which parts need no
    check at the load, is set by the runtime's maintenance discipline
    (§4.6).
  - **Stores expect the predicted type in.** The value must already
    conform by its type; guard-at-defs normally guarantees this, and
    otherwise the builder guards the value and exits on failure. So an
    OPT store never clears `TYPES`/`RANGES`: the store choke is
    statically satisfied and elided. OPT stores are therefore **not
    fences** for `types` claims.
  - `types` is killable. Fences that may perform engine stores (generic
    `js.setprop`/`setelem`, calls, arbitrary JS) kill `types` claims,
    subject to §4.5.
- **`SLOTS` is local and tolerant.**
  - Each `load_field`/`store_field` lowering tests the `SLOTS` bit
    itself. If set, it does a direct fixed-slot access; if clear, it
    runs the inline IC ladder and stays in OPT.
  - On the IC arm, a load's result still has the claimed type, because
    `TYPES` was guarded and it constrains the field's *value* regardless
    of which slot holds it.
  - A store's IC arm can reach an add transition or a setter, so the op
    keeps `ok_clean`/`ok_dirty`/`err` successors. The add-slots check may
    clear `SLOTS` on a mispredicted add. That invalidates no type,
    because `SLOTS` is never in a type.
  - SLOTS-miss receivers are therefore served in OPT, not regressed to
    GEN as they are in today's backend.
- **Shallow `TYPES` for object-typed fields.** A valid `TYPES` bit on an
  object is shallow. It constrains what the parent's field holds, and
  says nothing about the child object's own `TYPES` bit: a deep meaning
  would need backlink-following on invalidation, which is impractical.
  As §4.6 explains, it also cannot soundly promise the child's *layout
  identity*, only its immutable components. In the lattice:

  ```
  o : Obj{layout K, types}
  load_field o, f        -- f's claim: object, kind Plain, class K2 predicted
    => r : Obj{kind Plain}        (object-ness and kind: yes; layout K2: NO; types: NO)
  ```

  This is after M5b (§4.6). Before it, object-ness is not maintained,
  so the load yields a plain `Val` and a guard-at-def tag check makes it
  `Obj` (exiting on failure), exactly as for an object argument.

  To specialize loads *from* `r`, `guard.layout K2 {types}` must run
  first: one masked compare of `r`'s stamp word. With local-first
  guarding it happens at `r`'s first field use. Guard
  folding and hoisting (§10.1, §10.2) then share it across uses, and
  hoist it out of loops when `r` is invariant.
- **Unpredicted sites** use `js.getprop`/`js.setprop` with the IC ladder
  in lowering and clean/dirty edges, as today.
- **Compiled stores never clear identity.** Only shape and proto
  mutation and generic engine paths can, and those are `js.*` or runtime
  ops, which are fences.

### 4.4 GC

- **GC is below the MIR's abstraction level.** `Obj`, `Str` and `Val`
  are managed and may be live across anything.
- **`Raw` values may not be live across a may-GC op.** The validator
  checks this. LICM-hoisted interior pointers are `Raw`, so they are
  rematerialized (recomputed from the managed base) after a may-GC op,
  or hoisting is limited to GC-free loops.
- **Rooting happens during lowering**, only where a may-GC op is, and
  only for what is live across it:
  - Each managed value that may be live across a may-GC op gets a home
    slot in a fixed rooting area. Values never live at once share a
    slot: in SSA, two values interfere iff one is live at the other's
    definition, so greedy coloring in dominance order is exact.
  - The lowering tracks, along the emission, where each managed value
    is: in a register (a waffle value), in its slot, or both.
  - Before a may-GC op, each live value not yet in its slot is stored,
    boxed. An SSA value never changes and the GC updates the slot in
    place, so a stored value stays stored across later calls.
  - After the op, register copies are dropped. A value is reloaded
    where it is next used, and kept until the next may-GC op.
  - Unboxed numbers and booleans are never rooted. Locals stay in their
    own representations, never written through to the baseline frame
    (exits write them), except the formals a mapped `arguments`
    aliases.
  - At a block entry, each managed live-in's location is decided from
    the edges already lowered (every one but back edges). A value that
    may cross a may-GC op before a back edge enters only in its slot, so
    a loop stores it once, before the loop. Otherwise it enters in a
    register if every edge has one, or every edge but a helper's slow
    path does (that path reloads it). Else it enters only in its slot.
    Each edge gets its own waffle block to reconcile locations; the
    empty ones are removed.
  - Every may-GC op's GC scan covers the whole rooting area, which the
    entry initializes. A slot that holds a dead value is not cleared: the
    value stays alive until the slot is reused or the activation returns.
    GC timing is unobservable, and `WeakRef` targets may be kept alive
    longer; that retention is bounded by the frame. (Amended 2026-09-29:
    clearing dead slots cost richards 2.8% and bought nothing.)

### 4.5 Fences versus predictions

**The OPT invariant.** At each bytecode boundary, OPT state is at least
as strong as the likelier prediction in the components that define OPT:
- tags/prims;
- object-ness;
- typed-array kind;
- class, at loop headers (§5.2).

Tags and kinds are invariant, so fences cannot weaken them. Only
killable components (layout identity, ghost facts) can go dead.

Two different things can weaken killable state:

1. **Tolerated: a predicted kill, followed by a local re-guard.** A
   fence kills a component *that the prediction also says may be
   invalidated*. The value runs with the component dead until its next
   use, whose local guard (§8) re-establishes it or exits. This is
   today's lazy-class regime after a `CallGc`.
2. **Forbidden: a kill that contradicts the prediction.** Suppose MIR
   classifies an op as possibly invalidating something that likelier's
   model says it cannot. Examples: a generic op on values the prediction
   says are primitives, or a store to a field of class J believed to
   invalidate K's claims. OPT would then pay re-guards, or run weakened,
   for a scenario the prediction excludes.

**Rule: every kill is either predicted or dynamic.**
- A static kill (a single-successor fence, or a kill on a non-dirty
  edge) of a component is allowed only if the op's prediction says it
  may invalidate that component.
- Otherwise the op must report its effect dynamically, putting the kill
  on `ok_dirty`. There, re-guard failure exits. When reality contradicts
  the prediction we leave OPT; we never absorb the contradiction as a
  silent weakening.

**How this is checked.** The builder attaches each op's *predicted
effect* as a **prediction witness**: a validator-only side table
recording what likelier's effect summaries and op model say the op may
invalidate. The validator asserts the rule for every static kill, so
passes that add fences (inlining, for example) are checked
too. Witnesses are never read by lowering or by optimization decisions.
They are the only prediction data MIR retains.

### 4.6 Field type claims: what `TYPES` can guarantee

**Status (2026-09-27): M5b built for MIR, as below.**

- **Emission:** each field carries its full predicted type
  (`ClassFieldFacts::types`: every prim class plus the object bit; none
  where an unknown value may flow in), served as
  `layout_field_types_in`. Legacy keeps its numeric masks.
- **Maintenance:**
  - The engine store mask clears `TYPES` on every store
    (`kStoreClearMask = RANGES | TYPES`; `SLOTS` is left out).
  - MIR's stores to a known field carry its type (`field_mask`) and keep
    `TYPES` iff the value conforms, statically or by its tag. A
    nonconforming value on a published object goes to the engine, which
    clears the bit, and the op reports dirty; under construction the bit
    is cleared inline. A store without a known field drops `TYPES`.
  - (2026-09-28) Stores that reach a set helper keep `TYPES` too when the
    value conforms: the compiled store vouches (MIR's by `field_types`,
    baseline's by `field_classes`), and the helper also checks the
    field's claim for the object's class itself (the layout table carries
    each field's claim; `NightStoreConforms`, under the any-type flag of
    the MIR and baseline pipelines). A vouched store keeps the bit where
    it runs no JS: add replays, the set-add table, the mega-set probe, a
    plain slot write or plain add (`PlainStore`). The engine's store
    choke itself still drops it (it knows no field; `defineProperty`'s
    accessor slots, say, demote an object whose layout they are not in).
  - Element stores owe the array stamp's claims only on arrays: a plain
    object's `TYPES` claims its fields (`array_key_min`).
- **Consumption:** a typed site's reads trust the layout's type for the
  field, any type (`load_field -> val{null,object}` etc.), under a
  `guard.layout {types}`.
- **Stamps:** MIR's and baseline's allocations seed `TYPES` and their
  ctor stamps and restamps keep it for any layout with a typed field
  (`layout_types_bit`, shared). Snapshot objects are stamped with any row
  of their constructor's clump they match exactly, with `TYPES` iff
  every field's value in the image conforms. Before a call made during
  construction, `this` is stamped once all of its fields are there
  (`ctor_publish`: §2.3's `publish_layout`, dynamically).
- **Not yet:** the object component (kind, script, singleton).

The rest of this section is the design as written before M5b.

**Today (answering "gap in emission, or in the analysis?"): it is
emission plus runtime maintenance. The fixpoint analysis tracks
everything.**

- **The analysis.** Each class's per-field view cell
  (`CellKey::ClassView`) is a full `TypeSet`: all prim classes (string,
  boolean, null/undefined included), a bounded function set, the object
  abstraction (class, region), a range and an interval. So the analysis
  does see through the heap for object, string and boolean fields.
- **Emission gates it down to numbers.** `class_view_prims`
  (`likelier/emit.rs:2857`) returns a field mask only when the field is
  purely numeric (or numeric plus null/undefined/unknown "poison", which
  is widened to int|double). The typed-read tier applies the same gate
  (`emit.rs:2711`). The reason is the next point.
- **Runtime maintenance only knows numberness.** The engine store choke
  is a pair of *global* masks, not a per-field check
  (`NightObjectWord.h`, `INTEGRATION.md`):
  - `storeClearMask` clears `RANGES` on every engine-path store;
  - `storeNonNumberClearMask` clears `TYPES` when the stored value is not
    a number.

  So today `TYPES` means only "every protected field holds a number". An
  int32-only claim is re-checked with a tag test at the load
  (`push_typed_field`, `property.rs:836`), whose double arm leaves OPT.
- **Structural changes wipe the whole word, identity included.** This
  covers dictionary mode, property change or removal, freeze/seal,
  swap, and object-flag changes.

**Extension, in v1 (plan item M5b):** per-field claims for strings,
booleans, null/undefined and objects.

1. **Emission.** Replace the numeric gate with a per-field claim drawn
   from the view cell:
   - a tag set, over all prim classes plus object;
   - for object-typed fields, an optional immutable **object
     component**: JSClass kind (plain, array, typed array of kind k,
     function), function script (from the fn set, when singular), or
     snapshot singleton;
   - the predicted layout-key range, emitted as an *advisory* hint that
     the builder guards at first use (see point 4).

   The "poison" widening rules need revisiting per class of evidence.
2. **Maintenance: generic writes clear unconditionally.** There is no
   per-field check on the generic side.
   - Any field write by generic code clears `TYPES`, `SLOTS` and
     `RANGES`, whatever the value. Generic code here means the C++
     runtime and engine (`setSlot`/`initSlot`), runtime helpers (so
     every baseline store), and legacy GEN's compiled stores.
   - In the engine hook, this becomes
     `storeClearMask = RANGES | TYPES | SLOTS`, and
     `storeNonNumberClearMask` becomes redundant.
   - GEN's inline choke (`emit_store_choke`, `bbv/facts.rs:1545`)
     becomes an unconditional clear.
   - No claim tables are fed to the generic side.
   - OPT stores (§4.3) are the only writers that leave the bits set.
     They are allowed to because the stored value conforms by its type.
3. **So `TYPES` becomes exact per field.** Every writer that leaves it
   set has proven conformance to the field's full claim, so an int32-only
   claim needs no tag test at the load, and neither does a string,
   boolean, or object-kind claim. This holds as soon as step 2 lands.
   - **Transition hazard:** while legacy-OPT-compiled scripts coexist
     with MIR scripts, legacy OPT stores must not leave `TYPES` set on a
     value that only satisfies the old "is a number" rule. Their typed
     sites can check the exact per-field claim statically, since the
     compiler knows the layout and field. Every other legacy store
     clears, like GEN's. This is part of M5b.
   - **Consequences to watch:**
     - *Permanent demotion.* A generic write clears the bits for good,
       and nothing re-establishes them except a constructor-exit or
       delegate restamp. So an object that has been written by baseline,
       GEN, the runtime or the interpreter even once will fail its
       `types` guard in OPT from then on. That includes each
       exit-then-onramp cycle whose baseline portion stores to it. Today, number-conforming generic
       stores keep `TYPES`, so this is a behavior change we should
       measure (demotion census by bump site, which already exists).
       Mitigation if needed: GEN stores whose site has a static claim
       could check it inline, as legacy typed sites will.
     - *Construction outside OPT.* Objects built by the interpreter,
       baseline or GEN never keep `TYPES`, because their initializing
       stores are generic.
     - *Epoch churn.* Every clear bumps `gNightStampEpoch`, so callees
       that run in baseline or GEN report dirty more often. Callers then take
       `ok_dirty` and re-guard, which is correct but costlier.
     - *`SLOTS` on value stores.* Clearing `SLOTS` on a plain value
       store is stronger than needed, since slots don't move. It only
       costs IC fallbacks (§4.3), which stay in OPT, so it's accepted
       for simplicity.
4. **Why the child's layout identity cannot be part of a
   store-maintained claim.** A child's identity is wiped by structural
   changes *to the child*. Those never touch the parent, so keeping the
   parent's claim sound would need child-to-parent backlinks, which is
   the deep-claim problem again. The immutable components (kind,
   function script, singleton) have no such issue. So a loaded object
   carries kind/script/singleton in its type, and its layout K2 is
   predicted, not proven.
   - The builder emits `guard.layout K2 {types}` at first use.
   - That guard is one stamp compare. It is shareable (§10.1) and
     hoistable (§10.2).
   - Function script alone already gives direct calls through fields
     (`this.cb(x)`) with no guard, which is a real win for
     callback-heavy code.
5. **Prediction witnesses and fences** need nothing new. A `types`
   claim is still killed only by engine-store fences.

## 5. The MIR/baseline boundary: exits, onramps, throws

The baseline tier (`docs/BASELINE.md`) keeps the whole JS frame in
NightStack memory. Its frame format (BASELINE.md §2) is the only
interface between the tiers: state at a pc is the frame plus the static
operand depth there. MIR and baseline are separate Wasm functions per
script, and the MIR body is the script's table entry.

**Boundary rule:** every value crossing between MIR and baseline has
type `Val(⊤)` (boxed, nothing else known). `Val(⊤)` includes magic
values (TDZ, element holes), since frames hold them.

- Deopt upcasts, infallibly: `box` if needed, then `weaken` to `Val(⊤)`.
- An onramp reestablishes knowledge by running ordinary MIR guards. The
  guard implementations are therefore shared with the rest of MIR, and
  the lowering has no separate onramp proof machinery.

### 5.1 Exits

```
exit pc, this, [args…], [locals…], rval, [stack…]   -- any boxable reprs
```

- **The arity is fixed by the script:** all formals, all locals, the
  rval, and the operand-stack depth at `pc`.
- **The frame is written through (amended 2026-09-27).** Every write
  of a formal, a local or the rval also stores it to its baseline frame
  slot, as the Value it is: `frame.store k, v`. An i32 or bool is
  tagged, and an f64 goes in as a double with NaN canonicalized (a
  valid Value, if not the int32 `NumberValue` would pick). A merge that
  changes a slot's representation keeps its JS value, so the frame
  copy stays equal to the slot everywhere, and nothing is stored on
  edges. The frame is thus the boxed truth for those slots, as in bbv.
  An exit leaves them as the frame has them: they go as
  `const.val dead`, like slots that are dead at the exit's pc. What an
  exit carries is `this` (sloppy code boxes it in place, so it is not
  written through) and the operand stack.
  - **Why:** before this, every exit boxed every live slot. That was
    O(exits × live slots) per function, and quadratic in function size.
    Mandreel's 16–32 KiB functions lowered to about 660K waffle values
    each, and the batch outgrew the in-process compiler. After it,
    mandreel's MIR bodies total 6.3M values rather than 17.7M, and grow
    linearly (about 5 values per bytecode byte). No Octane score moved,
    because the stores are one per assignment.
  - Sinking stores of loop-carried locals out of their loops (so exits
    in the loop carry them) is the obvious refinement, if the stores
    ever show up in a profile.
- **Operands keep their representation.** The lowering boxes them, not
  the builder. **One exit hub per frame shape:** the shape is each
  operand's representation kind, with dead ones omitted. The hub's
  params are the resume word and the operands as they are. It boxes
  each once, writes the frame, and calls baseline (or returns DEOPT).
  An exit is a branch to its hub.
- **The env slot is not an operand.** The env chain is fixed for the
  whole activation, and the fresh entry writes it once: the callee's
  environment, or the one `env_setup` makes (a call object, a named
  lambda's scope). Ops that push a scope decline.
- **Resume rule:** an exit to an op's own PC is allowed only if no
  observable part of the op has happened. Otherwise it targets the
  successor PC, with the op's result on the stack.
- **The hub writes a complete baseline frame and resumes baseline:**
  1. Store every live operand, plus the arguments-object and
     new.target slots.
  2. Write the resume word: `pc`, in mode `continue` or `throw`.
  3. If this activation entered MIR at the function entry, call the
     baseline body with `ARGC_RESUME_BIT` and return its result. If it
     entered by an onramp from baseline, return `err = 2` (DEOPT) to
     that baseline caller, which resumes itself. A JS frame therefore
     never uses more than three native frames.

  MIR places its GC rooting slots and callee frames *above* the whole
  baseline frame (past its deepest operand stack). The frame itself
  stays a set of valid Values:
  - a fresh entry initializes it as baseline's prologue would;
  - an onramp entry finds it valid, and clears the operand slots above
    the header's depth.

  The GC can therefore trace it at any time.
- **Liveness pruning (implemented).** The builder computes the backward
  liveness of `this`, the formals, the locals and the rval over the
  bytecode. A slot dead at a block's entry takes no block param.
- **Reserved extensions:** a parent-frame chain (for inlining) and
  virtual-object recipes (for scalar replacement). v1's validator
  rejects both.

### 5.2 Onramps and loop preheaders

- **Onramp roots exist only at loop headers** (plus function entry).
  This matches the heuristic JITs have settled on for tier-up.
  Everywhere else, rejoining optimized code happens inside MIR, through
  the `ok_dirty` re-guard path (§4.2, §8).
- **MIR declares its loops**: header, preheader, from the bytecode
  loops. A loop's body is every block that reaches one of its latches
  without passing through the header. That is well-defined even though
  onramps make the CFG irreducible (§5.4).
- **Every MIR loop has a canonical preheader `P`.**
  - Its params are the full frame state at the header PC, typed with the
    prediction for that header, **including class (layout) claims**. It
    is not weakened to make reentry easier. So `O`, and any `ok_dirty`
    path inside the loop that reaches the back edge, guard stamps as
    well as tags.
  - `P` is the loop header's only predecessor from outside the loop. It
    is where LICM hoists to.
- **A loop may have an onramp root `O`.**
  - `O` is a root of the MIR CFG. A MIR function has several roots, and
    the validator's dominance uses a virtual root.
  - `O`'s params are the same frame state, all `Val(⊤)`.
  - Its body is a guard chain: guard each value up to `P`'s param type.
  - When every guard passes, it jumps to `P`.
  - When a guard fails, it re-deopts with `exit header_pc, …`, using
    `O`'s own params as the operands.
  - Which headers get an `O` is policy (BASELINE.md §7). Every
    outermost loop gets one. An inner loop gets one subject to the
    code-size cost of §5.4.
- **Lowering an onramp:**
  1. At a loop header, baseline calls the MIR body with its own `sp`
     and `ARGC_ONRAMP_BIT`, with the header named in the resume word.
     Backoff keeps failing guards from costing a call per iteration.
  2. The MIR body's single entry block dispatches with one `br_table` to
     `O`, whose lowering loads its params from the frame.
  3. If MIR returns normally, baseline returns the value. If it returns
     DEOPT, baseline resumes at the resume word's pc.
- **Progress:** a failure in `O`, or in a guard hoisted into `P`, exits
  to baseline at the header. Baseline runs at least one iteration
  before it attempts the onramp again, so there is no livelock.
- **Function entry** is the same construct at PC 0. Its root takes
  `callee`, `this` and the formals as `Val(⊤)`. The guard chain applies
  the builder's entry types (the `arg_types` guard-at-defs policy).

### 5.3 Throws

- **Any op that can throw, and any call that can return an error, has
  an `err` successor.** All such ops lowered from the same bytecode op
  share one throw block per PC:

  ```
  exit.throw pc, this, [args…], [locals…], rval, [stack…]   -- every operand : Val(⊤)
  ```

  Its operands are the state *before* the op, which dominates every
  throwing point within that op. The block therefore needs no params.
- **It lowers like `exit`**, with the resume word in mode `throw`.
  Baseline then runs its own exception landing for `pc`: iterator
  closes, env unwinding, and then the catch/finally handler or the
  error return.

  Scripts with try/catch are therefore supported, and MIR itself has no
  exceptional control flow.
- **Fallback plan:** if throw blocks turn out to dominate block count,
  fold throw semantics into the ops, and materialize them only in the
  lowering to waffle.

### 5.4 Reducibility

MIR has no reducibility invariant. An onramp into a nested loop enters
through that loop's preheader, which lies inside every enclosing loop,
so it side-enters each of them.

- The lowering emits the MIR CFG as-is. waffle's backend reducifier
  duplicates the partial first iteration from the side entry up to the
  enclosing loop's header, where the copy rejoins the original.
- The steady-state loop exists once, whichever block the reducifier
  picks as header. The choice only decides which fragment of one
  iteration is duplicated.
- The cost is measured on real MIR after M3 (BASELINE.md §8, step W)
  before any change to waffle is considered.

### 5.5 Inlining

bbv inlines by splicing the callee's bytecode into the caller's pc space.
Its guard failures inside the splice fall to GEN copies of the callee's
blocks in the same wasm function. MIR has no GEN copies. Its exits resume
baseline, and baseline has one body per script. The design:

- **Splice the callee's MIR.** Build the callee `K` standalone (the same
  builder, the same facts). Then copy its blocks into the caller at the
  call site, renaming values and remapping module entities (atoms,
  fuses). `K`'s entry root params become the call's callee, `this` and
  arguments; `K`'s onramp roots are dropped. A `return` becomes an edge
  to the call's continuation.
- **The callee's frame is real.** `K` gets a baseline-format frame at a
  fixed offset above the caller's (the *inline frame*). Write-through
  (§5.1) keeps its formals, locals and rval current, so `K`'s frame is
  exactly what baseline expects at every exit.
- **An exit inside `K` finishes `K` in baseline** (`exit.inline`). It
  writes `K`'s stack and resume word into the inline frame, then calls
  `K`'s own entry with `ARGC_RESUME_BIT`. A MIR main body forwards such
  a call to its baseline body. The call returns `K`'s result, or an
  exception. The caller continues in MIR from there, as it would after
  a generic call: a dirty `ok` edge to the continuation, or the `err`
  edge (an `exit.throw` at the call's pc). No caller state is lost,
  and no multi-frame deopt is needed.
- **Baseline bodies of inline-eligible scripts accept a resume at every
  op.** Whether a script is inline-eligible is a property of the script
  alone (small, no try, no generators, …). So no compile of `K` needs
  to know who inlines it, which also holds across in-process batches.
- **The guard** is on the callee's script. `night_call_classify` yields
  the callee's `JSScript*`, compared with `K`'s (the source's `addr`,
  stable since compaction is off). A miss runs the ordinary call. Up to
  a few targets get a dispatch chain (polymorphic inlining).
- **Stack layout.** The caller frame comes first, then the rooting
  area (§4.4), then the inline frames, then the frames of real calls.
  The rooting area is initialized at entry and each inline frame at its
  `inline.enter`, since the GC traces up to `top`. An inline frame's GC
  scan (`frame_top`) stops below the fixed slots its callee never reads
  while MIR runs: `inline.enter` writes callee, `this`, the actuals and
  the locals (as bbv's splice does), plus env only for a callee that sets
  its environment, and all six only for a construct or a callee reading
  its arguments object or new.target. The `exit.inline` hub writes the
  rest before entering the baseline body. (Amended 2026-09-29.)

## 6. Effects and memory

- **Every op has an effect summary**, computed from its opcode and
  operand types:
  - reads and writes, as access descriptors;
  - may-GC;
  - may-run-JS;
  - may-throw;
  - its kill pattern;
  - its contribution to the flags word.
- **Alias regions are an IR concept.** They are entities in a
  module-level table. An access touches a set of regions:
  - `Field(LayoutKey, name)`: one region per object class per field.
    An access through a receiver with layout claim `[lo, hi]` touches
    `Field(k, name)` for every `k` in the range. This is stored
    compactly as `(name, [lo, hi])`, with an overlap test.
  - `Elements(RegionRoot)` and `ArrayLength(RegionRoot)`: from the
    analysis's array class regions, proven by the receiver's stamp.
    Array stamp keys grow down from `0x7FFE` (`wasm/mod.rs:1545`).
    Today only arrays in a claiming population are stamped. As part of
    v1, the analysis will **stamp every array class region**, with or
    without an element claim, so that element accesses get alias
    regions.
  - `TypedArrayData(kind)`, `TypedArrayLength`.
  - `Global(binding)`.
  - `Env(scope, slot)`.
  - Partial wildcards:
    - `Field(*, name)` is a named access on an unproven receiver. It
      overlaps every `Field(_, name)` region.
    - `Elements(*)` is a dense access on an unstamped native object. It
      overlaps every `Elements(_)` region.
    - Neither overlaps other kinds of region.
  - `Unknown`: the access reads or writes **every** region.
- **Where regions come from.** An access gets a specific region set only
  when the receiver's *type* proves it. A receiver without a layout
  claim gets a wildcard, or `Unknown` when the op is generic (a getter
  or proxy could touch anything). The same SSA ref is must-alias. Otherwise, two
  accesses may alias only if their region sets overlap.
- **Two distinct kinds of fence:**
  - an **unknown-alias store** (or any may-run-JS op) is a memory fence:
    it clobbers all remembered loads and stores;
  - an **unknown-alias load** blocks only dead-store elimination and
    store sinking across it.

  These are separate from the type-invalidation fences of §4, although
  a may-run-JS op is both.
- **Load/store forwarding, redundant-load elimination, dead-store
  elimination and LICM** are classical passes over these descriptors.
- **Flags word:** each op's effect maps to `FLAG_MUT_THIS`/`OTHER`/
  `STAMPS`/`BIND` bits, or to "the callee's returned flags" for calls.
  The lowering threads the accumulator as a constant where possible and
  dynamically otherwise, and returns it at `return`. It is never an MIR
  value.

## 7. Opcode set

**(T)** marks a terminator. Every **(T)** fallible op has `ok` and
`fail` targets. Ops that can throw also have `err`.

**Constants**

- `const.val`, `const.i32`, `const.f64`, `const.bool`
- `const.obj SnapObj`, `const.str atom`

**Conversions**

- `box`
- `unbox.{i32,f64num,bool,obj,str}`: infallible
- `i32.to_int`, `i32.to_f64`, `int.to_f64`
- `weaken`

**Guards and checks (T)**

- `guard.unbox.{i32,f64num,bool,obj,str}`
- `guard.tags`
- `guard.kind` (clasp)
- `guard.layout keys {types}` (stamp check: identity, and optionally
  the `TYPES`/`RANGES` bits)
- `guard.singleton`
- `guard.script` (callee identity)
- `f64.to_int_exact`
- `check.fuse`, `check.binding`: produce `Fact`s

**Control**

- `jump`
- `br Bool`
- `switch I32`
- `return v`
- `exit pc, …`: all operands `Val(⊤)`
- `exit.throw pc, …`: all operands `Val(⊤)`, one per bytecode op
- `unreachable`

**Numeric**

- `i32.{add,sub,mul}.ovf` (T); `mul` also fails on -0
- `i32.{add,sub,mul}.wrap`: introduced only by demand analysis
- `int.{add,sub,mul}`: from interval proofs
- `f64.{add,sub,mul,div,mod,neg}`
- `i32.{and,or,xor,shl,shr}`, `i32.ushr → Int`
- `to_int32`
- `*.cmp.<cc> → Bool`
- `math.<fn>`

**Generic JS ops** on `Val` operands, lowered to today's helpers,
including the inline-cache ladders:

- `js.add`, `js.binop`, `js.compare`, `js.typeof`, `js.tobool`,
  `js.tonumeric`
- `js.getprop`, `js.setprop`, `js.getelem`, `js.setelem`
- `js.getname`
- …

These are fences with `err` edges. They are (T) with clean/dirty edges
where the helper reports cleanliness.

**Objects**

- `load_field recv:Obj{layout K, types}, name` (T: `ok_clean`,
  `ok_dirty`, `err`): lowering tests `SLOTS` locally, then does the
  direct slot load or the IC (§4.3). The result has the field's claimed
  type. For object-typed fields that means class identity but not
  `types` (shallow). Attachments carry the slot and the IC cell.
- `store_field recv:Obj{layout K, types}, name, v:<claimed type>` (T:
  `ok_clean`, `ok_dirty`, `err`): tests `SLOTS` locally, then does the
  direct store or the set IC. Barriers and the add-slots check stay as
  today, and the store choke is elided. It is not a fence (§4.3).
- `init_field`, `publish_layout` (§2.3)
- `new_object K`, `new_array n`
- `load_elem`, `store_elem` on `Obj{Array|Native}` with an `I32` index:
  (T) on bounds or holes
- `load_ta`, `store_ta`
- `length.{array,string,ta}`
- `elements_ptr → Raw`
- `str.char_code_at`
- …

**Globals and environments**

- `load_gname`, `store_gname`: consume and kill `Binding`/`Fuse` facts
- `env.current`, `env.load`, `env.store`

**Calls (T: `ok_clean`, `ok_dirty`, `err`)**

- `call`: generic
- `call_direct callee:Obj{Function(s)}`: compiled to compiled
- `construct`
- `call_native`

`this` and args are explicit operands. Attachments carry the call cell
and candidate targets.

## 8. JSOps to MIR

The builder is a function of (JSOps, likelier facts) that produces a MIR
body, or declines. It runs an abstract interpretation over the bytecode,
with the operand stack and locals as SSA values:

- Blockparams at every branch target. Each loop header gets its
  preheader `P` and onramp root `O` (§5.2). The function-entry root
  applies the entry guard chain.
- **Local-first guarding for killable components.** Every op that
  relies on a killable component (layout identity, a ghost fact) gets
  its own guard immediately before it, on its own operand. The only
  exception is an operand that was produced within the same bytecode op
  by something that proves the component (an allocation, or a guard
  emitted for the same op).
  - The builder does **not** try to reason about which earlier guard is
    still valid. Guard folding and hoisting (§10.1, §10.2) merge guards
    in a principled way, and the validator (§4.1) guarantees the merged
    result is sound.
  - Tag and prim guards are not killable, so they follow guard-at-defs
    as today.
  - **One rule for every object-typed value, whatever its source**
    (argument, `this`, field load, element load, call result, global,
    env slot):
    - its type is what is *proven*: object-ness from a guard at its
      definition (or from a maintained field claim, §4.6), plus any
      immutable components;
    - likelier's class prediction for it is *not* in the type;
    - because MIR is generated assuming likelier is right, each use that
      needs the class gets a local `guard.layout K {types}`, which exits
      on failure;
    - guard folding and hoisting (§10) then merge and hoist those
      guards.

    A loaded child object is thus no different from an object
    argument.
- **The default for `ok_dirty` edges** is to weaken only the killed
  types. It then re-guards each weakened value up to the type it
  carries on the `ok_clean` edge, and rejoins the clean path. The join
  therefore stays as strong as the clean path, and downstream guards can
  still fold against it. A failed re-guard exits at `pc_after`. This
  replaces today's call-return onramp without a trip through baseline.
- Explicit `box`/`weaken` upcasts before every `exit` and `exit.throw`.
- A guard-at-defs policy against the per-PC prediction: OPT state at a
  PC boundary must be at least as strong as the prediction in its
  OPT-defining components (§4.5), as it is today. A value that fails its
  guard exits. The builder asserts this at every boundary.
- A prediction witness attached to every op with an effect (§4.5).
- Generic `js.*` ops for unpredicted operations.

## 9. MIR to waffle

For each script:

1. Build the MIR body (or decline). Its exit and throw pcs, and its
   onramp headers, are the resume set the baseline compile needs.
2. Compile baseline for the script with that resume set
   (BASELINE.md §4).
3. Lower MIR into its own `FunctionBody`. The entry block dispatches
   to the function-entry root or, under `ARGC_ONRAMP_BIT`, to an onramp
   root. Op lowerings take MIR types and attachments rather than BBV's
   `Operand`/`Ctx`, and may share emit code where it fits.
4. Perform rooting (§4.4) and flags threading (§6) during this walk.
   Each exit writes the baseline frame (§5.1).
5. Emit. waffle's backend reducifies the body (§5.4).

## 10. Optimizations that must work

This section lists the mechanisms we must build and demonstrate, not
just believe in. Each item gets:
- textual before/after MIR tests;
- an end-to-end test whose **dynamic guard counts** (today's guard
  census, reused) show the expected reduction.

Local-first guarding (§8) is only acceptable because §10.1 and §10.2
exist, so those two land together with the ops that create the guards
(M4).

### 10.1 Guard folding (GVN on guards)

- **The problem.** Guards are terminators, so merging two of them is
  *branch folding*, not value numbering.
- **Guard identity.** A guard is identified by
  `(kind, static params, value number of operand)`.
- **The folding condition.** A guard `G2` is redundant given `G1` if
  `G1`'s `ok` outputs (the refined value `v1` and any ghost fact) could
  legally be used at `G2`. That means:
  - `G1.ok` dominates `G2`;
  - and no fence on any path from `G1.ok` to `G2` kills `v1`'s type.

  This is exactly the validator's condition for `v1` being live at
  `G2` (§4.1). So the pass rewrites `G2` into `jump G2.ok(v1, fact1)`,
  and the rewrite validates by construction.
- **Implementation:** an *available guards* forward dataflow over the
  CFG.
  - Gen: a guard's `ok` edge.
  - Kill: fences, by pattern. This covers kills on paths that merely
    rejoin, which a plain dominator-scoped hash table would miss.
  - Meet: intersection at merges.
- **Joins carry facts through param types.** If every predecessor
  passes a value carrying the fact, the param's type carries it, and
  guards on the param fold by type. The clean/dirty rejoin (§8) relies
  on this.
- **Type-based folding.**
  - A guard whose predicate the operand's type already proves becomes a
    `jump` to `ok`.
  - A guard the type *disproves* becomes a `jump` to `fail`. The pass
    warns: that is a builder/prediction mismatch.
- Afterwards, dead `fail` blocks are removed and identical exits are
  shared.

### 10.2 Guard hoisting into the preheader (LICM for guards)

A guard inside a loop is hoisted to `P` when all of these hold:
- its operand is loop-invariant (defined outside the loop, or a header
  param passed unchanged along every latch);
- no fence in the loop kills its fact;
- it dominates all latches (today's `licm.rs` rule, to avoid
  speculating guards that were conditional).

Its `fail` edge is re-anchored to `exit header_pc, P.params`. This is
correct because nothing in `P` has done any observable work of the
iteration yet. The in-loop copies then fold (§10.1). Since onramps
enter through `O → P`, hoisted guards also run on every onramp. A
typical case is the `TYPES` guard on an object loaded from a field
(shallow `TYPES`, §4.3) when that object is loop-invariant.

### 10.3 Fences and rejoins

The canonical test is `loop { a.x; f(); a.x }`:
- the first guard on `a` hoists to `P`;
- the second folds on `f`'s `ok_clean` edge;
- on `ok_dirty`, the re-guard runs, and the join stays strong.

Also covered here:
- a loop containing a static fence keeps its post-fence guard in the
  loop, and does not hoist;
- the §4.5 witness assertion fires on a deliberately wrong kill.

### 10.4 Box, unbox and weaken cleanup

- `unbox(box x) → x`.
- Chains of `weaken` collapse.
- A `box` whose only users are exits is sunk into the exit blocks, so
  the hot path doesn't box values that are only needed for deopt.

### 10.5 Memory: forwarding, RLE, DSE

These run over alias regions (§6):
- **Store-to-load forwarding:** `store a.x v; load a.x → v`.
- **Redundant-load elimination:** `load a.x; store b.y; load a.x`
  reuses the first load, because the fields differ.
- **Dead-store elimination.**

Memory knowledge survives an `ok_clean` edge. A clean flags word means
no mutation beyond the op's own declared access. It dies at `Unknown`
stores and may-run-JS fences.

### 10.6 Numeric

- Remove overflow checks using ranges.
- Rewrite `.ovf` to `.wrap` under `ToInt32` demand.
- Elide `-0` checks.
- Representation selection: an int32 induction variable becomes an
  `I32` blockparam, with no boxing on the back edge.

## 11. v1 scope

"Declined" means that **a script is compiled by baseline alone when the
MIR builder meets one of these** (under `pipeline=mir`; BASELINE.md §5):

- a generator or async body that reads its actuals past its formals (a
  resume re-enters with none)

(Generator and async bodies, `arguments` and rest, `with`, direct eval
and the environment ops were on this list; they compile now: M5d, M5i,
M5j.)

Try/catch is supported (§5.3). There is no hidden decline for inlining.
The MIR builder does not inline anything, so calls in a MIR-compiled
script are always real calls.

## 12. Decision log

**Rev 2**
- Invariants are structural: per-ref facts are types, global facts are
  ghost values, and fences are paired with weakening. A validator checks
  them, with no flow typing.
- GC stays below MIR. `Raw` values may not cross may-GC ops. Rooting is
  done in lowering, by value-stack pushes.
- Types carry both representation and refinement.
- Generic `js.*` ops are in MIR.
- Try/catch is supported: throws exit to GEN.
- Loop tokens and peel funnels are handled only in lowering.
- MIR is the sole backend input.
- There is no functional memory model; accesses carry descriptors.
- The flags word is implicit, flow-carried state.

**Rev 3**
- Constructors are in v1, with prefix subtyping.
- The OPT/GEN boundary is `Val(⊤)`. Onramps enter through guard-chain
  roots `O` that jump to the preheader `P`.
- Deopt writes the frame, and onramps read it.
- Throw blocks are shared per PC.
- Alias regions are IR entities, one per class per field.

**Rev 4**
- Onramp roots only at loop headers (and function entry). Calls rejoin
  inside MIR through `ok_dirty` re-guarding.
- Loop-header types carry class claims.
- Stamp every array class region.
- Exits store every local and arg, and liveness pruning comes later if
  needed.

**Rev 5**
- Optimizations that must work (§10) are an explicit deliverable, with
  guard-count tests.
- Killable components are guarded locally at each use, and guard
  folding and hoisting merge the guards.
- Every kill is predicted or dynamic, checked through prediction
  witnesses (§4.5).
- `SLOTS` is local and tolerant: each op tests it and falls back to
  the IC while staying in OPT.
- Identity and `TYPES` (+`RANGES`) are killable type components. On
  failure, including a class-key miss, OPT exits to GEN. Loads feed the
  claimed type out, and stores require it in, so OPT stores never clear
  it and are not fences.
- `TYPES` is shallow. For object-typed fields it guarantees only the
  child's immutable components (kind, function script, singleton), not
  its layout identity or its `TYPES` bit. Both of those are guarded at
  the child's first use (§4.6).
- Prediction witnesses stay.
- Field claims extend beyond numbers to strings, booleans,
  null/undefined and objects (M5b). Maintenance is not per-field:
  generic writes clear `TYPES`/`SLOTS`/`RANGES` unconditionally, so
  `TYPES` is exact and loads are checkless.
  An object claim carries only immutable components; a child's layout
  identity is guarded at first use.
- `ok_dirty` re-guarding stays eager (up to the clean edge's types).
  Heuristics can come later.

**M0 (implementation)**
- An `err` edge into a *throw block* is not a fence edge. A throw block
  has no params, contains only upcasts (`box`, `weaken`) and constants,
  and ends in `exit.throw`. Nothing in it relies on a killable
  component, so it may upcast pre-op values whose claims the op killed
  (§5.3's "no params"). An `err` edge to any other block is a fence edge
  with the op's kill pattern.
- A declared result type may be any supertype of the op's rule. `weaken`
  is the op whose only purpose is that.
- `new_object K` yields `Obj{Plain, K constructing(0)}`, and
  `init_field` is always a fallible terminator.
- `check.native` produces `Fact(NativeIntact)`. `f64.to_int_exact`
  yields an `I32`.
- Every static kill needs a witness, including structural ones such as
  `publish_layout`'s kill of constructing claims.

**Rev 6**
- The baseline tier (`docs/BASELINE.md`) replaces GEN as the deopt
  destination and onramp source. Its frame format is the interface
  between the tiers.
- MIR and baseline are separate Wasm functions. Exits write the frame
  and resume baseline (`ARGC_RESUME_BIT` plus the frame's resume word).
  Onramps are calls from baseline loop headers (`ARGC_ONRAMP_BIT`),
  and a MIR body entered that way returns `err = 2` to deopt. Loop
  tokens and peel funnels are gone.
- MIR has no reducibility invariant. MIR declares its loops, and
  waffle's reducifier handles onramp side entries. Measuring its cost
  comes after M3, and changing waffle comes only if the data calls for
  it.
- `exit`/`exit.throw` carry the rval. `Val(⊤)` includes magic values.
- MIR does not maintain a baseline frame while it runs. It uses the
  NightStack only for GC rooting, and writes the whole frame at an exit.
- `docs/MIR-GEN-SEAM.md` is retired.

## 13. Implementation plan

Each milestone ends with a test gate. MIR is enabled per script behind
an option (`Options`), and the legacy path remains the fallback when
the builder declines. Diagnostics report per-script MIR/legacy/decline
counts, with reasons, so that coverage is measured rather than assumed
(DESIGN.md §12).

**M0. IR core** (`compiler/src/mir/`)
- Entities, the type lattice with subtyping and join, the op
  definitions, and effect summaries.
- The printer and parser.
- The validator: dominance with multiple roots, edge subtyping, operand
  types, fences, `Raw` across may-GC, and exit arity.
- Gate: unit tests on hand-written textual MIR, including negative
  validator tests.

Baseline steps B0–B4 (BASELINE.md §8) come before M1: MIR needs a
total baseline to exit into.

**M0b. M0 follow-ups for rev 6**
- `TagSet` gains `magic`. `Val(⊤)` includes it, nothing unboxes it, and
  `guard.tags` can remove it.
- `exit`/`exit.throw` and onramp roots carry the rval.
- Loops are declared (header, preheader). The validator's
  "irreducible" error goes, and its preheader check keys off the
  declared loops.
- **Done.** The text format spells an exit `exit pc=N this=… args=[…]
  locals=[…] rval=… stack=[…]`, and a loop `loop bH preheader=bP` in the
  function header. The validator's loop rules:
  - a latch is a predecessor of the header, other than the preheader,
    that the header reaches;
  - any other predecessor enters the loop from outside and is an error;
  - the preheader jumps only to its header;
  - an edge to a block that dominates its source (a natural loop) must
    target a declared header.

**M1. Minimal lowering, MIR to its own waffle function**
- The function-entry root, and the entry dispatch.
- Lowering for constants, int32/f64/int arithmetic, compares, `br`,
  `jump`, loops, `return`, `exit`, and `exit.throw`. Exits and throws
  write the baseline frame and resume baseline (§5.1).
- Flags threading, returning `FLAGS_ALL` wherever it is not yet
  derived.
- Gate: hand-written MIR for small scripts runs correctly, including
  forced exits into baseline.
- **Done** (`wasm/mir/lower.rs`, with the driver in `wasm/mir/mod.rs`):
  - **Values.** Each MIR value lowers to waffle values of its machine
    type. A managed value (`Val`, `Obj`, `Str`) may also live in its
    home slot (§4.4).
  - **Rooting.** As in §4.4: home slots, stored once before the first
    may-GC op a value is live across, reloaded lazily. The entry pads
    the formals with undefined first and initializes the rooting area,
    so `[sp, top)` is always valid Values.
  - **Generic ops** always take `ok_dirty` until helpers report
    cleanliness (M4). That is sound, just conservative.
  - **Exits** write the whole frame and call the baseline body with
    `ARGC_RESUME_BIT`. The baseline side of M1 is in `BASELINE.md` §4
    and §8: an entry fork that routes by the resume word, plus
    throw-mode landings.
  - **Two bodies per script.** `Outcome::Compiled` carries the baseline
    body as an extra body, placed after the adapter block.
  - The gate ran through M2's builder rather than through hand-written
    MIR injected into a live script. The fixtures lower to valid Wasm
    (unit tests), and the jit-test lanes and the stress mode exercise
    them at runtime.

**M2. JSOps-to-MIR builder** for the M1 subset (locals and args as SSA,
guard-at-defs, `js.*` fallbacks for arithmetic and compare, and
declines for everything else).
- Gate: the jit-tests lane passes under `pipeline=mir`, and the counts
  show MIR actually compiled the scripts.
- Also add a **stress mode** that fails a fraction of guards (or every
  Nth one) at runtime. It exercises exits, throw exits and, later,
  onramps on code the tests would otherwise keep on the fast path.
- **Done** (`wasm/mir/build.rs`):
  - **Types.** Every frame slot (`this`, formals, locals, rval, stack)
    has an abstract type: a raw `I32`, `F64` or `Bool`, or `Val` with a
    tag set.
  - **Block entry types** come from a fixpoint. The builder runs over
    the whole script into a scratch function and records the types
    reaching every block. Where they are wider than the block's entry
    types, those widen (`I32 < F64`; anything else joins to `Val` of the
    union of the tags), and the builder runs again. The run where
    nothing widens is the result, so the type policy exists once, in
    the emitting code.
  - **Guard-at-defs** is applied to formals from `arg_types` at the
    entry root. A failure exits at pc 0.
  - **Numeric ops** take the int32 path (overflow-checked, exiting at
    the op's pc) when both operands are int32, the f64 path when both
    are numbers, and `js.*` otherwise. Compares follow the same rule.
  - **Every fallible op** exits at its own pc with the state from before
    the op. Every `js.*` op's `err` goes to its pc's throw block. Both
    blocks are shared per pc.
  - **Loops** get a preheader, and the builder declares them.
  - **Declined:** global scripts, generators and async functions, class
    constructors, scripts that read their actuals, scripts with an env
    chain, and any op outside the subset. That includes
    `Uninitialized`: MIR has no constant for the TDZ sentinel yet.
  - **The stress mode** is `--mir-stress N`. Every lowered guard also
    fails on every `N`th guard executed program-wide (a runtime counter,
    `night_runtime_mir_stress`).
  - **The fixpoint, revised.** Within a run, an edge to a block not yet
    entered goes through a trampoline that the block's entry fills in.
    So a block's entry types join every forward edge of the same run,
    and only a loop's back edges can call for another run. The first
    version needed a run per forward block that widened, and failed to
    converge on large functions.
  - **Size.** Scripts over 32 KiB of bytecode stay in baseline. A MIR
    script carries two bodies, and the gate keeps the batch's memory in
    bounds. (It was briefly 8 KiB, while exits were quadratic; see
    §5.1's write-through. With 128 KiB, mandreel's four 32-128 KiB
    functions still overrun the in-process compiler.)
  - **Gate met** (2026-09-26):
    - `--pipeline mir --strict-coverage` passes the full jit-test lane;
    - so does `--pipeline mir --mir-stress 3`;
    - a `--dump-tiers` census over every jit-test file counts 3408 MIR
      script compilations. The leading declines in user code are
      `GetGName`, `Uninitialized`, reading actuals, `TypeofEq` and
      string constants.

**M3. Onramps**
- Declared loops, preheaders `P`, and roots `O`, with the onramp-root
  policy.
- Baseline loop headers call into `O` with backoff, and handle a DEOPT
  return.
- Gate: tests under the stress mode, including onramps into nested
  loops.
- **Done:**
  - **Roots.** Every loop header that has a preheader gets an onramp
    root. The root re-deopts at the header with its own params, and the
    policy knob is still to come.
  - **Entry.** The MIR entry dispatches on `ARGC_ONRAMP_BIT` by the
    resume word, and loads the root's params from the frame. It pads
    the formals only on a fresh entry.
  - **Exits** also set the frame's onramp backoff. Under an onramp they
    return `ERR_DEOPT` instead of calling baseline.
  - The baseline side is in `BASELINE.md` §7.
  - **waffle fix.** Onramps into nested loops made waffle's reducifier
    fail. `resolve_aliases` left aliases in terminator operands, which
    the duplication did not remap. That is fixed in waffle (branch
    `cfallin/resolve-aliases-terminators`), which the workspace uses
    through `[patch.crates-io]` until a release.
  - **Tests.** `tests/jit-test/night/mir-onramps.js` covers re-entry,
    re-deopt, nested and triply nested loops, and loop-carried values
    of every representation. It and the jit-test lane pass under the
    stress mode.

**W. waffle's reducifier, driven by M3 data** (BASELINE.md §8): measure
the duplication on real onramp-shaped MIR, and change waffle only if
the numbers call for it.
- **Measured (2026-09-26)** over every jit-test file under `--pipeline
  mir`. The regex matchers, which reducify in every pipeline, were
  subtracted per file.
  - Only 12 MIR bodies needed reducification. Their blocks grew 1.30×
    (at most 1.40×) and their values 1.73× (at most 2.42×; the max-SSA
    cut's params), with at most 4 contexts.
  - With onramps on outermost loops only, none did.
- **The onramp-root policy** is `--mir-inner-onramp-bytes N` (default
  400): an inner loop gets a root only when its outermost enclosing loop
  spans at most `N` bytecode bytes. In this data the default behaved the
  same as no limit.
- **No reducifier change is called for.** The one waffle change so far
  is the alias fix M3 needed. MIR's coverage is still the M2 subset,
  so re-measure once M4 widens it.

**M4. Objects and calls**
- `guard.layout {types}`, and `load_field`/`store_field` with the local
  `SLOTS`-versus-IC lowering and typed results (§4.3).
- Local-first guarding, with **guard folding and hoisting (§10.1,
  §10.2)** and the §10.3 fence/rejoin tests.
- Prediction witnesses and the §4.5 validator rule.
- Generic `js.getprop`/`setprop`/… lowered through the IC ladders.
- Generic and direct calls with `ok_clean`/`ok_dirty`/`err` edges and
  `ok_dirty` re-guarding.
- Rooting in lowering.
- **M4a done (the generic half).** New ops and their lowerings:
  - `js.getname` (`GetGName`). It is `ok`/`err` with a static kill, so
    the builder attaches its prediction witness ("may kill anything").
  - `js.getprop`, `js.setprop[.strict]`, `js.getelem`,
    `js.setelem[.strict]`, through the runtime helpers.
  - `call` (`Call`, `CallIgnoresRv`, `CallContent`), lowered like
    baseline's calls. A compiled callee is entered directly through
    `call_indirect`, else through the generic helper. The callee's frame
    goes just above the rooting slots.
  - Strict `FunctionThis`.
  - `const.val uninitialized` (the TDZ sentinel, `Val{magic}`), so
    `let` bindings compile.
  - The leaf compares `js.typeof_eq` and `js.constant_strict_eq`, and
    `IsNullOrUndefined` as a `guard.tags` whose failure edge merges
    back.
  - The stress mode fails only guards whose failure exits.
  - Also `js.box_this` (sloppy `this`), `const.str` (lowered through
    the atom helper, with rooting at a non-terminator), `js.bindgname`
    and `js.setname[.strict]` (global assignment), and switch statements
    (`TableSwitch` as `switch`, plus `Case` and `Default`).
  - **Guard-at-defs on results.** A generic element or property read,
    or a call, has its result guarded to the analysis's claim
    (`elem_sites`, `field_sites`, `call_types`). The op has happened, so
    a failure exits at the *next* pc with the unguarded result on the
    stack.
  - A generic element read tries an in-bounds dense element inline.
    The runtime's `get_element` helper gained the same arm.
- **M4b, first part: typed property access.**
  - A `GetProp` at a site with a `prop_sites` prediction becomes
    `guard.unbox.obj`, then `guard.layout keys {types}`, then
    `load_field`. It is guarded locally at every use; folding comes
    next.
  - The module's layouts are filled from those sites. A slot the
    module does not describe is a `hole` (`Layout.fields` is
    `Vec<Option<FieldDef>>`).
  - `types` is asked for only where the claim is a number and the
    site's receivers can carry the bit: TYPES maintains numberness only
    (§4.6). An int32-only claim is then one `guard.unbox.i32` on the
    loaded value.
  - A `SetProp` of a number into a number-claimed field becomes
    `store_field`. A number over a number needs no barriers and keeps
    TYPES.
  - The lowering tests SLOTS locally: the fixed slot on a hit
    (`ok_clean`), the generic helper otherwise (`ok_dirty`).
  - **Validator rule relaxed:** a field whose claim is `Val(⊤)` needs no
    `types` on the receiver, since TYPES says nothing about it.
- **Numeric demand, the simple case (from §10.6).** An int32 `Add`/`Sub`
  whose result reaches only truncating ops (`|`, `&`, `^`, shifts, or
  another such add) is `i32.*.wrap`: no overflow exit. The builder finds
  them with a per-block stack simulation over the bytecode.
- **Guard folding (§10.1), first part** (`mir::opt`). A guard dominated
  by the same guard on the same value, with no fence between that kills
  its output's type, takes the dominating guard's output; block params
  whose incoming values all agree are forwarded. `check.fuse` is not
  folded yet.
- **Exit census.** `--mir-exit-census` counts every exit at runtime
  (census kind 90) and prints the static map `night: mir exit <id>
  sid#<s> pc <p> <mode>` while compiling. It found the next item.
- **Stamping outside bbv.** Nothing stamped objects outside the legacy
  tier, so every `guard.layout` failed and MIR exited to baseline at
  every typed access (richards took millions of exits). Now:
  - a baseline `new` passes the construct site's sized allocation and
    early stamp word, computed as bbv does
    (`bbv::construct_nslots`/`construct_alloc_word`, shared);
  - every return of a layout constructor (baseline or MIR) calls
    `night_runtime_ctor_stamp`, bbv's first-stamp gates as a leaf
    helper: the CONSTRUCTING sentinel with our early key or none, a
    slot span covering the layout, then the idx plus the surviving
    validity bits;
  - restamps (init delegates, fill scripts) are bbv-only still.
- **TYPES only on all-number layouts.** Outside bbv every store goes
  through the engine or MIR, and the engine drops TYPES on any
  non-number store to any field. So a constructor that stores one
  object field loses the bit for all of them. `types` is now requested
  only for layouts whose fields all carry number claims. Elsewhere a
  typed load is guarded at its def against the analysis's claim, as the
  generic reads are.
- **Typed stores of any value** into a layout without a TYPES claim.
  The lowering's fast path requires SLOTS, no RANGES (consumed
  checklessly, so an unchecked store must not keep it), and no TYPES
  unless the value is a number; anything else takes the generic helper
  (with the script's strictness), which maintains the bits. A store of a
  possible GC thing runs the incremental pre-barrier (zone flag inline)
  and the generational post-barrier (tenured owner, nursery value)
  inline, calling the runtime's barrier helpers only when they fire.
- **Fused globals (§3).** A `GetGName` of a global the runtime has
  fused to a primitive literal is `check.fuse F` (exit if the fuse word
  no longer reads 1) and then the literal as a typed constant.
  `FuseDef` gained the fuse word's address (`fuse F0 = "K" addr=N`).
- **Inline ToBoolean and equality.** `js.to_bool` dispatches on the tag
  inline, and objects are truthy while the runtime's emulates-undefined
  fuse is intact. Equality compares take `ok_clean` inline where the
  operands' bits decide:
  - strictly, when neither operand is a double, string or BigInt;
  - loosely, for int32/int32 and boolean/boolean pairs, and for
    null/undefined/object pairs while that fuse is intact.
- **Inline global reads.** A `js.getname` of a syntactic global
  binding (`syn_gnames`, in functions MIR compiles) has bbv's arms
  inline, each taking `ok`:
  - the binding's value-fuse cell, while armed;
  - else its cached slot row, while the global's shape is the one the
    row was resolved against;
  - else the resolve leaf (no GC), then the slot.
  Anything else (lexicals, TDZ, accessors, deleted globals) goes through
  the helper. deltablue under MIR: 1964 → 2682.
- **Inline numeric arms for untyped ops**, as baseline has: int32, then
  doubles, then the helper, so code whose types MIR does not know no
  longer runs slower than in baseline.
- **`new`.** `IsConstructing` is a magic constant, and `New` becomes
  `construct(nslots, word)`, carrying the site's sized allocation and
  early stamp word. It lowers to the runtime's construct.
- **Property ICs for unpredicted sites (§4.3).**
  - A `js.getprop` calls the module's shared probe `night_ic_get` with
    the site's IC row. It covers the own and holder ways, then the
    megamorphic table. A hit takes `ok_clean`; a miss calls
    `get_prop_ic_miss`, which fills the ways.
  - A `js.setprop` has bbv's way-0 arm inline: an overwrite of the own
    slot the way names, when the object's word has no RANGES and, for a
    value that is not a number, no TYPES. Barriers are as for
    `store_field`. A miss calls `set_prop_ic_miss`.
  - The transition (add) and megamorphic set arms stay bbv-only.
- **Inline dense element overwrite.** `js.setelem` stores an in-bounds,
  non-hole dense element inline when the elements are not frozen and the
  word has no RANGES, with the element barriers.
- **Environment chains, the fixed case (M5, first part).** A script
  whose activation environment is its callee's own (no call object, no
  named-lambda scope: baseline's `env_is_plain`) now compiles:
  - the fresh entry writes the callee's environment to the frame's env
    slot, where it stays for the activation (exits leave it alone), and
    `env.current` reads it back;
  - `GetAliasedVar` is `env.parent`^hops then `env.load`, and its result
    is guarded at the def against the analysis's `aliased_sites` claim;
  - `SetAliasedVar`/`InitAliasedLexical` are `env.store`, lowered to the
    runtime's leaf store (with its barriers); `CheckAliasedLexical` is
    `CheckLexical`'s guard; `Lambda` is `js.lambda` over the env;
  - scopes that push environments (`PushLexicalEnv` and the rest) still
    decline.
  Non-fused `GetGName` results are likewise guarded at the def against
  `gname_types`. navier-stokes, whose hot code reads closure variables,
  goes from 3987 to 11200.
- Measured at this point (Octane, in-process, best of two, versus
  `--pipeline baseline`): richards 424 → 634, crypto 3187 → 3780,
  deltablue 597 → 650, box2d 1970 → 2109; the rest are within noise
  or slightly below baseline (compile time: MIR scripts carry two
  bodies). The legacy tier is still 2-10x ahead; the remaining cost is
  mostly generic property access at sites without predictions and
  generic compares.

**M5. Remaining v1 coverage**
- Elements and typed arrays, including array stamping in the analysis.
- Globals: fused literals are done; syntactic bindings (`gcell`) remain.
- Constructors (`init_field`/`publish_layout`).
- Environment ops.
- Accurate flags words.
- Liveness-pruned exits, if needed.

**M5b. Richer field claims (§4.6)**
- Emission of per-field tag sets and immutable object components from
  the analysis's view cells.
- Generic writes clear `TYPES|SLOTS|RANGES` unconditionally: the engine
  hook's `storeClearMask`, GEN's inline choke, and runtime helpers.
- Legacy-OPT typed stores check the exact per-field claim statically
  (the transition hazard in §4.6); other legacy stores clear.
- Checkless loads for all claimed fields.
- Demotion census by bump site, to measure permanent demotion from
  generic writes.
- Gate: field-claim coverage counts (fields claimed per class, by
  category), and the guard census showing loads no longer tag-checking
  claimed fields.

**M5c. Direct calls and inlining (2026-09-27; see §5.5).** Profiles of
richards put the gap to bbv here: bbv's hot loop inlines the small task
methods, and MIR calls them, paying `night_call_classify` and a
`call_indirect` per call.
- **Implemented as designed in §5.5**, in `wasm/mir/inline.rs` and the
  builder's `inline_call`. Callees must be at most
  `INLINE_MAX_BYTECODE` (200) bytes and at most 800 MIR instructions.
  Nesting goes at most 2 deep, and a site takes at most 4 targets.
- The `guard.script` check is inline: a function class, the script
  slot, and a compiled script. Unpredicted property reads have way 0 of
  their IC inline: the own fixed slot, then the prototype holder.
- Structured control flow in waffle's backend (lowering, and drop of the
  `WasmBlock` tree) is now iterative. MIR's guard chains nest deep
  enough to overflow a rayon worker's stack (pdfjs).
- AOT richards: 3318 → 7442 (legacy bbv: 11886).

**M5d. Toward bbv parity (2026-09-27).** Driven by AOT Octane profiles
and exit censuses against bbv, not by op coverage.
- **Speculation.** Number claims without a double history are int32
  first (formals, elements, aliased vars, globals; not fields or call
  results, where it cost double exits). A typed field whose layout guard
  fails falls back to the site's IC instead of exiting.
- **Globals and ops.** Syntactic global writes are inline; `instanceof`,
  `in`, own-property tests, deletes and object/array literals are
  `js.rt` leaves or may-GC calls; `throw` and `typeof` are ops.
  `instanceof` walks the prototype chain inline from the site's cell.
- **Actuals.** Scripts reading `arguments`, rest or the actual count
  compile, with `vp` as baseline's. They are not inlined. A sloppy
  script with no formals may use `arguments` (nothing to map).
  `T.apply(this, arguments)` at bbv's proven sites does not make the
  object: known targets are inlined over the frame's actuals, else the
  runtime forwards them; an exit while it is elided makes it first.
  Nor does an object only read for `.length` and elements
  (`compute_args_reads`: no formals, each value consumed straight-line
  by those reads, stored only into locals written once before any
  branch; scheme runtimes' variadic `sc_list`, `sc_append`): `.length`
  is `args.length`, `a[i]` an int32 index within it reads `args.actual`,
  and anything else exits, making the object. (Added 2026-09-29:
  earley-boyer +5.0%. Such a script still inlines nothing, bbv's rule;
  letting it inline over the actuals read in place is to measure.)
- **Construction.** `new` of a compiled constructor is direct:
  `this` is a nursery bump from the site's construct cell (while the
  callee's shape, IC generation and `.prototype` match), else
  `create_this`; then a `call_indirect` of the body. Init-delegate
  restamps run as in bbv.
- **Property ICs.** The set IC replays its add-transition row inline
  when the add cannot falsify the class-word bits.
- **Environments and try.** Scripts with their own call object compile
  (`env_setup` at entry). Try/catch compiles as designed in §5.3; the
  catch code is baseline's.
- AOT, MIR vs legacy bbv: richards 7248/11886, deltablue 3782/6175,
  crypto 7422/15502, raytrace 6332/11754, earley-boyer 5162/13224,
  navier-stokes 11619/22660, splay 5906/7653, pdfjs 7700/20484.

**M5e. Proofs in the builder's types (2026-09-27).** Micro-benchmarks
isolating one pattern each (field updates through `this`, polymorphic
calls over a list, allocation, `am3`-style array arithmetic), AOT against
bbv, found the costs; the fixes are general.
- **Proven receivers.** The builder's slot types carry what a dominating
  guard proved: `Obj(keys, types)` (a raw object of those layouts),
  `ObjHint(keys)` (proved before a fence: the next typed access guards
  again, exiting on a miss) and `Native` (elements addressable). A
  method's `this` is guarded to `this_layouts` once, at `FunctionThis`;
  typed sites whose receiver the slot covers take no guard and no IC
  fallback. A fence weakens `Obj` slots in place (a `weaken` before the
  terminator), the fence rule's weaker param.
- **Dirty IC arms exit.** A typed load or store whose IC arm ran (a SLOTS
  miss) exits at the next pc instead of rejoining, so the clean path keeps
  its facts.
- **Guard folding** keys guards by their operand up to `unbox` and folds
  into an available guard of the same kind whose output implies it; block
  params whose incoming values agree are forwarded (not across a fence
  edge that kills the value's type), and the lowering runs in reverse
  postorder.
- **Elements.** Element accesses the analysis predicts on arrays (or whose
  reads it saw yield numbers or objects) with int32 keys are `load_elem`
  / `store_elem` on a `Native` receiver, with the generic op for holes and
  out-of-bounds indices. A receiver guard whose loop brings the proof back
  around is hoisted to the loop's entry (§10.2): the header's slot is
  `Native` and the entry edges guard, exiting at the header.
- **Stores and stamps.** Inline stores drop RANGES (no MIR claim rests on
  it) rather than take the engine path, and clear TYPES for a non-number
  only on an object still under construction, so constructors' field adds
  replay their transitions inline. A layout constructor's first stamp is
  inline. Snapshot objects are stamped by their constructor, not by their
  field list alone (two classes with one field list got one key, and
  their methods' `this` guards all missed).
- **Smaller things.** `StrictConstantEq` inline (MIR and baseline); MIR's
  rooting slots overlap baseline's operand slots, so the entry initializes
  only the fixed frame and locals; an overflow-checked multiply tests for
  -0 only on a zero product.
- Micro-benchmarks (ms, MIR / bbv): fields 190/187, calls 145/138,
  alloc 176/102, arith 150/128. Octane moves less: MIR's remaining gap
  there is spread across calls not inlined (constructors, callees over
  200 bytes), frame write-through and code size.

**M5f. Coverage and typed arrays (2026-09-27).**
- **Declines closed.** `ToPropertyKey` (compound element assignment; a
  no-op for an int32, string or symbol key), regexp literals, getter and
  setter literals, `GetFrameArg` (a formal's frame slot, as `GetArg`),
  and mapped `arguments` with formals: the entry makes the object before
  anything can exit, and `GetArg`/`SetArg` are the leaf ops
  `args.mapped`/`args.mapped_set` on it, as baseline's are.
- **Typed arrays.** Element accesses the analysis predicts on a typed
  array of one kind (`ta_elem_sites`) with int32 keys are
  `load_ta`/`store_ta` on a receiver of the builder's `Ta(kind)` slot
  type (`guard.kind TypedArray(k)`: a class compare), its guard hoisted
  to the loop's entry like a native receiver's; out of bounds, the
  generic op. Integer kinds load and store int32s, float kinds doubles
  (a NaN load is the canonical NaN); clamped and Uint32 arrays stay
  generic.
- **Fixes.** An inlined callee's getter/setter definitions kept their
  callee atom ids (the splice's op remap missed them). A script making
  its own environment read `this` and the formals from the frame before
  `env_setup`, which may GC: a moved nursery formal was then stored into
  the call object at its old address (earley-boyer crashed under AOT);
  they are read again after it.
- Octane under MIR vs bbv: crypto 11886/15378, navier-stokes
  20182/23058, earley-boyer 8479/13272.

**M5g. IC misses (2026-09-27).** `--mir-exit-census` also counts each
`js.getprop` site's IC misses (census kind 91, `night: mir getmiss`),
which found the helper calls the ICs cannot avoid:
- `length` is no slot: a string's length word, an array's elements
  header and an arguments object's packed length are read inline
  (deltablue took 11M misses on one array `length`; +14%).
- `s.charCodeAt`/`s.charAt` on a string read the cached pristine natives
  while the String fuse is intact, and the call arms (bbv's) load the
  char of a linear string inline; `String.fromCharCode(c < 256)` is a
  static unit string (crypto's 5M misses).

**M5h. Inlining constructors; inlining limits (2026-09-27).**
- `new F(…)` of a site's one constructor is inlined: with the callee
  that script's function and a constructor (`fn.is_ctor`: not an arrow
  function or a method), `create_this` makes `this` as a direct construct
  does (the site's construct cell, else the runtime), the body is spliced
  with its frame's new.target (`inline.enter`'s extra operand), and the
  result is the body's value if an object (`guard.tags`), else `this`.
  A layout constructor's stamp is now an op the builder emits at every
  return (`ctor.stamp`, a no-op unless `this` is under construction), so
  an inlined copy stamps too, and stamping constructors are inlinable.
- Inlining limits as bbv's: callees up to 500 bytes of bytecode and 2000
  MIR instructions, at most 8 inlined sites and 6000 spliced
  instructions per function (per built function: an inlined callee has
  its own), nesting 2 deep; a function past 60000 instructions stays in
  baseline. With inlined callees, only outermost loops get onramp roots:
  an inner loop's side entry makes waffle's reducifier duplicate the
  loops around it, inlined code and all (a pdfjs body reached 8.9 MB,
  past wasm's function size limit).
- The 500-byte limit is a trade: richards (its task methods are ~400
  bytes) gains 12% over 300 bytes, earley-boyer loses 9%; the cause of
  the latter is not yet known.
- Allocation micro-benchmark: 176 -> 116 ms (bbv 100).

**M5i. Completeness: the jit-test decline census (2026-09-28).** A
`--dump-tiers` census over the jit-tests (the first decline of each
script) ranked the ops; every one but generator and async bodies
compiles now, lowered onto baseline's helpers:
- **Class constructors** compile (a plain call is never inlined or
  forwarded to one; baseline's call throws). Derived constructors:
  `super(…)` is a `construct` with no site sizing, as baseline's;
  `super(...a)` is the spread helper; `CheckThisReinit`, `CheckReturn`
  (which reads the frame's rval, so rval liveness counts it),
  `SuperBase`/`SuperFun`, `super.x`/`super[k]` reads and writes,
  `InitHomeObject`, `FunWithProto`, and the class checks
  (`CheckClassHeritage`, `CheckThis`, `CheckPrivateField`), `SetFunName`.
- **The iterator protocol and spread.** `CallIter` is `call.iter` (the
  call, with the iterator error for an uncallable callee);
  `OptimizeGetIterator` is `iter.optimizable`; `CheckIsObj`, `CloseIter`,
  `OptimizeSpreadCall`, `SpreadCall`/`SpreadNew`, and array spread
  (`InitElemInc`, its index an int32, wrapping as baseline's) are
  `js.rt` ops.
- **Scopes that push environments (§5.1's fixed chain, extended).** The
  frame's env slot is write-through: a scope's entry (`PushLexicalEnv`,
  `PushClassBodyEnv`, `PushVarEnv`, `EnterWith`, `FreshenLexicalEnv`,
  `RecreateLexicalEnv`) makes the new environment with baseline's helper
  and `env.set` stores it; its exit (`PopLexicalEnv`, `LeaveWith`) is
  `env.pop`. An exit, and baseline's unwind after a throw, see the
  current environment in the frame as baseline would. `env.current`
  reads the new `frame.env` region, which `env.set`/`env.pop` write, so
  nothing hoists it across a scope. Nothing else writes it: code the
  frame calls runs in frames of its own, so `unknown` does not cover
  `frame.env`. (The first version let it; env reads then stopped hoisting
  out of loops with calls, and crypto lost 3.5% until 2026-09-28's fix.)
- **Names through the chain and eval.** `GetName`, `BindName`,
  `BindUnqualifiedName`, `SetName`, `DelName`, `BindVar` and
  `EnvCallee` read the frame's environment. A direct eval is `call.eval`,
  a call frame for baseline's eval helper over the frame's environment.
  (Such scripts keep their bindings in environments, which eval's code
  reads and writes; `call.eval`'s effects are a call's.)
- **The rest.** `Callee`, `GlobalThis`, BigInt literals, `MutateProto`,
  holes, `??`, `Object`/`CallSiteObj` (the script's object: no copy),
  computed-key accessors, `debugger` (a no-op, as baseline's), `ThrowMsg`,
  and a `CheckLexical` whose value is surely uninitialized, which exits
  (baseline throws).
- **A second census** after these left only generators and a short tail,
  now also `js.rt` ops over baseline's helpers: `using` declarations
  (`AddDisposable`, `TakeDisposeCapability`, `CreateSuppressedError`),
  `GetBoundName`, `ObjWithProto`, `NewPrivateName`, `DynamicImport`,
  and spread direct eval (`SpreadEval`).
- **Generators and async functions** remained declined here; M5j builds
  them.
- An inlined callee's `js.rt` atoms are renamed into the caller's table
  by `RtOp::map_atoms`, an exhaustive match: the splice's old list
  missed the new name ops, so an inlined `GetName` looked up an
  unrelated string (four jit-tests caught it).
- Night tests: mir-iter-spread.js, mir-scopes.js, mir-misc-ops.js,
  mir-rare-ops.js. One
  jit-test joins `jit-test-excludes-mir.txt`: bug1762575-3.js depends on
  a dead local keeping its object alive, as gc/compartment-revived-gc.js
  does.

**M5j. Generators, bbv's inlining limits, typed `length` and globals,
guard hoisting (2026-09-28).**
- **Generators and async functions (an extension of §5.2).** A yield
  (`InitialYield`, `Yield`, `Await`) is `gen.suspend`, a terminator with
  an exit's operands at its pc: the lowering writes the frame (a dead
  local as undefined, so an out-of-scope binding does not stay alive in
  the suspended generator), saves it into the generator with baseline's
  `gen_suspend`, and returns the yielded value. Each yield's landing is a
  `Resume { index, pc }` root: the frame there, `Val(⊤)`, guarded up to
  the types the slots had at the yield (a miss exits at the landing).
  The body's entry, after the resume and onramp forks, takes a
  generator's resume (`EnterNightResume`'s generator-closing `this`):
  it dispatches on the resume index first (compares for up to four
  yields, a `br_table` past that), restores the frame with
  `gen_restore`, pushes `[sent value, generator, resume kind]`, and
  enters the root; an index with no root (a yield in catch code, which
  is baseline's) goes to baseline's own dispatch, descriptor untouched.
  Baseline's entry now takes `ARGC_RESUME_BIT` over the magic `this`
  (an exit from a resumed activation). The rest are `js.rt` ops over
  baseline's helpers (`CheckResumeKind` raises through the helper with
  the rval slot left to it; `FinalYieldRval` counts as an rval use).
  A resume's path re-enters its loop at the header past the preheader:
  the validator allows that for blocks a `Resume` root reaches, and
  `licm`/`hoist_guards` leave such loops alone. A `for (…) yield`
  micro-benchmark runs in MIR with no exits per yield (1222 ms vs
  legacy's 1547).
- **Inlining admission is bbv's** (`Bbv::inline_candidates_for`, in its
  order): depth 8 below a call site in a loop, else 4; 8 spliced
  segments per function (one per target, nested ones included, counted
  depth-first: a callee is built with what the budget has left and
  charges what it used; the budget is checked once per site, as bbv
  does); per-target bytecode caps
  (150, 200 in a loop, 500 per target of a poly site); no loop-bearing
  callee under a loop; a construct's transitive closure cost
  (`splice_closure_cost`, now shared); no splicing into a function that
  uses `arguments`, mapped formals or actuals; no call site in a catch
  or finally range; bbv's splice fuel, at ~4 waffle values per MIR
  instruction (25000 instructions, 60000 for callees of at most 160
  bytes). MIR's own callee and per-function instruction budgets are
  gone. Richards' `Scheduler.schedule` now splices `TaskControlBlock.run`
  and the task `run`s under it as bbv does.
- **`length`** (§7): a proven string's `length.string`; a receiver the
  builder has evidence is an array (a native object its element accesses
  guarded, or an array layout's value class) is `guard.kind Array`,
  `length.array` and `int.to_i32` (a new guard: an `int` in int32's
  range). A summing loop over `a.length` goes from 105 to 61 ms (legacy
  102).
- **Globals** (§3): a syntactic global's read is `check.binding` then
  `load_gname`, its write `check.binding.write` then `store_gname` (the
  slot store with the barriers, the binding's value fuse, the bind
  epoch, and a fused literal's fuse, as the inline store did). The
  module's bindings carry the runtime's row (`slot`). An unresolvable
  binding exits (a syntactic global is a non-configurable data
  property: once resolved, the check holds). A read of a binding whose
  value fuse is armed takes the value table's copy, the check's armed
  arm going straight to `ok`. `fold_guards` folds repeated checks, not
  across JS (a global's shape changes with no epoch bump). Inlining
  merges bindings by row. Cost: in call-heavy code, where no check
  folds or hoists, a read is the check (one extra fuse-word test and a
  cold exit) plus the load; earley-boyer is ~2.5% below the generic
  op's inline arms. Removing that needs the binding fact to carry its
  armed state at run time.
- **Guard hoisting (§10.2)**: `opt::hoist_guards`, in the optimizer's
  fixpoint (which now forwards params first, so a loop's invariant
  values are visible as such). A guard in a loop whose operand is
  defined before the loop moves to the preheader when, judged on the
  loop as it would be with every such guard hoisted (their failure-only
  paths gone, as a greatest fixpoint), it runs on every iteration and
  nothing left in the loop kills its fact (a kill on an edge that leaves
  the loop does not count; `check.fuse`/`check.binding` also need no JS
  in the loop). A hoisted guard fails to an exit at the loop header with
  the loop's entry state, which the builder records per loop
  (`LoopEntry`). The in-loop guard becomes a jump carrying the hoisted
  outputs. A loop reading two fields of a parameter goes from 49 to 36
  ms (legacy 37).
- Night tests: mir-generators.js, mir-length.js, mir-globals.js,
  mir-hoist-guards.js.

**M5k. Analysis-chosen slot layouts (2026-09-29; KICKOFF-6).** A layout
row lists a class's fields in bytecode first-write order, the union over
the constructor's paths. An object whose path wrote them in another order,
or skipped some (pdfjs's `Font`: an early return after `type`, a `Type3`
return before `loadedName`), put later fields in lower slots than the row
said and lost SLOTS, and every `{types, slots}` guard on it exited. Now each
row field goes in its row slot whatever the order:
- **Engine** (the firefox fork, generic mechanism usable by any external
  tier): `SharedShape::getShapeWithPropertyAtSlot` makes the shape adding a
  property in a chosen slot (a hole or past the span; skipped slots become
  holes holding undefined), `NativeObject::addPropertyWithShape` installs
  it, and the `shapeForAdd` hook lets the tier place a property the engine
  adds (interpreter, IC misses, baseline's helpers). A slot other than the
  span sets `ObjectFlag::PermutedSlots`, inherited by derived shapes and
  mirrored into the shape's immutable flags (bit 21); such a shape's span is
  its highest slot plus one, computed when the shape is made. Engine paths
  that assume slot i holds property i refuse it (Object.assign's fast path,
  the JSON/`NewPlainObjectWithProps` cache, the megamorphic set cache, add
  stubs, remove-last-property). The visible property order is unchanged.
- **Runtime** (policy): `NightShapeForAdd` places a plain data property
  named by the object's layout (the early key while constructing, else the
  stamped idx) in its row position, or for a name the row lacks, its
  position in the rows extending it where they agree, if that is a fixed
  slot other than the span and SLOTS still holds. It memoizes (parent shape,
  key, slot) -> shape, purged at every major GC. `NightAddPropCheck` is
  unchanged: a placed field lands at its predicted slot, and a generic add
  onto a permuted shape inside the clump's bound clears SLOTS as before.
  The add-transition rows record only transitions that add one slot at the
  span, so a permuted transition always takes the helper.
- **Stamps**: a span covering the row no longer proves every row field is
  present (holes). Every stamp gate (MIR's `ctor.stamp`/`ctor.publish`
  inline, MIR's `restamp`, bbv's `emit_class_idx_stamp_impl`, the runtime's
  `ctor_stamp`/`ctor_restamp`) counts the properties below the row length
  on a permuted shape (`night_runtime_slots_covered`), and `guard.ctor`'s
  span compare includes the permuted bit (`constructing(n)` is the first n
  fields in order).
- pdfjs: the `Font` methods' entry exits (55.6k) are gone, 187k -> 140k
  exits. The rest are mostly int32-unbox guards (KICKOFF-6 open item 1).
- Night tests: permuted-slots.js (the engine mechanism, through the shell's
  `addPropertyAtSlot`), slot-layouts.js.

**M6. The rest of §10**: box/unbox cleanup, memory optimizations, and
numeric optimizations, each with its guard-count and instruction-count
tests.

After M6, work moves to the remaining optimization passes (representation selection,
numeric demand, memory optimizations, LICM, inlining, scalar
replacement). Once MIR's coverage and performance match the legacy
path, BBV can be deleted.
