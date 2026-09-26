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
- **Rooting happens during lowering**, following today's value-stack
  push design:
  - the lowering keeps a map from MIR value to waffle value;
  - before a may-GC op, it pushes the live managed values onto the
    NightStack above the current top and passes the new top;
  - afterwards, it reloads them into fresh waffle values and updates
    the map.

  There is no function-wide slot abstraction.

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
exit pc, this, [args…], [locals…], rval, [stack…]   -- every operand : Val(⊤)
```

- **The arity is fixed by the script:** all formals, all locals, the
  rval, and the operand-stack depth at `pc`. v1 passes and stores every
  one of them. A liveness analysis at the target PC can prune dead ones
  as soon as IR size or exit cost warrants it. The builder inserts the
  `box`/`weaken` upcasts explicitly. Boxing is thus visible to the
  optimizer; for example, a box can be sunk into the exit path.
- **The env slot is not an operand.** v1 declines env ops, so the env
  chain is fixed for the whole activation, and the MIR prologue writes
  it once.
- **Resume rule:** an exit to an op's own PC is allowed only if no
  observable part of the op has happened. Otherwise it targets the
  successor PC, with the op's result on the stack.
- **Lowering writes a complete baseline frame and resumes baseline:**
  1. Store every operand, plus the env, arguments-object and new.target
     slots, into the frame layout at `pc`.
  2. Write the resume word: `pc`, in mode `continue`.
  3. If this activation entered MIR at the function entry, call the
     baseline body with `ARGC_RESUME_BIT` and return its result. If it
     entered by an onramp from baseline, return `err = 2` (DEOPT) to
     that baseline caller, which resumes itself. A JS frame therefore
     never uses more than three native frames.

  MIR does not maintain a baseline frame while it runs. It uses the
  NightStack only for GC rooting, above the caller-built
  `[callee, this, args…]`, and only across may-GC ops. The exit writes
  the whole frame at once.
- **Each exit lowers its own stores.** Values reloaded after rooting are
  different waffle values on different paths, so exit blocks are never
  shared across predecessors in waffle.
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

- generator and async bodies
- `arguments` and rest
- `with` and eval
- scripts using env ops, until M5

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
  - **Values.** Each MIR value lowers to one waffle value of its
    machine type. A managed value (`Val`, `Obj`, `Str`) that is live
    into a block enters it as a waffle block param, because rooting
    reloads it into a fresh value on some paths and not others.
  - **Rooting.** Before a may-GC helper call, the managed values live
    across it are stored boxed just above the padded formals, and the
    helper's `top` sits above them. The entry pads the formals with
    undefined first, so `[sp, top)` is always valid Values.
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

**W. waffle's reducifier, driven by M3 data** (BASELINE.md §8): measure
the duplication on real onramp-shaped MIR, and change waffle only if
the numbers call for it.

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

**M5. Remaining v1 coverage**
- Elements and typed arrays, including array stamping in the analysis.
- Globals and fuse facts.
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

**M6. The rest of §10**: box/unbox cleanup, memory optimizations, and
numeric optimizations, each with its guard-count and instruction-count
tests.

After M6, work moves to the remaining optimization passes (representation selection,
numeric demand, memory optimizations, LICM, inlining, scalar
replacement). Once MIR's coverage and performance match the legacy
path, BBV can be deleted.
