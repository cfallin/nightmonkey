# MIR memory optimizations: LICM, alias analysis, DSE, escape analysis, SROA

Status: **design, 2026-09-30.** Extends MIR.md §6 (effects and memory)
and §10.2/§10.5 (hoisting, forwarding, RLE, DSE), and fills the "virtual
object recipes" reservation of §5.1. Decisions taken with the owner are
marked **(decided)**.

## 0. Where MIR stands

- `opt::licm` hoists non-terminator ops that are pure or read only regions
  nothing in the loop writes. `opt::hoist_guards` hoists guards.
  `opt::cse_loads` forwards a field load from an earlier load or store
  through the same SSA object, killed by any write to that field *name*
  in any class. There is no DSE, escape analysis or scalar replacement.
- Three things keep those passes from finding much:
  1. **`load_field` is a terminator** (`ok_clean`/`ok_dirty`/`err`) with
     effects `may_gc`, `may_throw`, kill ALL, whatever its receiver. With
     SLOTS proven its lowering is one `i64.load` and a branch to
     `ok_clean`; the other edges are dead. LICM skips terminators, and the
     kill blocks value numbering of anything typed past it.
  2. **Literal allocation is generic.** `NewInit`/`NewObject` build
     `js.rt.newobject` (+ `stamp.fresh`), and each `InitProp` a
     `js.rt.initprop`: `Unknown` reads and writes, may run JS, kill ALL.
     A loop that builds a literal loses every remembered load and guard.
     The lowering already has the inline paths (`alloc_inline`: nursery
     bump from the site's alloc cell; `init_prop_inline`: replay of the
     site's add transition), so this is only a matter of MIR's view.
  3. **A clean edge protects types, not memory.** A generic op takes
     `ok_clean` when the stamp epoch is unchanged (`js_keep`); a getter
     that writes a field conformingly leaves it unchanged. So memory
     knowledge cannot cross a generic op, clean or not, and the
     precision has to come from typed ops.

## 1. Abstract locations

An access touches a set of abstract locations (MIR.md §6's regions),
computed from the op and its operand *types* (never from predictions):

| location | accessed by | notes |
|---|---|---|
| `Field(K, name)` | `load_slot`, `load_field`, `store_field`, `init_field` through `Obj{K…}` | one per class per field; `K` a key range, `Field(*, name)` unproven |
| `Elements(root)` | `load_elem`, `store_elem`, `elements_ptr` | `store_elem` is an in-bounds overwrite: it never changes a length |
| `ArrayLength(root)` | `length.array` | written only by generic ops and calls (push, `length =`, holes) |
| `TypedArrayData(kind)`, `TypedArrayLength` | typed-array ops | as today |
| `Global(binding)` | `load_gname`, `store_gname` | |
| `Env(slot)`, `FrameEnv` | env ops | as today |
| `Alloc(a, name)` | fields of a non-escaped allocation `a` (§5) | overlaps nothing reached through any other object |
| `Unknown` | generic ops, calls, exits' resumed baseline | every location |

Two accesses may alias only if their location sets overlap, and, for
object locations, their receivers' **points-to sets** intersect (§5.2):
the fields of an allocation that has not escaped are reached only through
values derived from it.

Disambiguation by class (`Field(K1,x)` vs `Field(K2,x)`) is sound because
a receiver's layout claim holds at each access that uses it (the
validator's fence rule), and an object changes its class word only
through ops that write `Unknown` or kill the claim.

**Effects per edge.** An op's reads and writes are stated per successor
role. For a typed op the clean and dirty edges write the same locations
(a store's dirty edge demotes TYPES: a type kill, not a memory write);
for a generic op every edge reads and writes `Unknown`. Exits and throws
**read** `Unknown` (baseline resumes and may read anything). A may-GC op
reads nothing (a GC moves objects but changes no value a load returns).

### 1.1 Canonical memory ops (step M0)

- `load_slot name` (new, not a terminator): `load_field` through a
  receiver whose type proves the layout and SLOTS. Reads `Field(K,
  name)`; no GC, no throw, no kill; result of the field's claimed type.
  A pass rewrites every such `load_field` into `load_slot` + `jump
  ok_clean`. This is what lets LICM hoist field loads and GVN merge them.
- `store_field` keeps its shape (its dirty edge is the TYPES demotion),
  but its memory effect is precise on every edge.
- Allocation (`new_object`, §4) and literal init (`init_slot`, §4) are
  typed, with effects: `new_object` may GC, writes nothing that exists;
  `init_slot` writes `Alloc(a, name)` or `Field(K, name)` of a fresh
  object.

## 2. LICM (step M1)

MIR.md §10.2 plus general hoisting over §1's effects. A non-terminator
op in loop `L` moves to `L`'s preheader when:

1. its operands are defined outside `L` (or already hoisted);
2. it writes nothing, cannot throw or run JS, and kills nothing;
3. nothing in `L` writes a location it reads (by §1: location overlap
   and points-to);
4. it is safe to execute when `L` would not have: a `load_slot` is
   (the receiver's type proves the slot exists), as is every pure op.

Chains then hoist link by link through the existing fixpoint: a
loop-invariant `this` hoists its layout guard (`hoist_guards`), then
`this.arr` (`load_slot`), then the array's kind guard, then
`length.array` (only `store_elem`s in the loop: `Elements`, not
`ArrayLength`), then its `int.to_i32` guard. `i < this.arr.length`
becomes a compare against a preheader value.

**Managed values.** A hoisted object is live across the loop, so the
lowering spills and reloads it around every may-GC op in the loop.
Today `licm` refuses managed results for that reason. The new rule:
hoist them; the reload replaces the load it hoisted, and what hoisting
enables past it (guards, further loads) is the point. Measure code size
and scores both ways once, and record the result; no per-benchmark gate.

## 3. Alias analysis, forwarding, RLE, DSE (steps M2, M3)

### 3.1 Memory versions (last writer)

One forward dataflow over the CFG (in `opt::optimize`'s fixpoint loop),
per location key the function touches:

- **State:** location key -> version. A version is a writer instruction,
  a merge (`Phi(block, key)`, stable across iterations), or `Entry`.
- **Transfer:** a write of location set `W` sets every tracked key
  overlapping `W` to the writer; `Unknown` sets all keys. Per edge
  (§1): a generic op's edges all write `Unknown`.
- **Meet:** equal versions stay; different ones become the block's
  `Phi(block, key)`.
- **Clobber walk:** each single-location store records the version it
  replaced. A load through receiver `r` asks for its location's version
  and walks back past stores whose receiver is must-not-alias with `r`
  (disjoint points-to sets, §5.2): `store b.x; load a.x` with `a`, `b`
  distinct allocations sees the version before the store.

### 3.2 Loads: GVN, forwarding

- **RLE:** a load is keyed by (op, receiver up to unboxing and
  weakening, name, version). A repeat whose first occurrence dominates it
  is replaced by it. This subsumes `cse_loads`, and is precise across
  stores to other classes' fields (class-disjoint locations do not bump
  the version).
- **Store-to-load forwarding:** a load whose version is a store (or
  init) through the same receiver and name takes the stored value, if it
  dominates. The stored value is boxed where the load's result is boxed;
  §3.4 then cleans up.
- A `Phi` version is not forwarded through (no load-phis in v1).

### 3.3 Dead stores, sunk into exits (decided)

An exit resumes baseline, which may read anything, so a guard between two
stores observes the first. Nearly every store pair in real MIR has a
guard between them. So DSE *sinks* stores into exits:

- A store `S1` to (`r`, `name`) is **dead on the main path** when a store
  `S2` to the same receiver and name post-dominates it and, on every path
  from `S1` to `S2`, the only readers of an overlapping location are
  exits and throws.
- `S1` is deleted, and a copy of it is placed on each edge from the
  `S1`-`S2` region into an exit (a new block before the exit, or the exit
  block itself when all its predecessors are in the region). The copy's
  operands dominate the edge because `S1` did.
- A store with no later overwrite whose only readers are exits (a local
  object's fields before a return that drops it) is the §5 case.

The same machinery serves MIR.md §5.1's deferred note: `frame.store`s
of loop-carried locals sunk into the loop's exits.

### 3.4 Cleanups that forwarding exposes

- `unbox(box x) -> x`; `unbox(weaken(box x)) -> x`; guards on a value
  whose def proves them fold by type (already: `fold_guards`).
- Constant folding of integer and f64 ops on constants (with §10.6's
  ranges, a result with a singleton range is a constant).

The owner's example, `let o = {}; o.x = 123; return o.x + 2;`, should
end as `return 125` once §4 types the add and §5 removes the object:
the load forwards `box 123`, the unbox of the box folds, the guard on a
boxed int32 folds by type, `123 + 2` folds.

## 4. Typed literal allocation (step M4, prerequisite of §5) (decided)

- `new_object` *site*: the literal's allocation, the lowering's
  `alloc_inline` with the site's alloc cell, falling back to
  `night_runtime_new_object`. Result `Obj{Plain}`, with the site's layout
  claim `constructing(0)` when the analysis stamps the site
  (`lit_stamps`). Not a fence.
- `init_slot name`: an `InitProp` of that literal, as the lowering's
  `init_prop_inline` (the site's add-transition row), falling back to the
  helper. Typed: advances `constructing(n)` to `n+1`; the last one's
  successor holds the published layout (as `stamp.fresh` does today).
- **Literals filled by later adds** (`var o = {}; o.x = …`): the
  analysis already gives the add sites a site row. The builder treats a
  fresh literal like a constructing `this` (MIR.md §2.3): each add of the
  row's next field is an `init_field`; the object is published when the
  row is complete; a use before that (a call, an escape) demotes it as a
  fence demotes a `Ctor`.

## 5. Escape analysis and scalar replacement (step M5)

### 5.1 Allocations

Allocation sites in MIR: `new_object` (§4), and later (§6) a typed
`create_this` of an inlined construct. Each result is an allocation
`a`.

### 5.2 Points-to and the escaped bit

A forward dataflow over SSA values, one points-to set per object-typed
value: allocations it may be, plus `Esc` (anything else). Values derived
from `v` (guard outputs, `unbox`, `box`, `weaken`, `forward`ed params)
have `v`'s set; a block param is the union of its incoming values'.

Allocation `a` **escapes** when any of these holds:

- a value that may be `a` is an operand of a call (not inlined), a
  generic op, `return`, `throw`, a store to a global or environment, or
  a `store_field`/`store_elem`/`init_*` value operand whose receiver may
  be `Esc` or an escaped allocation (stores into another local
  allocation propagate: `a` escapes if that one does);
- a value that may be `a` meets another allocation or `Esc` at a block
  param (v1 needs one allocation per value);
- a field access through a value that may be `a` names a slot outside
  `a`'s layout, or a generic access reaches it;
- an identity compare with a value whose set is not exactly `{a}` or
  disjoint from `a` (then the compare folds).

Loads through `Esc`-only values produce `Esc`. **Exits, throws,
`exit.inline`, `gen.suspend`, `frame.store` and `inline.enter` do not
count as escapes** (decided): they rematerialize (§5.4).

### 5.3 Replacement

For each non-escaped allocation `a` (a mem2reg over its fields):

- each field of `a`'s layout becomes an SSA variable: initialized by the
  `init_slot`s, updated by stores, merged by block params at joins
  (standard SSA construction over the blocks where `a` is live);
- loads through `a` become the variable's current value; stores and
  inits are deleted; guards on `a` fold by type (its layout is known);
- the allocation is deleted.

### 5.4 Rematerialization at exits (decided)

- An exit (`exit`, `exit.throw`, `exit.inline`, `gen.suspend`) whose
  operands hold `a`, or whose frame slots hold `a` by a `frame.store`
  that reaches it, gets `a` rebuilt on its edge: `new_object` of `a`'s
  site and `init_slot`s of the fields' current values, in a block
  before the exit, then `frame.store`s of the slots that held it. One
  rebuild per exit edge serves every slot that holds `a` (identity is
  kept).
- `frame.store a k` is deleted; a reaching-frame-stores dataflow per
  slot finds the exit edges that need `k` rewritten. An exit reached
  both with `a` in `k` and with another value there gets per-edge
  blocks.
- Nested allocations (a field of `a` holding a non-escaped `b`) rebuild
  `b` first.
- MIR.md §5.1's validator rule against virtual-object recipes is
  lifted in this form: no recipe operand kind, just ordinary allocation
  ops on the exit edge, which the validator already accepts.

## 6. Constructors (step M6)

Inlined constructs allocate through `create_this` (generic: reads the
callee's `.prototype`). With the callee proven (`guard.script`) and its
prototype object fixed (a fuse on the `prototype` slot, or the snapshot
value), `create_this` becomes a typed allocation of the constructor's
alloc cell, and §5 applies to objects whose construction and every use
are inlined (raytrace's vectors).

## 7. Order and measurement

| step | content | shows up as |
|---|---|---|
| M0 | `load_slot`; precise per-edge effects; allocations not fences | guard/load census |
| M1 | LICM of reads and managed values | hot-loop MIR; Octane/React |
| M2 | memory versions, RLE, forwarding, box/unbox and constant folding | `cse_loads` retired |
| M3 | DSE with sinking into exits; frame-store sinking | earley-boyer frame stores (KICKOFF-5 item 1) |
| M4 | typed literal allocation and literal-then-add construction | `js.rt.newobject`/`initprop` gone from hot MIR |
| M5 | escape analysis, SROA, rematerialization | allocations per run (splay, raytrace, react); GC stats |
| M6 | typed `create_this`; SROA of constructs | raytrace |

Each step lands with textual MIR tests (before/after), a night test for
the exit paths it creates, both jit-test lanes, and an Octane + React
A/B over placements with code size (`--stats`) reported next to scores.

## 8. Status (2026-09-30, end of the first session)

Built (commits b06648e and after; MIR.md M5o has the measurements):

- **M0** `load_slot`, and `canon_loads` dropping the load's retaining
  frame stores.
- **M1** LICM over per-edge writes, object results, `int.to_i32` and
  `f64.to_int_exact` as hoistable guards; fixes to `hoist_guards` (entry
  state kept as values) and to both passes' loop bodies (unreachable
  predecessors). Not `box`/`weaken`: hoisting them lengthened live
  ranges for nothing (crypto -4%).
- **M2** `mem::mem_vn` (memory versions, numbering, forwarding, the
  fresh-allocation clobber walk). Not yet: phi versions, DSE (**M3**).
- **M4, first part** `lit.new`/`lit.init` for stamped literal sites. Not
  yet: literals filled by later adds (the owner's `{}` then `o.x = ...`;
  the analysis gives such a literal no row).
- **M5** `mem::sroa` for `lit.new` objects, with the optimistic escape
  check (the allocation's own guards pass, so their failures' uses do not
  count) and rebuilds before `exit`, `exit.throw` and `exit.inline`;
  `fold_unbox` and `fold_ints` after it. `{x: 123}.x + 2` folds to 125.
  On real code it rarely fires: react's 404 typed literals all escape
  (calls 35%, arrays, stores, closures, returns, nesting into other
  literals). Nested literals and constructed objects (**M6**) are the
  next reach.
- **Slowpath isolation** (the owner's "pushing the slowpaths aside"): a
  rejoining generic fallback kills every memory version at its join and
  keeps everything in its loop. Dense element loads and stores now exit on
  a miss instead, where no typed array can reach the site
  (`elem_poly_sites`); stores first try the runtime's no-JS append
  (`night_runtime_elem_grow`), so growth does not exit. Unconditional, it
  was navier-stokes +30% and pdfjs -33% (a typed array the analysis took
  for an array: 1.5M exits at one site).

Lessons:

- The validator declines invalid MIR to baseline silently
  (`BUG: invalid MIR` in `--dump-tiers`): an early `fold_unbox` that
  reused a pre-fence value declined 87 scripts with every lane passing.
  `~/work/nm-mir-scratch/prof8/bugcheck.sh` counts them over the suite.
- A pass that substitutes a value must not extend one with killable type
  components past a fence (`gvn`'s and `fold_unbox`'s rule).

## 9. Generic fallbacks with precise effects (KICKOFF-8 item 1)

A generic op's summary is `Unknown` because on operands nothing proved,
it may run code. Split, the common case is an op of its own that runs no
code, with precise effects; a case that would run code takes a `fail`
edge (an exit before the op, for baseline to do it), and a case that
demoted a claim takes the dirty edge (an exit after it). The two-track
rule holds: running user code is the GEN track. Which names may reach a
getter is static (`getter_names`: modeled `defineProperty` accessors,
literal and class accessors, every `defineProperty`-shaped call's name,
the builtins' accessors); a site of such a name keeps the generic op.

| op | runs | `fail` | effects (clean edge) |
|---|---|---|---|
| `getprop.data` | own or prototype data property, absence, pure builtin lengths | getter, proxy, resolve hook, null/undefined | reads `Field(*, name)` (+ `Global` of that name, lengths) |
| `setprop.data` | overwrite of a writable data property, add with nothing on the chain, writable array length | setter, read-only, non-extensible, the global, a watched object (prototype, fuse holder) | writes `Field(*, name)` (+ array length, elements) |
| `getelem.data` | elements (dense, holes through the prototypes, typed arrays, arguments, string chars), names by primitive keys | getter, proxy, object key | reads anything, writes nothing |
| `setelem.data` (int32 key) | element overwrite, append, sparse add, number to a typed array | setter on the chain, frozen, non-extensible, arguments, value needing conversion | writes elements, lengths, typed-array data |
| `prim.*` | arithmetic and compares on primitives, and on objects whose conversion is Object.prototype's own (a pure runtime check) | an object with its own conversion | none (may GC) |
| `js.box_this` | the global `this`, or a primitive's wrapper | (never) | an allocation |

The runtime helpers are pure lookups (`GetPropertyPure`,
`LookupPropertyPure`), the IC's populate paths (so a fallback still fills
the site's ways), and for stores the engine's own set behind those
checks, with the object's word compared before and after for a demotion
of TYPES, SLOTS or its class (RANGES, which no MIR claim reads, may drop
as on every engine store).

`opt::hoist_reads` then moves a loop's invariant read *diamond* to its
preheader: the predicted layout's guard, the slot load and the by-name
fallback rejoining, one invariant value whose guard does not exit (so
`hoist_guards` leaves it). Its exits become the loop's entry exit; the
`box`/`weaken`/`unbox` chain of its receiver (which `licm` leaves in
place) moves with it. Only a region every iteration passes moves: a read
under a condition (`if (o) s += o.x`) may be one whose receiver fails it
on every entry.

Lessons:

- Exit storms show in `--mir-exit-census` and nowhere else (the lanes
  pass, scores move a few percent). Every refusal of a split op needs a
  census over the suite: arrays carry an `addProperty` hook (the engine's
  own length bookkeeping), RegExps keep `lastIndex` as a plain data
  property, objects under construction take adds, a string's index past
  its end reaches `String.prototype`'s resolve hook, and `v == EOF` with
  `EOF = {}` converts an object through Object.prototype's builtins: each
  of these first exited at every execution.
- A split op's runtime half must keep every fast path of the generic
  helper it replaces, or the site's inline caches stop being filled:
  `getelem.data` without the megamorphic by-value lookup's fill sent
  react's string-keyed reads to the helper 5.2M times a run (react -5%,
  found by ablation); `setprop.data` running its purity walk before the
  IC's cached replays cost splay 2.6%.

- Tried and not landed: an inlined call's target miss exiting instead
  of calling generically (the same rule for call fallbacks). Where only
  some of a site's targets are spliced it storms (richards' polymorphic
  `run`: 1.7M exits); limited to sites whose analyzed callee set holds
  only scripts, every one spliced, react still made 780k (`clz32 =
  Math.clz32 ? Math.clz32 : clz32Fallback`: the analysis never sees the
  native reach the site). For box2d +1.2%, the rest flat (serial).

## 10. Constructed objects (KICKOFF-8 item 2), first steps

- **`new_this(callee, proto)`**: an inlined `new F()` of a layout
  constructor that is its own new.target allocates `this` from
  `F.prototype`, read by name first (`getprop.data`, whose fail exits
  before the `new`). An allocation (ok, err), not a fence: the generic
  `create_this` it replaces wrote `Unknown`. The site's construct cell
  serves it inline when `proto` is the cell's prototype; else
  `night_runtime_new_this`.
- **Forwarding wrapper constructors** (`this.initialize.apply(this,
  arguments)`, the target resolved per inlined copy): another target, or
  an `.apply` that is not the builtin, exits instead of forwarding
  generically, so no generic op sees the object under construction.

What blocks SROA of them (`prof8/ctorscan.py` over raytrace's MIR: all
41 inlined constructs escape): the object reaches `exit.inline`s on cold
paths of the inlined body (a `getprop.data` that fails inside the
wrapper), and `exit.inline` *returns to MIR*: its continuation keeps
using the object, which baseline may have changed (or stored) meanwhile.
(The current `sroa` is safe only because an `inline.enter` operand is an
escape, so no inlined callee's exit can name a replaced object.) Two
ways forward, an owner's decision:

1. **Partial escape**: at such an `exit.inline`, rebuild the object and
   continue with the real one (its later reads become real loads, and
   joins of the virtual and the real object materialize it there).
2. **An exit that leaves the whole inline stack** for baseline (Ion's
   bailout: every frame rebuilt, the caller continues in baseline too),
   for exits that name a replaced object; then a rebuild at the exit is
   the end of the object's MIR life.

**Decided (owner, 2026-10-01): neither; materialize once, then cache.**
An object rebuilt at an escape is real from then on: baseline may carry
the reference anywhere, identity is observable (`===`), and every later
escape must hand over the same reference. So `exit.inline` is an escape
like a store to a global. What survives is caching, which unifies SROA
with forwarding and loop-carried promotion (item 4):

- Per allocation, the state at each point: the fields as SSA values; a
  maybe-null reference (null until the first escape materializes it);
  whether the fields are newer than the object (dirty).
- At a merge (a loop header) the fields and the reference are block
  params; the reference is null on paths that never materialized.
- At an escape: allocate and initialize if the reference is null, else
  write the dirty fields back; hand over the reference; after a point
  that returns (`exit.inline`, a call), reload the fields. Write-backs go
  on the edges into escape points, so the hot path stays scalar and the
  reference "just sits there".
- After materialization the effect summaries decide staleness: a writer
  of `Unknown` or of `Field(*, name)` reloads the cache, a reader of
  `Unknown` gets the write-back first. The same state then serves objects
  that are not fresh allocations (load once, carry, write back).

## 11. Materialize once, then cache: what landed (2026-10-01)

Two passes, run once each after `optimize`'s fixpoint converges (then
the fixpoint again). Neither may see its own output as input: `pea` would
virtualize its own materializations, `promote` would count its own
write-backs and reloads as accesses.

**`pea` (`mir/pea.rs`), partial escape of `lit.new` objects.** The
object is virtual until, on each path, its first escape (`exit.inline`,
a call, a store, any use that is not an init, stamp, slot load or store,
guard, conversion or frame store). There it is materialized: `lit.new`,
`stamp.fresh`, `lit.init` of the fields' current values, then
`guard.unbox.obj`/`guard.kind Plain`/`guard.layout`, whose fail edges are
`unreachable` (asserts: the object was just made with that layout),
giving a typed view. From there every block of the real part carries
(value, view) as params; a virtual edge into a real block materializes
on the edge. In the virtual part loads are the values last stored,
guards pass, and exits that do not return rebuild the object (as
`sroa`'s do). The view is typed until an op or a fence edge kills a
component of it (the call the object escaped into may reshape it):
before that op a `weaken` gives `obj{Plain}`, and a real block any such
path reaches carries that view instead.

**`promote` (`mir/promote.rs`), loop-carried caching.** An env slot,
or a `store_slot`-able field of an object defined before the loop that
the loop both reads and writes, is loaded in the preheader and carried
as a header param. Memory is written back before any op that may read
the location (its effects say so) and on edges leaving the loop while
dirty. It is reloaded after any op that may write it, and on the edges
of terminators that write it. Cost rule: those barriers must be fewer
than the accesses they replace.

**Limits, each a design item:**

- A pass cannot add an exit: it has no frame state at an arbitrary
  point. So every op it inserts is infallible (the asserts above), and
  the owner's maybe-null reference, materialized lazily at the first
  escape *inside* a loop, is not built. That needs frame states the
  builder keeps for every point a pass may want to exit at.
- `pea` declines objects whose fields differ by path where needed (no
  field params at merges yet), objects that escape before every field is
  added, and objects that meet another value at a param. It handles
  `lit.new` only; `new_this` constructs are next.
- `promote` caches nothing that polymorphic stores reach, since those
  cannot become `store_slot`. Most of what it caches is env slots.

**Compile time.** A jit-test with hundreds of literals in one 16k-instruction
function (`basic/testComparisons.js`) went from 1 s to more than 10 minutes.
Three fixes:

- `sroa` plans every candidate against one snapshot per round (the CFG,
  preds, uses), then applies every plan that doesn't collide with another.
  Before, it rebuilt everything after each replacement.
- `pea`'s exit rebuilds are `sroa`'s own form, with no view asserts, so
  `sroa` leaves them alone.
- `pea` examines at most 64 allocations per function, keeping its CFG
  across declined ones.

The test now compiles in 6 s. What remains is size: each virtualized object
is rebuilt before every exit in its virtual region, so that function grows
from 16k to 36k instructions. Sharing one rebuild among exits with the same
fields would fix that.
