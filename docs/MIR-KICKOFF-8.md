# MIR tier: kickoff for the next session (8): memory optimization, continued

Branch `cfallin/mir`. Read docs/MIR.md, docs/MIR-MEMORY.md (the design of
record for this work, with the owner's decisions and a status section),
docs/MIR-PARITY.md and docs/MIR-KICKOFF-7.md first; their working rules
still hold. MIR is now the default pipeline (`--pipeline legacy` keeps BBV
for comparison until the MIR PR).

## Measurement rules (new this session)

- **Check every build for silent declines.** The validator runs after
  `opt::optimize`; invalid MIR declines the script to baseline with
  `BUG: invalid MIR` in `--dump-tiers`, and every lane still passes. An
  early `fold_unbox` declined 87 scripts (deltablue -7.5%) before a profile
  showed it. `~/work/nm-mir-scratch/prof8/bugcheck.sh <nightmonkey> <js>`
  must print only `total 0`. A pass that substitutes one value for another
  must not extend a value with killable type components past a fence.
- **Keep the whole machine quiet during an A/B.** CPUs N and N+16 are SMT
  siblings: a lane pinned to 16-31 next to an A/B on 8-15 gave ±50-140%.
  Run lanes, compiles and A/Bs one after another.
- `~/work/nm-mir-scratch/prof8/`: `ab3.sh` (as prof7's), `bugcheck.sh`,
  `prof.sh <bench>` (a perf profile by script; run them one at a time,
  concurrent `perf record`s produce empty data), `invscan.py dump.mir`
  (loop-invariant heap reads left in loops, with what blocks each),
  `loopscan.py`, `ionflags.sh` (native Ion with LICM / scalar replacement /
  GVN toggled), `snapshot-other.sh` (the native and wasm-interp lanes).
- The compiler runs inside the Wasm guest during an AOT compile: host
  environment variables do not reach it. Temporary diagnostics print
  unconditionally, in a host-only build, and come out before lanes.

## Where things stand (HEAD 3ef18a4)

Snapshot, 2026-09-30 (Octane scores and react's score, higher is better; MIR
and legacy are medians over 4 placements, the rest best of 3):

| | native Ion | native baseline | wasm-interp | legacy | MIR |
|---|---|---|---|---|---|
| geomean | 51551 | 14354 | 1613 | 12681 | 14199 |

MIR/legacy 1.12x, MIR/wasm-interp 8.8x, MIR/native-baseline 0.99x,
Ion/MIR 3.63x. Per benchmark (Ion/MIR): navier-stokes 1.58, code-load 1.94,
crypto 2.21, richards 2.60, deltablue 2.71, mandreel 3.41, splay 3.67,
pdfjs 4.29, raytrace 4.63, box2d 4.92, react 5.55, earley-boyer 6.74,
regexp 8.72.

Landed this session (commit messages have the detail): typed `%` and
range-proven unchecked int ops (702acde); `load_slot`, memory value
numbering, LICM over per-edge effects, `lit.new`/`lit.init` (b06648e);
SROA of literals with rebuilds at exits, `fold_unbox`, `fold_ints`
(6f3788b); element misses exiting where no typed array can reach, and the
runtime's no-JS append (3ef18a4). The owner's example in literal form,
`{x: 123}.x + 2`, folds to `const.i32 125` (a MIR test).

## What the measurements say

### Ion's memory optimizations, per benchmark

Native Ion (SpiderMonkey 140), default against each pass off, best of 3
(`ionflags.sh`; `snap/ionflags.txt`):

| | LICM | scalar repl. | both | GVN |
|---|---|---|---|---|
| raytrace | +0.4% | **+77%** | +75% | +33% |
| earley-boyer | +2.2% | **+19%** | +20% | +13% |
| box2d | +1.3% | **+14%** | +17% | +54% |
| splay | +3.8% | +8.7% | +1.7% | -8% |
| react | +1.3% | +5.7% | +4.8% | +20% |
| crypto | **+28%** | +2.2% | +28% | +31% |
| mandreel | **+22%** | -2.1% | +22% | +60% |
| navier-stokes | **+11%** | +0.2% | +11% | +16% |
| geomean | +6.2% | +8.4% | +13.7% | +22.4% |

(GVN is where Ion's redundant-load elimination happens, over its alias
analysis.) So scalar replacement is worth most in raytrace, earley-boyer,
box2d and splay, and those allocations are `new`-constructed temporaries
(vectors, cons cells): Ion inlines the constructor and allocates from a
template (`MNewObject`), which its SR handles. LICM is worth most in
crypto, mandreel and navier-stokes.

### MIR's loops

`invscan.py` over HEAD's MIR, crossed with perf profiles:

- **No LICM gaps.** Every loop-invariant read still in a loop is blocked by
  something in the loop: a call or generic op (`Unknown` writer), or a store
  to the same field. navier-stokes' `lin_solve` and crypto's `am3` (the two
  hottest numeric kernels) have nothing left; `lin_solve`'s closure reads
  hoisted once its element fallbacks exited (+25%).
- **The blockers in hot loops are mostly generic property fallbacks**: the
  IC path a typed access takes when its layout guard misses, which rejoins,
  and whose effect summary is `Unknown` (a getter may run).
  crypto's `montReduce` and `bnpSquareTo` (`js.getprop .t`, `.am`), box2d's
  contact solver (54 `js.getprop .x`, 54 `.y`, `.rA`, `.rB`, and
  `js.binop.mul`), raytrace's render loop (`js.getprop .RayTracer`,
  `.prototype`, `.Color`: namespace reads off globals).
- **Fields read and written through an invariant receiver in the loop**:
  richards (`v2`), box2d (`x`, `y`), earley-boyer and pdfjs (closure
  variables, `env.load` / `env.store`).
- crypto's Ion LICM win is most likely `am3`'s element headers: Ion splits
  an element access into `MElements`, `MInitializedLength`,
  `MBoundsCheck`, `MLoadElement` and hoists the first two. MIR's
  `load_elem` loads the elements pointer and initialized length inside the
  op, every iteration.

## Work, in order

### 1. Precise effects for property fallbacks (the largest lever)

A typed field access whose layout guard misses falls back to the generic
IC op (`js.getprop`, via `guard_layout_or`) and rejoins. The guard is not
the problem (it reads), nor are layout changes (type facts and memory
versions are tracked separately). The problem is the fallback's effect
summary: every generic op gets `Effects::generic` (`Unknown` reads and
writes, may run JS), because on a receiver the guard did not prove, the
property may be a getter or the receiver a proxy, and then arbitrary JS
runs. That one summary covers both the common miss (a plain data property:
a pure read) and the rare one (a getter: anything). In a loop it is an
`Unknown` writer, so nothing hoists; at the rejoin every memory version dies.

- **Split the fallback.** A data-only property read: the IC's inline ways
  and probe, restricted to data properties (own slot, prototype holder),
  with effects `reads Field(*, name)` and nothing else; a lookup that would
  run code (getter, proxy, resolve hook) takes a fail edge, which exits or
  goes generic. The common miss then stays in MIR as a read, with no exit
  storm when a class prediction is wrong (the risk an exit-on-guard-miss
  policy would carry: pdfjs's typed array made 1.5M exits at one site).
- **The same for stores**: `js.setprop`'s continuing path is a data write of
  `Field(*, name)` (it blocks reads of that name only); setters, proxies
  and non-writable properties fail.
- **And for generic arithmetic** (`js.binop.mul` in box2d's solver): the
  numbers-only arms are pure; only object operands (`valueOf`) run JS, so
  they take the fail edge.
- Measure with `invscan.py`: the blockers listed above (crypto's
  `montReduce`/`bnpSquareTo`, box2d's contact solver, raytrace's render
  loop) should turn into hoists and numbered loads.
- Global namespace reads in loops (`Flog.RayTracer.Vector` in raytrace)
  are the same split, plus constant-object reads (item 6).
- The element fallbacks (3ef18a4 made their misses exit) could use the same
  split instead (a hole or out-of-bounds read through prototypes without
  indexed properties is a read of `undefined`), lifting the
  no-typed-array condition.

### 2. SROA of constructed objects (MIR-MEMORY.md §6, M6)

Ion's SR is +77% on raytrace, +19% earley-boyer, +14% box2d, almost all
`new`-constructed temporaries. In MIR an inlined construct is `create_this`
(generic: reads the callee's `.prototype`), `guard.ctor`, `init_field`s,
`publish_layout`.

- Make `create_this` a typed allocation where the callee is proven
  (`guard.script` on a scripted function: its `prototype` is a
  non-configurable data property, so the read runs no JS), with effects
  like `lit.new`'s.
- Extend `mem::sroa` to it: fields from `init_field`, the class word's
  states (constructing(n), published) recreated at rebuilds
  (`create_this`, `init_field`s, `publish_layout` as the exit's state has
  them).
- Measure on raytrace's `Vector` arithmetic first: objects escape unless
  the producing and consuming calls are both inlined, so check how many
  `construct`s stay calls (58 in raytrace today, against 44 inlined).

### 3. SROA extensions

- **Merges.** v1 gives up when two different values of a field reach a
  use; Ion's `MObjectState` puts phis there. Insert block params for the
  fields (the dataflow already finds the conflicts).
- **Nested literals**: 74 of react's literal escapes are into another
  literal (`lit.init` as the value). Replace both when the outer one does
  not escape.
- **Call objects** (Ion's `MNewCallObject`): a function's environment whose
  closures are all inlined or none escapes; `env.load`/`env.store` become
  SSA values.
- **Arrays with constant indices** (Ion's `MNewArrayObject`).
- **Literals filled by later adds** (the owner's `{}` then `o.x = 123`):
  the analysis gives `{}` no row (`lit_order` is empty). Give the site a
  row from its fill sequence (the constructor `local_fill_row` machinery),
  then build the adds as `lit.init`s.

### 4. Loop-carried field promotion

A field read and written in a loop only through a loop-invariant receiver,
with no `Unknown` writer in the loop: load it in the preheader, carry it as
a block param, store it on the loop's exits (and on exits from inside the
loop, which `frame.store`-style sinking already has to handle). richards,
box2d (`x`, `y` in the contact solver) and the closure-variable loops of
earley-boyer and pdfjs have this shape once their other blockers go.

### 5. Element access splitting

Split `load_elem`/`store_elem` into elements-pointer, initialized-length,
bounds-check and access ops so LICM hoists the header loads (Ion's crypto
+28% is most likely this, in `am3`). Constraints: the elements pointer is
`Raw` (not across a may-GC op), and `store_elem.append` may reallocate the
elements and changes the lengths (its effects say so: `ArrayLength`, and the
elements pointer must be killed by it). Distinguish arrays by region root
where the stamps prove it, so an append to `w_array` does not reload
`this_array`'s header.

### 6. Constant values in the analysis (owner's request)

Extend likelier's types with constant values (a `Const(v)` component on
cells; joins of different constants go to the existing type), for globals
and for object fields. Where a value is a constant, guard it (or fuse it,
for globals: the fused-gname machinery, extended from the root script's
literal walk to the snapshot's values for globals nothing writes after the
snapshot) and constant-propagate its uses. crypto's `BI_*` (set in the root
script from `dbits`) are the first case: `1 << BI_F1`, `% BI_DV` and
`& BI_DM` then fold, the element and product ranges follow, and the two
overflow sites (`bnpInvDigit`, `bnpDivRemTo`: 12k exits) become exact
`int` arithmetic. Fields: a per-class constant claim checked like TYPES, or
a value guard at the load, then propagation.

### 7. DSE and store sinking (M3)

As designed (MIR-MEMORY.md §3.3): a store overwritten on every path with
only exits between moves into the exits; frame-store sinking in loops
(KICKOFF-5 item 1: earley-boyer's frame traffic).

### 8. Port Ion's cases

Build a native shell with `--enable-jitspew` (the 2026-09-16
`firefox/obj-ion` is an opt build) and, per benchmark where LICM or SR
matters above, dump Ion's MIR for the hot functions with each pass on and
off (`IONFLAGS=licm,escape` or iongraph), diff the hot loops, and check the
same loops in MIR's dumps. Mine `jit-test/tests/ion/` scalar-replacement
and LICM tests (e.g. `gc-during-bailout.js`, which found an infinite loop
in `sroa`) for MIR text tests and night tests.

## Open from before

1. KICKOFF-7 items 1 and 2 (pdfjs's optional fields and this-binding):
   about 0.5% of pdfjs by the exits-to-score ratio; parked.
2. Rooting only values that may hold a GC thing (`Type::may_hold_gc_thing`)
   breaks `gc/weak-marking-01.js`: home slots then keep dead objects. It
   needs dead-slot clearing that does not reopen cross-frame retention
   (the rooting-store memory note).
3. KICKOFF-4 item 4 (splay GC) stands; SROA (items 2, 3) is its lever.
