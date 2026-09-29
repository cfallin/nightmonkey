# MIR tier: kickoff for the next session (4)

Branch `cfallin/mir`. Read docs/MIR.md, docs/MIR-AUDIT.md, docs/MIR-PARITY.md
and docs/MIR-KICKOFF-3.md first; its working rules still hold (build to the
design and to legacy parity, no hill-climbing, facts fixed / kills exit,
commit and push as you go, never the shared stash, lanes on a fresh
`js-inproc`, no "pre-existing" failures). Two rules settled this session:

- **No slot lookup in the engine's generic store path**, and no change to the
  firefox fork's store hook to pass one (KICKOFF-3's item 4 is withdrawn).
  An object that loses TYPES through an engine-path store is fixed by keeping
  that store out of GEN (a compiled, vouched store), not by making the engine
  layout-aware.
- **Layout guards**: TYPES always; SLOTS only where the access has a slot
  prediction (a miss exits). A field the layouts type but place in no slot
  (added outside the constructors) is a `named` field: read and written in
  OPT through the site's IC for the slot, its value of the claimed type. A
  `{types, slots}` guard folds a later `{types}` one; a slotted access after
  a `{types}`-only guard guards SLOTS itself. Decided from data: guarding
  SLOTS beats testing it per access (richards 10707 vs 8102, pdfjs 21774 vs
  19047), and SLOTS-only guard misses are rare (10.7k in pdfjs, none
  elsewhere).

## Where things stand

Octane and react-bench (AOT, 10 in parallel, best of 2; after 25b3fca):

| | MIR | legacy |
|---|---|---|
| crypto | 17105 | 15579 |
| deltablue | 9098 | 5851 |
| earley-boyer | 11878 | 12876 |
| navier-stokes | 21179 | 22910 |
| pdfjs | 20643 | 21031 |
| raytrace | 12075 | 12173 |
| regexp | 2224 | 2190 |
| richards | 10481 | 11392 |
| splay | 7614 | 7654 |
| react | 31256 | 31800 |

The parallel run is noisy (splay, pdfjs and react move by 3% between runs)
and flatters MIR on richards and earley-boyer. Single runs on a quiet
machine, best of 3 (MIR / legacy): richards 11064 / 12109 (-9%),
earley-boyer 12167 / 13393 (-9%), navier-stokes 22408 / 23673 (-5%), splay
8704 / 8816, raytrace 12481 / 12456, react 33245 / 33211.

react-bench (`~/work/nm-mir-scratch/bench/react.js`: seeded `Math.random`, a
global `main` that renders for 3 s and prints `Score (version 9)`) is in the
scratch `octall.sh` beside Octane. Its output is byte-identical across the
interpreter, baseline, legacy and MIR.

What landed this session (commit messages have detail):

- Forward wrappers spliced per site (`Class.create`'s
  `this.initialize.apply(this, arguments)`), jump threading, one-compare
  layout guards, lazy rooting-area init, `arguments[i]`, string-char and
  string-key mega arms, inline `restamp`, concat.
- SLOTS as its own claim (above); typed fields with no slot; construction
  delegates; `ctor_publish` methods take no entry `this` guard.
- Accessors: `accessor.probe` (bbv's accessor-call cache) and a direct call
  of the getter/setter.
- `x ==/=== "lit"`: bbv's literal ladder.
- `hasOwnProperty.call(o, k)`: bbv's native arm.
- `box.double`: a dense store whose write claim admits Double stores the
  double as it is (navier-stokes +11%).
- The set IC's mega arm (`night_ic_set_cold`) and bbv's past-the-layout rule
  for adds under SLOTS.
- Analysis: no field claim on a plain object that takes computed-name
  writes (a for-in copy); this removed raytrace's 127k exits.

## Next

1. **richards and earley-boyer (-9% each, quiet)**: no exits. MIR retires *fewer*
   instructions than legacy (richards 4.7M vs 5.6M per score point) at
   lower IPC (1.35 vs 1.68 in `schedule`). It dispatches about 16% more
   stores, with store-queue dispatch stalls about 2x legacy's. The stores
   are the back edges' clears of dead rooting slots and `inline.enter`'s
   frame writes. Two experiments moved them and did not help (details in
   the memory note): deferring the loop clears to GC points was neutral,
   and deferring `inline.enter`'s fixed-slot stores lost 5%. Dropping
   those five stores outright (unsafe) bounds that gain at +3%. So look at
   register pressure and spills (`0x..(%rsp)` traffic in the hot loop)
   and the inline frame's actuals/this writes, not the clears.
2. **earley-boyer store-buffer traffic**: `StoreBuffer::putSlot` is 70%
   higher than legacy's, and promotion (`promotePlainObject`) is up too.
   Either MIR keeps objects alive longer across minor GCs (rooted values,
   exit operands) or it stores nursery values into tenured objects legacy
   doesn't. Count minor GCs and promoted bytes per lane first.
3. **navier-stokes (-5%)**: `lin_solve` still runs about 3% more cycles
   than legacy, then `advect` and `set_bnd`. The MIR is clean (typed loads,
   f64 arithmetic), so compare the lowered loop against legacy's
   instruction by instruction: bounds and hole checks per `load_elem`,
   and the index `i32.add.ovf` chains.
4. **splay (-1% quiet)**: the set-IC misses are gone. The rest is GC work
   (`memory.fill`, promotion), which is the same question as item 2. The
   set IC's mega arm costs richards about 1.5% (it never takes it, but 103
   sites carry the arm), even with the way-0 and mega stores sharing one
   tail. It is bbv's arm at bbv's sites, so it stays; an arm out of line,
   or only at sites seen polymorphic, is the lever if that matters.
5. **pdfjs**: the remaining TYPES losses (the canvas context's accessor
   slots written through `defineProperty`, `Font` losing TYPES and SLOTS);
   about 291k entry-guard exits. `decrypt` runs an untyped loop.
6. **Open from KICKOFF-3**: int32 accumulators that overflow exit under
   int-first speculation and re-enter; typed globals' residual cost in
   call-heavy code.

For review (deviations from the MIR design doc or from bbv):

- A forwarded target is inlined at a wrapper's `apply` site (bbv calls it
  directly), and `needs_args_obj` is relaxed for an elided forward and for
  a mapped `arguments` with no formals.
- `ctor_publish` methods skip the entry `this` guard.
- A store falsifying TYPES at a known slot demotes the object inline (bbv's
  store choke) instead of taking the engine's generic set.
- The runtime's `PlainStore` lets the first property found on the proto
  chain decide, so shadowing a writable data property counts as a plain
  add (raytrace's constructors had exited on every such add).
