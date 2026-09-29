# MIR tier: kickoff for the next session (5)

Branch `cfallin/mir`. Read docs/MIR.md, docs/MIR-AUDIT.md, docs/MIR-PARITY.md
and docs/MIR-KICKOFF-4.md first; their working rules still hold. One rule
added this session:

- **Compare builds across code placements.** Code placement alone moves
  Octane scores by up to 15%. deltablue's `Plan.execute` ran 15% more
  cycles from byte-identical code at the same alignment after unrelated
  functions changed size. richards is bimodal (10.7k / 11.3k) across builds
  that only shift code. Compile with `NIGHT_PAD_SEED=1..N` (f4436d4) and
  compare medians. The scratch `sweep.sh` (in `~/work/nm-mir-scratch/prof5/`)
  does it. Single-build A/Bs of a few percent are noise, in either
  direction, including MIR against legacy.

## Where things stand

Median over 4 placements (quiet runs for earley-boyer, regexp, react and
navier-stokes; the rest 10 in parallel):

| | MIR | legacy | |
|---|---|---|---|
| crypto | 17030 | 15415 | +10.5% |
| deltablue | 8912 | 5720 | +56% |
| earley-boyer | 11570 | 12500 | -7.4% |
| navier-stokes | 21369 | 20408 | +4.7% |
| pdfjs | 21073 | 20876 | +0.9% |
| raytrace | 11828 | 11526 | +2.6% |
| regexp | 2228 | 2171 | +2.6% |
| richards | 10676 | 10776 | -0.9% |
| splay | 7714 | 7641 | +1.0% |
| react | 31672 | 31656 | +0.1% |

earley-boyer is the one real gap. KICKOFF-4's navier-stokes -5% and most
of richards' -9% were placement.

What landed:

- **Lean inline frames** (ad88751). `inline.enter` writes callee, `this`,
  the actuals and the locals, as bbv's splice does. It writes env only for
  a callee with `EnvSet`/`EnvPop`, and all six fixed slots only for a
  construct or a callee reading its arguments object or new.target. The
  frame's GC scan (`frame_top`) stops below what it left out, and the
  `exit.inline` hub writes those slots. By placement medians: richards
  +5.7%, deltablue +6.8%, earley-boyer 0. (KICKOFF-4's "+3% upper bound"
  from dropping five of these stores was a single-placement number.)
- `NIGHT_PAD_SEED` and `NIGHT_GC_STATS` (f4436d4). GC stats print the minor
  GCs, promoted bytes, major GCs and the NightStack slots traced.

## The store traffic, characterized

Measured with a temporary census (per-block store counts, and per rooting
category in both backends; `~/work/nm-mir-scratch/kickoff5-experiments.patch`).
Figures are per score point.

- **The excess is all frame stores.** Heap stores are equal (richards 34k
  / 35k, earley-boyer 88k / 87k). Frame stores (`sp`/`vp`-addressed) before
  lean frames: richards 352k / 152k, earley-boyer 420k / 204k. After:
  richards 241k, earley-boyer 420k.
- **It costs through code size, not the store queue.** Store-queue stalls
  are negligible (richards 55 cycles per point of about 1M). The penalty is
  frontend. Before lean frames, richards spent 23.4% of dispatch slots
  frontend-bandwidth-bound against legacy's 16.5%, with 89% more ops from
  the legacy decoder (op-cache misses). That was at equal retired
  instructions and lower backend-memory-bound time. earley-boyer now: +2.6%
  instructions, +20% stores, +53% decoder ops, +9.7% cycles. Its hot code
  is 13-15% bigger (90% of samples in 66.5 KiB against 58.8 KiB). In
  `rewrite_nboyer`, frame stores and their boxed constants are about 70% of
  MIR's extra hot bytes: 199 hot linear-memory stores against 97.
- **GC behaviour is the same.** Per score point, minor GCs, promoted bytes
  and major GCs match legacy on earley-boyer and splay (0.0626 / 0.0629
  minors, 69.9 / 70.8 KB promoted per point). The rooting scheme does not
  retain or promote more. MIR's stack is 2.5-2.8x deeper at each GC (975
  vs 2474 slots per trace on earley-boyer; bigger frames: the full baseline
  layout, the rooting area and inline frames). The tracing cost is small,
  and L1D fills are +11%.

Where MIR's frame stores come from, against bbv's (per point, after lean
frames):

| | richards MIR | bbv | earley MIR | bbv |
|---|---|---|---|---|
| inline frame init / splice init + seam | 71k | 91k | 74k | 48k |
| home stores + dead clears / operand spills | 72k | 12k | 150k | 53k |
| entry + call frames / prologue (+ other) | 48k | 18k | 149k | 77k |
| retaining stores / local write-through | 49k | 31k | 39k | 27k |

- bbv scans only its dense spill area (`top` just past the live operands),
  so it never clears. MIR's fixed rooting area needs clears. In call-heavy
  code (earley-boyer) nearly all of them are **entry junk**: the first GC
  point of each activation clears every slot not yet written, because the
  area sits on stale bits of popped frames that a minor GC may have left
  dangling. The fixed-slot stores at entry (resume, backoff, args_obj,
  new_target, rval) exist for the same validity reason. bbv's frame is
  compact: env, args_obj and new_target only when used, and no
  resume/backoff.
- Retaining stores: the same object reaches a loop header under fresh
  names (block params, `weaken`), so `framed` never matches and each
  re-stated `frame.store` becomes a store at the next GC point or inline
  entry. Deduplicating by copy class was tried (below) and removes almost
  nothing dynamically, so the retain count has another source.

## Experiments not landed

All in `~/work/nm-mir-scratch/kickoff5-experiments.patch`, env-gated, with
placement medians against lean:

- `NIGHT_EXP_KEEPDEAD`: no dead-value clears after the entry junk (a
  written slot stays valid; the GC updates it). richards +2.8%, deltablue
  +1.3%, earley-boyer 0, splay 0. It changes retention: a dead object stays
  referenced from its frame slot until reuse or return. That is **a design
  decision** (MIR.md §4.4's `WeakRef` rule).
- `NIGHT_EXP_NOJUNK` with the runtime's `NIGHT_STACKCLEAR` (clear the
  NightStack above `top` at each GC, so stale slots are never dangling). The
  entry then leaves the rooting area clean and skips the unread fixed
  slots. Upper bound without the clear's cost: earley-boyer +1.4%, richards
  +2.7%, splay +2.4%. Without the clear it is unsafe (2 of 6 splay
  placements crashed). A clear to a high-water mark that only grows cost
  4% on earley-boyer (deep recursion pushes the mark up). A sound version
  needs compiled entries to keep a since-last-GC mark (compare and rare
  store) that the GC clears to and resets. **A design decision**; the same
  invariant would let baseline and bbv skip their prologue stores too.
- `NIGHT_EXP_FOLDFIX` (the fixed slots as dirty rooting slots) and
  `NIGHT_EXP_NOCLEAR` (init the area at entry, no clears): no better than
  lean once combined. Every function then pays extra clears or inits.
- Copy classes for `framed`: neutral to -1%, 0.2% fewer stores.

## Landed after the first write-up (same session)

- **Retention** (afcffa2): a dead value stays in its home slot; only
  slots not yet written since entry are cleared. richards +2.8%,
  deltablue +1.3%.
- **Stack clearing, shelved** (patches in `prof5/stackclear-*.patch`).
  Zeroing the NightStack above `top` at each GC, up to a since-GC mark
  that every body raises on entry, is memory-sound and lets frames skip
  every GC-only store. But a slot a frame never writes then keeps what a
  popped sibling left there: `f(obj); obj = null; longRunning()` pins
  `obj` for longRunning's whole activation, and mirstress failed
  gc/weak-marking-01.js on exactly that. Gain over retention alone:
  earley-boyer +0.9%, others about 0. Decided: keep the bounded
  retention, not this.
- **Compact frames** (dcf19fa): env, arguments-object and new.target
  slots only where used. -3.8% stores, time unchanged. It exposed a latent
  overlap: a lean inline frame's retaining store past its scan landed in
  a nested frame (closures/t001).
- **GVN** (77364e3) of env/global/unbox ops: env chain reads halved in
  earley-boyer's closures; time unchanged.
- **Standalone constructors** (00a2d60) type their constructing `this`
  (KICKOFF-3 item 3): earley-boyer +4.2%, splay +5.9%.
- **Arguments elision** for `.length`/element reads (`sc_list`,
  `sc_append`): earley-boyer +5.0% (measured with inlining into such
  scripts allowed; landed without that relaxation, to be re-measured, as
  pdfjs/raytrace/react dipped 1-2% with it).

## Next

1. **earley-boyer**: about at legacy after the constructor and arguments
   work (MIR 12460 vs legacy 12300-12650 in same-day sweeps; re-measure
   quietly). What remains is per-activation frame traffic and hot code
   size. The levers that were open:
   - retention (KEEPDEAD);
   - the runtime stack clear with a since-GC mark (NOJUNK);
   - a compact frame layout shared by baseline and MIR (fixed slots only
     when used, as bbv's);
   - home slots per copy class (coalesce a loop-carried object's names into
     one slot, so edges stop re-storing it).
   A get IC on a receiver known to be an object skips the tag test in bbv
   but not in MIR (after `instanceof`).
2. Items 3-6 of KICKOFF-4 stand, minus navier-stokes, which now leads.
