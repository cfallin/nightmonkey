# MIR tier: kickoff for the next session (7)

Branch `cfallin/mir`. Read docs/MIR.md, docs/MIR-AUDIT.md, docs/MIR-PARITY.md
and docs/MIR-KICKOFF-6.md first; their working rules still hold.

The build now needs the firefox fork's `nightmonkey-slots` branch
(`git@github.com:cfallin/firefox`, one commit on `nightmonkey-external`):
configure with `-DSPIDERMONKEY_DIST=<that checkout>/obj-nightmonkey-sm/dist`.
It adds the `shapeForAdd` hook to `JS::ExternalCompilerHooks`, so an older
dist no longer compiles `runtime/NightHooks.cpp`.

## Measurement notes

- **Benchmark sources.** The Octane files in `~/work/firefox-scratch/octane`
  end with a top-level `main();`, so wizening runs the whole benchmark once
  (interpreted) before the runtime calls `main` again. box2d's and mandreel's
  `tearDown` break that second run (`Box2D = null`; mandreel's
  `setupMandreel` wraps its own wrapper and recurses), so they reported no
  score in either pipeline. `~/work/nm-mir-scratch/prof7/octane/` has copies
  of those two without the call; the other files are kept as earlier
  sessions measured them.
- **A/B script.** `~/work/nm-mir-scratch/prof7/ab3.sh "variants" "benches"
  "seeds"`: each variant is a directory `prof7/v/<name>/` with its own
  `nightmonkey` and `js` (the shell carries the runtime, so runtime changes
  need their own shell) and an optional `pipe` file. It allocates run cores
  with atomic locks. prof6's `ab2.sh` picked the core as job index mod 4,
  which put two running jobs on one core whenever jobs finished out of
  order; those runs score half. `robust.py` then drops them as outliers, but
  it is wasted work.
- Never `pkill -f` a pattern that appears in your own command line (the
  tool's shell carries it, heredocs included): kill by PID, or with
  `prof7/stopab.sh`-style scripts written to a file first.

## Landed (this session)

Final comparison (commit 80e7414; 6 placements, best of 2, per-variant
outlier rejection, none dropped; MIR / legacy):

| | MIR | legacy | |
|---|---|---|---|
| box2d | 18524 | 18744 | -1.2% |
| code-load | 34272 | 33795 | +1.4% |
| crypto | 17403 | 15292 | +13.8% |
| deltablue | 10136 | 5792 | +75.0% |
| earley-boyer | 12428 | 12158 | +2.2% |
| mandreel | 19094 | 16604 | +15.0% |
| navier-stokes | 21210 | 20660 | +2.7% |
| pdfjs | 21658 | 19708 | +9.9% |
| raytrace | 12234 | 11620 | +5.3% |
| react | 32650 | 32328 | +1.0% |
| regexp | 2138 | 2052 | +4.2% |
| richards | 11263 | 11224 | +0.3% |
| splay | 7644 | 7704 | -0.8% |

Geomean +8.6% (+4.4% without deltablue), the same lead as at the session's
start (+8.7%): the runtime fixes below help every tier. box2d and splay are
inside placement noise. Commits (messages and MIR.md M5k-M5n have detail):

- **Slot layouts** (the planned work; e8bb25c, 80e7414, firefox
  `nightmonkey-slots` 4dae0902): custom-slot shapes, `PermutedSlots`, the
  stored span and the `shapeForAdd` hook in the engine; the row-slot policy
  and memo in the runtime; stamp gates that count properties on permuted
  shapes; add-transition replays of hole fills (site rows) and skips (C++
  tables only). pdfjs: the Font methods' 55.6k entry exits are gone. One
  deviation from the plan: NightMonkey's own adds reach the placement
  through the engine hook (their replays are populated from engine adds),
  not by calling the API directly.
- **Literal allocation size** (ca21507): literals of 5+ fields spilled to
  dynamic slots and cleared SLOTS on every allocation (react 1.19M times a
  run). react +4.9% MIR, +15.7% legacy; pdfjs +3%.
- **By-name dispatch** in the analysis (efe3653): pdfjs MIR exits 140k ->
  52k.
- **`instanceof` narrowing** (05bc9d9): open item 2 of KICKOFF-6.
- **Diamonds with a generic arm** (9f47f15): two constructors had been
  declined as invalid MIR since before this session.

All four jit-test lanes pass (MIR 12895, legacy 12907, baseline 12897,
interp 13094) and 71 night tests, 6 of them new.

## Open

1. **Optional fields.** A field written on some constructor paths only
   (pdfjs's `XRef.encrypt`, `Font` on its Type3 and early-return paths)
   leaves a hole under the new slot layouts, and a stamp needs every row
   field present, so those objects are never stamped: every `this`-guarded
   method call on one exits (pdfjs: XRef methods, about 7.8k exits). It
   was the same before (the span fell short). A layout could put the
   fields every path writes first and stamp on those, with the optional
   ones as `named` fields (typed, read through the IC), but a named field's
   typed read does not check presence today (an absent one reads the
   prototype's value, usually undefined, under a claim that may exclude
   it), so that needs a presence rule first.
2. **pdfjs's remaining int32 exits** (about 31k: `current.fontSize`,
   `current.x` claimed int32). The operator methods are reached by
   `this[fnName].apply(this, args)` in `executeOperatorList`, and its
   `operatorList` still reads Empty: it arrives through
   `PDFPageProxy.display`, which runs from pdf.js's own promise callbacks
   and `Function.prototype.bind` (unmodeled), then a `gfx` formal that no
   resolved call binds. Two steps that did not help alone are in
   `prof7/this-binding-experiment.patch` (bind a computed-name dispatch's
   receiver as `this`; bind `this` in by-name calls when the context budget
   refuses one). Writes through an AnyObject `this` are dropped by design,
   which is what keeps these claims optimistic.
3. **crypto's `i32.mul.ovf` exits** (12k, `bnpInvDigit` and
   `bnpDivRemTo`, 28-bit digit products that overflow on every call).
   Legacy's interval track computes them exactly in i64 or continues in
   f64; MIR has no ranges (MIR-PARITY 1.5).
4. KICKOFF-4 item 4 (splay GC) and KICKOFF-5 item 1 (earley-boyer frame
   traffic) stand.
