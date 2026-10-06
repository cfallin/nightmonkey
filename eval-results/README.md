# NightMonkey evaluation data (2026-10-06)

Octane (12) + react, NightMonkey ablations vs. native Ion / native Baseline /
wasm interpreter / weval. All scores are Octane-style: higher is better.

## Files

| file | shape | what |
|---|---|---|
| `scores.csv` | bench x config | absolute scores. Rows: 13 benches, `geomean` (over benches where the config has a number), `geomean_common` (over the 10 benches every config has), `n_benches`. |
| `relative.csv` | bench x config | same, relative to `nm_default` (1.0 = no change). |
| `spread.csv` | long | per bench x variant: median ratio and min/max over the 4 pad seeds (seed-paired with the same batch's default) -- error bars. |
| `raw_long.csv` | long | every measurement: bench, config, batch, seed, score. |
| `configs.csv` | dictionary | what each config turns off, the knob, and whether the result is clean or an exit storm. |
| `exits.csv` | long | MIR exits to baseline per config x bench (exit census), with a storm flag. |
| `profile_split.csv` | bench | NM default: % of perf samples in compiled scripts / regex / glue / runtime helpers / engine C++ / host. |
| `vcensus_ops.csv`, `vcensus_categories.csv` | long / bench | NM default: executed Wasm instructions by the MIR op that emitted them (Octane deterministic mode, iterations / 20), and grouped into categories. |
| `propgap.csv` | long | generic (IC-served) property ops, weighted by execution, by the analysis's reason for not predicting the site. |
| `reducibility.csv` | bench x policy | waffle reducifier duplication in MIR bodies under three inner-onramp policies, plus the inlining-off blowups. |
| `analysis_census.csv` | bench | static analysis size and receiver precision per property-read site (Empty/One/ClassAny/AnyOf/AnyObject). |
| `compile_time.csv` | bench | AOT compile phases (ms), single core (pinned; translation normally runs in parallel), wasmtime compile (s), peak RSS. |
| `code_size.csv` | bench x config | `.cwasm` bytes (seed 1). Dominated by the ~33 MB linked runtime. |

## Method

- **NM variants**: one binary (branch `cfallin/ablations-exp`, experiment-only
  `NIGHT_ABLATE` knobs); a variant differs only in its env. Every former
  `const X: bool = true` mechanism switch in the MIR builder, optimizer and
  lowering is a knob; fact groups clear tables of the analysis output
  (sound: every fact is a guarded prediction).
- Each variant x bench: AOT-compiled with code-placement seeds
  `NIGHT_PAD_SEED=1..4`, best of 2 runs per module, median over seeds (scores
  < 80% of the variant's own median dropped; 0 drops occurred). Runs
  shuffled, pinned to CPU 2 or CPU 10 (separate CCDs/L3s), SMT siblings idle,
  fresh `.cwasm` copy per run.
- Variants ran in 6 batches; every batch includes `nm_default`, and each
  variant is compared to its own batch's default. Absolute variant scores in
  `scores.csv` are (variant/same-batch default) x pooled default median.
- **Noise floor**: `nm_default` medians across the 6 batches (hours apart)
  agree within 0.7-3.2% per bench. Treat per-bench changes under ~3% and
  geomean changes under ~1% as noise.
- **Engines** (`lanes.sh`, best of 3, CPU 10): system `js` C140 (Ion,
  `--no-ion`); wasm interp and weval shells from `~/work/firefox/obj-wasm`
  (-O2) and `obj-weval` (-O3, PBL + AOT ICs), built 2026-07-14 -- not NM's
  exact SpiderMonkey revision. Engines are best-of-3, NM cells medians: the
  `nm_lanes_check` column (NM default, best of 3 in the lanes run) agrees with
  `nm_default` to 0.2% geomean.
- Every variant was compiled with `--dump-tiers`: zero silent invalid-MIR
  declines except `nm_noexitops` (2 scripts). Large regressions were checked
  with the exit census (`exits.csv`).

## Caveats (read before quoting)

- **Exit storms (inconsistent ablations)**: `nm_facts_calls` and
  `nm_field_masks` remove one fact/mechanism that others depend on, and the
  fixed-facts design (a failed guard exits, nothing recompiles) turns that
  into millions of exits. Use `nm_calls_cg` for the value of call targets and
  `nm_facts_heap` for the value of field types. `nm_facts_all` on box2d also
  has 275K exits (vs 476).
- **Failures**: `nm_inlining` / `nm_calls_cg` fail on earley-boyer, mandreel
  and pdfjs: with inlining off the reducifier blows up (compile > 20 GB, see
  `reducibility.csv`). `nm_facts_calls` and `nm_nothing` fail on mandreel:
  a function exceeds wasm's 7.65 MB function-size limit. Geomeans of these
  variants cover fewer benches -- use `geomean_common`.
- `dirty_exits` off produces invalid MIR (unmaintained rejoin path), so it is
  not in any variant.

## Headlines (geomean vs NM default; `geomean_common` in parentheses)

- Cross-engine: NM is 13.3x wasm interp, 7.8x weval, 1.47x native Baseline;
  native Ion is 2.48x NM.
- Baseline tier alone: 0.16x (MIR tier is 6.4x over NM's own baseline tier).
- The analysis: no facts at all 0.44x; no heap value types 0.76x (navier
  0.15x, box2d 0.48x, crypto 0.50x; pdfjs 1.12x -- its wrong heap
  predictions cost it); no slot prediction 0.88x (box2d 0.46x, richards
  0.62x); no interprocedural arg/return types 0.88x.
- Calls: no codegen use of call targets 0.82x (deltablue 0.41x, richards
  0.53x) and inlining off 0.87x, both over 10 benches.
- Optimizer: all passes off 0.955x; PEA, SROA, GVN, LICM, guard hoisting,
  mem-VN, hoist-reads, promote each within noise individually. The speedup
  is the predictions plus specialized lowering, not classic mid-end opts.
- Speculation: int32-first off 0.89x (crypto 0.25x); exit-on-rare-path
  generic ops off 0.94x (navier 0.76x).
- Onramps: outermost-only and uncapped are both within noise of the 400-byte
  cap at runtime.
- Reducibility: duplication is +0.6% instructions at the shipped cap, +4.1%
  uncapped (navier +12.6%, pdfjs +9.2%; single functions up to 6x); the cap
  admits 55 of 153 inner-loop onramp candidates. With inlining off it still
  explodes: earley-boyer sid 793, 1,680 -> 6.13M blocks (11.9K -> 56.9M
  insts). Multiloop's case is robustness/compile cost, not steady-state speed.
- What's left: compiled code is 76-99% of time except splay (69% engine:
  GC/alloc), code-load (93% parse/eval), pdfjs (40% engine: strings/GC, 13%
  helpers), regexp (62% helpers+engine). Executed-instruction mix: guards +
  box/unbox are 37-57% in box2d, richards, mandreel; generic/IC-served ops
  31-64% in deltablue, earley, raytrace, pdfjs, splay. Unpredicted property
  sites are mostly "no agreed class" (earley: 68% AnyObject receivers).

## Reproducing

`scripts/` holds the drivers (originally in `~/.cache/nm-bench`):
`abx.sh` (one A/B batch, module cache, per-compile 20 GB memcap),
`queue.sh` + `queue.txt` (the batch list), `agg.py` (per-batch table),
`make_csv.py` (these CSVs), `census-session.sh` (lanes, value census,
profiles), `excensus-env.sh` (exit census honoring a variant's env),
`val1.sh` (decline check), `knobify.pl` (turned the `const X: bool`
switches into `knob!`s). A variant is `~/.cache/nm-bench/v/<name>/` with
`nightmonkey`, `js` and an `env` file (`NIGHT_ABLATE=...`; see `configs.csv`).

**Build note:** this branch's `Cargo.toml` patches waffle to a local copy
(`/home/cfallin/.cache/nm-bench/waffle-exp`) that only makes waffle's
`backend` module public, for the reducifier statistics
(`scripts/waffle-pub-backend.patch`). To build elsewhere, apply that patch
to a waffle checkout and point the `[patch.crates-io]` entry at it.
