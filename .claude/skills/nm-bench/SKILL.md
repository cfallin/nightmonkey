---
name: nm-bench
description: Benchmark NightMonkey on Octane + react. Use to A/B two builds (keep/drop calls, reported deltas), to check a build for silent baseline fallbacks and exit storms before measuring, or to produce the cross-engine table (native Ion and baseline, the wasm interpreter, weval, NightMonkey MIR, and a second NightMonkey build).
---

# nm-bench

Scripts in this directory. Scratch (variants, modules, results) goes to
`$NM_BENCH_DIR` (default `${XDG_CACHE_HOME:-~/.cache}/nm-bench`, shared by
all checkouts). A `.cwasm` is about 100 MB, so keep it out of the repo.
The benchmark sources are in the repo under `bench/`. `wasmtime` must be
on `PATH`, or set `WASMTIME`.

## Before measuring a build

1. `declines.sh`: lists scripts that silently fell back to baseline, either
   because the MIR validator rejected the optimized MIR or because the wasm
   lowering lacks an op a pass emitted. It must print only `total 0`. These
   fail no test; they only cost score. One missing op lowering cost react
   48% and pdfjs 42%.
2. `ab.sh snap <name>`, then `excensus.sh <name>`: per-bench MIR exit
   totals. Compare them against the base variant's census. An exit that
   fires on every execution (an exit storm) also fails no test.
3. Lanes and tests first, A/B last: see "Quiet machine" below.

## A/B two builds

```
.claude/skills/nm-bench/ab.sh snap base      # at the base commit, after building
.claude/skills/nm-bench/ab.sh snap new       # at the change
.claude/skills/nm-bench/ab.sh run "base new"                 # all 13, seeds 1-4
.claude/skills/nm-bench/ab.sh run "base new" "pdfjs react" "1 2 3"
```

Output: a median per bench and variant (with `n=` kept scores), the number
of dropped outliers, and each variant relative to the first.

A variant is a directory `$W/v/<name>/` with `nightmonkey` and `js`. The
wasm shell links the runtime, so a runtime change needs its own `js`.
Optional files: `pipe` (the `--pipeline`: mir or baseline) and
`env` (`VAR=value` lines for the compile). To ablate a pass, build with its
flag flipped, `snap` it, and flip it back.

The method behind the defaults. Each item cost an earlier session a wrong
keep/drop call:

- **Placement noise of up to ±15%.** Code placement alone moves scores:
  deltablue lost 15% with byte-identical hot code, and richards is bimodal.
  So every variant is compiled with `NIGHT_PAD_SEED=1..4`, and medians are
  compared. Never judge a single build.
- **Run serially.** `PAR=1 CORES=10` is the default. Four parallel jobs
  share caches and skew pdfjs by ±6% per placement. Use `PAR>1` only for a
  rough screen.
- **SMT siblings.** CPU N and N+16 share a core (Ryzen 9950X: 16 cores, 32
  threads). Nothing may run on 26 while 10 is measuring.
- **Shuffled order and core locks.** Jobs run in random order, each taking
  an atomic lock on a core. Assigning cores by job index once put each
  variant on its own core, and a core bias read as a +3–9% "gain".
- **Outliers.** External slow periods halve whole runs. `robust.py` drops
  scores under 80% of the variant's own median and reports how many it
  dropped. Best of `R=2` runs per module.
- **Precompiled modules.** Phase 1 runs `wasmtime compile` once per module
  in parallel. Each timed run loads a fresh copy of the `.cwasm`: its page
  layout is worth a stable 2–3%, and copying re-randomizes it.

## Where the executed instructions go

`--value-census` counts executed Wasm values (instructions) by the MIR op
that emitted them. Octane runs each benchmark for a fixed time, so a faster
build does more iterations and its totals grow; compare builds on fixed
work:

```
.claude/skills/nm-bench/vcensus.sh <tag> "deltablue richards" [nightmonkey js]
```

runs Octane's deterministic mode (warmup off, `deterministicIterations`
divided by `DIV`, default 20) and leaves `$W/vcensus/<tag>-<bench>.{out,map}`.
On those (or any `--value-census` run's stdout and compile log):

- `valcen.py out map [--sites] [--grep RE] [--top N]`: values by op, or by
  op@site;
- `propw.py out map [--sites]`: generic property access (`getprop.data`,
  `setprop.data`, `js.getprop`, `js.setprop`) weighted by the analysis's
  reason the site has no `prop_sites` row; compile with `--dump-propgap`
  too.

## Where the time goes (profiles)

```
.claude/skills/nm-bench/prof.sh <bench> [tag] [nightmonkey js]
python3 .claude/skills/nm-bench/prof.py $W/prof/<tag>-<bench>/stacks.txt \
    --tiers $W/prof/<tag>-<bench>/tiers.txt --under '^night_runtime_call$'
```

`prof.sh` compiles with `--keep-names --dump-tiers`, precompiles, runs
`perf record -g` on CPU 10 (`FREQ`, default 4000 Hz) and leaves
`stacks.txt` (`perf script`) and `tiers.txt` under `$W/prof/<tag>-<bench>`.
`prof.py` prints:
- the split by leaf class: `script` (compiled bodies, `night_script_<sid>`),
  `regex` (compiled matchers), `glue` (adapters, classify, `night_ic_*`),
  `helper` (`night_*` C++ entry points), `engine` (other SpiderMonkey C++),
  `host` (wasmtime, kernel);
- leaf functions, what compiled scripts enter (the first non-glue frame
  above the innermost script: the helper), scripts' self time, and
  script -> entered helper pairs;
- with `--under RE`: a helper's immediate callees, the leaves under it,
  and its calling scripts.

Scripts are named from the tier log, self-hosted ones as `[self-hosted]
<path>`. For one function's machine code, `nm -S m.cwasm | grep <name>`
gives its address and size; `objdump -d --start-address=...` on the
`.cwasm` (an ELF) disassembles it, jump tables included (`wasmtime
objdump` stops at the first one). The leaf frames' `+0x..` offsets in
`stacks.txt` are per-instruction samples to annotate it with.

Compare against native Ion with `perf stat -e cycles,instructions` on
`$SYS_JS <b>.run.js`: at equal run time, instructions per score point is
the codegen-quality ratio (crypto: Ion runs half our instructions per
point at the same IPC).

## The cross-engine table

```
.claude/skills/nm-bench/lanes.sh 3                  # best of 3 per cell
LANES="native-ion aot aot-base" BASE_NIGHTMONKEY=... BASE_JS=... .claude/skills/nm-bench/lanes.sh 3
```

| lane | what | needs |
|---|---|---|
| native-ion | system `js`, full JIT: the ceiling | `SYS_JS` (default `js` on `PATH`) |
| native-baseline | `js --no-ion` | same |
| wasm-interp | the C++ interpreter on wasm32-wasi: the floor | `WASM_JS`, built with `configs/mozconfig-wasm`; reads the program on stdin |
| weval | weval + PBL over the wizer shell: the peer wasm AOT | `WEVAL_JS` (`configs/mozconfig-weval`), `WEVAL` (default `weval` on `PATH`); init function `wizer.initialize` (with a dot) |
| aot | this checkout (MIR) | `make -C build` |
| aot-base | another build's `nightmonkey` and `js`, its default pipeline (or `BASE_PIPE`) | `BASE_NIGHTMONKEY`, `BASE_JS` |

wasm-interp and weval run only when `WASM_JS` and `WEVAL_JS` are set.
`lanes.sh` checks every chosen lane's inputs before it runs anything.

The ratio columns are A/B speedups: aot over wasm-interp and weval, and ion
and baseline over aot. The geomean row covers every bench, since react
reports an Octane-style score too.

## Benchmarks and sources

Vendored in the repo; `bench/README.md` gives their provenance and
licenses.

- **Octane:** `bench/octane/` (or `$OCTANE_DIR`), the 12 benchmarks.
- **React:** `bench/react/react.js` (or `$REACT_JS`), a server-render
  harness with seeded `Math.random` that prints `Score (version 9)`.
- **Entry point:** each program defines a global `main()`. `lib.sh` writes
  two forms of each:
  - **`<b>.js`** drops Octane's trailing `main();` line. The snapshot flows
    (aot, weval) run the top level at wizen time, and the resumed snapshot
    calls `main()`. A top-level call would also run the whole benchmark at
    wizen time. That wastes the time, makes the wizened heap (and so the
    AOT output) vary from run to run, and breaks box2d and mandreel, whose
    `tearDown` spoils the second run.
  - **`<b>.run.js`** adds the call back, for engines that just run a file.

## Traps

- **Never benchmark under `wasm-jit-runner`.** It exists only for the
  jit-tests' in-module compiles. It caches nothing, so every run
  re-Cranelifts the whole SpiderMonkey runtime (the 38 MB module) on the
  one pinned core. More than half of each run was compile. It also uses a
  256 MB wasm stack, so the jit-tests' over-recursion cases hit
  SpiderMonkey's catchable limit first; benchmarks don't need that. The AOT
  modules are plain WASI: use the `wasmtime` CLI with default settings.
- **Quiet machine.** Keep it quiet while `ab.sh` phase 2 or `lanes.sh` runs:
  no jit-test lanes, builds, `cargo test`, `find /` or other A/Bs. One A/B
  next to a lane on the sibling CPUs swung by 50–140%.
- **Never `pkill -f <pattern>`** where the pattern also appears in your own
  command line: it kills your shell. Kill by PID.
- **Failed onramps are quiet.** An onramp whose guards miss re-deopts,
  and baseline then runs the rest of that loop: one exit in the census,
  but the loop's time moves to baseline. A wrong onramp guard (it once
  checked a loop counter against its start value) cost mandreel 51% with
  136 exits. Look at a regressed bench's profile, not only `excensus`.
- **`--dump-tiers` per script** shows which tier compiled each script.
  `--dump-mir` prints a declined script's MIR with the validator's errors.
