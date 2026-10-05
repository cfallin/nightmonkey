# NightMonkey benchmarks, 2026-10-05

Branch `cfallin/mir` at 9912c4f (the MIR tier; the legacy BBV backend is
deleted on this branch). Octane (12 benchmarks) plus a React server-render
harness that reports an Octane-style score. Higher is better everywhere.

## Setup

- Machine: AMD Ryzen 9 9950X (16 cores / 32 threads), Linux; every timed
  run pinned to one core (CPU 10), with nothing on its SMT sibling, best of
  3 runs per cell.
- **Ion**: SpiderMonkey's native shell (`js`, JavaScript-C140.17), full JIT.
- **baseline**: the same shell with `--no-ion` (interpreter + baseline JIT).
- **wasm-interp**: SpiderMonkey's C++ interpreter built for wasm32-wasi:
  the floor for JS-in-Wasm.
- **weval**: weval + the portable baseline interpreter over the wizened
  shell: the peer ahead-of-time Wasm approach.
- **legacy BBV**: NightMonkey's previous (basic-block-versioning) backend,
  now deleted.
- **MIR**: NightMonkey's MIR tier (this branch): JS compiled ahead of time
  to Wasm, run with the `wasmtime` CLI (47.0) on a precompiled module.

Ion, baseline and MIR were measured on 2026-10-05. The wasm-interp, weval
and legacy BBV columns come from an earlier run on the same machine with
the same harness (those engines have not changed since; legacy no longer
builds on this branch).

## Scores

| bench | Ion | baseline | wasm-interp | weval | legacy BBV | **MIR** | MIR / legacy | MIR / weval | MIR / wasm-interp | Ion / MIR | baseline / MIR |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| box2d | 97401 | 21062 | 1815 | 4062 | 19044 | **32370** | 1.70 | 7.97 | 17.83 | 3.01 | 0.65 |
| code-load | 68500 | 67329 | 36484 | 35824 | 36435 | **37041** | 1.02 | 1.03 | 1.02 | 1.85 | 1.82 |
| crypto | 41989 | 5070 | 662 | 972 | 15758 | **28425** | 1.80 | 29.24 | 42.94 | 1.48 | 0.18 |
| deltablue | 28140 | 6182 | 381 | 996 | 6037 | **14063** | 2.33 | 14.12 | 36.91 | 2.00 | 0.44 |
| earley-boyer | 84788 | 19774 | 1448 | 3938 | 13979 | **41200** | 2.95 | 10.46 | 28.45 | 2.06 | 0.48 |
| mandreel | 79316 | 10420 | 840 | 1261 | 18001 | **23640** | 1.31 | 18.75 | 28.14 | 3.36 | 0.44 |
| navier-stokes | 42993 | 7588 | 1157 | 2093 | 24536 | **32648** | 1.33 | 15.60 | 28.22 | 1.32 | 0.23 |
| pdfjs | 93414 | 37055 | 3998 | 6179 | 24251 | **31231** | 1.29 | 5.05 | 7.81 | 2.99 | 1.19 |
| raytrace | 58311 | 11129 | 1006 | 1787 | 12173 | **14652** | 1.20 | 8.20 | 14.56 | 3.98 | 0.76 |
| regexp | 18329 | 6661 | 585 | 763 | 2311 | **2810** | 1.22 | 3.68 | 4.80 | 6.52 | 2.37 |
| richards | 29354 | 5715 | 358 | 926 | 11484 | **15586** | 1.36 | 16.83 | 43.54 | 1.88 | 0.37 |
| splay | 30147 | 23334 | 5162 | 6799 | 10416 | **10605** | 1.02 | 1.56 | 2.05 | 2.84 | 2.20 |
| react | 184367 | 68800 | 6398 | 8625 | 35233 | **83767** | 2.38 | 9.71 | 13.09 | 2.20 | 0.82 |
| **geomean** | 54467 | 14879 | 1647 | 2806 | 14426 | **21930** | **1.52** | **7.81** | **13.32** | **2.48** | **0.68** |

Ratios read "A is N× B": MIR / legacy 1.52 means MIR scores 1.52× the
legacy backend (geomean); Ion / MIR 2.48 means Ion scores 2.48× MIR.

In short (geomean): MIR is 13.3× SpiderMonkey's interpreter in Wasm, 7.8×
weval, 1.5× the legacy backend, and 1.47× native SpiderMonkey with only its
baseline JIT; native Ion is 2.5× MIR.

## Module size

Every module contains the SpiderMonkey runtime: compiling an empty program
gives the fixed part. `.wasm` is NightMonkey's output; `.cwasm` is
`wasmtime compile`'s native code for it.

| | .wasm (MB) | .cwasm (MB) |
|---|---:|---:|
| runtime alone (empty program) | 10.8 | 31.9 |

| bench | .wasm (MB) | above runtime (MB) | .cwasm (MB) |
|---|---:|---:|---:|
| box2d | 50.8 | 40.0 | 82.9 |
| code-load | 12.5 | 1.7 | 33.4 |
| crypto | 15.3 | 4.5 | 39.1 |
| deltablue | 13.2 | 2.4 | 35.5 |
| earley-boyer | 18.5 | 7.7 | 42.9 |
| mandreel | 236.4 | 225.6 | 368.2 |
| navier-stokes | 12.3 | 1.5 | 34.1 |
| pdfjs | 76.5 | 65.8 | 132.2 |
| raytrace | 13.6 | 2.8 | 36.3 |
| regexp | 21.8 | 11.0 | 43.7 |
| richards | 12.2 | 1.5 | 34.1 |
| splay | 11.8 | 1.0 | 33.5 |
| react | 38.8 | 28.0 | 72.2 |

(1 MB = 10^6 bytes.)

## Compile time

Wall time on an otherwise idle machine, all cores available (both tools
are multithreaded). NightMonkey's time includes wizening the program,
the whole-program type analysis, and building, optimizing and lowering
MIR; `wasmtime compile` turns the `.wasm` into native code.

| bench | NightMonkey (s) | of which analysis (s) | wasmtime compile (s) |
|---|---:|---:|---:|
| box2d | 3.9 | 0.3 | 1.7 |
| code-load | 0.3 | 0.0 | 0.4 |
| crypto | 7.1 | 6.4 | 0.5 |
| deltablue | 0.4 | 0.0 | 0.5 |
| earley-boyer | 0.8 | 0.1 | 0.7 |
| mandreel | 79.1 | 1.9 | 7.9 |
| navier-stokes | 0.4 | 0.1 | 0.4 |
| pdfjs | 7.6 | 2.1 | 8.7 |
| raytrace | 0.5 | 0.0 | 0.5 |
| regexp | 1.7 | 0.8 | 1.0 |
| richards | 0.4 | 0.0 | 0.4 |
| splay | 0.3 | 0.0 | 0.4 |
| react | 5.7 | 3.0 | 1.5 |

The outliers: mandreel's time is MIR building and lowering of its very
large functions (73 s of the 79); crypto's is the analysis, whose
call-string context budget runs out on it (bounding contexts per script
brings it to 0.6 s; see MIR.md M5aa).
