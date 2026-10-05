# NightMonkey: AOT JavaScript-to-WebAssembly compilation

**NightMonkey** is an ahead-of-time JS-to-Wasm compilation tier layered
on top of SpiderMonkey. NIGHT expands to *Nonlocal Inference with Guiding
Heuristics for Types*: an optimistic whole-program type analysis guides
code generation, with dynamic guards for correctness. (The night monkey,
genus *Aotus*, is the only truly nocturnal monkey: it does its work in
the night, before the program runs during the day.)

Each JS function's bytecode is compiled to a WebAssembly function that
runs alongside the runtime compiled to Wasm. There are two modes of use:

- **Snapshot** (the shipping flow): the `nightmonkey` host binary drives
  Wizer in-process to snapshot the runtime plus loaded user program (or
  processes an existing Wizer snapshot), reads out JS bytecode and heap
  objects (such as prototype objects), and rewrites that snapshot with
  compiled bodies.
- **In-process** (the testing flow): the JS shell compiled to Wasm runs
  under `wasm-jit-runner` and, with `--night-inprocess`, asks it to compile
  its script tree (one hostcall). The runner walks the shell's live heap,
  runs the compiler natively, and injects the bodies into the running
  instance. A drop-in shell for jit-tests.

NightMonkey has a two-part structure: an *optimistic static type
analysis* and a *guard-based codegen backend*. The idea is that we:

1. "Predict" types statically, using a model of JavaScript semantics
   that is intentionally optimistic (elides corner-cases). We call this
   the "likelier-types analysis" (in a nod to the initial version of the
   analysis, the "likely-types analysis"; this one is a little better).

2. Generate an optimistic Wasm body for a given JS function bytecode
   body, using those predicted types.

3. Insert dynamic guards checking those assumptions, with fallbacks to a
   fully generic (but still compiled!) Wasm body.

The *key constraint* that NightMonkey adheres to, and attempts to solve:
we cannot derive type information, or any other profiling information,
by observing a running program. In other words, unlike the standard JIT
approach based on the "JIT hypothesis" (that a warmed-up program will
reach a steady state with stable types, which we can then specialize
for), we must decide any specialization we will do ahead-of-time, based
on whatever analysis or heuristics we can come up with. The thing we
permit ourselves in return is much more analysis time: unlike a JIT
engine, we do not need to compile in milliseconds.

NightMonkey performs its analysis using a whole-program, call-sensitive,
points-to (heap abstraction) + callgraph analysis, over a lattice that
is a hybrid of a Steensgaard (union-find-based) and capped Andersen
(points-to-set/membership-based) design.

The codegen using the types that come out of this analysis is then a
"two-track" approach: there is one optimistic track that adheres to
"type contexts" that are maximally optimal, and one fully generic track.
(Earlier experiments tried to do more multiversioning, a la Static Basic
Block Versioning, but that did not converge well.)

## Layout

| Path | Contents |
|---|---|
| `compiler/` | The compiler crate (`night-compiler`). |
| `compiler/src/source.rs` | The `Source` object graph: the sole input to the compiler. |
| `compiler/src/bytecode.rs` | Bytecode parser and `OpcodeVisitor`. |
| `compiler/src/opcodes/` | The `JSOp` enum, lengths and stack effects, generated from the engine's `vm/Opcodes.h` by `scripts/gen_opcodes.py` and checked in per engine version (`ff147.rs`, ...); a cargo feature of the same name selects one. |
| `compiler/src/options.rs` | `Options`/`Diagnostics`: the entire configuration surface. |
| `compiler/src/likelier/` | The speculative likely-types analysis (`scan`/`heap`/`calls`/`engine`/`emit`/`dump`). |
| `compiler/src/opsem.rs` | Interval algebra and op semantics; the vocabulary shared by analysis and codegen. |
| `compiler/src/facts.rs` | `LikelyFacts`: the analysis-to-codegen fact contract. |
| `compiler/src/mir/` | MIR: the typed SSA IR, its validator and optimizer (`docs/MIR.md`). |
| `compiler/src/wasm/mir/` | The MIR tier: building MIR from bytecode, lowering it to Wasm, inlining, plus the shared ABI constants (`abi.rs`), class-word rules (`stamp.rs`) and out-of-line runtime helpers (`helpers.rs`). |
| `compiler/src/wasm/baseline/` | The baseline tier: the generic one-op-at-a-time lowering MIR exits to (`docs/BASELINE.md`). |
| `compiler/src/wasm/translate.rs` | Shared translation substrate: `Helpers`/`AtomTable`/`Outcome`/ctx types, layout constants. |
| `compiler/src/wasm/regex.rs` | The regex AOT compiler (irregexp bytecode to Wasm matchers). |
| `compiler/src/wasm/mod.rs` | The `layout_env` / `translate_all` seams: analysis prepass, reserved linear-memory region layout, body translation, table patching. |
| `compiler/src/wasm/inprocess.rs` | In-process batch builder, run by `wasm-jit-runner`'s `night_compile` hostcall. |
| `runtime/` | The night runtime: `NightRuntime.cpp` is the `night_runtime_*` C ABI generated code calls, in front of the engine halves it forwards to -- `NightOps.cpp` (bytecode ops), `NightInlineCaches.cpp` (property-cache populate and replay), `NightInlineHeap.cpp` (inline allocation, write barriers, and the baked-layout asserts), `NightGenerator.cpp`, `NightRegExp.cpp`. `NightEntry.cpp` is the other direction: entering compiled bodies. `NightHooks.cpp` is the engine's external compiler hook table (see `docs/INTEGRATION.md`). Plus the value stack and snapshot registration/activation/capture. Built against SpiderMonkey's private headers. |
| `shell/` | `nightshell.cpp`: the NightMonkey wasm shell, SpiderMonkey's shell (`libjsshell`) with the hooks installed and the `--night-snapshot` / `--night-inprocess` flows. |
| `spidermonkey/` | The mozconfig that builds SpiderMonkey the way NightMonkey needs it. |
| `scripts/` | `build-spidermonkey.sh`, `run-jit-tests.sh`, `run-jstests.sh`, and the harness shell wrapper template. |
| `tests/` | The jit-test and jstests exclusion lists for the AOT lane. |
| `snapshot/` | Snapshot/live-heap reader crate (`night-snapshot`): parses the registration block and walks the script graph into a `Source`. |
| `nightmonkey/` | The `nightmonkey` binary: snapshot in, AOT-compiled module out. The optional `wizen` Cargo feature also accepts programs and drives wizer as a library. |
| `wasm-jit-runner/` | Wasmtime-based runner for the in-process flow: the `night_compile` hostcall runs the compiler over the shell's live heap and injects the bodies. |
| `configs/` | Benchmark-lane mozconfigs for the SpiderMonkey tree (`mozconfig-native`/`-ion`/`-wasm`/`-weval`); the NightMonkey build itself uses `spidermonkey/mozconfig`. |
| `docs/` | `DESIGN.md`, `INTEGRATION.md` (the SpiderMonkey hook surface), `TODO`. |
| `tools/` | Profiling and benchmarking helpers (`opprof.py`, `hotloop.py`, `pairab.sh`, ...). |

## Building

NightMonkey lives in its own repository and links against a SpiderMonkey
build. SpiderMonkey needs a small patch: `--enable-external-compiler-hooks`,
which adds the per-object/per-script words and the hook table the tier plugs
into, exports the engine's private headers, and builds the shell as a static
library (`docs/INTEGRATION.md`).

Step 1 -- build SpiderMonkey (wasm32-wasi, wizer-capable shell, hooks on):

```
scripts/build-spidermonkey.sh /path/to/firefox
# -> /path/to/firefox/obj-nightmonkey-sm/dist
```

This is `MOZCONFIG=spidermonkey/mozconfig ./mach build` in the SpiderMonkey
checkout. `dist/include-private/` mirrors `js/src` (source and generated
headers) and records the compile flags libjs was built with in
`js-build-config.json`; `dist/lib/` holds `libjsshell.a`, `libjs_static.a`,
`libjsrust.a` and `libpure_virtual.a`.

Step 2 -- build NightMonkey against it:

```
cmake -S . -B build -DSPIDERMONKEY_DIST=/path/to/firefox/obj-nightmonkey-sm/dist
cmake --build build
# -> build/bin/js               (the NightMonkey wasm32-wasi shell)
# -> build/bin/js-inproc        (the same, with the --night-inprocess driver)
# -> build/bin/nightmonkey      (the host AOT compiler)
# -> build/bin/wasm-jit-runner  (the in-process test host, with the compiler)
# -> build/bin/inproc-shell.sh  (the harness wrapper)
```

The CMake build compiles the runtime and the shell with exactly the flags
libjs used (same sysroot, target, ABI flags and force-included configuration
headers), and drives Cargo for the host tools. Options:
`-DNIGHT_INPROCESS=OFF` drops the in-process lane (no `js-inproc`, no
runner); `-DNIGHT_DEBUG=ON` turns on the runtime diagnostics and
the crash-on-failure of the in-process lane; `-DNIGHT_ENGINE_VERSION=ff147`
selects the engine version (below).

Plain `cargo build` works for the Rust crates.

### Engine versions

The compiler's opcode table (`JSOp`, opcode lengths and stack effects)
is generated from the engine's `vm/Opcodes.h` by
`scripts/gen_opcodes.py` and checked in under `compiler/src/opcodes/`,
one file per supported engine version, each recording a digest of the
header it came from. A cargo feature named after the version (e.g.,
`ff147`) selects the table a build targets, and the lowerings
feature-guard any per-version differences. The CMake build checks that
the selected table is what the engine being built against generates:

```
scripts/gen_opcodes.py check ff147 /path/to/firefox/obj-nightmonkey-sm/dist/include-private/vm/Opcodes.h
```

so an engine whose bytecode differs from the table, in shape or in
meaning, forces a build failure. To support a new engine: review its
`Opcodes.h` diff against the lowerings, then (e.g. for version
`ff153`)

```
scripts/gen_opcodes.py generate ff153 /path/to/that/Opcodes.h
```

declare the `ff153` feature in `compiler/Cargo.toml` and the crates
that forward it (`snapshot`, `nightmonkey`, `wasm-jit-runner`), add its arm to
`compiler/src/opcodes/mod.rs`, and condition the lowering changes on
`feature = "ff153"`.

CI (`.github/workflows/ci.yml`) builds both trees and runs the jit-test
suite in the AOT lane.

## Prerequisites

- A SpiderMonkey checkout on the tracked branch, bootstrapped for the JS
  shell (`./mach --no-interactive bootstrap --application-choice=js`) plus
  the wasm32-wasi sysroot in `~/.mozbuild` (see `.github/workflows/ci.yml`
  for the exact steps).
- A Rust toolchain with the `wasm32-wasip1` target
  (`rustup target add wasm32-wasip1`), CMake 3.20+.
- `wasmtime` on `$PATH` or at `$HOME/bin/wasmtime`, to run compiled modules.

Wizer is a library dependency of `nightmonkey`; there is nothing to install.

## Flow 1: snapshot (the shipping flow)

To compile a program:

```
build/bin/nightmonkey --shell build/bin/js program.js -o program-aot.wasm
wasmtime run program-aot.wasm
```

`nightmonkey` snapshots the shell with Wizer in-process, then rewrites
the snapshot and appends compiled bodies. The program's top level runs
*during* wizening, so setup and class construction are captured in the
image, and the resumed snapshot calls the program's global `main()`.

Passing a pre-made snapshot instead of a `.js` file also works, and is the
fast inner loop for compiler work:

```
nightmonkey --shell build/bin/js program.js --keep-snapshot snap.wasm -o out.wasm
nightmonkey snap.wasm -o out.wasm      # recompile without re-wizening
```

`nightmonkey --help` lists the diagnostics (`--stats`, `--dump-tiers`,
`--dump-mir`, `--dump-facts`, `--dump-graph`, ...), the instrumentation
switches (`--mir-exit-census`, `--block-census`) and the compilation
options (`--keep-names`, `--pipeline`, `--strict-coverage`).
Debug sections are stripped by default; `--keep-names` retains them.

To see what a program compiles to, `tools/viz.py` writes one HTML page with,
per script, its source, its bytecode, its MIR and the lowered waffle IR side
by side, linked: click a line, op, instruction or value and its counterparts
in the other columns light up (the URL keeps the selection, so links can be
shared):

```
tools/viz.py program.js -o program.html                  # runs nightmonkey --viz
tools/viz.py react.js -o r.html --only '^pushAttribute$' # a big program: pick scripts
```

## Flow 2: in-process (drop-in shell for jit-tests)

Run a program:

```
build/bin/wasm-jit-runner --dir / --cache-dir ~/.cache/wjr \
    build/bin/js-inproc -- --night-inprocess /abs/path/program.js
```

The script path must be **absolute**: the guest resolves paths against the
runner's preopen root (`--dir /`). `--cache-dir` caches the compiled shell.
Everything after `--` goes to the JS shell. Omitting `--night-inprocess` runs
the same binary as a plain interpreter -- the interpreter-only ("interp")
lane, the differential reference for the compiled lanes.

The compiler runs in the runner, not in the shell: a compiler change
reaches the lanes through `make -C build wasm_jit_runner`, a runtime or
engine change through `make -C build js-inproc` (or `make -C build` for
both). The runner compiles with Rayon; `WJR_COMPILE_THREADS` caps its
threads, and `WJR_COMPILE_STATS=1` prints the walk and compile times.

The jit-test suite in the default (MIR) lane and the interp lane, from
the SpiderMonkey checkout's harness:

```
scripts/run-jit-tests.sh /path/to/firefox build -- -j16
NIGHT_INPROCESS_OFF=1 scripts/run-jit-tests.sh /path/to/firefox build -- -j16
```

Compiler flags for the in-process batch (the same ones `nightmonkey`
takes) go in `NIGHT_OPTIONS`, which the wrapper passes to the shell as
`--night-options`. For example, the baseline-tier lane, failing any test
whose script ends up interpreted:

```
NIGHT_OPTIONS="--pipeline baseline --strict-coverage" \
    scripts/run-jit-tests.sh /path/to/firefox build -- -j16
```

`--dump-tiers` reports, per script, which tier compiled it and why others
declined (`docs/BASELINE.md`).

`scripts/run-jstests.sh` does the same for jstests (hours for the full
suite; append a path to scope). Every lane is expected to pass completely.
Every lane skips `tests/wasi-jit-test-excludes.txt` and
`tests/wasi-jstests-excludes.txt`: tests the wasm32-wasi shell cannot run at
all (no Intl, no shared memory or Atomics, no threads, no time zone database,
a small native stack), independent of the tier. The compiled lanes additionally
skips `tests/jit-test-excludes.txt` and `tests/jstests-excludes.txt` (passed
as `--exclude-from` / `--exclude-file`, so the same tests still run in the
interp lane): tests exercising designed-out capability -- the debugger /
frame-introspection / interrupt classes -- plus an annotated artifact class
(GC-introspection tests sensitive to the tier's literal-string and
allocation profile; each carries a comment). The SpiderMonkey tree carries
no test annotations for NightMonkey. NightMonkey's own regression tests
(`tests/jit-test/`) run in the compiled and interp lanes with
`scripts/run-night-tests.sh`.

## Build-system notes

- The shells link no NightMonkey Rust code: the compiler is a host tool
  (`nightmonkey`, `wasm-jit-runner`), and the in-process driver in
  `js-inproc` is a C++ stub around the `night_compile` hostcall.
- Layout facts the compiler bakes into generated code are pinned by
  `static_assert`s in `runtime/NightInlineHeap.cpp` against the engine
  headers, and the snapshot reader checks the registration block's ABI
  version and layout descriptor at runtime, so a SpiderMonkey upgrade that
  moves a field fails to build or refuses to compile rather than
  miscompiling. The opcode table is checked in per engine version and
  verified against the engine's `Opcodes.h` by every build (see "Engine
  versions").

For performance work, the benchmark-lane configs
(`mozconfig-native`/`-ion`/`-wasm`/`-weval`) live in `configs/`.

## Documentation

- **[`docs/DESIGN.md`](docs/DESIGN.md)**: the design of record: the
  soundness model and the object stamp, the MIR and baseline tiers, the
  analysis (data structures,
  lattices, abstract interpretation), the runtime ABI, and the known
  limitations and rough edges.
- **[`docs/MIR.md`](docs/MIR.md)** and **[`docs/BASELINE.md`](docs/BASELINE.md)**:
  the two compiled tiers: MIR's IR, types, exits and onramps, and the
  baseline tier MIR exits to.
- **[`docs/INTEGRATION.md`](docs/INTEGRATION.md)**: the SpiderMonkey side:
  the `--enable-external-compiler-hooks` surface NightMonkey plugs into,
  organized by mechanism, and how to port it to another SpiderMonkey.
- **[`docs/TODO`](docs/TODO)**.

## Performance

As of 2026-09-04, comparing to native IonMonkey and baseline tiers, and
against Wasm-hosted interpreter and weval+PBL execution:

```plain
bench            native-ion nat-baseline  wasm-interp        weval          aot   aot/wasm-int      aot/weval weval/wasm-int      ion/weval        ion/aot   baseline/aot
richards              29205         6489          377          936        11893          31.55          12.71           2.48          31.20           2.46           0.55
deltablue             28179         6870          395          978         6678          16.91           6.83           2.48          28.81           4.22           1.03
crypto                42755         5654          714          949        15696          21.98          16.54           1.33          45.05           2.72           0.36
raytrace              58549        11458         1045         1815        11964          11.45           6.59           1.74          32.26           4.89           0.96
earley-boyer          83262        21153         1510         3982        15088           9.99           3.79           2.64          20.91           5.52           1.40
navier-stokes         43926         8269         1223         2090        24980          20.43          11.95           1.71          21.02           1.76           0.33
splay                 29291        23303         5248         6853        10693           2.04           1.56           1.31           4.27           2.74           2.18
regexp                18601         7223          596          766         2484           4.17           3.24           1.29          24.28           7.49           2.91
pdfjs                 95804        40738         4116         6185        24743           6.01           4.00           1.50          15.49           3.87           1.65
mandreel              73940        11619          865         1269        19545          22.60          15.40           1.47          58.27           3.78           0.59
code-load             70224        69259        37108        37005        37271           1.00           1.01           1.00           1.90           1.88           1.86
box2d                 99321        22370         1896         4135        25999          13.71           6.29           2.18          24.02           3.82           0.86
react-bench           0.631        1.415       15.026       10.421        2.862           5.25           3.64           1.44          16.52           4.54           2.02
geomean               49233        14111         1527         2569        14247           8.93           5.37           1.66          18.94           3.53           1.05
(octane = Score higher-better; react-bench = ms/render lower-better; best-of-3, taskset -c 1)
(ratio cols = speedup of A over B, direction-corrected for react-bench;
 geomean row: lane cols over octane scores only, ratio cols over all benches)
```

We can conclude that NightMonkey is ~9x faster than the Wasm interpreter on
average, or ~5x faster than weval+PBL. It is nearly on par with the native
baseline compiler, and within ~3.5x of the IonMonkey optimized native-code
ceiling (while running within a Wasm engine). On benchmarks where type-based
specialization works especially well, NightMonkey comes within ~2.5x (e.g.
Richards) of native Ion.
