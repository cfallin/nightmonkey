# Code-size and instruction-fetch tooling

Tools for measuring generated-code size and instruction-fetch behaviour;
re-run them after any lowering change that moves code size.

The join that makes all of this work: our compiler *appends* its functions
after the snapshot's, so the cutoff index is `21 imports + the snapshot wasm's
defined-function count`, and every function above it is ours. `wasmtime
compile` writes an ELF whose symbol table names each function by wasm index,
and `--profile=perfmap` names the same indices at run time.

| tool | what it answers |
|---|---|
| `cwasm_syms.py` | per-wasm-function native `.text` size from a `.cwasm` |
| `wasmnames.py` | wasm function index -> name (needs `nightmonkey --keep-names`) |
| `sizecmp.py` | baseline vs candidate generated-code size, per bench |
| `ab.sh` | Octane A/B over two artifact sets, arm order alternated per rep |
| `disan.py` | static instruction mix + spill/reload traffic |
| `footprint.py` | how much generated code actually executes, and over what span |
| `roles.py` | **the gate**: every basic block classified by role, hot vs cold |
| `opsize.py` | per-JSOp code-size census (needs `nightmonkey --dump-opsize`; records carry `track` and `rung`) |
| `pstat.py` / `ptable.py` / `pcmp.py` | hardware-counter sweep (FE/BE-bound, L1i, op cache, iTLB) over an artifact dir, aot and ion lanes; table; A-vs-B per-work comparison |
| `hotmix.py` / `hotann.py` | sample-weighted instruction-class mix and annotated disassembly of one generated function (perf.data + perfmap + cwasm) |

`roles.py` is the one to re-run after each out-of-lining change. If a role's
share of cycles rises while its executed share stays flat, the change
lengthened the executed trace rather than compacting it -- which is the failure
mode the whole exercise is trying to avoid.

Typical loop:

```
nightmonkey bench.snap.wasm -o new.wasm && wasmtime compile new.wasm -o new.cwasm
python3 sizecmp.py richards box2d          # did it shrink?
N=3 ./ab.sh                                # did it cost anything?
python3 roles.py dis.txt perf.data map.txt new.cwasm named.wasm 18433
```
