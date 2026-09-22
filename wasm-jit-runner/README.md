# wasm-jit-runner

A small WASI **preview 1** CLI runner built on the [`wasmtime`](https://crates.io/crates/wasmtime)
crate, with one extra capability: the running guest can **add new wasm functions
to itself at runtime** and call them — no round-trip back out to the runner.

This is meant for testing a wasm-targeting compiler *in situ*: emit a function,
hand its bytes to the runner, get back a callable funcptr, and invoke it
immediately, all from inside one guest process.

```
wasm-jit-runner <module.wasm> [guest args...]
```

It otherwise behaves as an ordinary wasip1 command runner (inherits stdio/env,
forwards argv, propagates the exit code).

## The `wasm_add_funcs` API

The runner injects one host import, `env.wasm_add_funcs`:

```c
err_t wasm_add_funcs(uint8_t** bytecode, size_t* lens, int nfuncs, funcptr_t* out);
```

* `bytecode[i]` / `lens[i]` describe `nfuncs` **function blobs** (see below).
* On success it writes `nfuncs` **funcptrs** (indices into table 0, the
  indirect-function-table) into `out` and returns `0`. On failure it returns
  non-zero and logs a diagnostic to stderr (the guest keeps running).

### Semantics

The supplied functions are assembled into a single fresh core-wasm module and
instantiated into the *same* store, where:

* there are **no imported functions**, so the new functions call each other
  directly by index — function `0` is the first blob you pass;
* the host module's **memories, tables, and globals are imported at their
  existing indices**, so new code can reference them directly;
* the host module's **functions are deliberately not visible**. To call back
  into existing guest code, do an **indirect call through table 0** (a C
  funcptr is exactly a table-0 index, so `&some_func` gives you the index).

Each new function is appended to table 0, and its slot index is returned as the
funcptr. The guest needs no special linker flags: the runner makes the funcptr
table growable when it loads the module (see below).

### Function blob format

Each blob is a wasm functype followed by a wasm code body:

```
0x60                       ; functype tag
uleb(nparams) param-types  ; valtype bytes (0x7f=i32, 0x7e=i64, ...)
uleb(nresults) result-types
uleb(nlocalruns) localruns ; each: uleb(count) valtype
<expr bytes...>            ; instructions, terminated by `end` (0x0b)
```

The core API is the small, dependency-free header
[`guest/wasm_add.h`](guest/wasm_add.h) (just the import declaration and types) —
copy it into any project that uses the API. Header-only helpers for *building*
the blobs live separately in [`guest/wasm_build.h`](guest/wasm_build.h).

## How it works

1. The guest module is stream-edited (`src/modedit.rs`) to (a) add synthetic
   exports for every memory, table, and global, so the runner can get live
   handles to them, and (b) strip the maximum off every table type so the
   funcptr table can grow (no `-Wl,--growable-table` needed on the guest).
2. On each `wasm_add_funcs` call (`src/addfuncs.rs`) the runner parses the
   blobs, reads the live items' types, assembles a new module that imports those
   items and defines the new functions, compiles and instantiates it, then grows
   table 0 and writes the new functions into it.

## Building and testing

```sh
cargo build                 # build the runner
sh guest/example/build.sh   # build the example guest (needs wasi-sdk)
sh test.sh                  # build everything and run the example
```

The example guest ([`guest/example/test_guest.c`](guest/example/test_guest.c))
builds three functions at runtime and checks:

* basic computation (`func0(x) = x + 100`);
* a direct call between added functions (`func1` calls `func0` by index);
* an added function that reads parameters, performs an **indirect call back into
  an existing guest function** via table 0, and **writes to linear memory**
  (`func2`).

Expected output:

```
added 3 functions, funcptrs = 6, 7, 8
func0(5)            = 105 (expect 105)
func1(5)            = 106 (expect 106)
func2(helper,7,&sink)= 98 (expect 98)
g_sink              = 49 (expect 49)
ALL TESTS PASSED
```

The example guest builds with no special linker flags. The wasi-sdk is expected
at `/opt/wasi-sdk` (override the compiler with
`WASI_CC=/path/to/wasm32-wasip1-clang`).


## NightMonkey extensions (wasm-jit-runner/)

This copy is extended from the standalone wasm-jit-runner project for the
SpiderMonkey AOT in-process test flow:

- `--dir HOST[::GUEST]` preopens (repeatable; default preopens `/`), so the
  guest shell can read test files by absolute path.
- `--cache-dir DIR`: content-addressed cwasm cache (sha256 of edited module
  bytes + engine compatibility hash); makes repeated runs of a large guest
  module start in tens of milliseconds.
- `env.wasm_table_size() -> u32`: current table-0 size. Added functions are
  appended contiguously (API guarantee), so a guest can predict the funcptr
  of blob i in the next add call as `size + i`.
- `env.wasm_add_funcs2(bytecode, lens, nfuncs, extern_funcs, nextern, out)`:
  like `wasm_add_funcs`, but the assembled module also imports `nextern`
  functions resolved by the host from the given table-0 indices; they occupy
  function indices `0..nextern` so blob code can `call` them directly, and
  each import's type is taken from the live table entry (a signature mismatch
  fails instantiation loudly).
