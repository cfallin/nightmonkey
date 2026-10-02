# Kickoff: the in-process compiler moves to the host

Owner's direction (2026-10-01): take the NightMonkey compiler out of the
in-process guest and put it in `wasm-jit-runner`. The engine build keeps a
small stub that makes one hostcall ("compile this tree"). The host does
everything native `nightmonkey` does, up to arming the compiled scripts.

Two reasons:
- **Speed.** The compiler runs natively, with Rayon, instead of as
  interpreted-speed wasm inside the guest.
- **Size.** The guest gets smaller: `js-inproc` stops linking
  `libnight_guest.a`, which is the whole compiler plus the snapshot reader.

Do it together with the second request: parallelize the pipeline with Rayon
wherever it isn't yet.

## Where things stand

The in-process lane is `scripts/run-jit-tests.sh` and
`build/bin/inproc-shell.sh`. It runs `build/bin/js-inproc` under
`wasm-jit-runner`. One batch per process: `js::CompileInProcess`
(`runtime/NightInproc.cpp`) compiles the first registered tree.

1. Register the root script (`JS::NightRegisterRoot`). Resolve and
   delazify the self-hosted roots (`ResolveSelfHostedRoots`). Collect regex
   programs (`CollectRegexPrograms`). Seal the registration addresses
   (`NightSealSnapshotAddresses`), since the steps before can GC.
2. Walk the live heap in the guest: `night_snapshot_walk_live`
   (`snapshot/src/ffi.rs`) builds a `Source`. Then the guest annotates it:
   `night_source_mark_selfhosted`, `night_source_add_regex_program`.
3. Compile in the guest: `night_inproc_build` (`compiler/src/lib.rs:98`)
   calls `build_inprocess_batch` (`compiler/src/wasm/inprocess.rs:214`).
   - Inputs: the helper table (names, signature strings, funcref-table
     indices from `kNightHelpers`), `tableBase` (from the
     `wasm_table_size` hostcall), an allocator callback (`InprocAlloc`:
     calloc, 8-aligned, never freed) and the option string.
   - The allocator is called twice: once for the fixed region (sized by a
     base-0 `layout_env`), once for the post-translation prop-IC/cell
     region and string-literal blob.
   - It translates with `translate_all`, then carves the module's defined
     functions into runner blobs (`carve_blobs`).
4. Inject: `InprocHostAddFuncs` calls the `wasm_add_funcs2` hostcall
   (`wasm-jit-runner/src/addfuncs.rs`). The guest checks that each blob
   landed at `tableBase + i`.
5. Install the environment from the env_desc. That means checking the ABI
   version and region count, copying the string-literal payload, and
   reading the region words (`NightEnvDesc`). Then arm each compiled
   script's `nightFuncIndex`.

What already helps:
- **The walker is memory-generic.** It is written against `MemAccess`
  (`snapshot/src/mem.rs`). `SliceMem` reads "a snapshot image or a
  wasmtime memory view", so the host can walk the guest's linear memory
  directly. The native flow does the same over a wizer image
  (`nightmonkey/src/main.rs`, `image.rs`).
- **The runner is in the workspace.** `wasm-jit-runner` already sits in the
  Cargo workspace next to `compiler` and `snapshot`, so it can depend on
  them.

## Target design

**Guest stub** (`runtime/NightInproc.cpp`, slimmed):
- Steps 1 and 5 stay in the guest. They need the engine: GC, rooting,
  delazification, regex compilation, installing the environment, arming
  scripts.
- Step 2's annotations become plain data the stub hands over: the
  self-hosted roots and their paths, and the regex programs.
- Steps 2–4 become one hostcall.

**Hostcall** (new, in `wasm-jit-runner/src/`, next to `addfuncs.rs`):
`night_compile(req_ptr, req_len, resp_ptr_out) -> i32`.
- `req` is a small serialized request in guest memory:
  - the registration block's address;
  - the self-hosted root addresses and paths;
  - the regex programs (or their addresses);
  - the helper table (name, signature, funcref index);
  - the option string.
  The helper table could also be read by the host from the registration
  digest; see "Decisions" below.
- The host then:
  - **walks** the live memory with `night_snapshot::walk` over a
    `SliceMem` of the instance's memory;
  - **applies** the annotations;
  - **compiles** with `build_inprocess_batch`;
  - **injects** the blobs with the existing `add_funcs` code, in-process,
    without a guest round trip;
  - **returns** the env_desc and the (source id → table index) script map
    to the guest. The guest installs the environment and arms the scripts.
- **Allocation.** The host needs guest-heap regions twice. Two ways:
  - (a) A reentrant call into an exported guest allocator. The stub
    exports `night_inproc_alloc(size) -> addr`; the host calls it through
    `Caller::get_export` from inside the hostcall. wasmtime allows
    reentrant calls. Watch for memory growth: re-fetch the memory view
    after every guest call, since the slice can move.
  - (b) Two hostcalls with the sizes in between. This splits
    `build_inprocess_batch` at its two `alloc` calls.
  Prefer (a): it keeps `build_inprocess_batch` whole.
- **Writes into guest memory.** The string-literal payload and anything
  else the guest copied before can be written by the host directly, or
  left to the guest, as long as there is exactly one owner per write.

**Build:**
- `js-inproc` drops `libnight_guest.a` (`CMakeLists.txt:191-250`, the
  `night_guest` target, and `--allow-multiple-definition`).
- The `guest/` crate goes away. Check first whether anything else links it.
- The engine-side `night_*` C declarations the stub no longer calls go
  away (`compiler/night-compiler.h`, `snapshot/night-snapshot.h`).
- The memory note [[jit-tests-use-js-inproc]] changes meaning. Today a
  compiler change needs `make -C build js-inproc`; afterwards it needs a
  rebuild of `wasm-jit-runner`. Update the notes, the README's lane
  section and `scripts/` comments.

**Rayon** (the second request):
- **waffle's backend:** already parallel. `nightmonkey` enables waffle's
  `parallel` feature. The runner must enable it too.
- **`translate_all`:** serial. On pdfjs (natively) MIR `optimize` takes
  5.8 s, lowering 1.4 s, verify 0.8 s, build 0.4 s. `optimize` is pure per
  function (`&Module`, `&mut Func`), so build, optimize and verify can run
  in parallel ahead of the serial lower-and-insert loop.
- **The catch:** each script's translation mutates the waffle `Module` and
  the `AtomTable` (interning, cell numbering). MIR `build` also reads the
  growing name table: gname fusion does `names.lookup(..)`
  (`compiler/src/wasm/mir/build.rs:674`), and a lookup can succeed only
  because an earlier script's codegen interned the name. So building ahead
  against a snapshot of the names could change output.
  - Settle that first: show the lookups are order-independent, or give
    `build` the analysis-time names explicitly.
  - Then check that the parallel and serial builds emit byte-identical
    code sections. The data section varies between runs anyway; see
    `docs/TODO`.
- **`layout_env`** (the whole-program type analysis, 2.6 s on pdfjs) is
  global. Leave it.
- **Thread safety:** `TranslateCtx` holds only shared references, but
  check that everything it reaches is `Sync`.

**waffle `validate`:** the owner's call (2026-10-01).
- waffle 0.3.2 runs `FunctionBody::validate` at the top of every
  `WasmFuncBackend::compile`. Its dominance check walks the idom chain, so
  validation is quadratic: 34.6 s of pdfjs's 46.4 s compile.
- The owner is upstreaming an O(1) dominance check and wants `validate`
  off the production path. The local fix (branch
  `cfallin/fast-dominates` in `~/work/waffle`) took pdfjs's backend phase
  from 34.6 s to 0.8 s with byte-identical code.
- Keep the check where testing needs it. Invalid SSA (a use its definition
  doesn't dominate) does not always fail later: wasm locals are
  zero-initialized, so the module validates and the use reads 0. So call
  `body.validate()` from NightMonkey in the lanes, both for MIR (already
  under `--strict-coverage`/`--mir-stress`) and for baseline bodies.
- NightMonkey stays on crates.io waffle 0.3.2 until a release has the fix.

## Steps

1. **Measure the lane as it is.** Per-test compile time in
   `inproc-shell.sh`, total lane time, and the largest compiles, such as
   `basic/testComparisons.js` at 13.6 s in-process versus 6 s natively.
2. **Hostcall and stub, behind a flag.** Keep the guest path working until
   the host path passes both lanes. The runner registers `night_compile`;
   the stub picks the path.
3. **Walk from the host.** Run the snapshot reader over the instance's
   memory. Compare the host-built `Source` with the guest-built one on a
   few tests: same scripts, same ids.
4. **Compile and inject from the host.** Allocate through the exported
   guest allocator. Both lanes must pass, with the same tier census
   (`--dump-tiers`) as the guest path.
5. **Remove the guest compiler.** Drop the `js-inproc` link, the `guest/`
   crate and the dead C declarations. Record the shell's size before and
   after.
6. **Rayon in `translate_all`.** Do this after the determinism question
   above is settled. Check byte-identical code sections. Measure native
   (pdfjs, react) and lane compile times.
7. **Update the docs.** The README's lane and build sections,
   `docs/INTEGRATION.md` if the engine interface changes, and the memory
   notes.

## Done when

- Both jit-test lanes pass:
  - MIR: 12,895 passed, 0 failed at cafe06d;
  - legacy: 12,907 passed, 0 failed.
- `tests/jit-test/night` passes in both pipelines.
- `js-inproc` contains no compiler code.
- Lane wall time is measured before and after.
- The nm-bench checks are unchanged: `declines.sh` prints `total 0`, and
  benchmark compile output keeps byte-identical code sections.

## Decisions to make early

- **The helper table:** sent in the request, or read by the host from the
  registration digest? The digest is already versioned (ABI check).
- **Who copies the string-literal payload** and writes the env words: host
  or guest. Keep one owner.
- **Error reporting.** Today failures degrade to the interpreter
  (`InprocFail`, fatal under `NIGHTMONKEY_DEBUG`). Keep that: the hostcall
  returns a status, and the host's message goes to stderr.
