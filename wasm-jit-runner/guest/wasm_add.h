/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */
/*
 * wasm_add.h — core API for the `wasm-jit-runner` runtime-function-adding host
 * import. This is the minimal, dependency-free header to copy into a project
 * that wants to use the API; for convenience helpers that *build* the function
 * blobs, see the separate `wasm_build.h`.
 *
 * The runner exposes one import that lets a running wasm guest assemble
 * brand-new wasm functions at runtime and obtain "funcptrs" (entries in table
 * 0, the indirect-function-table) that can be called like any other function
 * pointer.
 *
 *   wa_err wasm_add_funcs(uint8_t** bytecode, size_t* lens, int nfuncs,
 *                         wa_funcptr* out);
 *
 *   - bytecode[i] / lens[i] describe `nfuncs` "function blobs" (format below).
 *   - On success the call writes `nfuncs` funcptrs into `out` and returns 0.
 *     On failure it returns non-zero (and the runner logs a diagnostic); the
 *     guest keeps running.
 *
 * Semantics: the supplied functions are assembled into a single fresh module
 * and instantiated into the same store, where:
 *   - there are no imported functions, so the new functions call each other
 *     directly by index — function 0 is the first blob you pass;
 *   - the host module's memories, tables and globals are imported at their
 *     existing indices, so new code can reference them directly;
 *   - the host module's functions are not visible. To call back into existing
 *     guest code, do an indirect call through table 0 (a C funcptr is exactly a
 *     table-0 index, so `&some_func` gives you the index).
 * Each new function is appended to table 0; its slot index is the returned
 * funcptr.
 *
 * Function blob format (per function):
 *
 *     0x60                       ; functype tag
 *     uleb(nparams) param-types  ; valtype bytes (0x7f=i32, 0x7e=i64, ...)
 *     uleb(nresults) result-types
 *     uleb(nlocalruns) localruns ; each: uleb(count) valtype
 *     <expr bytes...>            ; instructions, terminated by `end` (0x0b)
 */
#ifndef WASM_ADD_H
#define WASM_ADD_H

#include <stddef.h>
#include <stdint.h>

typedef int wa_err;     /* 0 == success */
typedef int wa_funcptr; /* index into table 0 */

extern wa_err wasm_add_funcs(uint8_t** bytecode, size_t* lens, int nfuncs,
                             wa_funcptr* out)
    __attribute__((import_module("env"), import_name("wasm_add_funcs")));

/*
 * Like wasm_add_funcs, but the assembled module additionally IMPORTS
 * `nextern` functions, resolved by the host from table-0 entries
 * `extern_funcs[0..nextern)` (a C funcptr is exactly such an index). The
 * imported functions occupy the new module's function indices 0..nextern, so
 * blob code can `call` them directly; blob i is function index nextern+i.
 * Each import's type is taken from the live table entry, so a signature
 * mismatch in blob code fails instantiation (loudly) rather than trapping
 * later.
 */
extern wa_err wasm_add_funcs2(uint8_t** bytecode, size_t* lens, int nfuncs,
                              const wa_funcptr* extern_funcs, int nextern,
                              wa_funcptr* out)
    __attribute__((import_module("env"), import_name("wasm_add_funcs2")));

/*
 * Current size of table 0. Added functions are appended contiguously at the
 * end of the table (an API guarantee), so after querying this a guest can
 * predict the funcptr of blob i in the next wasm_add_funcs* call as
 * `size + i` -- e.g. to bake callee indices into blob code before the call.
 * Returns -1 on failure.
 */
extern int wasm_table_size(void)
    __attribute__((import_module("env"), import_name("wasm_table_size")));

#endif /* WASM_ADD_H */
