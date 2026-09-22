/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#ifndef night_runtime_NightInprocHost_h
#define night_runtime_NightInprocHost_h

#include <stdint.h>

namespace js {
namespace night {

// Wrappers over the wasm-jit-runner hostcall imports (env.wasm_table_size,
// env.wasm_add_funcs2). The imports make the module instantiable only under
// hosts that provide them (the runner; wizer stubs unknown imports; plain
// `wasmtime run` needs `-W unknown-imports-trap`), so callers must gate on
// --night-inprocess. On non-wasm targets the wrappers fail unconditionally.

// Current size of funcref table 0, or a negative value on failure. Appended
// functions are contiguous: blob i lands at the returned size + i.
int32_t InprocHostTableSize();

// Inject `nblobs` function blobs (runner blob format) resolving the extern
// function imports from live table entries `externIdxs[0..nextern)`; writes
// each blob's new table index to `out`. Returns 0 on success.
int32_t InprocHostAddFuncs(const uint32_t* blobPtrs, const uint32_t* blobLens,
                           uint32_t nblobs, const uint32_t* externIdxs,
                           uint32_t nextern, uint32_t* out);

}  // namespace night
}  // namespace js

#endif  // night_runtime_NightInprocHost_h
