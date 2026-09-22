/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// The wasm-jit-runner hostcall imports, isolated in their own TU. The runner
// also provides a third hostcall, env.wasm_add_funcs (no extern-function
// resolution); the driver does not use it.

#include "runtime/NightInprocHost.h"

#ifdef __wasm__

extern "C" {
__attribute__((import_module("env"), import_name("wasm_table_size"))) int32_t
wasm_table_size();
__attribute__((import_module("env"), import_name("wasm_add_funcs2"))) int32_t
wasm_add_funcs2(uint32_t bytecodeArr, uint32_t lensArr, int32_t nfuncs,
                uint32_t externArr, int32_t nextern, uint32_t outPtr);
}

int32_t js::night::InprocHostTableSize() { return wasm_table_size(); }

int32_t js::night::InprocHostAddFuncs(const uint32_t* blobPtrs,
                                      const uint32_t* blobLens, uint32_t nblobs,
                                      const uint32_t* externIdxs,
                                      uint32_t nextern, uint32_t* out) {
  return wasm_add_funcs2(
      static_cast<uint32_t>(reinterpret_cast<uintptr_t>(blobPtrs)),
      static_cast<uint32_t>(reinterpret_cast<uintptr_t>(blobLens)),
      static_cast<int32_t>(nblobs),
      static_cast<uint32_t>(reinterpret_cast<uintptr_t>(externIdxs)),
      static_cast<int32_t>(nextern),
      static_cast<uint32_t>(reinterpret_cast<uintptr_t>(out)));
}

#else

int32_t js::night::InprocHostTableSize() { return -1; }

int32_t js::night::InprocHostAddFuncs(const uint32_t*, const uint32_t*,
                                      uint32_t, const uint32_t*, uint32_t,
                                      uint32_t*) {
  return -1;
}

#endif  // __wasm__
