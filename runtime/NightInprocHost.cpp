/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80: */

// The wasm-jit-runner hostcall import, isolated in its own TU. The runner
// also provides env.wasm_table_size and env.wasm_add_funcs{,2} for guests
// that compile themselves; the driver does not use them.

#include "runtime/NightInprocHost.h"

#ifdef __wasm__

extern "C" {
__attribute__((import_module("env"), import_name("night_compile"))) int32_t
night_compile(uint32_t reqPtr, uint32_t reqLen, uint32_t respPtr);
}

int32_t js::night::InprocHostCompile(const uint32_t* req, uint32_t reqLen,
                                     uint32_t* resp) {
  return night_compile(
      static_cast<uint32_t>(reinterpret_cast<uintptr_t>(req)), reqLen,
      static_cast<uint32_t>(reinterpret_cast<uintptr_t>(resp)));
}

#else

int32_t js::night::InprocHostCompile(const uint32_t*, uint32_t, uint32_t*) {
  return -1;
}

#endif  // __wasm__
