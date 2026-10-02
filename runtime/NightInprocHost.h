/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80: */

#ifndef night_runtime_NightInprocHost_h
#define night_runtime_NightInprocHost_h

#include <stddef.h>
#include <stdint.h>

namespace js {
namespace night {

// The night_compile hostcall (wasm-jit-runner): the host compiles the
// registered tree, injects the bodies, and writes the env_desc and the
// script map into buffers from night_inproc_alloc. See
// wasm-jit-runner/src/compile.rs for the request and response words. Returns
// 0 on success; the host reports failures on stderr. The import makes the
// module instantiable only under hosts that provide it (the runner; wizer
// stubs unknown imports; plain `wasmtime run` needs
// `-W unknown-imports-trap`), so callers must gate on --night-inprocess. On
// non-wasm targets it fails unconditionally.
inline constexpr uint32_t kNightCompileRequestVersion = 1;
inline constexpr size_t kNightCompileRequestWords = 5;
inline constexpr size_t kNightCompileResponseWords = 6;
int32_t InprocHostCompile(const uint32_t* req, uint32_t reqLen, uint32_t* resp);

}  // namespace night
}  // namespace js

#endif  // night_runtime_NightInprocHost_h
