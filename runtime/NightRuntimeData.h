/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#ifndef night_runtime_NightRuntimeData_h
#define night_runtime_NightRuntimeData_h

#include <stdint.h>  // uint32_t

namespace js {
namespace night {

// AOT-compiled regex matchers (Wasm functions compiled alongside the
// scripts). Published by night_runtime_install_env; consulted by
// irregexp::TryNightRegexMatch before the engine's own matcher runs. The
// matcher is called through a C function pointer whose value is a Wasm table
// index.
struct NightRegexEntry {
  const char16_t* pattern;
  uint32_t patternLen;
  uint32_t flags;
  // Wasm indirect-table indices of the per-encoding matchers; 0 = none.
  uint32_t latin1Idx;
  uint32_t twobyteIdx;
  uint32_t numRegisters;
  uint32_t pairCount;
};

// Status word an AOT-compiled regex matcher returns. These mirror
// v8::internal::RegExp::kInternalRegExpSuccess / kInternalRegExpFailure
// (irregexp/imported/regexp.h), which the matcher path deliberately does not
// include; static_asserts in irregexp/RegExpAPI.cpp pin them together.
inline constexpr int32_t kRegexMatcherSuccess = 1;
inline constexpr int32_t kRegexMatcherFailure = 0;

// Per-runtime AOT state.
struct NightRuntimeData {
  // AOT-compiled regex matcher table and shared backtrack scratch, published
  // once by night_runtime_install_env and consulted by
  // irregexp::TryNightRegexMatch. The table and scratch are heap-allocated once
  // and intentionally live for the runtime's lifetime (never freed).
  NightRegexEntry* regexTable = nullptr;
  uint32_t regexTableCount = 0;
  int32_t* regexBtStack = nullptr;
  uint32_t regexBtStackElems = 0;

  // Diagnostics: matches decided by an AOT matcher / fell back to the
  // bytecode interpreter (no matcher, or the matcher returned RETRY).
  uint64_t regexNightMatches = 0;
  uint64_t regexNightFallbacks = 0;
};

// The process-wide instance (one runtime per wasm instance).
NightRuntimeData& NightData();

}  // namespace night
}  // namespace js

#endif /* night_runtime_NightRuntimeData_h */
