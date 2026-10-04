/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80: */

// The tier's per-context state: what the ExternalCompilerHooks newContext
// hook makes for each JSContext (and destroyContext frees), reached through
// JSContext::getExternalCompilerState. Everything a context's compiled code
// and runtime helpers keep between calls belongs here, not in a global.

#ifndef night_runtime_NightContext_h
#define night_runtime_NightContext_h

#include "mozilla/Assertions.h"

#include <stdint.h>

#include "runtime/NightStack.h"
#include "vm/JSContext.h"  // JSContext::getExternalCompilerState

class JSLinearString;

namespace js {
class RegExpShared;

namespace night {
// runtime/NightRuntime.cpp's state: its caches, tables and flags.
struct NightRuntimeState;
NightRuntimeState* NewNightRuntimeState();
void DeleteNightRuntimeState(NightRuntimeState* state);
}  // namespace night

namespace nightrt {

// A successful exec() the compiled call's leaf decided (NightRegExpLeaf):
// its match pairs, so the generic path that builds the result object need
// not run the matcher again. Valid for the same shared and input, from
// position 0, while no GC has run (the pointers identify the objects only
// until one may move or free them).
struct NightLeafMatch {
  static constexpr uint32_t kMaxPairs = 16;
  RegExpShared* shared = nullptr;
  JSLinearString* input = nullptr;
  uint64_t gcNumber = 0;
  uint32_t pairCount = 0;  // 0: nothing cached
  int32_t pairs[2 * kMaxPairs] = {};
};

struct NightContextState {
  // The property-IC region's base (NightEnvDesc::propicPtr), at offset 0:
  // compiled code loads it from the state it reaches through its context
  // (JSContext::offsetOfExternalCompilerState) and addresses each site's
  // ways relative to it.
  uint32_t propIcBase = 0;
  NightStack stack;
  NightLeafMatch leafMatch;
  js::night::NightRuntimeState* runtime = nullptr;
};

// Null when the context has no state (the hooks are not installed, or the
// state could not be allocated): no compiled code runs on such a context.
inline NightContextState* NightStateOf(JSContext* cx) {
  return static_cast<NightContextState*>(cx->getExternalCompilerState());
}

// The context's value stack. Only for a context that runs compiled code
// (whose state exists: every entry checks NightStateOf first).
inline NightStack& TheNightStackInline(JSContext* cx) {
  NightContextState* state = NightStateOf(cx);
  MOZ_ASSERT(state);
  return state->stack;
}

}  // namespace nightrt
}  // namespace js

#endif  // night_runtime_NightContext_h
