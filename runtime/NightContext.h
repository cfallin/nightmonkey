/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80: */

// The tier's per-context state: what the ExternalCompilerHooks newContext
// hook makes for each JSContext (and destroyContext frees), reached through
// JSContext::getExternalCompilerState. Everything a context's compiled code
// and runtime helpers keep between calls belongs here, not in a global.

#ifndef night_runtime_NightContext_h
#define night_runtime_NightContext_h

#include "mozilla/Assertions.h"

#include "runtime/NightStack.h"
#include "vm/JSContext.h"  // JSContext::getExternalCompilerState

namespace js {
namespace nightrt {

struct NightContextState {
  NightStack stack;
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
