/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80: */

// NightMonkey's implementation of the engine's external compiler hook table
// (js/public/ExternalCompilerHooks.h): the object-model invalidation
// points, global-object writes, script entry, GC roots, the dynamic-code
// fuse and the regexp matcher divert.

#ifndef night_runtime_NightHooks_h
#define night_runtime_NightHooks_h

#include "js/ExternalCompilerHooks.h"

namespace js {
namespace night {

// The registered table. Mutable so the runtime can adjust policy fields
// (the wizening constructor slot floor).
extern JS::ExternalCompilerHooks gNightHooks;

// Register the table on the runtime. Call once the context exists, before
// any script runs.
void NightInstallHooks(JSRuntime* rt);

}  // namespace night
}  // namespace js

#endif  // night_runtime_NightHooks_h
