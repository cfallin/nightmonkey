/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

/*
 * Engine-half implementations of the bytecode operations a compiled body
 * cannot do itself. NightRuntime.cpp's `night_runtime_*` shims are the Wasm
 * ABI in front of these; every `uint64_t` here is a boxed `JS::Value`'s raw
 * bits and every `void*` a linear-memory pointer the shim already widened.
 */

#ifndef night_runtime_NightOps_h
#define night_runtime_NightOps_h

#ifdef ENABLE_JS_NIGHTMONKEY

#  include <stddef.h>
#  include <stdint.h>

#  include "js/Id.h"
#  include "js/RootingAPI.h"
#  include "js/TypeDecls.h"
#  include "js/Value.h"

namespace js {
namespace night {

// --- Names and global bindings ------------------------------------------

// `GetGName`: resolve against the global lexical environment chain exactly as
// the interpreter's CASE(GetGName) does. Takes a pre-interned name.
bool NightGetGName(JSContext* cx, JS::Handle<JS::PropertyKey> id,
                   bool forTypeof, JS::MutableHandleValue out);
bool NightBindUnqualifiedGName(JSContext* cx, JS::Handle<JS::PropertyKey> id,
                               JS::MutableHandleValue out);
bool NightSetName(JSContext* cx, JS::Handle<JS::PropertyKey> id,
                  uint64_t envBits, uint64_t valBits, bool strict);

// `lookupPure` `id` on the global object and return the encoded gGlobalSlots
// entry (bit0 resolved, bit1 is-dynamic-slot, bit2 writable, bits[31:3] slot
// index); a leaf. `NightSetGlobalSlot` stores through NativeObject::setSlot,
// barriers included.
uint32_t NightResolveGlobalSlot(JSContext* cx, JS::PropertyKey id);
void NightSetGlobalSlot(JSContext* cx, JS::PropertyKey id, uint64_t valBits);

// Guarded variant for an arbitrary `GetGName` operand, where resolution may
// fail: the encoded entry ONLY for an own plain data slot of the global not
// shadowed by a global lexical, with the global's shape word (the inline
// read's guard) to *shapeOut; else 0 ("not cacheable").
uint32_t NightResolveGlobalSlotGuarded(JSContext* cx, JS::PropertyKey id,
                                       uint32_t* shapeOut);

// Global binding `id`'s current (tenured-only) value bits, for the
// per-binding fuse cell.
bool NightTryBindingValue(JSContext* cx, JS::PropertyKey id, uint64_t* valOut,
                          bool* nurseryOut = nullptr);

// Guard-word addresses the compiled module's fused arms test: the realm's
// OptimizeStringCharOpsFuse, and the runtime's
// HasSeenObjectEmulateUndefinedFuse.
size_t* NightStringCharOpsFuseWord(JSContext* cx);
size_t* NightEmulatesUndefinedFuseWord(JSContext* cx);

// --- Unary and relational slow paths ------------------------------------

bool NightNeg(JSContext* cx, uint64_t aBits, uint64_t* out);
bool NightInc(JSContext* cx, uint64_t aBits, uint64_t* out);
bool NightDec(JSContext* cx, uint64_t aBits, uint64_t* out);
bool NightInstanceof(JSContext* cx, uint64_t lBits, uint64_t rBits,
                     uint64_t* out);
bool NightDelProp(JSContext* cx, uint64_t valBits, JS::PropertyKey id,
                  bool strict, uint64_t* out);
// `typeof a` -> boxed type string. Leaf: no GC, no throw.
uint64_t NightTypeof(JSContext* cx, uint64_t valBits);

// --- Environments, closures and arguments objects -----------------------

bool NightEnvSetup(JSContext* cx, void* spPtr, void* scriptPtr, uint64_t* out);
bool NightGlobalDeclInstantiation(JSContext* cx, void* scriptPtr,
                                  uint32_t gcthingIndex);
uint64_t NightObject(JSContext* cx, void* scriptPtr, uint32_t gcthingIndex);
uint64_t NightGetAliased(JSContext* cx, uint64_t envBits, uint32_t hops,
                         uint32_t slot);
void NightSetAliased(JSContext* cx, uint64_t envBits, uint32_t hops,
                     uint32_t slot, uint64_t valBits);
bool NightLambda(JSContext* cx, uint64_t envBits, void* scriptPtr,
                 uint32_t funcIndex, uint64_t* out);

// The (unmapped, strict) arguments object from `argc` actuals at `args`
// (marked locations). The Env variant takes the activation's environment
// head instead of the callee's, so a mapped args object forwards its
// closed-over formals to the CallObject slots.
bool NightArguments(JSContext* cx, uint64_t calleeBits, const JS::Value* args,
                    uint32_t argc, uint64_t* out);
bool NightArgumentsEnv(JSContext* cx, uint64_t calleeBits,
                       const JS::Value* args, uint32_t argc, uint64_t envBits,
                       uint64_t* out);

// --- Calls, construct and exceptions ------------------------------------

// Classify a runtime call target: packed `(JSScript* << 32) | nightFuncIndex`
// when it is an interpreted JSFunction with a compiled AOT body (low half
// non-zero), else 0. Leaf.
uint64_t NightCalleeNightTarget(uint64_t calleeBits);

// Build the `new` from the compiled-body frame at `spPtr`. A sized construct
// site (`nSlots != UINT32_MAX`) creates an empty fixed-slot-sized `this` and
// constructs on it (no CreateThis hook); else an ordinary `js::Construct`.
bool NightConstruct(JSContext* cx, void* spPtr, uint32_t argc, uint32_t nSlots,
                    uint32_t stampWord, uint64_t* out);
// Create `this` for a specialized `new`: an empty object sized for the
// predicted layout, else an ordinary `CreateThis`.
bool NightCreateThis(JSContext* cx, uint64_t calleeBits, uint64_t newTargetBits,
                     uint32_t nSlots, uint64_t* out, uint32_t stampWord);

bool NightException(JSContext* cx, uint64_t* out);
void NightThrow(JSContext* cx, uint64_t valBits);
void NightThrowWithStack(JSContext* cx, uint64_t valBits, uint64_t stackBits);
bool NightGetExceptionForFinally(JSContext* cx, uint64_t* excOut,
                                 uint64_t* stackOut);

}  // namespace night
}  // namespace js

#endif  // ENABLE_JS_NIGHTMONKEY

#endif  // night_runtime_NightOps_h
