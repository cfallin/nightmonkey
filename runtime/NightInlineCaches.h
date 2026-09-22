/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

/*
 * The engine half of the compiled body's property caches. The hit paths are
 * emitted inline in wasm; these run on the miss side, doing the NativeObject
 * and Shape work needed to fill a linear-memory cache row the inline path can
 * read directly, plus the add-transition replay a cached property ADD uses.
 * A populate that returns false leaves the row untouched, so the site simply
 * keeps calling its miss helper.
 */

#ifndef night_runtime_NightInlineCaches_h
#define night_runtime_NightInlineCaches_h

#ifdef ENABLE_JS_NIGHTMONKEY

#  include <stdint.h>

#  include "js/Id.h"
#  include "js/TypeDecls.h"

namespace js {
namespace night {

// The slot coordinate every cache row hands compiled code: the slot's BYTE
// OFFSET from its base, with bit 0 set when the base is the object's
// out-of-line `slots_` vector rather than the object itself. Offsets are
// multiples of 8, so the bit is free and the decode is two masks, a select
// and an add (`Bbv::emit_slot_addr`).
static inline uint32_t NightSlotEnc(bool isDynamic, uint32_t idx) {
  return isDynamic ? (idx * 8u) | 1u : 16u + idx * 8u;
}
static inline bool NightSlotEncIsDynamic(uint32_t enc) { return enc & 1u; }
static inline uint32_t NightSlotEncIndex(uint32_t enc) {
  return NightSlotEncIsDynamic(enc) ? (enc & ~1u) / 8u : (enc - 16u) / 8u;
}

// Shape leaves: the object's shape word, and the slot span of its SHARED
// shape (UINT32_MAX when not a non-dictionary NativeObject), captured before
// a generic set so the populate side can prove exactly one data slot was
// appended.
uint32_t NightObjectShape(JSObject* obj);
uint32_t NightObjectSlotSpanIfShared(JSObject* obj);

// Add-transition cache. Populate runs after a generic set CHANGED the
// receiver's shape; the replays apply the cached (oldShape, id) -> newShape
// transition to another object of oldShape. `nurseryOut` asks the caller to
// zero the row at the next minor-GC end.
bool NightPopulateAddTransition(JSContext* cx, JSObject* obj, jsid id,
                                uint32_t oldSpan, uint32_t* newShapeOut,
                                uint32_t* slotOut, uint32_t protoPtrsOut[4],
                                uint32_t protoShapesOut[4],
                                uint32_t* numProtosOut, bool* nurseryOut);
bool NightTryAddPropTransition(JSContext* cx, uint64_t recvBits,
                               uint32_t oldShapeW, uint32_t newShapeW,
                               uint32_t slot, const uint32_t* protoPtrs,
                               const uint32_t* protoShapes, uint32_t numProtos,
                               uint64_t valBits);
// Define-flavor replay (an own definition: no proto guards).
bool NightTryInitAddTransition(JSContext* cx, uint64_t objBits,
                               uint32_t oldShapeW, uint32_t newShapeW,
                               uint32_t slot, uint64_t valBits);

// Inline GetProp-IC populate: a proto-holder coordinate the inline hit path
// can read directly (holder pointer + W1-encoded slot). False for accessors
// and nursery proto holders; an own field is cached receiver-relative
// (holderPtr == 0).
bool NightPopulateInlineGetIC(JSContext* cx, JSObject* obj, jsid id,
                              uint32_t* recvShapeOut, uint32_t* holderPtrOut,
                              uint32_t* holderShapeOut, uint32_t* slotEncOut);
// Guarded proto-chain populate (the invalidated-teleporting fallback):
// per-hop [ptr, shape] pairs from the first proto through the holder.
bool NightPopulateGuardedChain(JSContext* cx, JSObject* obj, jsid id,
                               uint32_t maxHops, uint32_t* nHopsOut,
                               uint32_t* protoPtrs, uint32_t* protoShapes,
                               uint32_t* slotEncOut);
// Accessor-call cache populate: resolve `id` on the proto chain to a scripted
// getter/setter and yield the guard words the compiled accessor arm checks.
bool NightPrimeAccessor(JSContext* cx, JSObject* obj, jsid id, bool wantSetter,
                        uint64_t* calleeOut, uint32_t* recvShapeOut,
                        uint32_t* holderPtrOut, uint32_t* holderShapeOut);
// Inline SetProp-IC populate: an own writable data slot the inline hit path
// can store to (encoded slot for the address, absolute slot for the barrier
// edge).
bool NightPopulateInlineSetIC(JSContext* cx, JSObject* obj, jsid id,
                              uint32_t* recvShapeOut, uint32_t* slotEncOut,
                              uint32_t* absSlotOut, uint32_t* reasonOut);

}  // namespace night
}  // namespace js

#endif  // ENABLE_JS_NIGHTMONKEY

#endif  // night_runtime_NightInlineCaches_h
