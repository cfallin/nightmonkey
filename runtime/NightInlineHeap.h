/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

/*
 * The engine half of the compiled body's inline heap access: the
 * nursery bump-allocation cells the literal and construct sites replay, and
 * the GC write barriers the inlined slot and element stores call.
 */

#ifndef night_runtime_NightInlineHeap_h
#define night_runtime_NightInlineHeap_h

#ifdef ENABLE_JS_NIGHTMONKEY

#  include <stdint.h>

#  include "js/TypeDecls.h"

namespace js {
namespace night {

/*
 * Inline-allocation cells.
 *
 * A literal or construct site that allocates gets one reserved row in the
 * module's linear memory. The row starts zeroed; the first allocation at the
 * site goes through the generic helper, which copies the resulting object's
 * header words into the row. From then on the compiled body allocates
 * inline: bump the nursery by `totalSize` and stamp these words into the
 * fresh cell, reproducing exactly what the generic path produced.
 *
 * The compiler's half of this layout is `ALLOC_CELL_BYTES` /
 * `CONSTRUCT_CELL_BYTES` in compiler/src/wasm/translate.rs; the emitted
 * stores are in compiler/src/wasm/bbv/object.rs. The static_asserts in
 * NightInlineHeap.cpp pin the field offsets those constants encode, so
 * changing a field here without changing translate.rs is a build error
 * rather than a silent miscompile.
 *
 * `shape == 0` means the row is empty -- not yet filled, or zeroed by a
 * major GC (which may move the cached shape).
 */
struct NightAllocCell {
  uint32_t shape;
  uint32_t totalSize;  // bytes to bump, nursery cell header included
  uint32_t slotsWord;
  // The object's `elements_` word. An array-literal row stores the elements'
  // BYTE OFFSET from the object here instead, because the replayed elements
  // are in-cell and their address therefore depends on the fresh allocation.
  uint32_t elementsWord;
  uint32_t headerWord;  // the nursery cell header ahead of the object
};

// An array-literal row: an alloc cell plus the dense-elements header the
// replay stamps ahead of element 0.
struct NightArrayAllocCell {
  NightAllocCell alloc;
  uint32_t elemFlags;
  uint32_t capacity;
  uint32_t length;
};

// A construct site's row: an alloc cell for the fresh `this`, plus the guard
// words the inline path checks before replaying it -- the constructor's own
// shape and the property-IC generation, then a LIVE re-read of the
// constructor's `.prototype` (a reassignment is a slot write, so the ctor
// shape alone would not catch it).
struct NightConstructCell {
  NightAllocCell alloc;
  uint32_t ctorShape;
  uint32_t gen;
  uint32_t protoPtr;
  uint32_t protoSlotEnc;
};

// The addresses of the nursery bump words (the pair the JIT's
// bumpPointerAllocate uses). False when nursery object allocation is off --
// the caller then leaves the linmem slots zero and no cell ever fills.
bool NightNurseryAddresses(JSContext* cx, uint32_t* posAddr, uint32_t* endAddr);

// Fill a site's row from the first object the generic helper allocated
// there. Both return whether they filled it: only an object the inline path
// can reproduce exactly qualifies (see the definitions for the conditions).
// The object form also fills the leading `alloc` of a construct row.
bool NightFillAllocCellObject(NightAllocCell* cell, JSObject* obj);
bool NightFillAllocCellArray(NightArrayAllocCell* cell, JSObject* obj,
                             uint32_t length);

// The generational (post-write) barrier behind an inlined store. The
// compiled code already performed the store and checked inline that the
// value is a GC thing in the nursery, so this only records the store-buffer
// edge -- the slot form for a fixed-slot store, the elem form for a dense
// `SetElem` (a different edge). LEAF: a store-buffer append allocates no JS,
// moves nothing and runs no user code, so the caller needs no rooting
// handshake.
void NightPostWriteBarrier(uint64_t ownerBits, uint32_t slot, uint64_t valBits);
void NightPostWriteBarrierElem(uint64_t ownerBits, uint32_t index,
                               uint64_t valBits);

// The pre-write (incremental-marking) barrier slow path: mark the old value
// being overwritten. The compiled code inlines the gate, calling this only
// while the zone's `needsIncrementalBarrier` flag is set.
void NightPreWriteBarrier(uint64_t valBits);

}  // namespace night
}  // namespace js

#endif  // ENABLE_JS_NIGHTMONKEY

#endif  // night_runtime_NightInlineHeap_h
