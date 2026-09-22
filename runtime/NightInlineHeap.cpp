/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80: */

/*
 * The engine half of the compiled body's inline heap access: the nursery
 * bump-allocation cells the object/array/construct sites replay, and the GC
 * write barriers the inlined slot and element stores call.
 *
 * This file also pins every engine offset and flag constant the compiler
 * bakes into the emitted wasm -- see "The baked layout" below.
 */

#include "runtime/NightInlineHeap.h"

#include "gc/Nursery.h"
#include "gc/StoreBuffer.h"  // js::gc::StoreBuffer::putSlot (post-barrier)
#include "js/Realm.h"        // JS::Realm::offsetOfActiveGlobal
#include "runtime/NightRegionShape.h"  // Night_allocCellBytes, Night_constructCellBytes
#include "vm/ArrayObject.h"
#include "vm/JSContext.h"
#include "vm/JSFunction.h"  // js::FunctionFlags::BASESCRIPT
#include "vm/JSObject.h"
#include "vm/JSScript.h"  // BaseScript::offsetOfExternalTierWord
#include "vm/PlainObject.h"
#include "vm/Shape.h"
#include "vm/StringType.h"

#include "vm/NativeObject-inl.h"

#ifdef ENABLE_JS_NIGHTMONKEY

using namespace js;

namespace js {
namespace night {

// ==========================================================================
// The baked layout
// ==========================================================================
//
// The compiled module addresses SpiderMonkey's own data structures directly:
// a fixed-slot load is an `i32.load` at a constant offset, a shape guard
// compares the word at offset 0, the pre-write barrier walks
// `cx -> zone -> needsIncrementalBarrier`. Every one of those offsets and
// flag bits is a compile-time constant baked into the wasm, and its other
// half is a constant in the compiler:
//
//   js/src/night/compiler/src/wasm/bbv/abi.rs   the object/shape/string/
//                                               context offsets and flag bits
//   js/src/night/compiler/src/wasm/translate.rs FIXED_SLOTS_BASE and the
//                                               reserved-region row layouts
//
// The asserts below are the other side of that contract. If one fires, the
// ENGINE moved a field and the compiler is now emitting the right load of
// the wrong address:
//
//   1. read the new value out of the engine header the assert names;
//   2. update the matching constant in abi.rs (each assert's message is that
//      constant's name) or, for the alloc-cell rows, the layout comment and
//      byte size in translate.rs.
//
// These are static_asserts, not startup checks, on purpose: a layout drift
// is a build error, never a running binary that miscompiles. They are
// evaluated only in the reactor's wasm32 build, which is the only place the
// compiled module runs -- the native driver build has different offsets and
// compiles this file out entirely.

// --- JSObject / NativeObject header ---------------------------------------
static_assert(offsetof(JS::shadow::Object, shape) == 0, "SHAPE_OFFSET");
static_assert(offsetof(JS::shadow::Object, externalWord_) == 4,
              "OBJ_CLASS_IDX_OFFSET (the night stamp word)");
static_assert(JSObject::offsetOfExternalWord() == 4,
              "OBJ_CLASS_IDX_OFFSET (the night stamp word)");
static_assert(NativeObject::offsetOfSlots() == 8,
              "OBJ_SLOTS_OFFSET / NATIVE_SLOTS_OFFSET");
static_assert(NativeObject::offsetOfElements() == 12, "OBJ_ELEMENTS_OFFSET");
static_assert(NativeObject::getFixedSlotOffset(0) == 16, "FIXED_SLOTS_BASE");
static_assert(sizeof(NativeObject) == 16, "FIXED_SLOTS_BASE");
static_assert(sizeof(JS::Value) == 8, "SLOT_SIZE (the fixed-slot stride)");
static_assert(NativeObject::getFixedSlotOffset(1) -
                      NativeObject::getFixedSlotOffset(0) ==
                  sizeof(JS::Value),
              "SLOT_SIZE (the fixed-slot stride)");
static_assert(NativeObject::MAX_FIXED_SLOTS == 16, "MAX_FIXED_SLOTS");

// --- Shape ----------------------------------------------------------------
//
// The codegen decodes numFixedSlots() out of the shape header exactly as
// JS::shadow::Object does, and tests the native bit before trusting any
// slot or element offset above.
static_assert(Shape::offsetOfImmutableFlags() == 4,
              "SHAPE_IMMUTABLE_FLAGS_OFFSET");
static_assert(JS::shadow::Shape::FIXED_SLOTS_SHIFT == 6,
              "SHAPE_FIXED_SLOTS_SHIFT");
static_assert((JS::shadow::Shape::FIXED_SLOTS_MASK >>
               JS::shadow::Shape::FIXED_SLOTS_SHIFT) == 0x1f,
              "SHAPE_FIXED_SLOTS_MASK_BITS");
static_assert(Shape::isNativeBit() == (1u << 4), "SHAPE_IS_NATIVE_BIT");
static_assert(js::Shape::offsetOfBaseShape() == 0, "SHAPE_BASESHAPE_OFFSET");
static_assert(js::BaseShape::offsetOfClasp() == 0, "BASESHAPE_CLASP_OFFSET");

// --- Dense elements -------------------------------------------------------
//
// The inline element arms read the header words behind element 0: the
// initialized length (the bounds test), the capacity (the append arm), and
// the flags (a frozen array must not take the inline store).
static_assert(sizeof(ObjectElements) == 16, "ELEMENTS_HEADER_BYTES");
static_assert(ObjectElements::offsetOfFlags() == -16, "ELEMENTS_FLAGS_BACK");
static_assert(ObjectElements::offsetOfInitializedLength() == -12,
              "ELEMENTS_INITLEN_BACK");
static_assert(ObjectElements::offsetOfCapacity() == -8,
              "ELEMENTS_CAPACITY_BACK");
static_assert(ObjectElements::offsetOfLength() == -4, "ELEMENTS_LENGTH_BACK");
static_assert(ObjectElements::FROZEN == 0x40, "ELEMENTS_FROZEN_FLAG");

// --- Nursery and the write barriers ---------------------------------------
//
// A boxed Value is a GC thing iff its tag half is at or above
// ValueLowerInclGCThingTag; a cell is in the nursery iff its chunk's
// storeBuffer pointer (ChunkBase's first field) is non-null. The compiled
// store tests both inline and calls the barrier helpers below only on a hit.
static_assert(Nursery::nurseryCellHeaderSize() == 8, "NURSERY_HEADER_BYTES");
static_assert(uint32_t(JS::detail::ValueLowerInclGCThingTag) == 0xFFFFFF86u,
              "VAL_GCTHING_TAG_MIN");
static_assert(js::gc::ChunkStoreBufferOffset == 0, "CHUNK_STORE_BUFFER_OFFSET");
static_assert(js::gc::ChunkMask == 0xFFFFFu, "NOT_CHUNK_MASK");

// --- JSContext, Zone and Realm --------------------------------------------
//
// The pre-write barrier gate is `i32.load(cx + ZONE) -> i32.load(zone +
// NEEDS_BARRIER)`; an inline global read re-derives the global from cx each
// access as `*(*(cx + REALM) + GLOBAL)`.
static_assert(JSContext::offsetOfZone() == 84, "JSCONTEXT_ZONE_OFFSET");
static_assert(js::Zone::offsetOfNeedsIncrementalBarrier() == 8,
              "ZONE_NEEDS_BARRIER_OFFSET");
static_assert(JSContext::offsetOfRealm() == 88, "JSCONTEXT_REALM_OFFSET");
static_assert(JS::Realm::offsetOfActiveGlobal() == 72, "REALM_GLOBAL_OFFSET");

// --- Callee classify ------------------------------------------------------
//
// An interpreted JSFunction keeps its BaseScript* as a PrivateValue in fixed
// slot 2, and a compiled body's funcref index lives in the script. The
// specialized call path loads both inline instead of calling
// night_runtime_callee_night_target.
static_assert(uint16_t(js::FunctionFlags::BASESCRIPT) == (1u << 5),
              "FUNCTION_FLAGS_BASESCRIPT");
static_assert(NativeObject::getFixedSlotOffset(2) == 32,
              "NIGHT_FUNC_SCRIPT_SLOT_OFFSET");
static_assert(BaseScript::offsetOfExternalTierWord() == 56,
              "BASESCRIPT_NIGHTFUNCINDEX_OFFSET");

// --- JSString -------------------------------------------------------------
//
// The inline string-element read tests the flag bits, then takes either the
// inline char storage or the out-of-line pointer -- both at +8.
static_assert(JSString::offsetOfFlags() == 0, "STRING_FLAGS_OFFSET");
static_assert(JSString::offsetOfLength() == 4, "STRING_LENGTH_OFFSET");
static_assert(offsetof(JS::shadow::String, nonInlineCharsLatin1) == 8,
              "STRING_CHARS_OFFSET (non-inline)");
static_assert(offsetof(JS::shadow::String, inlineStorageLatin1) == 8,
              "STRING_CHARS_OFFSET (inline)");
static_assert(JS::shadow::String::LINEAR_BIT == (1u << 4), "STRING_LINEAR_BIT");
static_assert(JS::shadow::String::INLINE_CHARS_BIT == (1u << 6),
              "STRING_INLINE_CHARS_BIT");
static_assert(JS::shadow::String::LATIN1_CHARS_BIT == (1u << 10),
              "STRING_LATIN1_CHARS_BIT");

// --- The alloc-cell rows --------------------------------------------------
//
// The row sizes are shared with the compiler through NightRegionShape.h; the
// field offsets inside a row are asserted here and mirrored in object.rs's
// layout comment, where the stores are emitted. A construct row opens with an
// alloc row, so NightFillAllocCellObject fills it unchanged.
static_assert(sizeof(NightAllocCell) == 20, "ALLOC_CELL fields");
static_assert(sizeof(NightArrayAllocCell) <= js::night::Night_allocCellBytes,
              "ALLOC_CELL_BYTES");
static_assert(sizeof(NightConstructCell) <= js::night::Night_constructCellBytes,
              "CONSTRUCT_CELL_BYTES");
static_assert(offsetof(NightAllocCell, shape) == 0, "alloc cell shape@0");
static_assert(offsetof(NightAllocCell, totalSize) == 4, "alloc cell total@4");
static_assert(offsetof(NightAllocCell, slotsWord) == 8, "alloc cell slots@8");
static_assert(offsetof(NightAllocCell, elementsWord) == 12,
              "alloc cell elements@12");
static_assert(offsetof(NightAllocCell, headerWord) == 16,
              "alloc cell header@16");
static_assert(offsetof(NightArrayAllocCell, elemFlags) == 20,
              "array cell elemFlags@20");
static_assert(offsetof(NightArrayAllocCell, capacity) == 24,
              "array cell capacity@24");
static_assert(offsetof(NightArrayAllocCell, length) == 28,
              "array cell length@28");
static_assert(offsetof(NightConstructCell, ctorShape) == 20,
              "construct cell ctorShape@20");
static_assert(offsetof(NightConstructCell, gen) == 24, "construct cell gen@24");
static_assert(offsetof(NightConstructCell, protoPtr) == 28,
              "construct cell protoPtr@28");
static_assert(offsetof(NightConstructCell, protoSlotEnc) == 32,
              "construct cell protoSlotEnc@32");

// ==========================================================================
// Inline nursery allocation
// ==========================================================================

bool NightNurseryAddresses(JSContext* cx, uint32_t* posAddr,
                           uint32_t* endAddr) {
  Nursery& nursery = cx->nursery();
  if (!nursery.isEnabled() || !cx->zone()->allocNurseryObjects()) {
    return false;
  }
  uintptr_t pos = reinterpret_cast<uintptr_t>(nursery.addressOfPosition());
  *posAddr = uint32_t(pos);
  *endAddr = uint32_t(pos + Nursery::offsetOfCurrentEndFromPosition());
  return true;
}

namespace {
// The object's own layout words, read as the replay will write them. The
// slots and elements words have no typed accessor (both members are private
// to NativeObject), so they come off the shadow mirror, whose layout the
// asserts above pin to the real one. The nursery cell header sits just
// before the object.
struct RawObjectWords {
  uint32_t slots;
  uint32_t elements;
  uint32_t header;

  explicit RawObjectWords(const JSObject* obj) {
    const auto* shadow = reinterpret_cast<const JS::shadow::Object*>(obj);
    slots = uint32_t(reinterpret_cast<uintptr_t>(shadow->slots));
    elements = uint32_t(reinterpret_cast<uintptr_t>(shadow->_1));
    header = *reinterpret_cast<const uint32_t*>(
        reinterpret_cast<uintptr_t>(obj) - Nursery::nurseryCellHeaderSize());
  }
};
}  // namespace

// Only a nursery PlainObject with the empty slotSpan-0 shared shape and no
// dynamic slots/elements qualifies: the inline path does no slot init and no
// malloc, so anything else it could not reproduce.
bool NightFillAllocCellObject(NightAllocCell* cell, JSObject* obj) {
  if (!cell || !gc::IsInsideNursery(obj) || !obj->is<PlainObject>()) {
    return false;
  }
  NativeObject* nobj = &obj->as<NativeObject>();
  if (!nobj->shape()->isShared() || nobj->shape()->asShared().slotSpan() != 0 ||
      nobj->hasDynamicSlots()) {
    return false;
  }
  gc::AllocKind kind = gc::GetGCObjectKind(nobj->numFixedSlots());
  RawObjectWords words(obj);
  cell->totalSize =
      uint32_t(gc::Arena::thingSize(kind) + Nursery::nurseryCellHeaderSize());
  cell->slotsWord = words.slots;
  cell->elementsWord = words.elements;
  cell->headerWord = words.header;
  // The shape word arms the row, so it is written last: a compiled body can
  // read the row between any two of these stores.
  cell->shape = uint32_t(reinterpret_cast<uintptr_t>(nobj->shape()));
  return true;
}

// Only a nursery ArrayObject whose elements live inside the cell (fixed)
// with initializedLength 0 qualifies. The in-cell layout is what makes
// totalSize = elemOffset + capacity * sizeof(Value): the elements vector
// fills the alloc kind exactly.
bool NightFillAllocCellArray(NightArrayAllocCell* cell, JSObject* obj,
                             uint32_t length) {
  if (!cell || !gc::IsInsideNursery(obj) || !obj->is<ArrayObject>()) {
    return false;
  }
  ArrayObject* arr = &obj->as<ArrayObject>();
  if (!arr->shape()->isShared() || arr->getDenseInitializedLength() != 0 ||
      arr->length() != length || arr->hasDynamicSlots()) {
    return false;
  }
  RawObjectWords words(obj);
  uintptr_t o = reinterpret_cast<uintptr_t>(arr);
  uintptr_t elems = words.elements;
  if (elems <= o || elems - o > 4096) {
    return false;  // dynamic (heap) or shared-empty elements: not replayable
  }
  uint32_t capacity = arr->getDenseCapacity();
  if (capacity < length || arr->length() != length) {
    return false;
  }
  // ObjectElements::flags has no public accessor; read it at the engine's own
  // (asserted) offset behind element 0 rather than at a bare -16.
  uint32_t elemFlags = *reinterpret_cast<const uint32_t*>(
      elems + ObjectElements::offsetOfFlags());
  uint32_t elemOff = uint32_t(elems - o);
  cell->alloc.totalSize = elemOff + uint32_t(capacity * sizeof(JS::Value) +
                                             Nursery::nurseryCellHeaderSize());
  cell->alloc.slotsWord = words.slots;
  cell->alloc.elementsWord = elemOff;
  cell->alloc.headerWord = words.header;
  cell->elemFlags = elemFlags;
  cell->capacity = capacity;
  cell->length = length;
  cell->alloc.shape = uint32_t(reinterpret_cast<uintptr_t>(arr->shape()));
  return true;
}

// ==========================================================================
// Write barriers
// ==========================================================================

void NightPostWriteBarrier(uint64_t ownerBits, uint32_t slot,
                           uint64_t valBits) {
  JS::Value v = JS::Value::fromRawBits(valBits);
  MOZ_ASSERT(v.isGCThing());
  gc::Cell* cell = v.toGCThing();
  MOZ_ASSERT(cell->storeBuffer(), "post-barrier called for a tenured value");
  NativeObject* owner =
      &JS::Value::fromRawBits(ownerBits).toObject().as<NativeObject>();
  cell->storeBuffer()->putSlot(owner, HeapSlot::Slot, slot, 1);
}

// The element edge is a DIFFERENT store-buffer edge than the slot one, and
// takes the store buffer's unshifted index from the owner -- exactly what
// NativeObject::setDenseElementUnchecked does.
void NightPostWriteBarrierElem(uint64_t ownerBits, uint32_t index,
                               uint64_t valBits) {
  JS::Value v = JS::Value::fromRawBits(valBits);
  MOZ_ASSERT(v.isGCThing());
  gc::Cell* cell = v.toGCThing();
  MOZ_ASSERT(cell->storeBuffer(), "post-barrier called for a tenured value");
  NativeObject* owner =
      &JS::Value::fromRawBits(ownerBits).toObject().as<NativeObject>();
  cell->storeBuffer()->putSlot(owner, HeapSlot::Element,
                               owner->unshiftedIndex(index), 1);
}

// Idempotent (marking an already-black cell is a no-op) and non-moving, so
// the caller needs no rooting.
void NightPreWriteBarrier(uint64_t valBits) {
  JS::Value v = JS::Value::fromRawBits(valBits);
  if (v.isGCThing()) {
    gc::ValuePreWriteBarrier(v);
  }
}

}  // namespace night
}  // namespace js

#endif  // ENABLE_JS_NIGHTMONKEY
