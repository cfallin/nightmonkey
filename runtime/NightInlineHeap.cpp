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

#include "runtime/NightContext.h"
#include "builtin/MapObject.h"
#include "vm/Iteration.h"
#include "vm/StringType.h"

#include "gc/Nursery.h"
#include "gc/StoreBuffer.h"  // js::gc::StoreBuffer::putSlot (post-barrier)
#include "gc/StoreBuffer-inl.h"  // js::gc::StoreBuffer::putWholeCell
#include "js/Realm.h"        // JS::Realm::offsetOfActiveGlobal
#include "runtime/NightRegionShape.h"  // Night_allocCellBytes, Night_constructCellBytes
#include "vm/ArrayObject.h"
#include "vm/EnvironmentObject.h"  // CallObject (the environment rows)
#include "vm/JSContext.h"
#include "vm/JSFunction.h"  // js::FunctionFlags::BASESCRIPT
#include "vm/JSObject.h"
#include "vm/JSScript.h"  // BaseScript::offsetOfExternalTierWord
#include "vm/PlainObject.h"
#include "vm/RegExpObject.h"
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
//   js/src/night/compiler/src/wasm/mir/abi.rs   the object/shape/string/
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
static_assert(JSContext::offsetOfExternalCompilerState() == 144,
              "CX_EXT_STATE_OFFSET");
static_assert(offsetof(js::nightrt::NightContextState, propIcBase) == 0,
              "CTX_PROPIC_BASE_OFFSET");
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
static_assert(NativeShape::smallSlotSpanShift() == 11,
              "SHAPE_SMALL_SLOTSPAN_SHIFT");
static_assert((NativeShape::smallSlotSpanMask() >>
               NativeShape::smallSlotSpanShift()) == 0x3ff,
              "SHAPE_SMALL_SLOTSPAN_MASK_BITS");
static_assert(NativeShape::permutedSlotsBit() == (1u << 21),
              "SHAPE_PERMUTED_SLOTS_BIT");
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

// --- JSClass: the inline typeof --------------------------------------------
static_assert(offsetof(JSClass, flags) == 4, "JSCLASS_FLAGS_OFFSET");
static_assert(offsetof(JSClass, cOps) == 8, "JSCLASS_COPS_OFFSET");
static_assert(offsetof(JSClassOps, call) == 28, "JSCLASSOPS_CALL_OFFSET");
static_assert(JSCLASS_EMULATES_UNDEFINED == 1u << 6, "JSCLASS_EMULATES_UNDEFINED");
static_assert(JSCLASS_IS_PROXY == 1u << 19, "JSCLASS_IS_PROXY");
static_assert(JSTYPE_UNDEFINED == 0 && JSTYPE_OBJECT == 1 &&
                  JSTYPE_FUNCTION == 2 && JSTYPE_STRING == 3 &&
                  JSTYPE_NUMBER == 4 && JSTYPE_BOOLEAN == 5 &&
                  JSTYPE_SYMBOL == 6 && JSTYPE_BIGINT == 7,
              "the JSType numbering typeof_eq decodes");

// --- MapObject: the inline Map.prototype.get ------------------------------
//
// The compiled get hashes an atom or int32 key as the table does
// (`OrderedHashTableImpl::prepareHash`), finds the bucket by the hash shift
// and walks the chain comparing key bits.
static_assert(MapObject::offsetOfHashTable() == 16, "MAP_HASH_TABLE_OFFSET");
static_assert(MapObject::offsetOfLiveCount() == 48, "MAP_LIVE_COUNT_OFFSET");
static_assert(MapObject::offsetOfHashShift() == 56, "MAP_HASH_SHIFT_OFFSET");
static_assert(MapObject::Table::offsetOfEntryKey() == 0, "MAP_ENTRY_KEY_OFFSET");
static_assert(MapObject::Table::Entry::offsetOfValue() == 8, "MAP_ENTRY_VALUE_OFFSET");
static_assert(MapObject::Table::offsetOfImplDataChain() == 16, "MAP_ENTRY_CHAIN_OFFSET");
static_assert(NormalAtom::offsetOfHash() == 20, "ATOM_HASH_OFFSET");
static_assert(FatInlineAtom::offsetOfHash() == 28, "FAT_ATOM_HASH_OFFSET");
static_assert(JSString::FAT_INLINE_MASK == 0xC0, "STRING_FAT_INLINE_MASK");
static_assert(mozilla::kGoldenRatioU32 == 0x9E3779B9U, "GOLDEN_RATIO");

// --- NativeIterator: the inline for-in steps ------------------------------
//
// A for-in's `more` and `end` run in compiled code as the JIT's
// iteratorMore / iteratorClose do. (The iterator object's slot offset is
// not constexpr: NightCheckIteratorLayout checks it.)
static_assert(NativeIterator::offsetOfObjectBeingIterated() == 8, "NI_OBJECT_OFFSET");
static_assert(NativeIterator::offsetOfPropertyCursor() == 24, "NI_CURSOR_OFFSET");
static_assert(NativeIterator::offsetOfPropertyCount() == 20, "NI_COUNT_OFFSET");
static_assert(NativeIterator::offsetOfFlags() == 38, "NI_FLAGS_OFFSET (a byte)");
static_assert(NativeIterator::offsetOfFirstProperty() == 40, "NI_FIRST_PROPERTY_OFFSET");
static_assert(NativeIterator::offsetOfNext() == 4, "NI_NEXT_OFFSET");
static_assert(NativeIterator::offsetOfPrev() == 0, "NI_PREV_OFFSET");
static_assert(sizeof(IteratorProperty) == 4, "NI_PROPERTY_BYTES");
static_assert(IteratorProperty::DeletedBit == 1, "NI_DELETED_BIT");
static_assert(NativeIterator::Flags::Active == 2, "NI_FLAG_ACTIVE");
static_assert(NativeIterator::Flags::HasUnvisitedPropertyDeletion == 4,
              "NI_FLAG_UNVISITED_DELETION");
static_assert(NativeIterator::Flags::IsEmptyIteratorSingleton == 8,
              "NI_FLAG_EMPTY_SINGLETON");

// The for-in's start runs in compiled code as the JIT's
// maybeLoadIteratorFromShape and registerIterator do: the iterator the
// receiver's shape caches, checked against the prototypes' shapes it
// recorded (after its properties, and their indices if allocated).
static_assert(NativeIterator::Flags::Initialized == 1, "NI_FLAG_INITIALIZED");
static_assert(NativeIterator::Flags::IndicesAllocated == 0x20,
              "NI_FLAG_INDICES_ALLOCATED");
static_assert(sizeof(PropertyIndex) == 4, "NI_INDEX_BYTES");
static_assert(sizeof(GCPtr<Shape*>) == 4, "NI_PROTO_SHAPE_BYTES");
static_assert(Shape::offsetOfCachePtr() == 12, "SHAPE_CACHE_OFFSET");
static_assert(RegExpObject::offsetOfLastIndex() == 16, "REGEXP_LAST_INDEX_OFFSET");
static_assert(RegExpObject::offsetOfShared() == 40, "REGEXP_SHARED_OFFSET");
static_assert(sizeof(ShapeCachePtr) == sizeof(uintptr_t), "SHAPE_CACHE_OFFSET");

bool NightCheckIteratorLayout() {
  // ShapeCachePtr's tags are private: an iterator's is the low bits of a
  // word that holds one (SHAPE_CACHE_ITERATOR, under SHAPE_CACHE_TAG_MASK).
  ShapeCachePtr p;
  p.setIterator(reinterpret_cast<PropertyIteratorObject*>(uintptr_t(0x1000)));
  uintptr_t bits;
  memcpy(&bits, &p, sizeof(bits));
  return PropertyIteratorObject::offsetOfIteratorSlot() == 16 && bits == 0x1003;
}

// --- JSString and the inline rope -----------------------------------------
//
// A compiled concat allocates a JSRope in the nursery as the JIT's concat
// stub does: flags (Latin1 iff both halves are), length, then the children.
static_assert(JSString::offsetOfFlags() == 0, "STRING_FLAGS_OFFSET");
static_assert(JSString::offsetOfLength() == 4, "STRING_LENGTH_OFFSET");
static_assert(sizeof(JSString) == 16, "ROPE_BYTES");
// (The children's offsets, ROPE_LEFT_OFFSET 8 and ROPE_RIGHT_OFFSET 12, are
// private to JSRope: NightCheckRopeLayout checks them on a real rope.)
static_assert(JSString::INIT_ROPE_FLAGS == 0, "a rope's flags are its Latin1 bit");
static_assert(JSString::LATIN1_CHARS_BIT == 1u << 10, "STRING_LATIN1_CHARS_BIT");
static_assert(JSString::MAX_LENGTH == (1u << 30) - 2, "STRING_MAX_LENGTH");
static_assert(JSFatInlineString::MAX_LENGTH_LATIN1 == 24 &&
                  JSFatInlineString::MAX_LENGTH_TWO_BYTE == 12,
              "FAT_INLINE_MAX_LATIN1 / FAT_INLINE_MAX_TWO_BYTE");
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
// call classify (the inline probe and night_call_classify) loads both.
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
static_assert(sizeof(NightLambdaCell) <= js::night::Night_constructCellBytes,
              "a Lambda row fits a construct row");
static_assert(offsetof(NightLambdaCell, templateFun) == 20,
              "lambda cell templateFun@20");
static_assert(offsetof(NightLambdaCell, gen) == 24, "lambda cell gen@24");
static_assert(sizeof(NightEnvCell) <= js::night::Night_constructCellBytes,
              "an environment row fits a construct row");
static_assert(offsetof(NightEnvCell, armed) == 20, "env cell armed@20");
static_assert(offsetof(NightEnvCell, gen) == 24, "env cell gen@24");
static_assert(offsetof(NightEnvCell, classWord) == 28,
              "env cell classWord@28");

static_assert(offsetof(NightConstructCell, gen) == 24, "construct cell gen@24");
static_assert(offsetof(NightConstructCell, protoPtr) == 28,
              "construct cell protoPtr@28");
static_assert(offsetof(NightConstructCell, protoSlotEnc) == 32,
              "construct cell protoSlotEnc@32");
static_assert(offsetof(NightConstructCell, finalShape) == 36,
              "construct cell finalShape@36");
static_assert(offsetof(NightConstructCell, protoShape) == 40,
              "construct cell protoShape@40");
static_assert(offsetof(NightConstructCell, proto2Ptr) == 44,
              "construct cell proto2Ptr@44");
static_assert(offsetof(NightConstructCell, proto2Shape) == 48,
              "construct cell proto2Shape@48");

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

bool NightCheckRopeLayout(JSContext* cx) {
  static const char kHalf[] = "night-rope-layout-check-half";
  JS::RootedString l(cx, JS_NewStringCopyZ(cx, kHalf));
  JS::RootedString r(cx, l ? JS_NewStringCopyZ(cx, kHalf) : nullptr);
  JSString* rope = r ? JS_ConcatStrings(cx, l, r) : nullptr;
  if (!rope || !rope->isRope()) {
    return false;
  }
  const uint32_t* w = reinterpret_cast<const uint32_t*>(rope);
  return w[2] == uint32_t(reinterpret_cast<uintptr_t>(rope->asRope().leftChild())) &&
         w[3] == uint32_t(reinterpret_cast<uintptr_t>(rope->asRope().rightChild()));
}

bool NightNurseryStringAlloc(JSContext* cx, uint32_t* header,
                             uint32_t* countAddr) {
  Zone* zone = cx->zone();
  if (!cx->nursery().isEnabled() || !zone->allocNurseryStrings()) {
    return false;
  }
  gc::AllocSite* site = zone->unknownAllocSite(JS::TraceKind::String);
  *header = uint32_t(gc::NurseryCellHeader::MakeValue(site, JS::TraceKind::String));
  *countAddr = uint32_t(reinterpret_cast<uintptr_t>(site->nurseryAllocCountAddress()));
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

// Only a nursery clone of a tenured canonical function with only fixed slots
// qualifies: the inline path copies the canonical function's words.
bool NightFillLambdaCell(NightLambdaCell* cell, JSObject* clone) {
  if (!cell || !gc::IsInsideNursery(clone) || !clone->is<JSFunction>()) {
    return false;
  }
  NativeObject* nobj = &clone->as<NativeObject>();
  if (nobj->hasDynamicSlots()) {
    return false;
  }
  gc::AllocKind kind = clone->as<JSFunction>().getAllocKind();
  RawObjectWords words(clone);
  cell->alloc.shape = uint32_t(reinterpret_cast<uintptr_t>(nobj->shape()));
  cell->alloc.totalSize =
      uint32_t(gc::Arena::thingSize(kind) + Nursery::nurseryCellHeaderSize());
  cell->alloc.slotsWord = words.slots;
  cell->alloc.elementsWord = words.elements;
  cell->alloc.headerWord = words.header;
  return true;
}

// Only a nursery CallObject with only fixed slots qualifies.
bool NightFillEnvCell(NightEnvCell* cell, JSObject* callobj) {
  if (!cell || !gc::IsInsideNursery(callobj) || !callobj->is<CallObject>()) {
    return false;
  }
  // The replay writes the enclosing environment to fixed slot 0 and the
  // callee to fixed slot 1 (CALLOBJ_ENCLOSING_OFFSET, CALLOBJ_CALLEE_OFFSET).
  if (EnvironmentObject::enclosingEnvironmentSlot() != 0 ||
      CallObject::calleeSlot() != 1) {
    return false;
  }
  NativeObject* nobj = &callobj->as<NativeObject>();
  if (nobj->hasDynamicSlots() ||
      nobj->slotSpan() > nobj->numFixedSlots()) {
    return false;
  }
  gc::AllocKind kind = gc::GetGCObjectKind(nobj->numFixedSlots());
  RawObjectWords words(callobj);
  cell->classWord = *reinterpret_cast<const uint32_t*>(
      reinterpret_cast<uintptr_t>(callobj) + sizeof(uint32_t));
  cell->alloc.shape = uint32_t(reinterpret_cast<uintptr_t>(nobj->shape()));
  cell->alloc.totalSize =
      uint32_t(gc::Arena::thingSize(kind) + Nursery::nurseryCellHeaderSize());
  cell->alloc.slotsWord = words.slots;
  cell->alloc.elementsWord = words.elements;
  cell->alloc.headerWord = words.header;
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

// The JIT's whole-cell post barrier (jit::PostWriteBarrier): tenured `cell`
// now holds a nursery pointer outside its slots (an iterator's
// objectBeingIterated_, stored raw), so the next minor GC traces all of it.
// One bit per cell until then, where the field's own barrier would add and
// remove a hashed edge at every for-in's start and close.
void NightPostWholeCell(JSContext* cx, uint32_t cell) {
  cx->runtime()->gc.storeBuffer().putWholeCell(
      reinterpret_cast<gc::Cell*>(uintptr_t(cell)));
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
