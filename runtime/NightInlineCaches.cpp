/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

/*
 * The engine half of the compiled body's property caches. The hit paths are
 * emitted inline in wasm (shape / generation / holder guards plus a slot
 * load or store); everything here runs on the miss side, doing the
 * NativeObject and Shape work needed to populate a linear-memory cache row
 * the inline path can then read directly -- plus the add-transition replay
 * that lets a cached property ADD skip the generic set.
 */

#include "runtime/NightInlineCaches.h"

#include "mozilla/Maybe.h"

#include "runtime/Night.h"  // js::night::NightAddPropCheck
#include "vm/JSContext.h"
#include "vm/JSFunction.h"
#include "vm/JSObject.h"
#include "vm/PlainObject.h"
#include "vm/Shape.h"
#include "vm/TypedArrayObject.h"  // js::ToTypedArrayIndex (get-IC populate)
#include "vm/Watchtower.h"  // js::Watchtower (add-transition cacheability)

#include "vm/JSObject-inl.h"
#include "vm/NativeObject-inl.h"
#include "vm/ObjectOperations-inl.h"

#ifdef ENABLE_JS_NIGHTMONKEY

using namespace js;

namespace js {
namespace night {

// The shape word of an object (a leaf; the add-transition cache reads the
// pre-set shape through this rather than reaching into object layout from the
// reactor).
uint32_t NightObjectShape(JSObject* obj) {
  return uint32_t(reinterpret_cast<uintptr_t>(obj->shape()));
}

// The slot span of an object's SHARED shape, or UINT32_MAX when not a
// non-dictionary NativeObject. Captured before a generic set so the populate
// side can prove the set appended EXACTLY ONE data slot (a proto setter /
// valueOf running user code could have added others first -- replaying the
// transition on another object would leave those intermediate slots
// uninitialized).
uint32_t NightObjectSlotSpanIfShared(JSObject* obj) {
  if (!obj->is<NativeObject>() || obj->shape()->isDictionary()) {
    return UINT32_MAX;
  }
  return obj->shape()->asShared().slotSpan();
}

// Add-transition cache, populate side. Called by the set-IC miss helper
// after a generic set CHANGED the receiver's shape (a property ADD). Cacheable
// iff the add was a plain own writable data slot on a non-dictionary
// NativeObject with no addProperty class hook, and the proto chain is static,
// native, and short (<= 4 links) -- each proto's shape word is cached and
// re-checked on every hit, so a later proto mutation (a setter or a readonly
// shadow for this name) invalidates. A NURSERY proto is cacheable too:
// `*nurseryOut` tells the caller to zero the rows at the next minor-GC end
// (the pointers are stable between minor GCs and a dead-then-reused address
// can therefore never false-hit). The (oldShape, id) -> newShape transition
// is deterministic (the engine's memoized shape tree keyed on the same
// class/nfixed/protos, all encoded in oldShape), so replaying
// grow+setShape+initSlot on ANOTHER object of oldShape reproduces exactly
// what the generic path would do.
bool NightPopulateAddTransition(JSContext* cx, JSObject* obj, jsid id,
                                uint32_t oldSpan, uint32_t* newShapeOut,
                                uint32_t* slotOut, uint32_t protoPtrsOut[4],
                                uint32_t protoShapesOut[4],
                                uint32_t* numProtosOut, bool* nurseryOut) {
  if (!obj->is<NativeObject>()) {
    return false;
  }
  NativeObject* nobj = &obj->as<NativeObject>();
  if (nobj->shape()->isDictionary()) {
    return false;
  }
  if (nobj->getClass()->getAddProperty()) {
    return false;
  }
  // A class resolve hook that could lazily materialize THIS id (e.g. a
  // plain function's `prototype` via fun_resolve) makes the plain-slot
  // replay wrong on another same-shape receiver whose hook has not run:
  // mirrors CacheIR's ClassMayResolveId refusal.
  if (ClassMayResolveId(cx->names(), nobj->getClass(), id, nobj)) {
    return false;
  }
  // A row cached from a Watchtower-watched receiver would let the inline
  // replay skip the engine's add notification (object flags ride the shape,
  // so refusing here keeps watched shapes out of the rows entirely).
  if (js::Watchtower::watchesPropertyAdd(nobj)) {
    return false;
  }
  // The set must have appended EXACTLY our property (one new data slot, and
  // it is the shape's last): replaying the transition initializes only that
  // slot, so any other same-set mutation would leave garbage slots.
  SharedShape& ns = nobj->shape()->asShared();
  if (oldSpan == UINT32_MAX || ns.slotSpan() != oldSpan + 1) {
    return false;
  }
  PropertyInfoWithKey last = ns.lastProperty();
  if (last.key() != id || !last.isDataProperty()) {
    return false;
  }
  mozilla::Maybe<PropertyInfo> prop = nobj->lookupPure(id);
  if (prop.isNothing() || !prop->isDataProperty() || !prop->hasSlot() ||
      !prop->writable() || !prop->enumerable() || !prop->configurable()) {
    return false;
  }
  *nurseryOut = false;
  uint32_t n = 0;
  for (JSObject* proto = nobj->staticPrototype(); proto;
       proto = proto->staticPrototype()) {
    if (n == 4 || !proto->is<NativeObject>() || !proto->hasStaticPrototype()) {
      return false;
    }
    if (js::gc::IsInsideNursery(proto)) {
      *nurseryOut = true;
    }
    protoPtrsOut[n] = uint32_t(reinterpret_cast<uintptr_t>(proto));
    protoShapesOut[n] = uint32_t(reinterpret_cast<uintptr_t>(proto->shape()));
    n++;
  }
  *numProtosOut = n;
  *newShapeOut = uint32_t(reinterpret_cast<uintptr_t>(nobj->shape()));
  *slotOut = prop->slot();
  return true;
}

// Add-transition cache, hit side. The caller checked generation validity;
// this re-checks the receiver shape and every cached proto shape, then replays
// the add without any lookup: grow the dynamic slots if the new span needs it,
// install the cached transition-target shape (barriered HeapPtr write), and
// init the fresh slot. Returns false (having done nothing observable beyond a
// possible pure slot grow) to send the caller to the generic path.
bool NightTryAddPropTransition(JSContext* cx, uint64_t recvBits,
                               uint32_t oldShapeW, uint32_t newShapeW,
                               uint32_t slot, const uint32_t* protoPtrs,
                               const uint32_t* protoShapes, uint32_t numProtos,
                               uint64_t valBits) {
  JS::Value rv = JS::Value::fromRawBits(recvBits);
  if (!rv.isObject()) {
    return false;
  }
  JSObject* obj = &rv.toObject();
  if (uint32_t(reinterpret_cast<uintptr_t>(obj->shape())) != oldShapeW) {
    return false;
  }
  // Watchtower-watched receivers need the engine's notification path.
  if (js::Watchtower::watchesPropertyAdd(&obj->as<NativeObject>())) {
    return false;
  }
  // oldShape match pins class / numFixedSlots / proto IDENTITY; the cached
  // proto shape words pin proto CONTENTS (no new setter/readonly shadow).
  JSObject* proto = obj->staticPrototype();
  for (uint32_t i = 0; i < numProtos; i++) {
    if (uint32_t(reinterpret_cast<uintptr_t>(proto)) != protoPtrs[i] ||
        uint32_t(reinterpret_cast<uintptr_t>(proto->shape())) !=
            protoShapes[i]) {
      return false;
    }
    proto = proto->staticPrototype();
  }
  if (proto) {
    return false;  // chain grew beyond the cached links
  }
  NativeObject* nobj = &obj->as<NativeObject>();
  SharedShape* newShape =
      reinterpret_cast<SharedShape*>(static_cast<uintptr_t>(newShapeW));
  uint32_t nfixed = nobj->numFixedSlots();
  if (slot >= nfixed) {
    uint32_t dynCount = NativeObject::calculateDynamicSlots(
        nfixed, newShape->slotSpan(), nobj->getClass());
    if (dynCount > nobj->numDynamicSlots()) {
      if (!NativeObject::growSlotsPure(cx, nobj, dynCount)) {
        return false;  // OOM: the generic path reports properly
      }
    }
  }
  nobj->setShape(newShape);
  nobj->initSlot(slot, JS::Value::fromRawBits(valBits));
  NightAddPropCheck(nobj, newShape->lastProperty().key(), slot,
                    nobj->numFixedSlots());
  return true;
}

// Init (define) flavor of the add-transition replay: a DEFINE on a literal
// under construction never consults the proto chain, so no proto guards are
// needed. The oldShape match pins class (no addProperty hook, validated at
// populate), extensibility, and the property's absence; the shape tree makes
// (oldShape, id) -> newShape deterministic.
bool NightTryInitAddTransition(JSContext* cx, uint64_t objBits,
                               uint32_t oldShapeW, uint32_t newShapeW,
                               uint32_t slot, uint64_t valBits) {
  JS::Value ov = JS::Value::fromRawBits(objBits);
  if (!ov.isObject()) {
    return false;
  }
  JSObject* obj = &ov.toObject();
  if (uint32_t(reinterpret_cast<uintptr_t>(obj->shape())) != oldShapeW) {
    return false;
  }
  if (js::Watchtower::watchesPropertyAdd(&obj->as<NativeObject>())) {
    return false;
  }
  NativeObject* nobj = &obj->as<NativeObject>();
  SharedShape* newShape =
      reinterpret_cast<SharedShape*>(static_cast<uintptr_t>(newShapeW));
  uint32_t nfixed = nobj->numFixedSlots();
  if (slot >= nfixed) {
    uint32_t dynCount = NativeObject::calculateDynamicSlots(
        nfixed, newShape->slotSpan(), nobj->getClass());
    if (dynCount > nobj->numDynamicSlots()) {
      if (!NativeObject::growSlotsPure(cx, nobj, dynCount)) {
        return false;
      }
    }
  }
  nobj->setShape(newShape);
  nobj->initSlot(slot, JS::Value::fromRawBits(valBits));
  NightAddPropCheck(nobj, newShape->lastProperty().key(), slot,
                    nobj->numFixedSlots());
  return true;
}

// Inline get-IC populate (the inline GetProp hit path's miss helper).
// Resolve `id` along the prototype chain from `obj`.
// Cacheable iff the holder is a NativeObject with an own data slot, and, when
// the holder is a *prototype* (hops > 0), TENURED. An own field (hops == 0) is
// cached RECEIVER-RELATIVE instead -- holderPtr = 0 tells the hit path to load
// off the live receiver, so no holder pointer is stored and the receiver may be
// in the nursery. For a proto holder the cache stores the raw holder POINTER
// (so the hit path reads the slot with no proto walk); a tenured holder is
// immovable except by a major GC, which bumps the inline cache's generation
// guard, so the cached pointer is never stale when the guard matches (a minor
// GC never moves a tenured cell). The receiver-shape guard pins the whole
// proto-chain identity (the proto is part of the shape) so the cached holder
// stays the correct one.
// On success fills the receiver shape (low 32), holder pointer (low 32), holder
// shape (low 32), and the W1-encoded slot (bit1 = is-dynamic, bits[31:2] =
// index) and returns true; else false (the way is left untouched, so the site
// keeps calling the miss helper). Leaf (lookupPure / static-proto walk: no GC).
bool NightPopulateInlineGetIC(JSContext* cx, JSObject* obj, jsid id,
                              uint32_t* recvShapeOut, uint32_t* holderPtrOut,
                              uint32_t* holderShapeOut, uint32_t* slotEncOut) {
  if (!obj->is<NativeObject>()) {
    return false;
  }
  uint32_t recvShape = uint32_t(reinterpret_cast<uintptr_t>(obj->shape()));
  JSObject* holder = obj;
  uint32_t hops = 0;
  for (;;) {
    if (!holder->is<NativeObject>()) {
      return false;
    }
    NativeObject* nholder = &holder->as<NativeObject>();
    // A canonical numeric index string on a typed array never consults the
    // proto chain and is never a stored property; absence on the TA is not
    // shape-guarded, so a chain through it is uncacheable (mirrors CacheIR's
    // CheckHasNoSuchOwnProperty).
    if (nholder->is<TypedArrayObject>() && ToTypedArrayIndex(id).isSome()) {
      return false;
    }
    mozilla::Maybe<PropertyInfo> prop = nholder->lookupPure(id);
    if (prop.isSome()) {
      if (!prop->isDataProperty() || !prop->hasSlot()) {
        return false;  // accessor / non-slot: stay on the generic path.
      }
      uint32_t slot = prop->slot();
      uint32_t nfixed = nholder->numFixedSlots();
      uint32_t isDynamic = (slot >= nfixed) ? 1u : 0u;
      uint32_t idx = isDynamic ? (slot - nfixed) : slot;
      if (hops == 0) {
        // Own field: cache RECEIVER-RELATIVE (like the set IC). holderPtr = 0
        // tells the inline hit path to load the slot off the LIVE receiver
        // pointer (nursery movement is then harmless), and holderShape =
        // recvShape makes the holder-shape guard a benign re-check of the
        // receiver-shape guard.
        *recvShapeOut = recvShape;
        *holderPtrOut = 0;
        *holderShapeOut = recvShape;
        *slotEncOut = NightSlotEnc(isDynamic != 0, idx);
        return true;
      }
      if (js::gc::IsInsideNursery(nholder)) {
        return false;  // a moving (nursery) holder pointer would go stale.
      }
      *recvShapeOut = recvShape;
      *holderPtrOut = uint32_t(reinterpret_cast<uintptr_t>(nholder));
      *holderShapeOut = uint32_t(reinterpret_cast<uintptr_t>(nholder->shape()));
      *slotEncOut = NightSlotEnc(isDynamic != 0, idx);
      return true;
    }
    // A class resolve hook that could lazily materialize `id` on this hop
    // (a function's `name`/`length` via fun_resolve) makes the chain
    // unstable: the engine's lookup would define the property here instead
    // of reading the holder's, and the receiver's shape does not change
    // until it does. Mirrors CacheIR's ClassMayResolveId refusal.
    if (ClassMayResolveId(cx->names(), nholder->getClass(), id, nholder)) {
      return false;
    }
    if (!holder->hasStaticPrototype()) {
      return false;  // dynamic prototype (proxy): not cacheable.
    }
    holder = holder->staticPrototype();
    if (!holder) {
      return false;  // end of chain without finding `id`.
    }
    // Shape-teleporting validity (see the CacheIR comment): the receiver+
    // holder shape guards catch a shadowing add on an intermediate proto only
    // while shadowed adds still reshape the old holder (Watchtower's
    // ReshapeForShadowedProp). Once a chain object has INVALIDATED
    // teleporting, later shadowing adds no longer reshape it, so a cached
    // coordinate through it could go stale under unchanged guards -- refuse,
    // exactly as CacheIR refuses to attach a teleporting stub.
    if (holder->hasInvalidatedTeleporting()) {
      return false;
    }
    hops++;
  }
}

// Guarded proto-chain populate: the fallback when
// NightPopulateInlineGetIC refuses (typically an invalidated-teleporting chain
// object -- e.g. a deep subclass hierarchy). Mirrors CacheIR's non-teleporting
// stubs: record the LIVE shape of EVERY hop from the first proto through the
// holder; the probe re-validates each before serving the slot, so a shadowing
// add / delete / proto-set on any hop (all of which reshape that hop) misses.
// Chain objects must be tenured (their pointers are cached; the major-GC zero
// resets the table before compaction can move them). Own properties (hops == 0)
// are the mono-way/mega path's job -- refuse.
bool NightPopulateGuardedChain(JSContext* cx, JSObject* obj, jsid id,
                               uint32_t maxHops, uint32_t* nHopsOut,
                               uint32_t* protoPtrs, uint32_t* protoShapes,
                               uint32_t* slotEncOut) {
  if (!obj->is<NativeObject>()) {
    return false;
  }
  JSObject* holder = obj;
  uint32_t hops = 0;
  bool sawResolveHook = false;
  for (;;) {
    if (!holder->is<NativeObject>()) {
      return false;
    }
    NativeObject* nholder = &holder->as<NativeObject>();
    // Canonical numeric index string on a typed array: uncacheable (see
    // NightPopulateInlineGetIC).
    if (nholder->is<TypedArrayObject>() && ToTypedArrayIndex(id).isSome()) {
      return false;
    }
    // A resolve hook only blocks the ABSENT cache if it could resolve THIS
    // id (mirrors CacheIR): Function's length/name, the global's standard
    // classes. Classes with a resolve hook but no mayResolve stay blocked.
    sawResolveHook |=
        ClassMayResolveId(cx->names(), nholder->getClass(), id, nholder);
    mozilla::Maybe<PropertyInfo> prop = nholder->lookupPure(id);
    if (prop.isSome()) {
      if (hops == 0) {
        return false;  // own property: the mono/mega path serves it.
      }
      // A hop below the holder whose class could resolve `id` lazily (a
      // function's `name`) would define it there on the engine's lookup
      // without changing the receiver's shape; the cached holder is wrong.
      if (sawResolveHook) {
        return false;
      }
      if (!prop->isDataProperty() || !prop->hasSlot()) {
        return false;
      }
      uint32_t slot = prop->slot();
      uint32_t nfixed = nholder->numFixedSlots();
      uint32_t isDynamic = (slot >= nfixed) ? 1u : 0u;
      uint32_t idx = isDynamic ? (slot - nfixed) : slot;
      *nHopsOut = hops;
      *slotEncOut = NightSlotEnc(isDynamic != 0, idx);
      return true;
    }
    if (!holder->hasStaticPrototype()) {
      return false;
    }
    holder = holder->staticPrototype();
    if (!holder) {
      // MISSING property: every hop's shape (and the receiver's, the entry
      // key) pins its own-property set AND its proto link, so the full-chain
      // guard set proves continued absence -- serve `undefined` with no
      // lookup. Not provable when: a hop's class has a lazy resolve hook
      // (the cache hit would skip materialization -- the global object), or
      // the id is an integer key (dense elements are not shape-pinned).
      if (hops == 0 || sawResolveHook || id.isInt()) {
        return false;
      }
      *nHopsOut = hops;
      *slotEncOut = UINT32_MAX;  // the ABSENT sentinel (see GChainEntry)
      return true;
    }
    if (hops == maxHops) {
      return false;
    }
    if (js::gc::IsInsideNursery(holder)) {
      return false;
    }
    protoPtrs[hops] = uint32_t(reinterpret_cast<uintptr_t>(holder));
    protoShapes[hops] = uint32_t(reinterpret_cast<uintptr_t>(holder->shape()));
    hops++;
  }
}

// Accessor-call cache populate: resolve `id` on the receiver's proto chain
// to a SCRIPTED getter/setter, yielding the guard words the compiled
// accessor arm needs (receiver shape word, holder pointer + shape word,
// callee value). Tenured-only for the cached pointers (the region is
// zeroed on major GC; minor GCs must not be able to move a cached cell).
bool NightPrimeAccessor(JSContext* cx, JSObject* obj, jsid id, bool wantSetter,
                        uint64_t* calleeOut, uint32_t* recvShapeOut,
                        uint32_t* holderPtrOut, uint32_t* holderShapeOut) {
  if (!obj->is<NativeObject>()) {
    return false;
  }
  NativeObject* recv = &obj->as<NativeObject>();
  NativeObject* cur = recv;
  for (int hops = 0; hops < 8; hops++) {
    mozilla::Maybe<PropertyInfo> prop = cur->lookupPure(id);
    if (prop.isSome()) {
      if (!prop->isAccessorProperty()) {
        return false;
      }
      GetterSetter* gs = cur->getGetterSetter(*prop);
      JSObject* fnobj = wantSetter ? gs->setter() : gs->getter();
      if (!fnobj || !fnobj->is<JSFunction>() ||
          !fnobj->as<JSFunction>().hasBaseScript()) {
        return false;
      }
      if (gc::IsInsideNursery(fnobj) || gc::IsInsideNursery(cur)) {
        return false;
      }
      *calleeOut = JS::ObjectValue(*fnobj).asRawBits();
      *recvShapeOut = uint32_t(reinterpret_cast<uintptr_t>(recv->shape()));
      *holderPtrOut = uint32_t(reinterpret_cast<uintptr_t>(cur));
      *holderShapeOut = uint32_t(reinterpret_cast<uintptr_t>(cur->shape()));
      return true;
    }
    JSObject* proto = cur->staticPrototype();
    if (!proto || !proto->is<NativeObject>()) {
      return false;
    }
    cur = &proto->as<NativeObject>();
  }
  return false;
}

// Inline SetProp IC populate. Cacheable iff `id` is an OWN writable data
// slot on the receiver (so the inline hit path can write it directly, guarded
// only by the receiver shape -- the holder IS the receiver). Returns the
// receiver shape (low 32), the W1-encoded slot for the store address
// (`bit1`=dynamic, `bits[31:2]`=index), and the ABSOLUTE slot index for the
// store-buffer post-write barrier edge (the `SlotsEdge` start is
// slot-span-relative). A non-own / accessor / non-writable / not-yet-present
// property leaves the way empty (stays on the miss path -- SetProp on a proto
// creates an own property, which the generic path handles and which then
// becomes cacheable at the new shape). Leaf.
bool NightPopulateInlineSetIC(JSContext* cx, JSObject* obj, jsid id,
                              uint32_t* recvShapeOut, uint32_t* slotEncOut,
                              uint32_t* absSlotOut, uint32_t* reasonOut) {
  *reasonOut = 0;
  if (!obj->is<NativeObject>()) {
    *reasonOut = 1;
    return false;
  }
  NativeObject* nobj = &obj->as<NativeObject>();
  if (js::Watchtower::watchesPropertyValueChange(nobj)) {
    *reasonOut = 2;
    return false;
  }
  mozilla::Maybe<PropertyInfo> prop = nobj->lookupPure(id);
  if (prop.isNothing()) {
    *reasonOut = 3;
    return false;
  }
  if (!prop->isDataProperty() || !prop->hasSlot() || !prop->writable()) {
    *reasonOut = 4;
    return false;
  }
  uint32_t slot = prop->slot();
  uint32_t nfixed = nobj->numFixedSlots();
  uint32_t isDynamic = (slot >= nfixed) ? 1u : 0u;
  uint32_t idx = isDynamic ? (slot - nfixed) : slot;
  *recvShapeOut = uint32_t(reinterpret_cast<uintptr_t>(nobj->shape()));
  *slotEncOut = NightSlotEnc(isDynamic != 0, idx);
  *absSlotOut = slot;
  return true;
}

}  // namespace night
}  // namespace js

#endif  // ENABLE_JS_NIGHTMONKEY
