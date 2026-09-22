/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80: */

// The likely-class word NightMonkey keeps in the engine's per-object
// external word (JSObject::externalWord, js/ExternalCompilerHooks.h):
// u16 stamped layout idx (low) + u16 flags half. Flags half: bit 0 (word
// 0x00010000) = TYPES (every masked layout field holds a value of its
// mask), bit 1 (0x00020000) = SLOTS (the static slot predictions are valid
// for this object; cleared only by add mismatches and delete/dictionary
// paths), bit 14 (0x40000000) = RANGES, bit 15 = CONSTRUCTING sentinel,
// bits 2..13 = the alloc site's early class key while the sentinel is set.
//
// The engine resets the word on any structural change and applies the
// store masks below on engine-path slot stores; NightHooks.cpp turns those
// notifications into epoch bumps. The helpers here are the runtime's own
// writes of the word.

#ifndef night_runtime_NightObjectWord_h
#define night_runtime_NightObjectWord_h

#include <stdint.h>

#include "vm/JSObject.h"

namespace js {

// Monotone stamp-invalidation epoch: advanced by every action that demotes
// or rewrites an EXISTING object's class word (claim-bit clears, restamps,
// full clears). Fresh-object stamping does not advance it. An unchanged
// epoch across a call proves every stamp-guarded fact the caller held still
// holds; compiled census builds advance it through the census helper for
// the inline demote arms.
extern uint64_t gNightStampEpoch;

// Bump-site census hook: called on every ACTUAL epoch bump with the path
// that performed it and the class word being demoted. Records into the
// runtime census (kind 66, id = (site << 16) | class idx) when a census
// module is running; near-free otherwise. Implemented in NightRuntime.cpp.
void NightNoteEpochBump(uint32_t site, uint32_t oldWord);

namespace night {

namespace NightBumpSite {
// Engine structural-change paths (JS::ExternalObjectMutation).
static constexpr uint32_t ToDictionary = 1;
static constexpr uint32_t ChangeProperty = 2;
static constexpr uint32_t ChangeCustomDataProp = 3;
static constexpr uint32_t RemoveProperty = 4;
static constexpr uint32_t FreezeOrSeal = 5;
static constexpr uint32_t ObjectSwap = 6;
// Engine value-store choke (the setSlot/initSlot flavors).
static constexpr uint32_t StoredValue = 7;
// NightSetClassWord overwriting a real prior stamp (ctor restamp).
static constexpr uint32_t ConstructStamp = 9;
// NightClearSlotsBit callers (NightRuntime add-mismatch paths).
static constexpr uint32_t SlotsAddMismatch = 10;
static constexpr uint32_t SlotsAddMismatch2 = 11;
static constexpr uint32_t SlotsAddMismatch3 = 12;
static constexpr uint32_t SlotsAddMismatch4 = 13;
// JSObject::setFlag (object-flag shape change, e.g. a Watchtower watch).
static constexpr uint32_t ObjectFlagChange = 14;
}  // namespace NightBumpSite

static constexpr uint32_t kWordTypes = 0x00010000u;
static constexpr uint32_t kWordSlots = 0x00020000u;
static constexpr uint32_t kWordAdvIneligible = 0x00040000u;
static constexpr uint32_t kWordRanges = 0x40000000u;
static constexpr uint32_t kWordConstructing = 0x80000000u;

// The engine-path store policy (JS::ExternalCompilerHooks store masks).
// TYPES asserts per-field NUMBERNESS and nothing finer: a number store
// through ANY path violates no class's claim and keeps the bit; the finer
// per-field mask survives only because every consumer unboxes through the
// number-tag dispatch, i.e. re-checks the mask at the load. RANGES is
// consumed CHECKLESSLY, so every store through the engine drops it (owner
// ruling 2026-08-16).
static constexpr uint32_t kStoreClearMask = kWordRanges;
static constexpr uint32_t kStoreNonNumberClearMask = kWordTypes;

// Epoch discipline: a demotion bumps the epoch only for a NON-sentinel word.
// A mid-construction object (CONSTRUCTING) has idx 0, so no compiled guard
// can pass on it and no fact anywhere is predicated on its bits -- clearing
// them invalidates nothing. This mirrors the compiled demote arms'
// `demote_delta` exactly.
inline void NightNoteDemotion(uint32_t oldWord, uint32_t site) {
  if (!(oldWord & kWordConstructing)) {
    gNightStampEpoch++;
    NightNoteEpochBump(site, oldWord);
  }
}

// SLOTS-only clear: an add deviated from the clump's slot predictions.
inline void NightClearSlotsBit(JSObject* obj, uint32_t site = 0) {
  uint32_t w = obj->externalWord();
  if (w & kWordSlots) {
    NightNoteDemotion(w, site);
    obj->setExternalWord(w & ~kWordSlots);
  }
}

// Advance-ineligibility marker (bit 18, the lowest early-key bit, dead once
// stamped): an unpredicted-key add landed beyond the object's own layout,
// so its own prefix predictions still hold (SLOTS stays, no epoch bump) but
// the bit history no longer certifies a clump sibling's extension -- the
// prefix-advance restamp declines on it. Only meaningful on a stamped
// (non-sentinel) word.
inline void NightSetAdvIneligible(JSObject* obj) {
  obj->setExternalWord(obj->externalWord() | kWordAdvIneligible);
}

// Construct-time allocation marker without a key: TYPES and RANGES seed
// (their discipline is key-free -- every unchecked write through the engine
// drops them), SLOTS cannot (adds are uncheckable without a layout).
inline void NightSetConstructingSentinel(JSObject* obj) {
  obj->setExternalWord(kWordConstructing | kWordRanges | kWordTypes);
}

// Construct-time allocation word from a resolved `new` site: sentinel +
// early key + optimistic validity bits. The idx half stays 0 -- no
// idx-guarded arm can hit a mid-construction object. A rewrite of a real
// existing stamp invalidates facts about it; the first stamp of a fresh
// object (word 0 or the CONSTRUCTING sentinel) invalidates nothing.
inline void NightSetClassWord(JSObject* obj, uint32_t w, uint32_t site = 0) {
  uint32_t old = obj->externalWord();
  if (old != 0 && !(old & kWordConstructing) && old != w) {
    gNightStampEpoch++;
    NightNoteEpochBump(site, old);
  }
  obj->setExternalWord(w);
}

}  // namespace night
}  // namespace js

#endif  // night_runtime_NightObjectWord_h
