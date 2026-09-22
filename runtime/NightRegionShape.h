/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#ifndef night_runtime_NightRegionShape_h
#define night_runtime_NightRegionShape_h

#include <stdint.h>

namespace js {
namespace night {

// Every entry stride, table size and intra-region offset that compiled code
// and this runtime must agree on, in one place.
//
// NIGHT_ENV_REGIONS (NightEnv.h) carries the region BASES across the wire and
// is checked by construction. What it does not carry is the shape of what
// lives inside a region: a cache's way count and stride, a table's size, the
// byte offset of a slot within the host-constant block. A mismatch in one of
// them is the one silent-miscompile class the everything-is-guarded argument
// does not cover, because the guard itself would read the wrong address.
//
// So this macro is the single source of truth, exactly as NIGHT_ENV_REGIONS
// is for the bases: C++ gets `Night<name>` constants from it below, and
// night-compiler's build.rs parses it into `crate::region_shape`, which is
// where the Rust side's constants come from. Neither side has a literal to
// get wrong.
//
// Values must be plain integer literals (build.rs parses, it does not
// evaluate). Anything derived -- a stride that is ways x way-bytes, a base
// that is another base plus a block size -- is spelled out as a literal here
// and re-derived on both sides behind a static assertion, so the arithmetic
// is checked rather than the result copied.
//
// A change here is an ABI change: bump NightAotAbiVersion.
#define NIGHT_REGION_SHAPE(_)                                                  \
  /* Per-site property IC (gEnv.propicPtr): the inline get ways (a set   */    \
  /* site uses way 0 alone), then the add-transition row. A get receiver  */   \
  /* past the last way is served by the mega table.                       */   \
  _(inlineIcWays, 4)                                                           \
  _(inlineIcWayBytes, 20)                                                      \
  _(inlineIcTransBytes, 48)                                                    \
  _(inlineIcStride, 128)                                                       \
  /* Global megamorphic GET table (gEnv.megaGetPtr): direct-mapped         */  \
  /* [shape, atomId, holderPtr, holderShape, slotEnc, pad].                */  \
  _(megaGetSize, 8192)                                                         \
  _(megaGetEntryBytes, 24)                                                     \
  /* Shape and atomId lead every entry of BOTH mega tables.               */   \
  _(megaShapeOff, 0)                                                           \
  _(megaAtomOff, 4)                                                            \
  /* Global megamorphic SET table (gEnv.megaSetPtr): same hash,            */  \
  /* [shape @0, atomId @4, slotEnc @8, absSlot @12].                       */  \
  _(megaSetSize, 8192)                                                         \
  _(megaSetEntryBytes, 16)                                                     \
  _(megaSetSlotEncOff, 8)                                                      \
  _(megaSetAbsSlotOff, 12)                                                     \
  /* Dense-append cache (gEnv.appendCachePtr): shape-hashed rows           */  \
  /* [shape, protoPtr0, protoShape0, protoPtr1, protoShape1, isArray, x2]. */  \
  _(appendCacheRows, 512)                                                      \
  _(appendCacheRowBytes, 32)                                                   \
  /* Accessor-call cache (gEnv.accessorCachePtr), (shape, atom^kind)-hashed */ \
  _(accessorCacheRows, 2048)                                                   \
  _(accessorCacheRowBytes, 32)                                                 \
  _(accessorCalleeOff, 0)                                                      \
  _(accessorRecvShapeOff, 8)                                                   \
  _(accessorAtomKindOff, 12)                                                   \
  _(accessorHolderPtrOff, 16)                                                  \
  _(accessorHolderShapeOff, 20)                                                \
  /* The host-constant block at gEnv.propicGenPtr. Startup writes these    */  \
  /* words; compiled code loads them at these offsets. Two of the region   */  \
  /* bases below are NOT in the region table -- C++ recomputes them from   */  \
  /* propicGenPtr, which is exactly why the offsets have to be shared.     */  \
  _(hostGenOff, 0)                                                             \
  _(hostStackLimitOff, 4)                                                      \
  _(hostFnClassOff, 8)                                                         \
  _(hostStaticStringsOff, 16)                                                  \
  _(hostAtomTableOff, 20)                                                      \
  _(hostNurseryPosOff, 24)                                                     \
  _(hostNurseryEndOff, 28)                                                     \
  _(hostStrCharCodeAtOff, 32)                                                  \
  _(hostStrCharAtOff, 40)                                                      \
  _(hostStrFromCharCodeOff, 48)                                                \
  _(hostStrCharOpsFuseOff, 56)                                                 \
  _(hostArrayClassOff, 60)                                                     \
  _(hostBuiltinCellsOff, 64)                                                   \
  /* Builtin callee-identity cells, in translate::BC_* order. The count is */  \
  /* what positions everything after them.                                 */  \
  _(builtinCellCount, 27)                                                      \
  _(builtinCellBytes, 8)                                                       \
  /* TA-clasp table, right after the builtin cells: 9 fixed-length         */  \
  /* typed-array class pointers (element kind 1..=9 at index kind-1), 36   */  \
  /* bytes padded to 40; the pad holds the emulates-undefined fuse address.*/  \
  _(taClassBlockBytes, 40)                                                     \
  _(taClassDdaFuseOff, 36)                                                     \
  /* Arguments-object metadata, right after the TA table: [mapped class,   */  \
  /* unmapped class, ArgumentsData::offsetOfArgs(), night dyncode fuse].   */  \
  _(argsClassBlockBytes, 16)                                                   \
  _(argsClassMappedOff, 0)                                                     \
  _(argsClassUnmappedOff, 4)                                                   \
  _(argsClassDataArgsOff, 8)                                                   \
  _(argsDynCodeFuseOff, 12)                                                    \
  /* Inline string-literal block, right after the args metadata:           */  \
  /* [emptyString @0, thin replay triple @4, fat triple @16, stamp-epoch   */  \
  /* address @28, binding-write epoch address @32, pad @36]. The major-GC  */  \
  /* purge zeroes exactly the triples ([@4, @28)): the two epoch addresses */  \
  /* are host constants and must survive it.                               */  \
  _(strlitBlockBytes, 40)                                                      \
  _(strlitEmptyStringOff, 0)                                                   \
  _(strlitTriplesEnd, 28)                                                      \
  _(strlitStampEpochAddrOff, 28)                                               \
  _(strlitBindEpochAddrOff, 32)                                                \
  /* Math native-pointer slots (gEnv.mathNativesPtr), 4 bytes per MN_*.    */  \
  _(mathNativeSlots, 16)                                                       \
  /* Inline-alloc and construct cell rows: the compiler sizes the regions  */  \
  /* from these and bakes the field offsets; NightInlineHeap.cpp asserts    */ \
  /* its structs against them. (The call, intrinsic and inline-of cell rows */ \
  /* are written only by compiled code and read back only by it, so their   */ \
  /* sizes are not shared and stay in translate.rs.)                        */ \
  _(allocCellBytes, 32)                                                        \
  _(constructCellBytes, 40)

#define NIGHT_REGION_SHAPE_CONST(name, value) \
  static constexpr uint32_t Night_##name = (value);
NIGHT_REGION_SHAPE(NIGHT_REGION_SHAPE_CONST)
#undef NIGHT_REGION_SHAPE_CONST

// The derived relationships, checked rather than copied. Each of these is
// also re-derived on the Rust side from the same literals.
static_assert(Night_inlineIcStride ==
                  Night_inlineIcWays * Night_inlineIcWayBytes +
                      Night_inlineIcTransBytes,
              "IC stride must be ways x way bytes plus the transition row");
static_assert(Night_taClassDdaFuseOff + 4 <= Night_taClassBlockBytes,
              "the emulates-undefined fuse address must fit the TA pad");
static_assert(Night_argsDynCodeFuseOff + 4 <= Night_argsClassBlockBytes,
              "the dyncode fuse word must fit the args block");
static_assert(Night_strlitStampEpochAddrOff + 4 <= Night_strlitBlockBytes,
              "the stamp-epoch address must fit the strlit block");
static_assert(Night_strlitBindEpochAddrOff + 4 <= Night_strlitBlockBytes,
              "the binding-epoch address must fit the strlit block");
static_assert(Night_strlitTriplesEnd <= Night_strlitStampEpochAddrOff,
              "the purge must not zero the published epoch addresses");

// The three block bases C++ recomputes off propicGenPtr, in one place so the
// arithmetic exists once. `genBase` is `gEnv.propicGenPtr`.
constexpr uint32_t NightTaClassBase(uint32_t genBase) {
  return genBase + Night_hostBuiltinCellsOff +
         Night_builtinCellBytes * Night_builtinCellCount;
}
constexpr uint32_t NightArgsClassBase(uint32_t genBase) {
  return NightTaClassBase(genBase) + Night_taClassBlockBytes;
}
constexpr uint32_t NightStrLitBase(uint32_t genBase) {
  return NightArgsClassBase(genBase) + Night_argsClassBlockBytes;
}

}  // namespace night
}  // namespace js

#endif /* night_runtime_NightRegionShape_h */
