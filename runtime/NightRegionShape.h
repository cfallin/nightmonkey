/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80: */

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
  /* A context's value stack (NightStack.h): a region of 1 << this many   */   \
  /* bytes, aligned to its size, so compiled code tests a frame's fit by  */   \
  /* whether its last byte shares the frame base's high bits.             */   \
  _(valueStackLog2, 21)                                                        \
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
  _(builtinCellCount, 30)                                                      \
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
  /* Inline string block, right after the args metadata: [emptyString @0, */  \
  /* string nursery header @4, its alloc site's count address @8, the    */  \
  /* guarded-chain table's address @12, &MapObject::class_ @16, unused   */  \
  /* @20..@28, stamp-epoch                                                */  \
  /* address @28, unused (0) @32,                                         */  \
  /* &PlainObject::class_ @36]. The header word is 0 while the zone does  */  \
  /* not allocate strings in the nursery; the runtime refreshes it after  */  \
  /* every GC, the only place the zone's flag moves.                      */  \
  _(strlitBlockBytes, 56)                                                      \
  _(strlitEmptyStringOff, 0)                                                   \
  _(strlitStrHeaderOff, 4)                                                     \
  _(strlitStrCountAddrOff, 8)                                                  \
  _(strlitGchainAddrOff, 12)                                                   \
  _(strlitMapClassOff, 16)                                                     \
  /* The guarded-chain GET table (its address in the strlit block):        */  \
  /* (shape, atom)-hashed as the mega table, rows [shape @0, atomId @4,     */  \
  /* nHops @8, slotEnc @12, protoPtr[4] @16, protoShape[4] @32]; a hit      */  \
  /* checks every hop's live shape, then reads the last hop's slot or       */  \
  /* serves undefined for the absent slotEnc.                               */  \
  _(gchainSize, 4096)                                                          \
  _(gchainEntryBytes, 48)                                                      \
  _(gchainMaxHops, 4)                                                          \
  _(gchainNhopsOff, 8)                                                         \
  _(gchainSlotEncOff, 12)                                                      \
  _(gchainProtoPtrOff, 16)                                                     \
  _(gchainProtoShapeOff, 32)                                                   \
  /* A get row's slotEnc for a proven absence (kNightSlotEncAbsent).        */  \
  _(icSlotEncAbsent, 4294967295)                                               \
  /* The receiver key a get row holds for a primitive (whose lookup starts */  \
  /* at its prototype): never a shape pointer (8-aligned), an empty row    */  \
  /* (0) or the set sites' poly sentinel (1).                              */  \
  _(icPrimNumberShape, 2)                                                      \
  _(icPrimBooleanShape, 3)                                                     \
  _(icPrimStringShape, 6)                                                      \
  _(strlitStampEpochAddrOff, 28)                                               \
  _(strlitEnumeratorsOff, 32)                                                  \
  _(strlitPlainClassOff, 36)                                                   \
  /* A regexp exec/test with no match, decided in compiled code (MIR's     */  \
  /* regexp arm): the shape of an optimizable RegExpObject (armed by the  */  \
  /* leaf, zeroed with the movable caches), the address of the realm's     */  \
  /* optimizeRegExpPrototypeFuse word, and the regex-leaf block's address. */  \
  _(strlitRegExpShapeOff, 40)                                                  \
  _(strlitRegExpFuseAddrOff, 44)                                               \
  _(strlitRegexLeafOff, 48)                                                    \
  /* MIR's element-add arm (`props[name] = v` adding `name`): the table's  */  \
  /* address. Rows are direct-mapped on (old shape, atomPtr | 1) as the     */  \
  /* global add table, each a site add-transition row (inlineIcTransBytes) */  \
  /* then the key; filled where night_runtime_set_element learns or replays */  \
  /* an add, zeroed with the movable caches.                                */  \
  _(strlitElemAddOff, 52)                                                      \
  _(elemAddRows, 1024)                                                         \
  _(elemAddRowBytes, 64)                                                       \
  _(elemAddKeyOff, 48)                                                         \
  /* The regex-leaf block (NightRuntimeData::regexLeaf): [btStack @0]      */  \
  /* [btElems @4] [output pairs @8, regexLeafMaxPairs * 8 bytes] [rows]:   */  \
  /* per RegExpShared (direct-mapped by its address >> 4), [shared @0]     */  \
  /* [latin1 matcher @4] [two-byte matcher @8] [pad], wasm table indices.  */  \
  _(regexLeafRows, 64)                                                         \
  _(regexLeafRowBytes, 16)                                                     \
  _(regexLeafMaxPairs, 8)                                                      \
  _(regexLeafBtStackOff, 0)                                                    \
  _(regexLeafBtElemsOff, 4)                                                    \
  _(regexLeafPairsOff, 8)                                                      \
  _(regexLeafRowsOff, 72)                                                      \
  /* Math native-pointer slots (gEnv.mathNativesPtr), 4 bytes per MN_*.    */  \
  _(mathNativeSlots, 16)                                                       \
  /* Inline-alloc and construct cell rows: the compiler sizes the regions  */  \
  /* from these and bakes the field offsets; NightInlineHeap.cpp asserts    */ \
  /* its structs against them. (The call, intrinsic and inline-of cell rows */ \
  /* are written only by compiled code and read back only by it, so their   */ \
  /* sizes are not shared and stay in translate.rs.)                        */ \
  _(allocCellBytes, 32)                                                        \
  _(constructCellBytes, 56)                                                    \
  /* Per-binding value-fuse cells (gGlobalVals, after the slot rows):      */  \
  /* [bits u64 @0][fuse word u32 @8][pad]. Fuse states: 0 unarmed, 1       */  \
  /* armed (bits are the value), 2 blown, 3 armed with the binding's       */  \
  /* predicted function (a compiled function of the script the binding    */  \
  /* table names). Armed is bit 0.                                         */  \
  _(bindingCellBytes, 16)                                                      \
  _(bindingCellFuseOff, 8)                                                     \
  _(bindingFuseArmed, 1)                                                       \
  _(bindingFuseBlown, 2)                                                       \
  _(bindingFusePredicted, 3)                                                   \
  /* Predicted-method cells (gEnv.methodCellsPtr): [proto u32 @0][pad]     */  \
  /* [fn bits u64 @8]. Armed: proto is the receivers' prototype through    */  \
  /* which the name resolves to fn, a compiled function of the predicted   */  \
  /* script held by a constant (ObjectFuse) property. 0 unarmed, 1 not     */  \
  /* armable until a GC.                                                   */  \
  _(methodCellBytes, 16)                                                       \
  _(methodCellFnOff, 8)                                                        \
  _(methodCellPoison, 1)

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
static_assert(Night_strlitEnumeratorsOff + 4 <= Night_strlitBlockBytes,
              "the active-iterator list address must fit the strlit block");
static_assert((Night_bindingFuseArmed & 1) && (Night_bindingFusePredicted & 1) &&
                  !(Night_bindingFuseBlown & 1),
              "a binding fuse is armed exactly when bit 0 is set");
static_assert(Night_strlitRegexLeafOff + 4 <= Night_strlitBlockBytes &&
                  Night_strlitBlockBytes % 8 == 0,
              "the regexp words must fit the (8-aligned) strlit block");
static_assert(Night_strlitElemAddOff + 4 <= Night_strlitBlockBytes,
              "the element-add table's address must fit the strlit block");
static_assert(Night_elemAddKeyOff >= Night_inlineIcTransBytes &&
                  Night_elemAddKeyOff + 4 <= Night_elemAddRowBytes &&
                  (Night_elemAddRows & (Night_elemAddRows - 1)) == 0,
              "an element-add row is a transition row, then its key");
static_assert(Night_regexLeafRowsOff ==
                  Night_regexLeafPairsOff + 8 * Night_regexLeafMaxPairs,
              "the regex-leaf rows follow the output pairs");
static_assert((Night_regexLeafRows & (Night_regexLeafRows - 1)) == 0,
              "the regex-leaf rows are a power of two");
static_assert(Night_strlitPlainClassOff + 4 <= Night_strlitBlockBytes,
              "the plain-object class must fit the strlit block");
static_assert(Night_strlitMapClassOff + 4 <= Night_strlitStampEpochAddrOff,
              "the strlit host words must not overlap the epoch address");

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
