/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! The byte layouts the emitted code addresses: SpiderMonkey's own object
//! representation, the compiler's reserved-region row formats, and the small
//! integer codes the runtime helpers take as arguments.
//!
//! Every constant here is half of a contract with something outside this
//! crate -- the engine's C++ headers, `NightRuntime.cpp`, or the environment
//! layout in `wasm/mod.rs` -- so none of them is a tuning knob. Changing one
//! without changing its other half miscompiles silently: the emitted code
//! loads the right address of the wrong field.
//!
//! Offsets are byte offsets from the start of the named structure unless the
//! name says `_BACK`, which counts backwards from a header's end.

// --- JS::Value ------------------------------------------------------------
//
// The nunbox32 tags and magic payloads live in translate.rs and are imported
// through `bbv::*`. What is here is the boundary the two halves of a boxed
// value are separated at.

/// Tag values at or above this are GC things (the tag half of a nunbox32
/// `JS::Value`, compared as a u32). Below it are the immediates.
pub(super) const VAL_GCTHING_TAG_MIN: u32 = 0xFFFF_FF86;

// --- JSObject / NativeObject ----------------------------------------------
//
//   +0   Shape*                    every object
//   +4   likely-class word         the night stamp (identity half u16, then
//                                  the flags half below)
//   +8   slots_       (NativeObject) dynamic slot vector
//   +12  elements_    (NativeObject) dense element vector
//   +16  fixed slots  (NativeObject) inline JS::Value slots
//
// Slots +8 and the fixed-slot base +16 are only meaningful once the object
// is proven native (`SHAPE_IS_NATIVE_BIT`); a proxy or WasmGC object stores
// unrelated fields there.

pub(crate) const SHAPE_OFFSET: u32 = 0;
pub(super) const OBJ_CLASS_IDX_OFFSET: u32 = 4;
pub(super) const OBJ_SLOTS_OFFSET: u32 = 8;
pub(super) const OBJ_ELEMENTS_OFFSET: u32 = 12;
pub(super) const FIXED_SLOTS_BASE: u32 = 16;
/// `slots_` again, reached from a `NativeObject*` in the slot-address
/// decoder rather than from the object header walk.
pub(super) const NATIVE_SLOTS_OFFSET: u32 = 8;

// --- the likely-class (stamp) word ----------------------------------------
//
// One u32 at `OBJ_CLASS_IDX_OFFSET`, read as two halves:
//
//   bits  0..15   identity: the layout key, +1-biased (0 = unstamped)
//   bit   16      TYPES/SHALLOW  every masked field holds a value of its mask
//   bit   17      SLOTS          the static slot predictions hold
//   bits  18..29  the predicted alloc site's early class key, while the
//                 CONSTRUCTING sentinel is set
//   bit   30      RANGES         the predicted field value ranges hold
//   bit   31      CONSTRUCTING sentinel
//
// TYPES, SLOTS and RANGES keep the same bit positions in both phases (during
// construction, under the sentinel, and after the ctor-exit stamp), which is
// what lets one guard form serve both.

/// The flags half, as a u16 at offset 6 -- the same bits as `CLASS_WORD_*`
/// shifted down 16, for the arms that load only the half they test.
pub(super) const OBJ_CLASS_FLAGS_OFFSET: u32 = 6;
pub(crate) const CLASS_WORD_SHALLOW: u32 = 0x0001_0000;
pub(super) const CLASS_WORD_SLOTS: u32 = 0x0002_0000;
/// The predicted VALUE RANGES of the layout's masked fields hold. Unlike
/// TYPES -- whose engine-wide claim is only numberness, with the finer mask
/// re-checked at every load -- this one is consumed checklessly, so it gets a
/// bit of its own that every unchecked write drops. It sits at the TOP of the
/// early-key region rather than beside SLOTS so the engine choke's
/// unconditional clear can never corrupt a key mid-construction; the key gave
/// up its 13th bit for it.
pub(crate) const CLASS_WORD_RANGES: u32 = 0x4000_0000;
pub(super) const CLASS_WORD_SENTINEL: u32 = 0x8000_0000;
/// Post-stamp reuse of the lowest early-key bit (the key space is dead
/// once the idx is stamped): an unpredicted-key add landed BEYOND the
/// object's own layout length, so its own prefix predictions still hold
/// (slots assign sequentially) but the bit history no longer certifies a
/// clump-sibling's extension -- the prefix-advance restamp declines on
/// it. Set only on stamped (non-sentinel) words; while the sentinel is
/// up this bit is part of the early key.
pub(super) const CLASS_WORD_ADV_INELIGIBLE: u32 = 0x0004_0000;
pub(super) const EARLY_KEY_SHIFT: u32 = 18;
pub const EARLY_KEY_MAX: u32 = 0x0FFF;

// --- Shape / BaseShape / JSClass ------------------------------------------
//
//   Shape      +0  BaseShape*
//              +4  immutableFlags: isNative at bit 4, numFixedSlots at
//                  bits 6..10, slotSpan at bits 11..20
//   BaseShape  +0  const JSClass*
//              +8  TaggedProto (the object's [[Prototype]])
//   JSClass    +4  flags

pub(super) const SHAPE_BASESHAPE_OFFSET: u32 = 0;
pub(crate) const SHAPE_IMMUTABLE_FLAGS_OFFSET: u32 = 4;
pub(super) const SHAPE_IS_NATIVE_BIT: u32 = 1 << 4;
pub(crate) const SHAPE_FIXED_SLOTS_SHIFT: u32 = 6;
pub(crate) const SHAPE_FIXED_SLOTS_MASK_BITS: u32 = 0x1f;
pub(super) const SHAPE_SMALL_SLOTSPAN_SHIFT: u32 = 11;
pub(super) const SHAPE_SMALL_SLOTSPAN_MASK_BITS: u32 = 0x3ff;
pub(super) const BASESHAPE_CLASP_OFFSET: u32 = 0;
pub(super) const BASESHAPE_PROTO_OFFSET: u32 = 8;
pub(super) const CLASP_FLAGS_OFFSET: u32 = 4;
pub(super) const JSCLASS_EMULATES_UNDEFINED: u32 = 1 << 6;

// --- ObjectElements -------------------------------------------------------
//
// `elements_` points PAST the header, at element 0, so the header fields are
// addressed backwards from it:
//
//   [-16] flags   [-12] initializedLength   [-8] capacity   [-4] length
//   [  0] element 0 ...

pub(super) const ELEMENTS_HEADER_BYTES: u32 = 16;
pub(super) const ELEMENTS_FLAGS_BACK: u32 = 16;
pub(super) const ELEMENTS_INITLEN_BACK: u32 = 12;
pub(super) const ELEMENTS_CAPACITY_BACK: u32 = 8;
pub(super) const ELEMENTS_LENGTH_BACK: u32 = 4;
pub(super) const ELEMENTS_FLAG_FIXED: u32 = 0x1;
pub(super) const ELEMENTS_FROZEN_FLAG: u32 = 0x40;
pub(super) const ELEMENTS_NON_PACKED_FLAG: u32 = 0x80;
/// Any of these set means the dense append arm must bail to the helper.
pub(super) const ELEMENTS_PUSH_BAIL_MASK: u32 = 0x72;

// --- TypedArrayObject -----------------------------------------------------
//
// The length and the data pointer are boxed values in fixed slots 1 and 3.

pub(super) const TA_LENGTH_PAYLOAD_OFFSET: u32 = FIXED_SLOTS_BASE + 8;
pub(super) const TA_DATA_PAYLOAD_OFFSET: u32 = FIXED_SLOTS_BASE + 8 * 3;

// --- JSString -------------------------------------------------------------
//
//   +0  flags     ATOM at bit 3, LINEAR at bit 4, INLINE_CHARS at bit 6,
//                 LATIN1_CHARS at bit 10
//   +4  length
//   +8  chars pointer, or the first inline char when INLINE_CHARS is set

pub(super) const STRING_FLAGS_OFFSET: u32 = 0;
pub(super) const STRING_LENGTH_OFFSET: u32 = 4;
pub(super) const STRING_CHARS_OFFSET: u32 = 8;
/// `JSString::ATOM_BIT` -- atoms are deduped, so two atoms compare by
/// pointer.
pub(super) const STRING_ATOM_BIT: u32 = 1 << 3;
pub(super) const STRING_LINEAR_BIT: u32 = 1 << 4;
pub(super) const STRING_INLINE_CHARS_BIT: u32 = 1 << 6;
pub(super) const STRING_LATIN1_CHARS_BIT: u32 = 1 << 10;

// --- JSFunction / BaseScript ----------------------------------------------
//
// A JSFunction's own fields live in its fixed slots:
//
//   +16 flags   +24 environment   +32 BaseScript* (when FLAGS_BASESCRIPT)
//
// and the compiled-body index the classify resolves to is a field the night
// build adds to BaseScript.

pub(super) const FUNC_FLAGS_SLOT_OFFSET: u32 = 16;
pub(super) const FUNC_ENV_SLOT_OFFSET: u32 = 24;
pub(super) const FUNC_SCRIPT_SLOT_OFFSET: u32 = 32;
pub(super) const FUNCTION_FLAGS_BASESCRIPT: u32 = 1 << 5;
pub(super) const FUNCTION_FLAGS_CONSTRUCTOR: u32 = 1 << 8;
pub(super) const FUNCTION_KIND_MASK: u32 = 0x0007;
pub(super) const FUNCTION_KIND_CLASS_CTOR: u32 = 3;
pub(super) const BASESCRIPT_NIGHTFUNCINDEX_OFFSET: u32 = 56;

// --- JSContext and the GC ------------------------------------------------
//
//   JSContext  +84 Zone*    +88 Realm*
//   Zone       +8  needsIncrementalBarrier
//   Realm      +72 global object
//   Chunk      +0  StoreBuffer*, found by masking a pointer down to its
//                  1 MiB chunk base
//
// Nursery allocations carry an 8-byte header before the object.

pub(super) const JSCONTEXT_ZONE_OFFSET: u32 = 84;
pub(super) const JSCONTEXT_REALM_OFFSET: u32 = 88;
pub(super) const ZONE_NEEDS_BARRIER_OFFSET: u32 = 8;
pub(super) const REALM_GLOBAL_OFFSET: u32 = 72;
pub(super) const NOT_CHUNK_MASK: u32 = !0xF_FFFF;
pub(super) const CHUNK_STORE_BUFFER_OFFSET: u32 = 0;
pub(super) const NURSERY_HEADER_BYTES: u32 = 8;

// --- the compiled frame ---------------------------------------------------

/// The frame's fixed head, in bytes: the callee slot and `this`. The formals
/// follow it, one boxed Value each, then the locals.
pub(super) const FRAME_ARGS_OFFSET: u32 = 16;

/// `Bbv::frame_stale` key bit for a formal (`STALE_ARG | argno`); the rest
/// of the space is local numbers.
pub(super) const STALE_ARG: u32 = 1 << 31;
/// Carried-key bit for a raw carrier of the PARENT frame's local riding
/// through an inline segment (`OUTER_LOCAL | localno`): the value stays in
/// SSA across the splice instead of a boxed store at the seam and a load
/// at the return. Immune to the callee's GCs by repr, invisible to the
/// callee (caller slots are private), handed back as a plain carrier on
/// the return edge, and flushed to its slot at any edge that drops it.
pub(super) const OUTER_LOCAL: u32 = 1 << 30;

// --- the sig2 return flags word -------------------------------------------
//
// Bits set = effects happened, so ORs accumulate and gen_only bodies return
// all-set. No GC bit by design: rooting stays static and may-GC is never a
// fact kill, so the word is mutation-only.

/// Wrote only through the body's own `this`.
pub(super) const FLAG_MUT_THIS: u32 = 1;
/// Any other heap mutation.
pub(super) const FLAG_MUT_OTHER: u32 = 2;
/// May have demoted or rewritten an EXISTING object's stamp (class-word
/// claim bits): set by every store arm that emits a demote path against a
/// non-fresh receiver, by restamps, and by saturation. MUT bits without
/// this bit mean "heap written, but every stamp-guarded fact still holds"
/// -- most root-attributed Dirty mass rejoins Opt through the fork's
/// keep-facts arm.
pub(super) const FLAG_STAMPS: u32 = 4;
/// Wrote a global binding (any `SetGName`-family store, inline or generic):
/// the kill signal for the per-binding value facts (`Ctx::gcells`), which
/// no stamp and no epoch can see -- a binding is a slot of the global
/// object, not a claimed class layout.
pub(super) const FLAG_BIND: u32 = 8;
pub(super) const FLAGS_ALL: u32 = FLAG_MUT_THIS | FLAG_MUT_OTHER | FLAG_STAMPS | FLAG_BIND;

// --- reserved-region cells the emitter addresses --------------------------
//
// Each of these is a row in a reserved linear-memory region (DESIGN.md
// section 8.5). The emitter cannot know the region base while it is building
// a body, so it emits the `*_ADDR_PLACEHOLDER` constant and records the row
// index; `wasm/mod.rs` rewrites the constant once the layout is fixed. The
// placeholder values are arbitrary but must stay distinct, because that is
// what makes an unpatched one findable in the output.

/// Per-site callee value cell: `[callee_bits i64][funcidx i32][script i32]`.
pub(super) const CALL_CELL_FUNCIDX: u32 = 8;
pub(super) const CALL_CELL_SCRIPT: u32 = 12;
pub(super) const CALL_CELL_ADDR_PLACEHOLDER: u32 = 0xDEAD_BEE0;

/// Per-site construct cell: the first 20 bytes mirror the call cell, then
/// `[ctorShape u32][gen u32][protoPtr u32][protoSlotEnc u32]`.
pub(super) const CONSTRUCT_CELL_CTORSHAPE: u32 = 20;
pub(super) const CONSTRUCT_CELL_GEN: u32 = 24;
pub(super) const CONSTRUCT_CELL_PROTOPTR: u32 = 28;
pub(super) const CONSTRUCT_CELL_PROTOSLOTENC: u32 = 32;
pub(super) const CONSTRUCT_CELL_ADDR_PLACEHOLDER: u32 = 0xDEAD_C000;

/// Base of the per-funcidx ctor-nslots region (u32 per funcref-table index,
/// 0 = unknown), patched by `translate_all` once table placement is done. An
/// unresolved construct site's fast arm indexes it with the classified
/// funcidx so `night_runtime_create_this` (and thus the construct cell it
/// primes) sizes `this` for the ctor's full layout. Sizing it generically
/// instead lands the ctor's later fields in dynamic slots, which defeats
/// every fixed-slot-only inline set arm downstream -- the whole field-init
/// sequence falls back to the set-miss helper.
pub(super) const NSLOTS_REGION_PLACEHOLDER: u32 = 0xDEAD_D000;

/// Instanceof cell: `[funShape u32][gen u32][slotenc u32]`. Must match
/// `NightRuntime.cpp`'s `populate`.
pub(super) const IOF_CELL_GEN: u32 = 4;
pub(super) const IOF_CELL_SLOTENC: u32 = 8;
pub(super) const IOF_CELL_ADDR_PLACEHOLDER: u32 = 0xDEAD_BF80;

pub(super) const ALLOC_CELL_ADDR_PLACEHOLDER: u32 = 0xDEAD_BF00;
pub(super) const INTRINSIC_CELL_ADDR_PLACEHOLDER: u32 = 0xDEAD_C100;

// --- the property inline caches -------------------------------------------
//
// One row per property site, `INLINE_IC_STRIDE` bytes:
//
//   +0                   the inline ways, INLINE_IC_WAY_BYTES each
//   +IC_TRANS_ROW_OFF    the add-transition row, IC_TRANS_ROW_BYTES
//
// A way is read differently by the get and set sides, which is why the two
// have separate offset names over the same bytes:
//
//   get  +0 recvShape  +4 own fixed-slot byte offset (0 = use the tail)
//        +8 holderPtr  +12 holderShape  +16 slotEnc
//   set  +0 recvShape                   +8 slotEnc  +12 absSlot
//
// The region is GC-zeroed, so there are no generation checks: a zeroed row
// matches no live shape.
//
// A GET site has `INLINE_IC_WAYS` ways, filled first-come by the miss
// helper (`NoteGetWay`, NightRuntime.cpp): the inline arm compares the
// receiver's shape against each in turn and every way shares one fast arm
// and one holder tail, the matched way's address travelling as a block
// parameter. A receiver past the last way goes to `night_ic_get`, which
// walks the ways again and then the global mega table. Several ways matter:
// with a single way, a two-shape site would be a call plus a hash on every
// access.
// A SET site uses way 0 alone; `recvShape == IC_POLY_SENTINEL` there
// means the site went polymorphic and the store probes the mega set table.
//
// The add-transition row replays one shape transition inline:
//
//   +0 oldShape  +4 newShape  +8 slotOff  +12 absSlot
//   +16 proto0 [ptr u32, shape u32] ... +40 proto3
//
// `IC_TRANS_PROTO_HOPS` rows are recorded; the inline arm validates the first
// `IC_TRANS_INLINE_HOPS` and requires the rest empty (see the hop-count note
// in `emit_set_prop_ic_inline`).

pub(super) use crate::region_shape::{INLINE_IC_WAYS, INLINE_IC_WAY_BYTES};
pub(super) const IC_TRANS_ROW_OFF: u32 = INLINE_IC_WAYS * INLINE_IC_WAY_BYTES;
pub(super) use crate::region_shape::INLINE_IC_TRANS_BYTES as IC_TRANS_ROW_BYTES;
pub(super) const INLINE_IC_STRIDE: u32 = IC_TRANS_ROW_OFF + IC_TRANS_ROW_BYTES;
const _: () = assert!(INLINE_IC_STRIDE == crate::region_shape::INLINE_IC_STRIDE);
pub(super) const IC_WAY_ADDR_PLACEHOLDER: u32 = 0xDEAD_C200;

pub(super) const IC_WAY_RECVSHAPE: u32 = 0;
pub(super) const IC_WAY_MONO_OFF: u32 = 4;
pub(super) const IC_WAY_HOLDERPTR: u32 = 8;
pub(super) const IC_SET_RECVSHAPE: u32 = 0;
pub(super) const IC_SET_SLOTENC: u32 = 8;
pub(super) const IC_SET_ABSSLOT: u32 = 12;
pub(super) const IC_POLY_SENTINEL: u32 = 1;

pub(super) const IC_TRANS_OLDSHAPE: u32 = 0;
pub(super) const IC_TRANS_NEWSHAPE: u32 = 4;
pub(super) const IC_TRANS_SLOTOFF: u32 = 8;
pub(super) const IC_TRANS_ABSSLOT: u32 = 12;
/// First proto row; row `n` is at `IC_TRANS_PROTO0 + 8 * n`, holding the
/// proto pointer then the shape it was validated against.
pub(super) const IC_TRANS_PROTO0: u32 = 16;
pub(super) const IC_TRANS_PROTO_ROW_BYTES: u32 = 8;
/// Proto rows the runtime records.
pub(super) const IC_TRANS_PROTO_HOPS: u32 = 4;
/// Proto rows the inline replay arm validates; deeper rows must be empty or
/// the arm falls to the helper, which replays against all of them.
pub(super) const IC_TRANS_INLINE_HOPS: u32 = 2;

/// A stamping ctor's proto-proof cell (one IC row, see `Bbv::proto_on`):
/// the root `this` the proof was minted on, then the `IC_TRANS_INLINE_HOPS`
/// proto shape words its replay validated live.
pub(super) const PROTO_CELL_RECV: u32 = 0;
pub(super) const PROTO_CELL_SHAPE0: u32 = 4;

// --- the global megamorphic tables ----------------------------------------
//
// Direct-mapped, power-of-two, GC-zeroed; the probe hashes (shape, atom).
//
//   get  +0 shape  +4 atom  +8 holderPtr  +12 holderShape  +16 slotEnc
//   set  +0 shape  +4 atom  +8 slotEnc    +12 absSlot

/// The (shape, atom) key, at the same offsets in both tables -- which is
/// what lets one probe emitter serve both.
pub(super) use crate::region_shape::{MEGA_ATOM_OFF as MEGA_ATOM, MEGA_SHAPE_OFF as MEGA_SHAPE};

// The get side's size/stride/holder offsets live in `translate`, next to
// `build_ic_get_helper`: the get probe is emitted once into `night_ic_get`
// rather than inlined at each site, so nothing here reads them.

pub(super) use crate::region_shape::{
    MEGA_SET_ABS_SLOT_OFF as MEGA_SET_ABSSLOT, MEGA_SET_ENTRY_BYTES, MEGA_SET_SIZE,
    MEGA_SET_SLOT_ENC_OFF as MEGA_SET_SLOTENC,
};

// --- helper-ABI argument codes --------------------------------------------
//
// Small integers the generic runtime helpers switch on. They are an ABI with
// `NightRuntime.cpp`, not an internal enum, which is why they are plain
// constants rather than a Rust `enum`.

/// `InitProp`/`InitElem` attribute selector.
pub(super) const INIT_ATTR_ENUMERATE: u32 = 0;
pub(super) const INIT_ATTR_HIDDEN: u32 = 1;
pub(super) const INIT_ATTR_LOCKED: u32 = 2;

/// Operation selector for the generic boxed binop helper.
pub(super) const BINOP_SUB: u32 = 0;
pub(super) const BINOP_MUL: u32 = 1;
pub(super) const BINOP_DIV: u32 = 2;
pub(super) const BINOP_MOD: u32 = 3;
pub(super) const BINOP_BITOR: u32 = 4;
pub(super) const BINOP_BITAND: u32 = 5;
pub(super) const BINOP_BITXOR: u32 = 6;
pub(super) const BINOP_LSH: u32 = 7;
pub(super) const BINOP_RSH: u32 = 8;
pub(super) const BINOP_URSH: u32 = 9;
pub(super) const BINOP_INC: u32 = 10;
pub(super) const BINOP_DEC: u32 = 11;
pub(super) const BINOP_BITNOT: u32 = 12;

/// Operation selector for the generic boxed compare helper.
pub(super) const CMP_LT: u32 = 0;
pub(super) const CMP_LE: u32 = 1;
pub(super) const CMP_GT: u32 = 2;
pub(super) const CMP_GE: u32 = 3;
pub(super) const CMP_EQ: u32 = 4;
pub(super) const CMP_NE: u32 = 5;
pub(super) const CMP_STRICTEQ: u32 = 6;
pub(super) const CMP_STRICTNE: u32 = 7;

/// Sentinel `ctor_nslots` value: the ctor's layout is unknown, so
/// `create_this` sizes generically.
pub(super) const NO_NSLOTS: u32 = 0xFFFF_FFFF;
