//! Class words: the allocation-time word a `new` seeds, the bits a
//! constructor's exit stamp keeps, and the restamp arguments of an init
//! delegate. One rule for the MIR and baseline tiers: an object built,
//! stamped or restamped in baseline (after an exit, say) must carry the
//! word MIR's would.

use super::abi::*;
use crate::ids::{ScriptId, Site};
use crate::wasm::translate::{StampCtorIn, TranslateCtx};

/// The construct-time allocation word for a resolved `new` site (see
/// translate.rs `early_stamp_word`): sentinel + early key + all three
/// validity bits seeded optimistically -- construction's checked stores
/// maintain them and the ctor-exit stamp carries forward whichever
/// survived. A key past the early-key space degrades gracefully: no key
/// means the engine add hook cannot check predictions, so SLOTS must not
/// be seeded.
/// `keep_shallow`/`keep_ranges`: seed SHALLOW/RANGES only when the
/// resolved layout has masked fields / range claims -- a vacuous bit
/// protects nothing and turns every engine-path non-number store into a
/// demote-and-epoch-bump (see the exit stamp's matching gate).
fn early_stamp_word(k_plus_1: u32, keep_shallow: bool, keep_ranges: bool) -> u32 {
    let validity = CLASS_WORD_SLOTS
        | if keep_shallow { CLASS_WORD_SHALLOW } else { 0 }
        | if keep_ranges { CLASS_WORD_RANGES } else { 0 };
    if k_plus_1 <= EARLY_KEY_MAX {
        CLASS_WORD_SENTINEL | validity | (k_plus_1 << EARLY_KEY_SHIFT)
    } else {
        CLASS_WORD_SENTINEL | validity
    }
}

/// The ctor full-layout slot count for a `new` at `site` whose likely
/// callee is `mono`, or `NO_NSLOTS` (shared with the baseline tier).
pub(crate) fn construct_nslots(ctx: &TranslateCtx<'_>, mono: Option<ScriptId>, site: Site) -> u32 {
    if let Some(f) = mono {
        if let Some(&n) = ctx.ctor_nslots_in.get(&f) {
            return n;
        }
    }
    if let Some(si) = ctx.construct_sites_in.get(&site) {
        return u32::try_from(si.fields.len()).unwrap().min(16);
    }
    NO_NSLOTS
}

/// The allocation-time class word for a `new` at `site` whose likely
/// callee is `mono` (shared with the baseline tier).
pub(crate) fn construct_alloc_word(ctx: &TranslateCtx<'_>, mono: Option<ScriptId>, site: Site) -> u32 {
    let word_of = |si: &StampCtorIn| {
        early_stamp_word(
            si.layout_id + 1,
            si.masks.iter().any(|m| !m.is_none()),
            si.ranges.iter().any(Option::is_some),
        )
    };
    if let Some(f) = mono {
        if let Some(si) = ctx.stamp_ctors_in.get(&f) {
            return word_of(si);
        }
    }
    if let Some(si) = ctx.construct_sites_in.get(&site) {
        return word_of(si);
    }
    // No key: SLOTS still seeds -- the delegate flows' static add
    // checks maintain it (positions are absolute, so an inconsistent
    // flow self-detects by position mismatch), and every unchecked
    // add path clears it conservatively (engine keyless clear; the
    // compiled runtime form's keyless arm).
    CLASS_WORD_SENTINEL | CLASS_WORD_SHALLOW | CLASS_WORD_SLOTS | CLASS_WORD_RANGES
}

/// TYPES (the SHALLOW bit) where layout `k` predicts a type for any field
/// (`layout_field_types_in`, docs/MIR.md §4.6): what the MIR and baseline
/// tiers' allocations seed and their stamps keep. One rule for both tiers:
/// an object built, stamped or restamped in baseline (after an exit, say)
/// must carry the bit as MIR's would.
pub(crate) fn layout_types_bit(ctx: &TranslateCtx<'_>, k: u32) -> u32 {
    let typed = ctx
        .layout_field_types_in
        .get(&crate::ids::LayoutKey::new(k).stamp())
        .is_some_and(|m| m.values().any(|c| !c.is_none()));
    if typed {
        CLASS_WORD_SHALLOW
    } else {
        0
    }
}

/// Every class whose layout types field `name` (a class word's identity,
/// layout key + 1), with its claim for it, by identity: what a store of
/// the field checks its value against to keep TYPES (the MIR tier's
/// `field_types`, the baseline tier's vouched stores).
pub(crate) fn field_classes(ctx: &TranslateCtx<'_>, name: crate::ids::NameId) -> Vec<(u32, crate::facts::Claim)> {
    let mut v: Vec<(u32, crate::facts::Claim)> = ctx
        .layout_field_types_in
        .iter()
        .filter_map(|(k, row)| {
            let c = *row.get(&name).filter(|c| !c.is_none())?;
            Some((k.get(), c))
        })
        .collect();
    v.sort_by_key(|e| e.0);
    v
}

/// The most classes a store checks its value against by the object's
/// identity (`field_classes`) before it settles for no check.
pub(crate) const MAX_STORE_CLASSES: usize = 8;

/// `construct_alloc_word` for the MIR and baseline tiers: TYPES seeded for
/// a layout that predicts field types (`layout_types_bit`).
pub(crate) fn typed_alloc_word(ctx: &TranslateCtx<'_>, mono: Option<ScriptId>, site: Site) -> u32 {
    let w = construct_alloc_word(ctx, mono, site);
    let si = mono
        .and_then(|f| ctx.stamp_ctors_in.get(&f))
        .or_else(|| ctx.construct_sites_in.get(&site));
    match si {
        Some(si) if w & CLASS_WORD_SENTINEL != 0 => w | layout_types_bit(ctx, si.layout_id),
        _ => w,
    }
}

/// `ctor_stamp_keep_bits` for the MIR and baseline tiers (TYPES kept by
/// `layout_types_bit`).
pub(crate) fn typed_keep_bits(ctx: &TranslateCtx<'_>, si: &StampCtorIn) -> u32 {
    ctor_stamp_keep_bits(si) | layout_types_bit(ctx, si.layout_id)
}

/// `restamp_args` for the MIR and baseline tiers (TYPES kept by
/// `layout_types_bit`).
pub(crate) fn typed_restamp_args(ctx: &TranslateCtx<'_>, si: &StampCtorIn) -> Option<[u32; 7]> {
    let mut r = restamp_args(si)?;
    r[2] |= layout_types_bit(ctx, si.layout_id);
    Some(r)
}

/// The validity bits a ctor-exit stamp of `si` carries forward: SLOTS,
/// plus SHALLOW/RANGES only when the layout has masked fields / range
/// claims (see `emit_class_idx_stamp_impl`). And CLOSED where the layout
/// may be, not as a bit to keep (under the sentinel it is a key bit) but
/// to say the stamp sets it where the object holds exactly its row.
pub(crate) fn ctor_stamp_keep_bits(si: &StampCtorIn) -> u32 {
    let closed = if si.closable { CLASS_WORD_CLOSED } else { 0 };
    closed
        | CLASS_WORD_SLOTS
        | if si.masks.iter().any(|m| !m.is_none()) { CLASS_WORD_SHALLOW } else { 0 }
        | if si.ranges.iter().any(Option::is_some) { CLASS_WORD_RANGES } else { 0 }
}

/// Whether the baseline and MIR tiers restamp at init delegates' returns.
const RESTAMPS: bool = true;

/// The arguments after `this` of `night_runtime_ctor_restamp` for init
/// delegate `si`: layout, field count, kept bits, then up to four prefix
/// layout ids + 1 (0: none). `None` for a delegate with more prefixes
/// (it is then not restamped, which costs typed accesses only).
pub(crate) fn restamp_args(si: &StampCtorIn) -> Option<[u32; 7]> {
    if !RESTAMPS || si.prefix_keys.len() > 4 {
        return None;
    }
    let mut a = [
        si.layout_id,
        u32::try_from(si.fields.len()).unwrap(),
        ctor_stamp_keep_bits(si),
        0,
        0,
        0,
        0,
    ];
    for (i, &p) in si.prefix_keys.iter().enumerate() {
        a[3 + i] = p + 1;
    }
    Some(a)
}

