/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! The context lattice (`SlotCtx`, `Ctx`), the operand representation, and
//! the `TypeDesc` predicates the lowerings consult.

use super::*;

// --- the context lattice --------------------------------------------------

/// The widened value-range domain. Ranges only ever widen I32 -> I53 -> Top
/// at theta merges; they never oscillate, so the lattice height is finite.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum RangeBucket {
    /// Proven int32-representable (integer, in [i32::MIN, i32::MAX], not -0).
    I32,
    /// Proven exact-integer with |v| <= 2^53 (the i64-exact unlock).
    I53,
    Top,
}

impl RangeBucket {
    pub(crate) fn implies(self, w: RangeBucket) -> bool {
        use RangeBucket::*;
        matches!((self, w), (I32, _) | (I53, I53) | (I53, Top) | (Top, Top))
    }
}

/// Provenance of a slot/operand fact: which analysis table claimed it
/// (low byte) and/or which emitted tag test derived it (high byte), OR'd
/// through transfers and joins. Empty means intrinsic -- the fact follows
/// from the bytecode alone (a literal, an op's own semantics) and needs no
/// analysis. Metadata, never a fact: its `PartialEq` is always-true and its
/// `Hash` writes nothing, so it can ride `SlotCtx`'s derived impls without
/// entering the version identity, ordering joins, or multiplying versions.
/// Consumed only by the provenance census instruments.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Prov(pub(crate) u16);

// Bits without an install site yet stay declared: they are the vocabulary
// the gap fixes will claim into.
#[allow(dead_code)]
impl Prov {
    pub(crate) const NONE: Prov = Prov(0);
    /// Claim-backed bits: the analysis table the fact validates.
    pub(crate) const C_ENTRY: Prov = Prov(0x0001);
    pub(crate) const C_ARG: Prov = Prov(0x0002);
    pub(crate) const C_CALLRET: Prov = Prov(0x0004);
    pub(crate) const C_FIELD: Prov = Prov(0x0008);
    pub(crate) const C_ELEM: Prov = Prov(0x0010);
    pub(crate) const C_ARITH: Prov = Prov(0x0020);
    pub(crate) const C_GNAME: Prov = Prov(0x0040);
    pub(crate) const C_ALIAS: Prov = Prov(0x0080);
    /// Test-derived bits: the tag-test family that discovered the fact
    /// with no table behind it.
    pub(crate) const T_ARITH: Prov = Prov(0x0100);
    pub(crate) const T_PROP: Prov = Prov(0x0200);
    pub(crate) const T_ELEM: Prov = Prov(0x0400);
    pub(crate) const T_CMP: Prov = Prov(0x0800);
    pub(crate) const T_FRAME: Prov = Prov(0x1000);
    pub(crate) const T_CALL: Prov = Prov(0x2000);

    const CLAIM_MASK: u16 = 0x00ff;
    const TEST_MASK: u16 = 0xff00;

    pub(crate) const fn or(self, w: Prov) -> Prov {
        Prov(self.0 | w.0)
    }

    /// The census bucket: 0 intrinsic, 1 claim-backed, 2 test-derived,
    /// 3 mixed (claim-backed on one arrival path, test-derived on another,
    /// or a fact resting on operands of both kinds).
    pub(crate) fn class(self) -> u32 {
        u32::from(self.0 & Self::CLAIM_MASK != 0) + 2 * u32::from(self.0 & Self::TEST_MASK != 0)
    }

    pub(crate) fn same_bits(self, w: Prov) -> bool {
        self.0 == w.0
    }
}

impl PartialEq for Prov {
    fn eq(&self, _: &Prov) -> bool {
        true
    }
}
impl Eq for Prov {}
impl std::hash::Hash for Prov {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}

/// Per-slot context entry: the prim-only projection of the TypeDesc domain
/// (a mask + the outside bit -- a ctx slot never carries a heap abstraction,
/// only the durable class fact below) + the range bucket.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) struct SlotCtx {
    pub prims: Prims,
    pub outside: bool,
    pub range: RangeBucket,
    /// Durable class fact: the value is an object whose class-idx
    /// word's identity half is proven in this [k_lo, k_hi] range (the
    /// +1-biased layout-id space the stamp guards compare against;
    /// row-restricted semantics -- identity only, never SHALLOW, never
    /// proto claims). Killed at every CallGc edge (user JS can restamp
    /// or clear); inline store arms never touch the identity half, so
    /// stores preserve it.
    pub cls: Option<(u16, u16)>,
    /// The class word's SHALLOW valid-types half is also proven
    /// set (a passed fullword or SHALLOW-bit guard). Meaningful only with
    /// `cls`. One fullword guard makes every later masked load of the
    /// lineage checkless. Dies at every CallGc (with cls) and at every
    /// emitted inline slot store whose value is not statically a number
    /// (the store choke may clear any aliased object's flags; number
    /// stores violate no claim).
    pub cls_shallow: bool,
    /// Two-bit family: the class word's SLOTS validity bit is also proven
    /// set (a passed fused identity+SLOTS or bare-bit guard). Meaningful
    /// only with `cls`. Licenses checkless slot immediates at cls-implied
    /// sites. Dies at every CallGc and at every inline set-IC emission
    /// (its add-transition replay may clear an aliased object's bit) --
    /// but survives value stores: the chokes are TYPES-only.
    pub cls_slots: bool,
    /// ADVISORY class hint, never proven: the analysis's per-site value
    /// class for the load that produced this value ("likely this class,
    /// unchecked"). No consumer may trust it without emitting its own
    /// guard -- `layout_site_for` synthesizes a class-fact site row from
    /// it, and that form's own idx guard is what transitions the hint to
    /// a proven `cls` (via the hit arm's `refine_src`). Because every use
    /// re-guards, the hint needs no kill discipline: it survives CallGc
    /// and restamps, where `cls` dies. Invisible to `implies`/the proof
    /// (advisory facts owe no guards and are delivered free); joins keep
    /// the union range when both sides hint, like `cls`.
    pub likely_cls: Option<(u16, u16)>,
    /// Durable class fact: the value is a fixed-length typed array of this
    /// kind. An object's clasp never changes, so unlike `cls` it survives
    /// every CallGc; it dies only with the slot's value.
    pub ta: Option<opsem::TaKind>,
    /// Provenance, not a fact: which frame slot this value currently IS.
    /// A guard that passes on the value refines that slot's tracked fact
    /// (`refine_src`), which is what makes a proof durable for the rest of
    /// the lineage -- test-once-per-lineage. It has to ride the ctx because
    /// in per-op BBV every operand a guard sees arrived as a block param,
    /// and `Operand::ranged` has no provenance to restore: without it
    /// every `refine_src` call early-returns and no property access ever
    /// sees a class fact.
    ///
    /// Being a location and not a claim, it is excluded from `implies` (it
    /// must not order or multiply versions, the treatment `carried` gets)
    /// and a join keeps it only when both arrivals agree.
    pub src: Option<SlotRef>,
    /// Exact-integer interval fact about the value (the opsem `Iv`
    /// contract's recorded form): a finite integer in [lo, hi], never -0,
    /// |bounds| <= 2^53, minted only from literals, guard arms and the
    /// vocabulary's modeled ops -- the provenance condition that makes an
    /// in-int32 interval prove an Int32 TAG under canonical boxing.
    /// Join growth keeps intra's exact-join tolerance and then quantizes
    /// to the widening rungs (`opsem::iv_join_tolerant`), so the
    /// fixpoint's interval raises per slot are bounded by construction.
    pub iv: Option<ValueRange>,
    /// Fixpoint metadata, not a claim (no `implies` clause): how many
    /// times this stored slot's interval has grown at joins -- the
    /// widening trigger.
    pub iv_grow: u8,
    /// Provenance of the slot's fact (see [`Prov`]): metadata for the
    /// census instruments, invisible to Eq/Hash/implies by construction.
    pub prov: Prov,
}

impl SlotCtx {
    pub(crate) const TOP: SlotCtx = SlotCtx {
        prims: ALL_PRIMS,
        outside: true,
        range: RangeBucket::Top,
        cls: None,
        cls_shallow: false,
        cls_slots: false,
        ta: None,
        likely_cls: None,
        src: None,
        iv: None,
        iv_grow: 0,
        prov: Prov::NONE,
    };

    pub(crate) fn is_top(&self) -> bool {
        *self == SlotCtx::TOP
    }

    pub(crate) fn with_prov(mut self, p: Prov) -> SlotCtx {
        self.prov = self.prov.or(p);
        self
    }

    /// TOP in every component the walk decides from: the interval, which
    /// no arm consults, does not count. A gate whose behavior depends on
    /// non-TOP-ness rather than on the interval must use this form.
    pub(crate) fn is_top_sans_iv(&self) -> bool {
        SlotCtx {
            iv: None,
            iv_grow: 0,
            ta: None,
            likely_cls: None,
            ..*self
        } == SlotCtx::TOP
    }

    /// The ctx claim an operand's tracked type supports. The empty claim
    /// (`prims.is_empty() && !outside`, e.g. a magic-value push) sanitizes to TOP:
    /// a ctx slot fact must be a sound positive claim about the boxed
    /// value, and empty means unmodeled, not "no value".
    pub(crate) fn of(ty: &TypeDesc, range: RangeBucket) -> SlotCtx {
        if ty.prims.is_empty() && !ty.outside {
            return SlotCtx::TOP;
        }
        let range = if is_exact_int32(ty) {
            RangeBucket::I32
        } else {
            range
        };
        SlotCtx {
            prims: ty.prims,
            outside: ty.outside,
            range,
            cls: None,
            cls_shallow: false,
            cls_slots: false,
            ta: None,
            likely_cls: None,
            src: None,
            iv: None,
            iv_grow: 0,
            prov: Prov::NONE,
        }
    }

    pub(crate) fn to_ty(self) -> TypeDesc {
        TypeDesc {
            prims: self.prims,
            outside: self.outside,
        }
    }

    /// `self` refines `w`: every value satisfying `self` satisfies `w`.
    pub(crate) fn implies(&self, w: &SlotCtx) -> bool {
        self.implies_sans_iv(w)
            && match (self.iv, w.iv) {
                (_, None) => true,
                (Some(s), Some(w)) => s.lo >= w.lo && s.hi <= w.hi,
                (None, Some(_)) => false,
            }
    }

    /// `implies` without the interval clause: the discriminator for the
    /// iv-only fixpoint step (see `theta` -- an arrival disagreeing only on
    /// the interval weakens it in place, never re-joining the components
    /// the walk decides from).
    pub(crate) fn implies_sans_iv(&self, w: &SlotCtx) -> bool {
        self.prims.subset_of(w.prims)
            && (w.outside || !self.outside)
            && self.range.implies(w.range)
            && match (self.cls, w.cls) {
                (_, None) => true,
                (Some((slo, shi)), Some((wlo, whi))) => slo >= wlo && shi <= whi,
                (None, Some(_)) => false,
            }
            && (!w.cls_shallow || self.cls_shallow)
            && (!w.cls_slots || self.cls_slots)
            && (w.ta.is_none() || self.ta == w.ta)
    }

    pub(crate) fn is_numeric(&self) -> bool {
        !self.prims.is_empty() && self.prims.subset_of(PRIM_INT32 | PRIM_DOUBLE) && !self.outside
    }

    /// Greatest lower bound (both claims hold). Ranges form a chain
    /// (I32 < I53 < Top), so the stronger one stands. A contradictory
    /// result (no primitive, no outside -- a dead path) yields None.
    pub(crate) fn meet(self, w: SlotCtx) -> Option<SlotCtx> {
        let prims = self.prims & w.prims;
        let outside = self.outside && w.outside;
        if prims.is_empty() && !outside {
            return None;
        }
        let range = if self.range.implies(w.range) {
            self.range
        } else {
            w.range
        };
        let cls = match (self.cls, w.cls) {
            (None, c) | (c, None) => c,
            (Some((alo, ahi)), Some((blo, bhi))) => {
                let lo = alo.max(blo);
                let hi = ahi.min(bhi);
                if lo <= hi {
                    Some((lo, hi))
                } else {
                    // Contradictory ranges: a dead path in cls-space; keep
                    // the newer claim (the just-passed guard).
                    w.cls
                }
            }
        };
        let iv = match (self.iv, w.iv) {
            (None, c) | (c, None) => c,
            (Some(a), Some(b)) => {
                let lo = a.lo.max(b.lo);
                let hi = a.hi.min(b.hi);
                if lo <= hi {
                    Some(ValueRange::new(lo, hi))
                } else {
                    // Contradictory intervals: a dead path in value space;
                    // keep the newer claim (the just-passed guard).
                    w.iv
                }
            }
        };
        Some(SlotCtx {
            prims,
            outside,
            range,
            cls,
            cls_shallow: self.cls_shallow || w.cls_shallow,
            cls_slots: self.cls_slots || w.cls_slots,
            // Advisory: keep whichever side hints (a refinement that says
            // nothing about the hint must not erase it).
            likely_cls: self.likely_cls.or(w.likely_cls),
            ta: self.ta.or(w.ta),
            src: self.src.or(w.src),
            iv,
            iv_grow: self.iv_grow.max(w.iv_grow),
            prov: self.prov.or(w.prov),
        })
    }

    /// Least upper bound (the weakest claim both arrivals satisfy) -- what
    /// a version's ctx is when it is the join of everything that reaches it
    /// instead of whatever happened to arrive first. Dual to `meet`; `a`
    /// and `b` both imply the result, so every arrival's edge conversion is
    /// licensed by construction.
    pub(crate) fn join(self, w: SlotCtx) -> SlotCtx {
        let range = if self.range.implies(w.range) {
            w.range
        } else {
            self.range
        };
        // `w` is the stored side in the fixpoint step (`ctx_in.join(cur)` in
        // theta): the union stays exact while it fits the stored bounds and
        // snaps up the widening rungs when it grows, so a loop accumulator
        // converges in rung-many raises.
        let (iv, iv_grow) = crate::opsem::iv_join_tolerant(self.iv, w.iv, w.iv_grow);
        SlotCtx {
            prims: self.prims | w.prims,
            outside: self.outside || w.outside,
            range,
            // A class claim survives a join only if both sides make one;
            // the union interval is the weakest both imply.
            cls: match (self.cls, w.cls) {
                (Some((alo, ahi)), Some((blo, bhi))) => Some((alo.min(blo), ahi.max(bhi))),
                _ => None,
            },
            cls_shallow: self.cls_shallow && w.cls_shallow,
            cls_slots: self.cls_slots && w.cls_slots,
            likely_cls: match (self.likely_cls, w.likely_cls) {
                (Some((alo, ahi)), Some((blo, bhi))) => Some((alo.min(blo), ahi.max(bhi))),
                _ => None,
            },
            ta: if self.ta == w.ta { self.ta } else { None },
            src: if self.src == w.src { self.src } else { None },
            iv,
            iv_grow,
            prov: self.prov.or(w.prov),
        }
    }
}

/// Write-back facts for the common guard shapes.
pub(crate) const OBJ_ONLY_SLOT: SlotCtx = SlotCtx {
    prims: Prims::EMPTY,
    outside: true,
    range: RangeBucket::Top,
    cls: None,
    cls_shallow: false,
    cls_slots: false,
    ta: None,
    likely_cls: None,
    src: None,
    iv: None,
    iv_grow: 0,
    prov: Prov::NONE,
};
pub(crate) const INT32_SLOT: SlotCtx = SlotCtx {
    prims: PRIM_INT32,
    outside: false,
    range: RangeBucket::I32,
    cls: None,
    cls_shallow: false,
    cls_slots: false,
    ta: None,
    likely_cls: None,
    src: None,
    iv: Some(ValueRange::new(i32::MIN as i64, i32::MAX as i64)),
    iv_grow: 0,
    prov: Prov::NONE,
};
pub(crate) const NUMERIC_SLOT: SlotCtx = SlotCtx {
    prims: PRIM_INT32.or(PRIM_DOUBLE),
    outside: false,
    range: RangeBucket::Top,
    cls: None,
    cls_shallow: false,
    cls_slots: false,
    ta: None,
    likely_cls: None,
    src: None,
    iv: None,
    iv_grow: 0,
    prov: Prov::NONE,
};
pub(crate) const DOUBLE_SLOT: SlotCtx = SlotCtx {
    prims: PRIM_DOUBLE,
    outside: false,
    range: RangeBucket::Top,
    cls: None,
    cls_shallow: false,
    cls_slots: false,
    ta: None,
    likely_cls: None,
    src: None,
    iv: None,
    iv_grow: 0,
    prov: Prov::NONE,
};
pub(crate) const STR_SLOT: SlotCtx = SlotCtx {
    prims: PRIM_STRING,
    outside: false,
    range: RangeBucket::Top,
    cls: None,
    cls_shallow: false,
    cls_slots: false,
    ta: None,
    likely_cls: None,
    src: None,
    iv: None,
    iv_grow: 0,
    prov: Prov::NONE,
};
pub(crate) const BOOL_SLOT: SlotCtx = SlotCtx {
    prims: PRIM_BOOLEAN,
    outside: false,
    range: RangeBucket::Top,
    cls: None,
    cls_shallow: false,
    cls_slots: false,
    ta: None,
    likely_cls: None,
    src: None,
    iv: None,
    iv_grow: 0,
    prov: Prov::NONE,
};
pub(crate) const SYM_SLOT: SlotCtx = SlotCtx {
    prims: PRIM_SYMBOL,
    outside: false,
    range: RangeBucket::Top,
    cls: None,
    cls_shallow: false,
    cls_slots: false,
    ta: None,
    likely_cls: None,
    src: None,
    iv: None,
    iv_grow: 0,
    prov: Prov::NONE,
};

/// The typed-entry selector bit on the ABI argc param: a resolved call site
/// whose operand facts statically imply every entry claim of the callee sets
/// it, and the callee's prologue
/// branches straight to the claims-proven entry, skipping validation.
/// Bit 31 -- runtime callers pass a plain argc (<= ARGS_LENGTH_MAX, far
/// below), so the bit is never set by accident, and every compiled
/// prologue masks it off before argc is used.
pub(crate) const ARGC_SEL_BIT: u32 = 0x8000_0000;

/// What an entry claim's guard proves on its pass arm -- the fact the
/// typed entry seeds and the caller must therefore statically imply.
/// Mirrors `push_load_typed`'s arm routing exactly: a pure int32 mask
/// proves exact int32, a pure double mask proves exact double, a MIXED
/// Int32|Double mask proves boxed NUMERIC (one number-tag test, both
/// tags admitted -- the numeric-category policy), 0x8000 proves
/// object-only. `None` = the mask has no guard arm (push_load_typed
/// pushes unguarded bottom), so the slot carries no entry claim.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ClaimShape {
    Obj,
    Int32,
    Double,
    /// A FRACTIONAL-reachable mixed Int32|Double mask (the claim carries
    /// the double-first fractional annotation): ONE number-tag test
    /// admitting both tags, pass-arm fact boxed numeric -- the numeric-
    /// category policy applied to the typed entry. An exact-shape mapping
    /// loses a population either way: exact-Int32 flunks the whole
    /// invocation onto the Dirty lineage at pc 0 the moment one entry
    /// arrives fractional (a per-step solver taking a timestep is a
    /// typical case), while mapping every mixed mask to Number costs the
    /// integral populations their exact int32 entry facts -- i53-bounded
    /// mixed claims want the exact shape, since their double evidence
    /// never materializes as a double TAG.
    Number,
    /// A string-only claim: one TAG_STRING test, pass-arm fact
    /// string-only (StrPtr repr at version seams via slot_repr).
    Str,
    /// A boolean-only claim: one TAG_BOOLEAN test, pass-arm fact
    /// boolean-only (Bool repr at seams; truthiness tests go checkless).
    Bool,
    /// A symbol-only claim: one TAG_SYMBOL test; the pass-arm fact makes a
    /// strict compare against the value a bit compare.
    Sym,
    /// A typed-array claim: the object tag test and the clasp test against
    /// the kind's class; the pass-arm fact lets element ops on the value
    /// skip their own clasp guard.
    Ta(opsem::TaKind),
}

pub(crate) fn claim_shape(claim: Claim) -> Option<ClaimShape> {
    if claim.is_object() {
        return Some(match claim.ta_kind() {
            Some(k) => ClaimShape::Ta(k),
            None => ClaimShape::Obj,
        });
    }
    let m = claim.prims();
    if claim.double_first() && m == PRIM_INT32.or(PRIM_DOUBLE) {
        Some(ClaimShape::Number)
    } else if m == PRIM_INT32 || m == PRIM_INT32 | PRIM_DOUBLE {
        Some(ClaimShape::Int32)
    } else if m == PRIM_DOUBLE {
        Some(ClaimShape::Double)
    } else if m == PRIM_STRING {
        Some(ClaimShape::Str)
    } else if m == PRIM_BOOLEAN {
        Some(ClaimShape::Bool)
    } else if m == PRIM_SYMBOL {
        Some(ClaimShape::Sym)
    } else {
        None
    }
}

pub(crate) fn claim_slot_ctx(shape: ClaimShape) -> SlotCtx {
    match shape {
        ClaimShape::Obj => OBJ_ONLY_SLOT,
        ClaimShape::Int32 => INT32_SLOT,
        ClaimShape::Double => DOUBLE_SLOT,
        ClaimShape::Number => NUMERIC_SLOT,
        ClaimShape::Str => STR_SLOT,
        ClaimShape::Bool => BOOL_SLOT,
        ClaimShape::Sym => SYM_SLOT,
        ClaimShape::Ta(k) => SlotCtx {
            ta: Some(k),
            ..OBJ_ONLY_SLOT
        },
    }
}

/// One enclosing frame's facts, as an inline segment carries them.
#[derive(Clone, Default, PartialEq, Eq, Debug)]
pub(crate) struct CallerFrame {
    pub locals: Vec<SlotCtx>,
    pub args: Vec<SlotCtx>,
}

impl CallerFrame {
    fn canon(mut self) -> CallerFrame {
        while self.locals.last().is_some_and(SlotCtx::is_top) {
            self.locals.pop();
        }
        while self.args.last().is_some_and(SlotCtx::is_top) {
            self.args.pop();
        }
        self
    }

    fn is_empty(&self) -> bool {
        self.locals.is_empty() && self.args.is_empty()
    }
}

/// A versioning context: per frame slot (locals + operand stack) facts, in
/// canonical form (trailing TOP slots trimmed; a slot beyond the vec is
/// TOP), plus the per-enclosing-loop header-version tokens. GEN facts
/// canonicalize to two empty vecs; tokens are an orthogonal dimension.
///
/// Tokens, marker form: for
/// each loop containing the version's pc (except the header pc itself),
/// a layer marker -- TOK_OPT (entered through the Opt header, cycling
/// there), TOK_CYCLE (through a non-Opt header), or TOK_PEEL (no header
/// passed at this level: side entries, mid-body track-steps -- acyclic).
/// Theta joins require marker equality, so every cycle's interior shares
/// its header's marker and no edge can enter a cycle anywhere but at its
/// header -- cross-lineage edges (deopt arms, weakened joins) land in
/// peel copies that are acyclic by construction (their only way to cycle
/// is through a header, which re-marks). This is what makes the emitted
/// version graph reducible with multiple versions per loop header, and
/// the vector is the 2-sides x depth-layers lattice in per-level form.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub(crate) struct Ctx {
    /// The slot vectors are DENSE and indexed by slot number, so a fact
    /// about local 23 alone is stored behind 23 TOP fillers. `canon` trims
    /// the trailing run; the interior fill stays.
    ///
    /// Most stored slots are TOP, but even the largest script's whole ctx
    /// table is a few MB against a multi-GB peak, so a sparse
    /// representation would save a fraction of a percent of peak, and it
    /// would pay for that with a search in `local`/`stack_slot`/`arg`,
    /// which are the innermost operations of the fixpoint. Dense on
    /// purpose.
    pub locals: Vec<SlotCtx>,
    pub stack: Vec<SlotCtx>,
    /// Frame-argument facts: index 0 is `this`, 1 + i is arg i -- args are
    /// ctx slots exactly like locals. Empty for mapped-args frames (the
    /// arguments object aliases the slots).
    pub args: Vec<SlotCtx>,
    /// The caller's frame facts carried through an inline segment
    /// (locals, then [this, args...]), restored at the segment's return
    /// edge. Sound across the splice: caller frame slots are private (no
    /// env in inline callees, no debugger/generator in this tier), so no
    /// callee can reassign them. Empty outside segments.
    pub caller_locals: Vec<SlotCtx>,
    pub caller_args: Vec<SlotCtx>,
    /// The frames ABOVE that caller, innermost first -- splices nest to
    /// depth 8 in a loop, and one caller frame is only enough for the
    /// innermost splice.
    ///
    /// Without this a nested splice's entry has nowhere to put its
    /// grandparent's facts, so it drops them; its return edge then arrives
    /// at the parent's continuation with an all-TOP caller frame, the
    /// per-pc join meets that against the sibling arm that kept them, and
    /// the root frame loses every class fact it held for the whole rest of
    /// the body -- e.g. a root local that dies inside a nested segment is
    /// gone in the caller for the rest of the body.
    ///
    /// Pass-through state: nothing inside a segment READS an outer frame's
    /// facts (a segment's `GetLocal` names the callee's own locals), so
    /// these frames are only carried, killed with everything else, and
    /// popped one at a time at each segment return.
    pub outer: Vec<CallerFrame>,
    /// Sorted by loop index (position in the sorted loop-interval list).
    pub tokens: Vec<(u32, u64)>,
    /// Locals-into-SSA, location dimension: the locals this version receives
    /// as block params (sorted). A local not listed lives in its frame slot.
    /// Carrying is thus a property of where the value IS, not of what we
    /// have proven about it -- a TOP-fact local is carried just as well --
    /// and it is part of the version key, so edge builders and
    /// `run_version` always agree on the param layout.
    ///
    /// A carrier is dropped, not reloaded, at a GC safepoint (write-through
    /// keeps the frame current); the next use re-loads it, and an edge into
    /// a version that expects the carrier reconciles with one load.
    pub carried: Vec<u32>,
    /// Per-binding value facts: `(binding id, fact)` sorted by id, TOP
    /// entries absent. The fact is about the global binding's VALUE ("the
    /// value of `heap32` is an object"), established by a `GetGName`
    /// read's tag test and consumed by later reads of the same binding,
    /// which then run the fuse/slot diamond with no tag ladder behind it.
    /// Frame-independent (a binding is program-wide), so one vector serves
    /// the root and every spliced segment. Killed by every `SetGName`-
    /// family store in the body; across a call it survives only a keep
    /// continuation whose word has `FLAG_BIND` clear, else it is re-proven
    /// there (fuse armed + tag) or the lineage leaves Opt.
    pub gcells: Vec<(u32, SlotCtx)>,
    /// Which track this version is on. Like `tokens` it is an identity, not
    /// a fact: two tracks never join, which is precisely what keeps `+`'s
    /// bottom-typed slow arm from defining the pc for the int lineage that
    /// falls through it.
    pub track: Track,
}

/// `a` refines `b` on the binding facts: every fact `b` holds, `a` holds
/// at least as strongly (a binding absent from `a` is TOP there).
fn gcells_implies(a: &[(u32, SlotCtx)], b: &[(u32, SlotCtx)], sans_iv: bool) -> bool {
    b.iter().all(|(bid, w)| {
        a.iter().find(|(x, _)| x == bid).is_some_and(|(_, s)| {
            if sans_iv {
                s.implies_sans_iv(w)
            } else {
                s.implies(w)
            }
        })
    })
}

/// Pointwise join of two binding-fact vectors: a binding either side
/// lacks is TOP in the result (and dropped).
fn gcells_join(a: &[(u32, SlotCtx)], b: &[(u32, SlotCtx)]) -> Vec<(u32, SlotCtx)> {
    let mut out: Vec<(u32, SlotCtx)> = Vec::new();
    for (bid, s) in a {
        if let Some((_, w)) = b.iter().find(|(x, _)| x == bid) {
            let j = s.join(*w);
            if !j.is_top() {
                out.push((*bid, j));
            }
        }
    }
    out
}

/// Sort by binding id and drop TOP entries (the vector's canonical form).
fn gcells_canon(mut v: Vec<(u32, SlotCtx)>) -> Vec<(u32, SlotCtx)> {
    v.retain(|(_, s)| !s.is_top());
    v.sort_by_key(|(bid, _)| *bid);
    v
}

impl Ctx {
    pub(crate) fn canon(mut self) -> Ctx {
        while self.locals.last().is_some_and(SlotCtx::is_top) {
            self.locals.pop();
        }
        while self.stack.last().is_some_and(SlotCtx::is_top) {
            self.stack.pop();
        }
        while self.args.last().is_some_and(SlotCtx::is_top) {
            self.args.pop();
        }
        while self.caller_locals.last().is_some_and(SlotCtx::is_top) {
            self.caller_locals.pop();
        }
        while self.caller_args.last().is_some_and(SlotCtx::is_top) {
            self.caller_args.pop();
        }
        self.outer = self.outer.into_iter().map(CallerFrame::canon).collect();
        while self.outer.last().is_some_and(CallerFrame::is_empty) {
            self.outer.pop();
        }
        self.gcells = gcells_canon(std::mem::take(&mut self.gcells));
        self
    }

    pub(crate) fn local(&self, i: usize) -> SlotCtx {
        self.locals.get(i).copied().unwrap_or(SlotCtx::TOP)
    }

    pub(crate) fn stack_slot(&self, i: usize) -> SlotCtx {
        self.stack.get(i).copied().unwrap_or(SlotCtx::TOP)
    }

    pub(crate) fn arg(&self, i: usize) -> SlotCtx {
        self.args.get(i).copied().unwrap_or(SlotCtx::TOP)
    }

    /// Pointwise implication on slots (missing slots are TOP on both
    /// sides); tokens must be equal -- a token is an identity, not a fact.
    pub(crate) fn implies(&self, w: &Ctx) -> bool {
        let le = |a: &[SlotCtx], b: &[SlotCtx]| {
            (0..a.len().max(b.len())).all(|i| {
                a.get(i)
                    .copied()
                    .unwrap_or(SlotCtx::TOP)
                    .implies(&b.get(i).copied().unwrap_or(SlotCtx::TOP))
            })
        };
        self.tokens == w.tokens
            && self.track == w.track
            && le(&self.locals, &w.locals)
            && le(&self.stack, &w.stack)
            && le(&self.args, &w.args)
            && le(&self.caller_locals, &w.caller_locals)
            && le(&self.caller_args, &w.caller_args)
            && (0..self.outer.len().max(w.outer.len())).all(|i| {
                let (a, b) = (self.outer.get(i), w.outer.get(i));
                let e = CallerFrame::default();
                let (a, b) = (a.unwrap_or(&e), b.unwrap_or(&e));
                le(&a.locals, &b.locals) && le(&a.args, &b.args)
            })
            && gcells_implies(&self.gcells, &w.gcells, false)
    }

    /// `implies` without the interval clause (see `SlotCtx::implies_sans_iv`).
    pub(crate) fn implies_sans_iv(&self, w: &Ctx) -> bool {
        let le = |a: &[SlotCtx], b: &[SlotCtx]| {
            (0..a.len().max(b.len())).all(|i| {
                a.get(i)
                    .copied()
                    .unwrap_or(SlotCtx::TOP)
                    .implies_sans_iv(&b.get(i).copied().unwrap_or(SlotCtx::TOP))
            })
        };
        self.tokens == w.tokens
            && self.track == w.track
            && le(&self.locals, &w.locals)
            && le(&self.stack, &w.stack)
            && le(&self.args, &w.args)
            && le(&self.caller_locals, &w.caller_locals)
            && le(&self.caller_args, &w.caller_args)
            && (0..self.outer.len().max(w.outer.len())).all(|i| {
                let (a, b) = (self.outer.get(i), w.outer.get(i));
                let e = CallerFrame::default();
                let (a, b) = (a.unwrap_or(&e), b.unwrap_or(&e));
                le(&a.locals, &b.locals) && le(&a.args, &b.args)
            })
            && gcells_implies(&self.gcells, &w.gcells, true)
    }

    /// Weaken only the interval component of `self` (the stored ctx) so
    /// that the arrival `arr` implies it, leaving every component the walk
    /// decides from -- masks, ranges, cls, provenance, carriers --
    /// untouched. This is the fixpoint step for an arrival that fails
    /// `implies` solely on intervals: routing it through the full `join`
    /// would drop disagreeing `src` provenance and so change codegen,
    /// which an interval (consumed by nothing until the rung cutover) must
    /// never do.
    pub(crate) fn join_iv_only(&self, arr: &Ctx) -> Ctx {
        let f = |cur: &[SlotCtx], a: &[SlotCtx]| -> Vec<SlotCtx> {
            (0..cur.len().max(a.len()))
                .map(|i| {
                    let c = cur.get(i).copied().unwrap_or(SlotCtx::TOP);
                    let av = a.get(i).copied().unwrap_or(SlotCtx::TOP);
                    {
                        let (iv, iv_grow) = crate::opsem::iv_join_tolerant(av.iv, c.iv, c.iv_grow);
                        SlotCtx { iv, iv_grow, ..c }
                    }
                })
                .collect()
        };
        Ctx {
            locals: f(&self.locals, &arr.locals),
            stack: f(&self.stack, &arr.stack),
            args: f(&self.args, &arr.args),
            caller_locals: f(&self.caller_locals, &arr.caller_locals),
            caller_args: f(&self.caller_args, &arr.caller_args),
            outer: (0..self.outer.len().max(arr.outer.len()))
                .map(|i| {
                    let e = CallerFrame::default();
                    let a = self.outer.get(i).unwrap_or(&e);
                    let b = arr.outer.get(i).unwrap_or(&e);
                    CallerFrame {
                        locals: f(&a.locals, &b.locals),
                        args: f(&a.args, &b.args),
                    }
                })
                .collect(),
            tokens: self.tokens.clone(),
            carried: self.carried.clone(),
            // Binding facts carry no interval (the re-proof vocabulary is
            // the tag test alone), so the stored vector stands.
            gcells: self.gcells.clone(),
            track: self.track,
        }
        .canon()
    }

    /// The version ctx two arrivals share: pointwise slot join, and the
    /// carried set intersected (a carrier the version receives as a block
    /// param has to be one every arrival can hand it -- an arrival that
    /// lacks it would have to reload, which is what dropping it does
    /// anyway). Both arrivals imply the result, so the edge conversions in
    /// `cont_at` stay licensed.
    pub(crate) fn join(&self, w: &Ctx) -> Ctx {
        let lub = |a: &[SlotCtx], b: &[SlotCtx]| -> Vec<SlotCtx> {
            (0..a.len().max(b.len()))
                .map(|i| {
                    a.get(i)
                        .copied()
                        .unwrap_or(SlotCtx::TOP)
                        .join(b.get(i).copied().unwrap_or(SlotCtx::TOP))
                })
                .collect()
        };
        Ctx {
            locals: lub(&self.locals, &w.locals),
            stack: lub(&self.stack, &w.stack),
            args: lub(&self.args, &w.args),
            caller_locals: lub(&self.caller_locals, &w.caller_locals),
            caller_args: lub(&self.caller_args, &w.caller_args),
            outer: (0..self.outer.len().max(w.outer.len()))
                .map(|i| {
                    let e = CallerFrame::default();
                    let a = self.outer.get(i).unwrap_or(&e);
                    let b = w.outer.get(i).unwrap_or(&e);
                    CallerFrame {
                        locals: lub(&a.locals, &b.locals),
                        args: lub(&a.args, &b.args),
                    }
                })
                .collect(),
            tokens: self.tokens.clone(),
            // `carried` is a location set, not a fact: `implies` ignores it
            // and `cont_at` reconciles a mismatch with one frame load, so it
            // needs no fixpoint and follows first arrival. (Intersecting and
            // unioning it here are byte-identical -- this path is never
            // reached with differing sets.)
            carried: w.carried.clone(),
            gcells: gcells_join(&self.gcells, &w.gcells),
            track: self.track,
        }
        .canon()
    }

    /// The all-TOP ctx of this identity: what a version widens to when the
    /// fixpoint has not settled within its round cap. Every lineage implies
    /// it, so it is always a sound landing.
    /// GEN-only is one version per pc -- and that is an identity collapse,
    /// not a reason to forget what we know. Drop every identity dimension
    /// (tokens, carriers, track) so the pc still gets exactly one version,
    /// and keep the facts: the fixpoint then joins them over all arrivals,
    /// so a slot every arrival agrees about still hands out an unboxed
    /// block param. Throwing the ctx away wholesale (`Ctx::default()`)
    /// instead would box everything on the fallback rung, even where the
    /// type was never in doubt.
    pub(crate) fn gen_collapsed(&self) -> Ctx {
        Ctx {
            locals: self.locals.clone(),
            stack: self.stack.clone(),
            args: self.args.clone(),
            caller_locals: self.caller_locals.clone(),
            caller_args: self.caller_args.clone(),
            outer: self.outer.clone(),
            tokens: Vec::new(),
            carried: Vec::new(),
            gcells: self.gcells.clone(),
            track: Track::Opt,
        }
    }

    /// The fact half alone, with every identity and location dimension
    /// normalized away. This is the form the per-program-point prediction
    /// is stored in: a prediction is keyed by the program point, so it must
    /// not carry one arrival's tokens or carried set.
    pub(crate) fn facts_only(&self) -> Ctx {
        Ctx {
            locals: self.locals.clone(),
            stack: self.stack.clone(),
            args: self.args.clone(),
            caller_locals: self.caller_locals.clone(),
            caller_args: self.caller_args.clone(),
            outer: self.outer.clone(),
            tokens: Vec::new(),
            carried: Vec::new(),
            gcells: self.gcells.clone(),
            track: Track::Opt,
        }
    }

    /// The GEN context, by definition: no facts at all, identity and
    /// location kept. Every value crosses a GEN edge boxed, because after
    /// out-of-lining every consumer on GEN is a generic helper call that
    /// wants a boxed operand -- a typed carrier there buys nothing and
    /// costs a conversion. Which locals ride the edge (`carried`) is a
    /// location decision and is deliberately untouched: keeping values in
    /// SSA dataflow rather than reloading the frame at every opcode is
    /// free and orthogonal.
    pub(crate) fn facts_free(&self) -> Ctx {
        Ctx {
            locals: Vec::new(),
            stack: Vec::new(),
            args: Vec::new(),
            caller_locals: Vec::new(),
            caller_args: Vec::new(),
            outer: Vec::new(),
            tokens: self.tokens.clone(),
            carried: self.carried.clone(),
            gcells: Vec::new(),
            track: self.track,
        }
    }

    pub(crate) fn stripped(&self) -> Ctx {
        Ctx {
            locals: Vec::new(),
            stack: Vec::new(),
            args: Vec::new(),
            caller_locals: Vec::new(),
            caller_args: Vec::new(),
            outer: Vec::new(),
            tokens: self.tokens.clone(),
            carried: Vec::new(),
            gcells: Vec::new(),
            track: self.track,
        }
    }
}

/// Which track a lineage runs on. `Opt` means exactly one thing: the
/// execution CONFORMS to the prediction at every program point it has
/// passed. `Dirty` (GEN) is where a non-conforming execution is shunted,
/// and it carries no facts at all.
///
/// The designation is structural and needs no new analysis: an op's happy
/// path is the arm that falls through, and every `side_arm(..., succ_pc,
/// ..)` -- a missed guard -- steps down to `Side`, which folds to `Dirty`
/// at the version key.
///
/// A call does not step the track: with the fact context keyed by the
/// program point alone there is no version for a call's weak post-call
/// facts to poison -- a pc has one prediction, the join of its own
/// arrivals. What remains is the pressure valve the design rests on: a
/// value the analysis cannot pin after a call
/// is predicted weakly and stays generic ON Opt (boxed, unguarded, no
/// shunt), instead of routing the whole call-heavy tail of every body into
/// fully generic code. Opt does not mean fast; it means conforming.
///
/// Steps only ever descend within a lineage, so the track is a sticky
/// property of how the flow got here.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default, PartialOrd, Ord)]
pub(crate) enum Track {
    #[default]
    Opt,
    Side,
    Dirty,
}

impl Track {
    pub(crate) fn step(self, to: Track) -> Track {
        self.max(to)
    }
}

// --- operands ------------------------------------------------------------

/// Operand representations.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Repr {
    Boxed,
    I32,
    F64,
    Bool,
    I64,
    /// Raw JSString* payload (low 32 bits of the box) for a string-only
    /// slot; `to_boxed` ORs the string tag back in. The GC never moves a
    /// value the frame does not root, and every spill goes through
    /// `to_boxed` (the frame scan sees a real box).
    StrPtr,
    /// Raw JSObject* payload for an object-only slot; `to_boxed` ORs the
    /// object tag back in.
    ObjPtr,
}

/// One live operand-stack entry: value + repr + tracked type/range fact.
/// The ctx supplies incoming facts, op semantics refine them.
///
/// The frame slot an operand was read from: a guard passing on the
/// operand refines the source slot's tracked fact, so the
/// proof holds for the lineage's remaining body (test-once-per-lineage).
/// Cleared when the slot is reassigned while the operand is still live.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum SlotRef {
    This,
    Arg(u16),
    Local(u32),
    /// A global binding's value cell (`Ctx::gcells`), by binding id.
    GCell(u32),
}

#[derive(Clone)]
pub(crate) struct Operand {
    pub(crate) val: Value,
    pub(crate) repr: Repr,
    pub(crate) ty: TypeDesc,
    pub(crate) range: RangeBucket,
    /// Proven class-idx range carried by the live operand (same
    /// semantics as `SlotCtx::cls`); killed with the slots at CallGc.
    pub(crate) cls: Option<(u16, u16)>,
    pub(crate) cls_shallow: bool,
    pub(crate) cls_slots: bool,
    /// The advisory class hint (see [`SlotCtx::likely_cls`]).
    pub(crate) likely_cls: Option<(u16, u16)>,
    /// Proven typed-array kind (see [`SlotCtx::ta`]).
    pub(crate) ta: Option<opsem::TaKind>,
    pub(crate) src: Option<SlotRef>,
    /// In-flight interval fact (full opsem `Iv`, -0 flag included so a
    /// flagged intermediate can still cleanse downstream); only the clean
    /// projection is ever recorded into a ctx slot.
    pub(crate) iv: opsem::Iv,
    /// Fresh bit: the value is an object
    /// allocated during this frame (literal alloc, or a construct whose
    /// resolved ctor provably returns its `this`), so no caller fact can
    /// reference it and stores through it contribute NO flag. Operand-
    /// local only: dies at version edges and slot round-trips
    /// (conservative), never propagated into callees.
    pub(crate) fresh: bool,
    /// Provenance of the operand's tracked fact (see [`Prov`]).
    pub(crate) prov: Prov,
}

impl Operand {
    pub(crate) fn plain(val: Value, repr: Repr, ty: TypeDesc) -> Operand {
        let range = derived_range(&ty, RangeBucket::Top);
        Operand {
            val,
            repr,
            ty,
            range,
            cls: None,
            cls_shallow: false,
            cls_slots: false,
            ta: None,
            likely_cls: None,
            src: None,
            iv: None,
            fresh: false,
            prov: Prov::NONE,
        }
    }

    pub(crate) fn ranged(val: Value, repr: Repr, ty: TypeDesc, range: RangeBucket) -> Operand {
        let range = derived_range(&ty, range);
        Operand {
            val,
            repr,
            ty,
            range,
            cls: None,
            cls_shallow: false,
            cls_slots: false,
            ta: None,
            likely_cls: None,
            src: None,
            iv: None,
            fresh: false,
            prov: Prov::NONE,
        }
    }

    pub(crate) fn with_iv(mut self, iv: opsem::Iv) -> Operand {
        self.iv = iv;
        self
    }

    pub(crate) fn with_prov(mut self, p: Prov) -> Operand {
        self.prov = self.prov.or(p);
        self
    }

    pub(crate) fn from_slot(val: Value, slot: SlotCtx, src: SlotRef) -> Operand {
        Operand {
            val,
            repr: Repr::Boxed,
            ty: slot.to_ty(),
            range: slot.range,
            cls: slot.cls,
            cls_shallow: slot.cls_shallow,
            cls_slots: slot.cls_slots,
            ta: slot.ta,
            likely_cls: slot.likely_cls,
            src: Some(src),
            iv: slot.iv.map(|r| (r.lo, r.hi, false)),
            fresh: false,
            prov: slot.prov,
        }
    }

    pub(crate) fn slot(&self) -> SlotCtx {
        SlotCtx {
            cls: self.cls,
            cls_shallow: self.cls_shallow,
            cls_slots: self.cls_slots,
            ta: self.ta,
            likely_cls: self.likely_cls,
            src: self.src,
            iv: opsem::iv_clean(op_iv(self)),
            iv_grow: 0,
            prov: self.prov,
            ..SlotCtx::of(&self.ty, self.range)
        }
    }

    /// The same claim written into the ctx cell of a frame slot (a local or
    /// an arg) rather than a stack slot: the cell IS the location, so it
    /// carries no provenance of its own.
    pub(crate) fn slot_cell(&self) -> SlotCtx {
        SlotCtx {
            src: None,
            ..self.slot()
        }
    }
}

/// An exactly-Int32 value is I32-bucketed by definition; otherwise the
/// caller-supplied bucket stands.
pub(crate) fn derived_range(ty: &TypeDesc, range: RangeBucket) -> RangeBucket {
    if is_exact_int32(ty) {
        RangeBucket::I32
    } else {
        range
    }
}

/// The operand's interval for the vocabulary's transfer functions,
/// up-seeded from what the operand's repr proves when no richer fact
/// rides it: an I32 carrier IS an int32 (whatever a joined mask says --
/// this is what keeps the exact-i64 rung alive on Dirty lineages, which
/// carry no facts of their own); an I64 carrier is minted
/// in-domain and never -0 by the RangeBucket contract; an exactly-Int32
/// mask is intra's `iv_of` rule. Booleans deliberately seed nothing: the
/// slot projection records `op_iv`, and an interval is a claim about a
/// number value.
/// The interval a fits-int32 check leaves: the op's result interval
/// intersected with the int32 range (the arm proves the value fits).
pub(crate) fn iv_clamp_i32(riv: opsem::Iv) -> opsem::Iv {
    let (lo, hi, nz) = riv?;
    let lo = lo.max(i64::from(i32::MIN));
    let hi = hi.min(i64::from(i32::MAX));
    if lo <= hi {
        Some((lo, hi, nz))
    } else {
        None
    }
}

/// What a compiled property store owes the receiver's RANGES claim.
///
/// A mask survives an imprecise store because every consumer re-checks it
/// at the load through the number-tag dispatch. A range has no such
/// fallback -- it is read back checklessly -- so a store that cannot show
/// conformance must drop the bit rather than hope.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum RangeAct {
    /// No layout this receiver could be claims a range at this name, or
    /// the stored value's interval already proves every candidate claim.
    Nothing,
    /// A claim exists but no testable bound covers every candidate.
    Clear,
    /// Keep the bit iff the stored value is an int32 within these bounds.
    /// They are the intersection over the candidate layouts, so passing
    /// once implies every candidate's claim still holds.
    Check(i64, i64),
}

pub(crate) fn op_iv(o: &Operand) -> opsem::Iv {
    o.iv.or_else(|| match o.repr {
        Repr::I32 => opsem::IV_I32,
        Repr::I64 => {
            if o.range == RangeBucket::I32 {
                opsem::IV_I32
            } else {
                Some((-(1 << 53), 1 << 53, false))
            }
        }
        _ if is_exact_int32(&o.ty) => opsem::IV_I32,
        _ => None,
    })
}

/// A `TypeDesc` for an exact primitive (no abs, no outside).
pub(crate) fn prim_desc(prims: Prims) -> TypeDesc {
    TypeDesc {
        prims,
        outside: false,
    }
}

/// The conservative "any value at all" type: every primitive plus the
/// outside world, so presence and absence-gated predicates both decline. An
/// empty TypeDesc is not a safe stand-in (an absence predicate would read it
/// as proven-none).
pub(crate) fn bottom_ty() -> TypeDesc {
    TypeDesc {
        prims: ALL_PRIMS,
        outside: true,
    }
}

/// The sound "definitely an object, nothing known about its class" claim
/// (no primitive component, outside world): what an allocation or Lambda
/// result supports. Slots carrying it hand out the ObjPtr repr.
pub(crate) fn obj_only_ty() -> TypeDesc {
    TypeDesc {
        prims: Prims::EMPTY,
        outside: true,
    }
}

pub(crate) fn is_exact_int32(ty: &TypeDesc) -> bool {
    ty.prims == PRIM_INT32 && !ty.outside
}

/// A value whose boxed form is a Double and nothing else. This is the fact
/// that makes an F64 carrier affordable: a double-tagged nunbox IS its f64
/// bits, so such a value boxes in one reinterpret where the general F64
/// carrier pays `box_f64_canonical` (two conversions, a compare and a
/// select) at every store, frame write and merge. The claim and the boxing
/// decision are one thing -- `to_boxed` must not canonicalize what this
/// says is exactly a Double.
pub(crate) fn is_exact_double(ty: &TypeDesc) -> bool {
    ty.prims == PRIM_DOUBLE && !ty.outside
}

/// The mask an f64-track arithmetic result carries: the opsem
/// vocabulary's exact-double rule. The claim and the boxing decision are
/// one decision (see `is_exact_double`): `to_boxed` must not canonicalize
/// what this says is exactly a Double.
pub(crate) fn f64_result_prims(a: &Operand, b: &Operand) -> Prims {
    crate::opsem::f64_track_result(is_exact_double(&a.ty), is_exact_double(&b.ty))
}

pub(crate) fn is_exact_bool(ty: &TypeDesc) -> bool {
    ty.prims == PRIM_BOOLEAN && !ty.outside
}

/// A value proven to be a symbol and nothing else.
pub(crate) fn is_symbol_only(ty: &TypeDesc) -> bool {
    ty.prims == PRIM_SYMBOL && !ty.outside
}

// --- type predicates for the ctx-consulting operator arms ----------------

/// Purely numeric (Int32 and/or Double, nothing else) -- so `ToNumeric` is
/// the identity and f64 arithmetic is exact JS arithmetic.
pub(crate) fn is_numeric(ty: &TypeDesc) -> bool {
    !ty.prims.is_empty() && ty.prims.subset_of(PRIM_INT32 | PRIM_DOUBLE) && !ty.outside
}

/// The stored value is statically a number, so the store choke elides
/// (the store_conforms_statically discipline): unboxed numeric carriers
/// box to numbers; a numeric fact proves the boxed form.
pub(crate) fn store_value_numeric(o: &Operand) -> bool {
    matches!(o.repr, Repr::I32 | Repr::F64 | Repr::I64) || is_numeric(&o.ty)
}

/// An unboxed repr proves its own type mask.
pub(crate) fn refine_by_repr(o: &Operand) -> Operand {
    let mask = match o.repr {
        Repr::I32 => PRIM_INT32,
        Repr::F64 | Repr::I64 => PRIM_INT32 | PRIM_DOUBLE,
        Repr::Bool => PRIM_BOOLEAN,
        Repr::StrPtr => PRIM_STRING,
        Repr::ObjPtr => {
            let mut r = o.clone();
            r.ty = TypeDesc {
                prims: Prims::EMPTY,
                outside: true,
            };
            return r;
        }
        Repr::Boxed => return o.clone(),
    };
    // Intersect, never overwrite: the repr's mask is a claim about the
    // value, not the whole truth about it. Overwriting widened an
    // exact-Double operand back to `Int32|Double` at the first arithmetic
    // op that touched it, which is what kept the F64 carrier paying
    // `box_f64_canonical` at every boundary.
    let narrowed = o.ty.prims & mask;
    let mut r = o.clone();
    r.ty = prim_desc(if narrowed == Prims::EMPTY {
        mask
    } else {
        narrowed
    });
    r
}

/// A bitop/shift operand for the raw i32 path: an exact-Int32 proof, or an
/// in-domain i64 whose low 32 bits are its ToInt32.
pub(crate) fn int32_wrap_operand_ok(o: &Operand) -> bool {
    is_exact_int32(&o.ty) || o.repr == Repr::I64
}

/// A raw f64 carrier the analysis calls numeric but not int32: an operand
/// that can never take an int32 arm, so a ladder pairing it with an
/// untyped operand has only a double fall-through.
pub(crate) fn raw_frac_operand(o: &Operand) -> bool {
    o.repr == Repr::F64 && is_numeric(&o.ty) && !is_exact_int32(&o.ty)
}

/// An operand that materializes as an exact i64 without an unbox diamond.
pub(crate) fn i64_arith_operand_ok(o: &Operand) -> bool {
    match o.repr {
        Repr::I64 | Repr::I32 => true,
        Repr::Boxed | Repr::F64 => is_exact_int32(&o.ty),
        Repr::Bool | Repr::StrPtr | Repr::ObjPtr => false,
    }
}

pub(crate) fn may_be_double(ty: &TypeDesc) -> bool {
    ty.prims.intersects(PRIM_DOUBLE) || ty.outside
}

pub(crate) fn may_be_string(ty: &TypeDesc) -> bool {
    ty.prims.intersects(PRIM_STRING) || ty.outside
}

/// A value proven to be a string and nothing else.
pub(crate) fn is_string_only(ty: &TypeDesc) -> bool {
    ty.prims == PRIM_STRING && !ty.outside
}

pub(crate) fn may_be_bigint(ty: &TypeDesc) -> bool {
    ty.prims.intersects(PRIM_BIGINT) || ty.outside
}

/// Strict eq/ne reducible to a raw boxed-bits comparison: object identity,
/// nullish, int/bool -- anything but both-String / both-BigInt /
/// either-Double. A side proven to hold only IDENTITY types (undefined,
/// null, boolean, symbol, object) decides it alone: each has one
/// canonical encoding per value and no double, string or BigInt can be
/// strictly equal to it, so the bits are exact whatever the other side
/// may be (react's `x === void 0` on an untyped `x`, and its `$$typeof
/// === REACT_ELEMENT_TYPE` symbol dispatch, ran the whole 38-IR ladder).
/// Int32 is not an identity type: a double 5.0 is `===` to the int32 5
/// with different bits.
#[allow(clippy::nonminimal_bool)]
pub(crate) fn strict_bits_eq_sound(a: &TypeDesc, b: &TypeDesc) -> bool {
    is_identity_only(a)
        || is_identity_only(b)
        || (!may_be_double(a)
            && !may_be_double(b)
            && !(may_be_string(a) && may_be_string(b))
            && !(may_be_bigint(a) && may_be_bigint(b)))
}

/// Proven to be undefined, null, a boolean, a symbol or an object and
/// nothing else.
pub(crate) fn is_identity_only(ty: &TypeDesc) -> bool {
    (!ty.prims.is_empty() || ty.outside)
        && ty
            .prims
            .subset_of(PRIM_NULL | PRIM_UNDEFINED | PRIM_BOOLEAN | PRIM_SYMBOL)
}

/// Proven to hold no GC pointer (only non-GC primitives); the emu-undefined
/// clasp check elides.
pub(crate) fn is_non_gc(ty: &TypeDesc) -> bool {
    const NON_GC_PRIMS: Prims = PRIM_INT32
        .or(PRIM_DOUBLE)
        .or(PRIM_UNDEFINED)
        .or(PRIM_NULL)
        .or(PRIM_BOOLEAN);
    !ty.prims.is_empty() && ty.prims.subset_of(NON_GC_PRIMS) && !ty.outside
}

/// Proven to always be an object: lets the prop-IC tag guard elide.
pub(crate) fn is_object_only(ty: &TypeDesc) -> bool {
    ty.prims.is_empty() && ty.outside
}

/// Exactly null and/or undefined: the constant side of a loose `== null`.
pub(crate) fn is_nullish_const(ty: &TypeDesc) -> bool {
    !ty.outside && !ty.prims.is_empty() && ty.prims.subset_of(PRIM_NULL | PRIM_UNDEFINED)
}

/// The f64 compare op for a kind: loose and strict number compares are both
/// IEEE.
pub(crate) fn f64_compare_op(kind: u32) -> Operator {
    match kind {
        CMP_LT => Operator::F64Lt,
        CMP_LE => Operator::F64Le,
        CMP_GT => Operator::F64Gt,
        CMP_GE => Operator::F64Ge,
        CMP_EQ | CMP_STRICTEQ => Operator::F64Eq,
        CMP_NE | CMP_STRICTNE => Operator::F64Ne,
        _ => unreachable!("non-compare kind {kind}"),
    }
}

/// The signed i64 compare for a kind (exact-i64 operands).
pub(crate) fn i64_compare_op(kind: u32) -> Operator {
    match kind {
        CMP_LT => Operator::I64LtS,
        CMP_LE => Operator::I64LeS,
        CMP_GT => Operator::I64GtS,
        CMP_GE => Operator::I64GeS,
        CMP_EQ | CMP_STRICTEQ => Operator::I64Eq,
        CMP_NE | CMP_STRICTNE => Operator::I64Ne,
        _ => unreachable!("non-compare kind {kind}"),
    }
}

/// The i32 compare op for a compare kind.
pub(crate) fn i32_compare_op(kind: u32) -> Operator {
    match kind {
        CMP_LT => Operator::I32LtS,
        CMP_LE => Operator::I32LeS,
        CMP_GT => Operator::I32GtS,
        CMP_GE => Operator::I32GeS,
        CMP_EQ | CMP_STRICTEQ => Operator::I32Eq,
        CMP_NE | CMP_STRICTNE => Operator::I32Ne,
        _ => unreachable!("non-compare kind {kind}"),
    }
}

/// The interval a typed-array element load proves, from the kind alone (see
/// [`opsem::TaKind::proven_range`]).
pub(crate) fn ta_kind_iv(kind: opsem::TaKind) -> opsem::Iv {
    let (lo, hi) = kind.proven_range()?;
    opsem::iv_ok(lo, hi, false)
}

pub(crate) fn f64_arith_op(kind: u32) -> Option<Operator> {
    match kind {
        BINOP_SUB => Some(Operator::F64Sub),
        BINOP_MUL => Some(Operator::F64Mul),
        BINOP_DIV => Some(Operator::F64Div),
        _ => None,
    }
}
