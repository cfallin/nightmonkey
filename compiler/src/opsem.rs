/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! The op-semantics vocabulary: the result-type algebra, the magnitude
//! (`Range`) rules, and the exact-integer interval algebra of the JS
//! numeric/string operators, written once and shared by the analysis and
//! the lowering.
//!
//! Everything here is stated at one epistemic level: what the whole program
//! suggests, shaped as the optimistic ladder the lowering committed to --
//! int32(op)int32 claims int32 with overflow and -0 as side-arm territory,
//! integral sums and products claim I53 the same way one domain up. Every
//! result is consumed behind a guard or a fence, never as a proof.

/// A set of JavaScript primitive type classes.
///
/// This is a *set*, not a mask: each bit names one primitive class the
/// value may belong to, so more bits is a weaker claim and clearing a bit
/// is a refinement. It says nothing about objects -- whether the value may
/// be an object is always carried separately (`TypeDesc::outside`,
/// `Opnd::wild`, `TypeSet::obj`), because "may be a string" and "may be an
/// object" are independent facts.
///
/// Deliberately holds only the seven primitive classes. Layer-private flag
/// bits (unresolved evidence in the analysis, the double-first hint on the
/// fact wire) are separate fields on the types that need them rather than
/// spare bits in this word, so no consumer has to remember to strip a bit
/// before reading the set.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Prims(u16);

impl Prims {
    pub const EMPTY: Prims = Prims(0);

    pub const fn bits(self) -> u16 {
        self.0
    }

    /// Reconstruct from a serialized word; bits outside the alphabet are
    /// dropped.
    pub const fn from_bits(bits: u16) -> Prims {
        Prims(bits & ALL_PRIMS.0)
    }

    /// Set union, usable in const context (where `|` is not).
    pub const fn or(self, other: Prims) -> Prims {
        Prims(self.0 | other.0)
    }

    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// Whether the two sets share any class ("may be one of these").
    pub const fn intersects(self, other: Prims) -> bool {
        self.0 & other.0 != 0
    }

    /// Whether every class in `self` is also in `other` (`self` is at least
    /// as strong a claim).
    pub const fn subset_of(self, other: Prims) -> bool {
        self.0 & !other.0 == 0
    }

    /// Whether `self` is exactly the one class `other`.
    pub const fn is_only(self, other: Prims) -> bool {
        self.0 == other.0
    }

    /// Whether the set is non-empty and contains nothing outside `other`.
    pub const fn is_nonempty_subset_of(self, other: Prims) -> bool {
        self.0 != 0 && self.0 & !other.0 == 0
    }
}

impl std::ops::BitOr for Prims {
    type Output = Prims;
    fn bitor(self, rhs: Prims) -> Prims {
        Prims(self.0 | rhs.0)
    }
}

impl std::ops::BitOrAssign for Prims {
    fn bitor_assign(&mut self, rhs: Prims) {
        self.0 |= rhs.0;
    }
}

impl std::ops::BitAnd for Prims {
    type Output = Prims;
    fn bitand(self, rhs: Prims) -> Prims {
        Prims(self.0 & rhs.0)
    }
}

impl std::ops::BitAndAssign for Prims {
    fn bitand_assign(&mut self, rhs: Prims) {
        self.0 &= rhs.0;
    }
}

/// Set difference: the classes in `self` that are not in `rhs`.
impl std::ops::Sub for Prims {
    type Output = Prims;
    fn sub(self, rhs: Prims) -> Prims {
        Prims(self.0 & !rhs.0)
    }
}

impl std::fmt::Debug for Prims {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_empty() {
            return f.write_str("{}");
        }
        let names = [
            (PRIM_INT32, "int32"),
            (PRIM_DOUBLE, "double"),
            (PRIM_STRING, "string"),
            (PRIM_UNDEFINED, "undefined"),
            (PRIM_NULL, "null"),
            (PRIM_BOOLEAN, "boolean"),
            (PRIM_BIGINT, "bigint"),
            (PRIM_SYMBOL, "symbol"),
        ];
        f.write_str("{")?;
        let mut first = true;
        for (bit, name) in names {
            if self.intersects(bit) {
                if !first {
                    f.write_str("|")?;
                }
                f.write_str(name)?;
                first = false;
            }
        }
        f.write_str("}")
    }
}

// The primitive-class alphabet. `wasm::translate` and the likelier's
// typeset both re-export these.
impl Prims {
    /// The set's members as diagnostic tokens, in a fixed order.
    ///
    /// One fixed order shared by every renderer (the lowering's trace and
    /// the analysis's), so they never disagree.
    pub fn viz_parts(self) -> Vec<&'static str> {
        [
            (PRIM_INT32, "i32"),
            (PRIM_DOUBLE, "dbl"),
            (PRIM_BOOLEAN, "bool"),
            (PRIM_STRING, "str"),
            (PRIM_UNDEFINED, "undef"),
            (PRIM_NULL, "null"),
            (PRIM_BIGINT, "bigint"),
            (PRIM_SYMBOL, "sym"),
        ]
        .into_iter()
        .filter(|&(bit, _)| self.intersects(bit))
        .map(|(_, name)| name)
        .collect()
    }
}

pub const PRIM_INT32: Prims = Prims(1 << 0);
pub const PRIM_DOUBLE: Prims = Prims(1 << 1);
pub const PRIM_STRING: Prims = Prims(1 << 2);
pub const PRIM_UNDEFINED: Prims = Prims(1 << 3);
pub const PRIM_NULL: Prims = Prims(1 << 4);
pub const PRIM_BOOLEAN: Prims = Prims(1 << 5);
pub const PRIM_BIGINT: Prims = Prims(1 << 6);
/// A symbol: identity semantics like an object (one canonical encoding per
/// value, `===` is bits), a GC thing like a string. The oracle transcribes
/// one from a snapshot value's tag; the type alone is what the compare
/// forms need.
pub const PRIM_SYMBOL: Prims = Prims(1 << 7);

/// Every primitive class (`PRIM_INT32 .. PRIM_SYMBOL`).
pub const ALL_PRIMS: Prims = Prims(0xff);

/// "Some number": the result class of every numeric op that proves
/// nothing narrower.
pub const NUM: Prims = Prims(PRIM_INT32.0 | PRIM_DOUBLE.0);

/// Numeric-magnitude component of a type claim: whether the value, when
/// it IS a number, is known integral and exact-i64-representable. `I32`
/// is the lattice bottom (no evidence of anything wider), `I53` means
/// integral within the exact-double domain, `Top` means arbitrary.
/// Joins widen (max).
///
/// It lives here rather than in the analysis's lattice because it is an
/// input and an output of the op algebra below: the algebra cannot be
/// written without it, and putting it in a layer above would make this
/// module depend on that layer. The analysis re-exports it as
/// `likelier::types::Range`. Note this is a coarse domain ladder, not an
/// interval -- bounds are `ValueRange`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Default)]
pub enum Range {
    #[default]
    I32,
    I53,
    Top,
}

/// The element kind of a typed array.
///
/// Shared vocabulary rather than analysis-private: the analysis predicts a
/// kind per element site and the lowering emits the kind-specific access,
/// so both sides must name the same nine kinds. The numeric `code` is the
/// wire form -- it packs into the typed-array constructor's reserved
/// function id (`likelier::types::FnId::typed_array_ctor`) and is what the
/// bytecode scanner reads off a constructor name.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum TaKind {
    Int8,
    Uint8,
    Uint8Clamped,
    Int16,
    Uint16,
    Int32,
    Uint32,
    Float32,
    Float64,
}

impl TaKind {
    pub const ALL: [TaKind; 9] = [
        TaKind::Int8,
        TaKind::Uint8,
        TaKind::Uint8Clamped,
        TaKind::Int16,
        TaKind::Uint16,
        TaKind::Int32,
        TaKind::Uint32,
        TaKind::Float32,
        TaKind::Float64,
    ];

    /// The wire code, 1..=9. Zero is reserved for "not a typed array" at
    /// the boundaries that still carry a bare integer.
    pub const fn code(self) -> u8 {
        self as u8 + 1
    }

    pub const fn from_code(code: u8) -> Option<TaKind> {
        Some(match code {
            1 => TaKind::Int8,
            2 => TaKind::Uint8,
            3 => TaKind::Uint8Clamped,
            4 => TaKind::Int16,
            5 => TaKind::Uint16,
            6 => TaKind::Int32,
            7 => TaKind::Uint32,
            8 => TaKind::Float32,
            9 => TaKind::Float64,
            _ => return None,
        })
    }

    /// log2 of the element size in bytes: the shift from an element index
    /// to a byte offset.
    pub const fn log2_bytes(self) -> u32 {
        match self {
            TaKind::Int8 | TaKind::Uint8 | TaKind::Uint8Clamped => 0,
            TaKind::Int16 | TaKind::Uint16 => 1,
            TaKind::Int32 | TaKind::Uint32 | TaKind::Float32 => 2,
            TaKind::Float64 => 3,
        }
    }

    /// The inclusive value range a load of this kind proves, for the
    /// integer kinds narrower than the carrier they land in. Unlike a heap
    /// range this is not a prediction: the clasp guard pins the kind and
    /// the load reads exactly that many bits, so the value cannot be
    /// outside. `Int32` is absent because it is already what an i32
    /// operand carries, and the float kinds prove nothing integral.
    pub const fn proven_range(self) -> Option<(i64, i64)> {
        Some(match self {
            TaKind::Int8 => (-128, 127),
            TaKind::Uint8 | TaKind::Uint8Clamped => (0, 255),
            TaKind::Int16 => (-32768, 32767),
            TaKind::Uint16 => (0, 65535),
            TaKind::Uint32 => (0, (1i64 << 32) - 1),
            _ => return None,
        })
    }
}

/// The vocabulary's view of one operand: its possible primitive classes,
/// whether the object/unresolved world is possible at all, and its
/// magnitude when numeric.
///
/// This is deliberately not either side's type representation. The
/// analysis carries a `TypeSet` (abstractions, function sets, contexts)
/// and the lowering carries a `TypeDesc` (SSA values, machine
/// representations); neither may become a dependency of this module, which
/// exists precisely so the two agree on operator semantics without
/// agreeing on anything else. Both project onto `Opnd` losslessly for the
/// ops modeled here, so the projection costs no precision.
#[derive(Clone, Copy, Debug)]
pub struct Opnd {
    pub prims: Prims,
    /// May be an object, a function, or executed-but-unresolved
    /// evidence: ToPrimitive/ToNumber can then surface anything.
    pub wild: bool,
    pub range: Range,
}

/// The numeric/string operators with modeled result semantics.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NumOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    Inc,
    Dec,
    Neg,
    Pos,
    ToNumeric,
    Ursh,
    BitAnd,
    BitOr,
    BitXor,
    Lsh,
    Rsh,
    BitNot,
}

impl NumOp {
    pub fn unary(self) -> bool {
        matches!(
            self,
            NumOp::Inc | NumOp::Dec | NumOp::Neg | NumOp::Pos | NumOp::ToNumeric | NumOp::BitNot
        )
    }
}

/// Provably exactly a String: the concat side of `+`.
fn def_string(o: &Opnd) -> bool {
    !o.wild && o.prims == PRIM_STRING
}

/// Whether `+` must consider a string result from this operand. An
/// object's ToPrimitive can yield a string, but a `wild` operand
/// deliberately does not count here: it claims numeric flow only, and a
/// string arriving is a guard miss the side arm absorbs. Counting it would
/// put maybe-string on every unresolved operand and poison the numeric
/// claim tiers.
fn may_string(o: &Opnd) -> bool {
    o.prims.intersects(PRIM_STRING)
}

/// ToNumber view of an operand: which numeric prim bits its values
/// coerce to. Strings and the wild world coerce to "some number", i.e.
/// Both bits: claiming double-only where int32s actually flow is the
/// expensive direction to be wrong in, since it costs every consumer the
/// int32 track. A BigInt bit contributes nothing (ToNumber of a bigint
/// throws).
fn to_number_bits(o: &Opnd) -> Prims {
    let mut m = Prims::EMPTY;
    if o.prims.intersects(PRIM_INT32 | PRIM_BOOLEAN | PRIM_NULL) {
        m |= PRIM_INT32;
    }
    if o.prims.intersects(PRIM_DOUBLE | PRIM_UNDEFINED) {
        m |= PRIM_DOUBLE;
    }
    if o.prims.intersects(PRIM_STRING) || o.wild {
        m |= NUM;
    }
    m
}

/// `Add`'s numeric side: a string operand never reaches ToNumber (it
/// concats), so it contributes nothing here.
fn add_number_bits(o: &Opnd) -> Prims {
    let mut m = Prims::EMPTY;
    if o.prims.intersects(PRIM_INT32 | PRIM_BOOLEAN | PRIM_NULL) {
        m |= PRIM_INT32;
    }
    if o.prims.intersects(PRIM_DOUBLE | PRIM_UNDEFINED) {
        m |= PRIM_DOUBLE;
    }
    if o.wild {
        m |= NUM;
    }
    m
}

/// The numeric-part combine for the exact-int-capable ops (+ - * ++ --
/// neg, and `>>>`) -- the committed ladder. int32 pairs claim int32
/// (overflow and -0 are side arms); pure-double pairs claim double, which
/// is sound only paired with the exact-double boxing regime (`to_boxed`
/// must not canonicalize what the mask says is exactly a Double); an empty
/// side (nothing flowed yet) claims nothing, and the fixpoint re-fires on
/// growth.
///
/// None of these are TAG proofs: int32(op)int32 can overflow into a double,
/// and under canonical boxing even dbl(op)dbl can int32-tag its result
/// (1.0 + 1.0). Every consumer guards.
fn num_part(na: Prims, nb: Prims) -> Prims {
    if na.is_empty() || nb.is_empty() {
        Prims::EMPTY
    } else if na == PRIM_INT32 && nb == PRIM_INT32 {
        PRIM_INT32
    } else if na == PRIM_DOUBLE && nb == PRIM_DOUBLE {
        PRIM_DOUBLE
    } else {
        NUM
    }
}

/// The numeric-part combine for `/` `%` `**`: never an exact int (float
/// semantics), so the int32 rung of the ladder is absent.
fn num_part_noint(na: Prims, nb: Prims) -> Prims {
    if na.is_empty() || nb.is_empty() {
        Prims::EMPTY
    } else if na == PRIM_DOUBLE && nb == PRIM_DOUBLE {
        PRIM_DOUBLE
    } else {
        NUM
    }
}

/// ToNumber view of an operand's magnitude: null/bool coerce to 0/1
/// (bottom); undefined (NaN), strings, and the wild world coerce to
/// arbitrary numbers.
fn coerced_range(o: &Opnd) -> Range {
    if o.prims.intersects(PRIM_UNDEFINED | PRIM_STRING) || o.wild {
        Range::Top
    } else {
        o.range
    }
}

/// Result magnitude of the exact-int-capable binary/unary int ops:
/// integral operands claim I53 optimistically. This is the
/// disregard-overflow philosophy one domain up -- the i53 sums and products
/// of an integer arithmetic chain stay I53 at the fixpoint, and the
/// consumption guards catch the rare violation. The exact bound, where a
/// consumer needs one, comes from the interval algebra below.
fn int_range(a: &Opnd, b: Option<&Opnd>) -> Range {
    let ra = coerced_range(a);
    let rb = b.map(coerced_range).unwrap_or(Range::I32);
    if ra.max(rb) <= Range::I53 {
        Range::I53
    } else {
        Range::Top
    }
}

/// Result (prim mask, range) of `op` over its operands. Monotone in both
/// operands (fixpoint-safe). The mask may carry `PRIM_STRING`; clients
/// whose lattice lacks the bit mask it off (their operands can never set it
/// either).
pub fn result(op: NumOp, a: &Opnd, b: Option<&Opnd>) -> (Prims, Range) {
    use NumOp::*;
    match op {
        Add => {
            let b = b.expect("binary op");
            // A definitely-string side forces concat on every path.
            if def_string(a) || def_string(b) {
                return (PRIM_STRING, Range::Top);
            }
            let mut m = num_part(add_number_bits(a), add_number_bits(b));
            if may_string(a) || may_string(b) {
                m |= PRIM_STRING;
            }
            (m, int_range(a, Some(b)))
        }
        Sub | Mul => {
            let b = b.expect("binary op");
            let m = num_part(to_number_bits(a), to_number_bits(b));
            (m, int_range(a, Some(b)))
        }
        Ursh => {
            // ToUint32 output: always integral in [0, 2^32), so I53 holds
            // unconditionally (a bigint operand throws).
            let b = b.expect("binary op");
            (num_part(to_number_bits(a), to_number_bits(b)), Range::I53)
        }
        Mod => {
            let b = b.expect("binary op");
            let m = num_part_noint(to_number_bits(a), to_number_bits(b));
            // Integral % integral is integral with |result| < |divisor|, so
            // Mod claims I53 for integrally-ranged operands -- `-0` (n%d
            // with n<0 dividing evenly) and `x%0`'s NaN are the guarded rare
            // cases, the same optimism as the arith ladder. This is what
            // keeps a bignum library's digit cells at I53 rather than Top
            // across a read-modify-write reduction cycle, where a `%` sits
            // in the middle of the loop and every widening compounds. Note
            // it is emphatically not a proof: -0 breaks the interval "never
            // -0" contract, so nothing downstream may treat it as one.
            let r = if coerced_range(a) <= Range::I53 && coerced_range(b) <= Range::I53 {
                Range::I53
            } else {
                Range::Top
            };
            (m, r)
        }
        Div | Pow => {
            let b = b.expect("binary op");
            let m = num_part_noint(to_number_bits(a), to_number_bits(b));
            (m, Range::Top)
        }
        Inc | Dec | Neg => {
            // Modeled as (value op int32-literal) on the numeric side.
            let m = num_part(to_number_bits(a), PRIM_INT32);
            (m, int_range(a, None))
        }
        // ToNumber: always a number; a bigint operand throws.
        Pos | ToNumeric => (to_number_bits(a), coerced_range(a)),
        BitAnd | BitOr | BitXor | Lsh | Rsh => {
            // ToInt32 wraps both operands: the result IS an int32, so the
            // I32 range holds unconditionally.
            let _ = b.expect("binary op");
            (PRIM_INT32, Range::I32)
        }
        BitNot => (PRIM_INT32, Range::I32),
    }
}

/// The mask an f64-track arithmetic result carries (the bbv lowering's
/// per-arm instance of `num_part`'s double rule): both operands proven
/// exactly-Double claims a Double result. The claim is a TAG claim and
/// is sound only because it rides with the exact-double boxing decision
/// (`to_boxed` must not canonicalize what this says is exactly a
/// Double); anything else keeps the mixed mask so an int32-bearing chain
/// still canonicalizes and stays visible to the int32 arms downstream.
pub fn f64_track_result(a_exact_double: bool, b_exact_double: bool) -> Prims {
    if a_exact_double && b_exact_double {
        PRIM_DOUBLE
    } else {
        NUM
    }
}

// --- The exact-integer interval algebra ---------------------------------

/// An inclusive interval of integer values, `lo <= hi`. The one interval
/// spelling shared by everything that names a value's magnitude: the
/// analysis's literal folds and lattice intervals, and the emitted range
/// facts.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ValueRange {
    pub lo: i64,
    pub hi: i64,
}

impl ValueRange {
    pub const fn new(lo: i64, hi: i64) -> ValueRange {
        ValueRange { lo, hi }
    }

    /// The hull of two intervals: the join of the interval lattice.
    pub fn hull(self, other: ValueRange) -> ValueRange {
        ValueRange::new(self.lo.min(other.lo), self.hi.max(other.hi))
    }
}

/// Exact-integer interval fact about one abstract value: the runtime
/// value is a finite, integer-valued number in `[lo, hi]` and is never
/// -0, with `|lo|, |hi| <= 2^53` (every such value -- and every
/// in-bounds intermediate of the modeled ops -- is an
/// exactly-representable double, so f64 evaluation of the modeled ops is
/// bit-exact integer arithmetic). Every value carrying a `Some` interval
/// traces to canonically-boxed producers (constants, bitop results,
/// int32-tag-guarded seeds, translator arith), so an interval within
/// int32 range additionally proves an Int32 TAG under the engine's
/// canonical-boxing invariant. `None` = no proof.
///
/// The third component is the may-BE-negative-zero flag: a flagged value
/// is an in-bounds integer OR -0. -0 propagates precisely: a product is
/// -0 only when one factor is 0 and the other negative; a sum is -0 only
/// when both addends may be; bitops/shifts cleanse it (ToInt32(-0) = 0).
/// Only clean (unflagged) intervals are recorded as facts -- but a
/// clean-result sum may still be computed over collapsed -0 operands
/// exactly (-0 + x == 0 + x whenever the result is not itself -0).
pub(crate) type Iv = Option<(i64, i64, bool)>;

/// The recorded (clean-only) form of an internal interval.
pub(crate) fn iv_clean(iv: Iv) -> Option<ValueRange> {
    match iv {
        Some((lo, hi, false)) => Some(ValueRange::new(lo, hi)),
        _ => None,
    }
}

pub(crate) const IV_LIM: i64 = 1 << 53;
pub(crate) const I32_LO: i64 = i32::MIN as i64;
pub(crate) const I32_HI: i64 = i32::MAX as i64;
pub(crate) const IV_I32: Iv = Some((I32_LO, I32_HI, false));
/// Exact joins tolerated per stored slot before a growing bound snaps up
/// the widening ladder -- keeps diamond joins exact while forcing loop
/// accumulators to converge in a few rounds.
pub(crate) const IV_WIDEN_JOINS: u8 = 3;

/// Widening rungs for a growing lower bound: the nearest rung at or
/// below. The intermediate rungs matter: am3-style carries stabilize
/// near +-2^35 (the `>>28` collapse), and a ladder that jumps straight
/// to +-2^53 pushes the dependent sums out of the domain before the
/// fixpoint can settle. Beyond +-2^48 the interval gives up (headroom
/// for further adds).
pub(crate) fn widen_lo(lo: i64) -> Option<i64> {
    if lo >= 0 {
        Some(0)
    } else if lo >= I32_LO {
        Some(I32_LO)
    } else if lo >= -(1 << 36) {
        Some(-(1 << 36))
    } else if lo >= -(1 << 48) {
        Some(-(1 << 48))
    } else {
        None
    }
}

pub(crate) fn widen_hi(hi: i64) -> Option<i64> {
    if hi <= 0 {
        Some(0)
    } else if hi <= I32_HI {
        Some(I32_HI)
    } else if hi <= 1 << 36 {
        Some(1 << 36)
    } else if hi <= 1 << 48 {
        Some(1 << 48)
    } else {
        None
    }
}

/// Quantized bound domain for the heap-interval lattice (likelier cell
/// component): magnitudes at most 8 stay exact, larger ones round
/// outward to the next power of two. Coarse on purpose -- see `hq_lo`
/// for why quantization is a finite-height device only, and why a consumer
/// needing a tight bound -- one whose real range sits within a power-of-two
/// step of int32 -- states it as an exact checked bound rather than asking
/// this ladder for more resolution.
fn hq_mag_up(mag: u64) -> u64 {
    if mag <= 8 {
        return mag;
    }
    mag.next_power_of_two()
}

/// The heap ladder is clipped to the int32 domain: a wider bound serves
/// no consumer (facts feed int32-tag-guarded reads), wide `In`s breed
/// `Num` through products anyway, and collapsing in one step instead of
/// climbing 20 more octaves of feedback rounds is worth several times the
/// solve time on a long integer chain. Masked/shifted chains recover from the
/// `Num` operand via the bitop rules, so nothing real is lost. The
/// ladder itself is coarse (powers of two; small magnitudes exact) --
/// quantization exists only for finite height, not order-independence
/// (the hull join is order-independent for any fixed inputs), so
/// runtime-check clamps may contribute exact non-ladder bounds.
pub(crate) fn hq_lo(lo: i64) -> Option<i64> {
    if lo >= 0 {
        Some(0)
    } else if lo >= I32_LO {
        Some((-(hq_mag_up(lo.unsigned_abs()) as i64)).max(I32_LO))
    } else {
        None
    }
}

pub(crate) fn hq_hi(hi: i64) -> Option<i64> {
    if hi <= 0 {
        Some(0)
    } else if hi <= I32_HI {
        Some(((hq_mag_up(hi as u64 + 1) - 1) as i64).min(I32_HI))
    } else {
        None
    }
}

pub(crate) fn hq(lo: i64, hi: i64) -> Option<(i64, i64)> {
    match (hq_lo(lo), hq_hi(hi)) {
        (Some(a), Some(b)) => Some((a, b)),
        _ => None,
    }
}

pub(crate) fn iv_ok(lo: i64, hi: i64, nz: bool) -> Iv {
    if lo <= hi && lo >= -IV_LIM && hi <= IV_LIM {
        Some((lo, hi, nz))
    } else {
        None
    }
}

/// Bounds-only check (a -0 collapses to 0 under ToInt32 consumers).
pub(crate) fn iv_nonneg_i32(iv: Iv) -> bool {
    matches!(iv, Some((lo, hi, _)) if lo >= 0 && hi <= I32_HI)
}

pub(crate) fn iv_const(iv: Iv) -> Option<i64> {
    match iv {
        Some((lo, hi, false)) if lo == hi => Some(lo),
        _ => None,
    }
}

pub(crate) fn iv_add(a: Iv, b: Iv) -> Iv {
    let ((al, ah, an), (bl, bh, bn)) = (a?, b?);
    // A sum is -0 only when both addends may be (-0 + -0); computing
    // over a collapsed -0 operand is exact whenever the result is clean.
    iv_ok(al + bl, ah + bh, an && bn)
}

pub(crate) fn iv_sub(a: Iv, b: Iv) -> Iv {
    let ((al, ah, an), (bl, bh, _)) = (a?, b?);
    // a - b is -0 only for (-0) - (+0); b's -0 never produces one.
    iv_ok(al - bh, ah - bl, an)
}

pub(crate) fn iv_mul(a: Iv, b: Iv) -> Iv {
    let ((al, ah, an), (bl, bh, bn)) = (a?, b?);
    // An integer product is -0 exactly when one factor is 0 and the
    // other negative (or an operand -0 times a positive) -- flag, don't
    // drop: downstream sums usually cleanse it.
    let nz = (al <= 0 && ah >= 0 && bl < 0)
        || (bl <= 0 && bh >= 0 && al < 0)
        || (an && bh > 0)
        || (bn && ah > 0);
    let mut lo = i64::MAX;
    let mut hi = i64::MIN;
    for x in [al, ah] {
        for y in [bl, bh] {
            let p = x.checked_mul(y)?;
            lo = lo.min(p);
            hi = hi.max(p);
        }
    }
    iv_ok(lo, hi, nz)
}

/// JS `%` on integers is exact (fmod) with the dividend's sign: in-domain
/// only for a provably non-negative dividend (else -0) and a divisor
/// excluding 0 (else NaN).
pub(crate) fn iv_mod(a: Iv, b: Iv) -> Iv {
    let ((al, ah, an), (bl, bh, _)) = (a?, b?);
    if al < 0 || an || (bl <= 0 && bh >= 0) {
        return None;
    }
    iv_ok(0, (bl.abs().max(bh.abs()) - 1).min(ah), false)
}

pub(crate) fn iv_neg(a: Iv) -> Iv {
    let (al, ah, _) = a?;
    // Neg of +0 is -0 (and of -0 is +0): flag when 0 is in range.
    let nz = al <= 0 && ah >= 0;
    iv_ok(-ah, -al, nz)
}

/// `a & b` after ToInt32 wraps: any int32 and-ed with a provably
/// non-negative (unwrapped) side is in `[0, that side's hi]`.
pub(crate) fn iv_bitand(a: Iv, b: Iv) -> Iv {
    match (iv_nonneg_i32(a), iv_nonneg_i32(b)) {
        (true, true) => Some((0, a.unwrap().1.min(b.unwrap().1), false)),
        (true, false) => Some((0, a.unwrap().1, false)),
        (false, true) => Some((0, b.unwrap().1, false)),
        (false, false) => IV_I32,
    }
}

/// `a | b` / `a ^ b`: two non-negative int32s only set bits up to the
/// higher operand's leading bit.
pub(crate) fn iv_bitorxor(a: Iv, b: Iv) -> Iv {
    if iv_nonneg_i32(a) && iv_nonneg_i32(b) {
        let m = a.unwrap().1.max(b.unwrap().1);
        Some((
            0,
            (((m + 1) as u64).next_power_of_two() as i64 - 1).min(I32_HI),
            false,
        ))
    } else {
        IV_I32
    }
}

pub(crate) fn iv_lsh(a: Iv, b: Iv) -> Iv {
    if let Some(k) = iv_const(b) {
        if (0..=31).contains(&k) {
            if let Some((al, ah, _)) = a {
                if al >= I32_LO && ah <= I32_HI {
                    let (lo, hi) = (al << k, ah << k);
                    if lo >= I32_LO && hi <= I32_HI {
                        return Some((lo, hi, false));
                    }
                }
            }
        }
    }
    IV_I32
}

pub(crate) fn iv_rsh(a: Iv, b: Iv) -> Iv {
    if let Some(k) = iv_const(b) {
        if (0..=31).contains(&k) {
            return match a {
                Some((al, ah, _)) if al >= I32_LO && ah <= I32_HI => {
                    Some((al >> k, ah >> k, false))
                }
                _ => Some((I32_LO >> k, I32_HI >> k, false)),
            };
        }
    }
    IV_I32
}

/// `>>>`: always in `[0, 2^32)` on the non-throwing path (a BigInt
/// operand throws); a non-negative int32 lhs shifts exactly.
pub(crate) fn iv_ursh(a: Iv, b: Iv) -> Iv {
    if let Some(k) = iv_const(b) {
        if (0..=31).contains(&k) {
            return if iv_nonneg_i32(a) {
                let (al, ah, _) = a.unwrap();
                Some((al >> k, ah >> k, false))
            } else {
                Some((0, (u32::MAX >> k) as i64, false))
            };
        }
    }
    Some((0, u32::MAX as i64, false))
}

pub(crate) fn iv_bitnot(a: Iv) -> Iv {
    match a {
        Some((al, ah, _)) if al >= I32_LO && ah <= I32_HI => Some((-ah - 1, -al - 1, false)),
        _ => IV_I32,
    }
}

/// Join (union) of a recorded interval into the stored fact it joins,
/// with growth quantized to the widening rungs: a bound staying within
/// the stored one keeps the exact union, a growing bound snaps up the
/// ladder (None past the top rung). The raises per stored fact are
/// bounded by the finite rung chain by construction -- the
/// MAX_CELL_CHANGES discipline -- which is what keeps a derived-ctx
/// fixpoint's interval component inside its round budget.
/// `iv_join_recorded` with intra's join tolerance (IV_WIDEN_JOINS): the
/// first few growths per stored slot keep the exact union -- which is
/// what lets a self-bounded loop accumulator converge to its true range
/// instead of snapping past it to a rung -- and only a slot that keeps
/// growing widens. Returns the joined interval and the updated grow
/// count; a missing side clears both (no claim, no history).
pub(crate) fn iv_join_tolerant(
    new: Option<ValueRange>,
    stored: Option<ValueRange>,
    grow: u8,
) -> (Option<ValueRange>, u8) {
    match (new, stored) {
        (Some(n), Some(st)) => {
            let u = n.hull(st);
            if u == st {
                (Some(st), grow)
            } else if grow >= IV_WIDEN_JOINS {
                (iv_join_recorded(n, st), grow)
            } else {
                (Some(u), grow + 1)
            }
        }
        _ => (None, 0),
    }
}

pub(crate) fn iv_join_recorded(new: ValueRange, stored: ValueRange) -> Option<ValueRange> {
    let u = new.hull(stored);
    let lo = if u.lo >= stored.lo {
        Some(u.lo)
    } else {
        widen_lo(u.lo)
    };
    let hi = if u.hi <= stored.hi {
        Some(u.hi)
    } else {
        widen_hi(u.hi)
    };
    match (lo, hi) {
        (Some(a), Some(b)) => Some(ValueRange::new(a, b)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Exhaustive equivalence against an independently written oracle.
    // Operand space: all prim subsets (bits 0..=5) x unresolved-evidence x
    // object-world x the three ranges.

    mod likely_oracle {
        use super::super::*;

        pub struct Ts {
            pub prims: Prims,
            pub unknown: bool,
            pub objworld: bool,
            pub range: Range,
        }

        fn to_number_bits(ts: &Ts) -> Prims {
            let mut m = Prims::EMPTY;
            if ts.prims.intersects(PRIM_INT32 | PRIM_BOOLEAN | PRIM_NULL) {
                m |= PRIM_INT32;
            }
            if ts.prims.intersects(PRIM_DOUBLE | PRIM_UNDEFINED) {
                m |= PRIM_DOUBLE;
            }
            if ts.unknown || ts.prims.intersects(PRIM_STRING) || ts.objworld {
                m |= NUM;
            }
            m
        }

        fn add_number_bits(ts: &Ts) -> Prims {
            let mut m = Prims::EMPTY;
            if ts.prims.intersects(PRIM_INT32 | PRIM_BOOLEAN | PRIM_NULL) {
                m |= PRIM_INT32;
            }
            if ts.prims.intersects(PRIM_DOUBLE | PRIM_UNDEFINED) {
                m |= PRIM_DOUBLE;
            }
            if ts.unknown || ts.objworld {
                m |= NUM;
            }
            m
        }

        fn combine_num(na: Prims, nb: Prims) -> Prims {
            if na.is_empty() || nb.is_empty() {
                Prims::EMPTY
            } else if na == PRIM_INT32 && nb == PRIM_INT32 {
                PRIM_INT32
            } else if na == PRIM_DOUBLE && nb == PRIM_DOUBLE {
                PRIM_DOUBLE
            } else {
                NUM
            }
        }

        fn coerced_range(ts: &Ts) -> Range {
            if ts.unknown || ts.prims.intersects(PRIM_UNDEFINED | PRIM_STRING) || ts.objworld {
                Range::Top
            } else {
                ts.range
            }
        }

        pub fn arith_transfer(op: NumOp, a: &Ts, b: Option<&Ts>) -> (Prims, Range) {
            use NumOp::*;
            let int_range = |a: &Ts, b: Option<&Ts>| -> Range {
                let r = b
                    .map(coerced_range)
                    .unwrap_or(Range::I32)
                    .max(coerced_range(a));
                if r <= Range::I53 {
                    Range::I53
                } else {
                    Range::Top
                }
            };
            match op {
                Add => {
                    let b = b.unwrap();
                    let mut res = Prims::EMPTY;
                    if (a.prims | b.prims).intersects(PRIM_STRING) {
                        res |= PRIM_STRING;
                    }
                    let m = res | combine_num(add_number_bits(a), add_number_bits(b));
                    (m, int_range(a, Some(b)))
                }
                Sub | Mul => {
                    let b = b.unwrap();
                    (
                        combine_num(to_number_bits(a), to_number_bits(b)),
                        int_range(a, Some(b)),
                    )
                }
                Ursh => {
                    let b = b.unwrap();
                    (
                        combine_num(to_number_bits(a), to_number_bits(b)),
                        Range::I53,
                    )
                }
                Mod => {
                    let b = b.unwrap();
                    let (na, nb) = (to_number_bits(a), to_number_bits(b));
                    let m = if na.is_empty() || nb.is_empty() {
                        Prims::EMPTY
                    } else if na == PRIM_DOUBLE && nb == PRIM_DOUBLE {
                        PRIM_DOUBLE
                    } else {
                        NUM
                    };
                    let r = if coerced_range(a) <= Range::I53 && coerced_range(b) <= Range::I53 {
                        Range::I53
                    } else {
                        Range::Top
                    };
                    (m, r)
                }
                Div | Pow => {
                    let b = b.unwrap();
                    let (na, nb) = (to_number_bits(a), to_number_bits(b));
                    let m = if na.is_empty() || nb.is_empty() {
                        Prims::EMPTY
                    } else if na == PRIM_DOUBLE && nb == PRIM_DOUBLE {
                        PRIM_DOUBLE
                    } else {
                        NUM
                    };
                    (m, Range::Top)
                }
                Inc | Dec | Neg => (
                    combine_num(to_number_bits(a), PRIM_INT32),
                    int_range(a, None),
                ),
                Pos | ToNumeric => (to_number_bits(a), coerced_range(a)),
                _ => unreachable!("not routed at the likely level"),
            }
        }
    }

    fn likely_states() -> Vec<likely_oracle::Ts> {
        let mut v = Vec::new();
        for base in 0u16..64 {
            for unk in [false, true] {
                for objworld in [false, true] {
                    for range in [Range::I32, Range::I53, Range::Top] {
                        v.push(likely_oracle::Ts {
                            prims: Prims::from_bits(base),
                            unknown: unk,
                            objworld,
                            range,
                        });
                    }
                }
            }
        }
        v
    }

    fn likely_opnd(ts: &likely_oracle::Ts) -> Opnd {
        Opnd {
            prims: ts.prims,
            wild: ts.unknown || ts.objworld,
            range: ts.range,
        }
    }

    #[test]
    fn likely_matches_arith_transfer_oracle() {
        use NumOp::*;
        let states = likely_states();
        for a in &states {
            let oa = likely_opnd(a);
            for op in [Inc, Dec, Neg, Pos, ToNumeric] {
                assert_eq!(
                    result(op, &oa, None),
                    likely_oracle::arith_transfer(op, a, None),
                    "unary {op:?} prims {:?} obj {}",
                    a.prims,
                    a.objworld
                );
            }
            for b in &states {
                let ob = likely_opnd(b);
                for op in [Add, Sub, Mul, Div, Mod, Pow, Ursh] {
                    assert_eq!(
                        result(op, &oa, Some(&ob)),
                        likely_oracle::arith_transfer(op, a, Some(b)),
                        "binary {op:?} a {:?}/{} b {:?}/{}",
                        a.prims,
                        a.objworld,
                        b.prims,
                        b.objworld
                    );
                }
            }
        }
    }

    #[test]
    fn f64_track_rule() {
        assert_eq!(f64_track_result(true, true), PRIM_DOUBLE);
        assert_eq!(f64_track_result(true, false), NUM);
        assert_eq!(f64_track_result(false, false), NUM);
    }
}
