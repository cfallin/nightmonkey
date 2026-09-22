/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! The typeset lattice. Constant height by construction: prims are a small
//! bit mask, the fn set is bounded (`BoundedFnSet::MAX` ids plus an
//! overflow flag), and the object part raises at most
//! Empty -> One -> ClassAny -> AnyObject. A cell can change O(1) times, so
//! total solve work is O(edges x live contexts).

use crate::facts::Claim;
use crate::ids::ScriptId;
pub(crate) use crate::ids::{NameId, Names};
pub use crate::opsem::Prims;
use crate::opsem::{
    PRIM_BOOLEAN, PRIM_DOUBLE, PRIM_INT32, PRIM_NULL, PRIM_STRING, PRIM_SYMBOL, PRIM_UNDEFINED,
};
use rustc_hash::FxHashMap as HashMap;

/// Every primitive class the analysis models. BigInt is deliberately
/// absent: nothing in the analysis raises it.
pub const MODELED_PRIMS: Prims = Prims::from_bits(
    PRIM_INT32.bits()
        | PRIM_DOUBLE.bits()
        | PRIM_STRING.bits()
        | PRIM_UNDEFINED.bits()
        | PRIM_NULL.bits()
        | PRIM_BOOLEAN.bits(),
);

/// Numeric-magnitude component of the typeset product: the shared
/// vocabulary's `Range` (the coarse I32/I53/Top ladder, not an interval --
/// `Interval` below carries the bounds). Like the prim claims, transfer
/// results are optimistic where the lowering committed to optimism (i53
/// sums and disregard-overflow products claim I53; consumption guards
/// catch the rare violation).
pub use crate::opsem::Range;

/// The numeric/string operators with an operand-sensitive transfer
/// function (`arith_transfer`), from the shared vocabulary. Scan routes
/// the arith subset; the bitops keep their generic int32 result until
/// they grow magnitude-aware rules.
pub use crate::opsem::NumOp;

/// Inclusive integer interval, the shape both the exact literal folds and
/// the lattice component below are stated in.
pub use crate::opsem::ValueRange;

/// Value-interval component of a cell: the likely bounds of its Number
/// inhabitants. A prediction like every other typeset component --
/// consumed behind the object stamp's range conformance (checked stores
/// maintain it, the RANGES stamp bit asserts it), never as proof. It
/// reaches codegen as `ClassFieldFacts::range` and the range half of
/// `LikelyFacts::array_elem_claims`, where it folds bounds checks and
/// overflow checks a `Range` claim alone cannot.
///
/// This is the bounds dimension; `Range` above is the coarse
/// int32/i53/arbitrary ladder that says which machine domain a number
/// fits in. A consumer that folds an index check or an overflow check
/// away needs the bounds, and no widening of `Range` can express them.
///
/// - `In(r)`: every Number inhabitant -- reading -0 as 0 -- is a finite
///   integer in `r`. Bounds are always quantized (`opsem::hq`), which
///   makes `join` a plain hull: commutative, associative,
///   order-independent, finite height.
/// - `Num`: a number, with no bounds (NaN and fractions included).
/// - `Empty`: no numeric inhabitant has been seen.
/// - `Any`: no claim at all.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum Interval {
    #[default]
    Empty,
    In(ValueRange),
    Num,
    Any,
}

impl Interval {
    /// A single known integer value (quantized).
    pub fn of_value(v: i64) -> Interval {
        Interval::of_range(v, v)
    }

    pub fn of_range(lo: i64, hi: i64) -> Interval {
        match crate::opsem::hq(lo, hi) {
            Some((lo, hi)) => Interval::In(ValueRange::new(lo, hi)),
            None => Interval::Num,
        }
    }

    /// A snapshot double value: integral-and-exact doubles join like the
    /// int32 they canonically box to; any other double (fractional, NaN,
    /// infinite, -0) is an unbounded-but-Number claim.
    pub fn of_double(v: f64) -> Interval {
        if v == 0.0 && v.is_sign_negative() {
            return Interval::Num;
        }
        if v.fract() == 0.0 && v.abs() <= (1u64 << 53) as f64 {
            Interval::of_value(v as i64)
        } else {
            Interval::Num
        }
    }

    /// Whether joining `o` in could not widen this interval.
    pub fn subsumes(self, o: Interval) -> bool {
        Interval::join(self, o) == self
    }

    pub fn join(a: Interval, b: Interval) -> Interval {
        use Interval::*;
        match (a, b) {
            (Empty, x) | (x, Empty) => x,
            (Any, _) | (_, Any) => Any,
            (Num, _) | (_, Num) => Num,
            (In(r), In(s)) => In(r.hull(s)),
        }
    }
}

/// Projection of a typeset onto the shared vocabulary's operand view.
/// `Opnd` is deliberately narrower than a `TypeSet`: the op algebra is
/// written once for both this analysis and the lowering, so it may not
/// depend on either side's lattice (abstractions, fn sets, contexts here;
/// SSA operands and representations there). Unresolved evidence and any
/// live fn/object part are the wild world.
fn opnd(ts: &TypeSet) -> crate::opsem::Opnd {
    crate::opsem::Opnd {
        prims: ts.prims,
        wild: ts.unknown || !ts.fns.is_empty() || ts.obj != ObjType::Empty,
        range: ts.range,
    }
}

/// The interval view of an arith operand: no claim once the operand
/// admits values whose ToNumber is arbitrary (string, undefined, the
/// unknown world, objects); the boolean/null coercion targets are 0/1.
pub fn operand_interval(ts: &TypeSet) -> Interval {
    if ts.unknown
        || ts.prims.intersects(PRIM_UNDEFINED | PRIM_STRING)
        || !ts.fns.is_empty()
        || ts.obj != ObjType::Empty
    {
        return Interval::Any;
    }
    let mut h = ts.interval;
    if ts.prims.intersects(PRIM_BOOLEAN | PRIM_NULL) {
        h = Interval::join(h, Interval::In(ValueRange::new(0, 1)));
    }
    h
}

/// Exact scan-time literal fold (no quantization): the interval of `op`
/// over known literal intervals, None when the op or operands leave the
/// exact domain. -0 read as 0, as everywhere in this channel.
pub fn arith_lit(op: NumOp, a: ValueRange, b: Option<ValueRange>) -> Option<ValueRange> {
    let r = iv_transfer(op, exact_iv(a), b.map(exact_iv), false)?;
    Some(ValueRange::new(r.0, r.1))
}

/// A literal interval in the shared algebra's internal form (never -0).
fn exact_iv(r: ValueRange) -> crate::opsem::Iv {
    Some((r.lo, r.hi, false))
}

/// The shared algebra over one op. `binary_needs_b` reports an absent
/// second operand as "no result" for the binary ops.
fn iv_transfer(
    op: NumOp,
    a: crate::opsem::Iv,
    b: Option<crate::opsem::Iv>,
    unbounded_b: bool,
) -> Option<(i64, i64, bool)> {
    use crate::opsem as o;
    use NumOp::*;
    if !op.unary() && b.is_none() && !unbounded_b {
        return None;
    }
    let b = b.unwrap_or(None);
    let one: o::Iv = Some((1, 1, false));
    match op {
        Add => o::iv_add(a, b),
        Sub => o::iv_sub(a, b),
        Mul => o::iv_mul(a, b),
        Mod => o::iv_mod(a, b),
        Div | Pow => None,
        Inc => o::iv_add(a, one),
        Dec => o::iv_sub(a, one),
        Neg => o::iv_neg(a),
        Pos | ToNumeric => a,
        Ursh => o::iv_ursh(a, b),
        BitAnd => o::iv_bitand(a, b),
        BitOr | BitXor => o::iv_bitorxor(a, b),
        Lsh => o::iv_lsh(a, b),
        Rsh => o::iv_rsh(a, b),
        BitNot => o::iv_bitnot(a),
    }
}

/// Interval transfer for the arith constraint: the shared exact-integer
/// algebra with -0 read as 0 on both sides (sound for the modeled ops
/// because a possibly--0 operand's claim already contains 0), result
/// re-quantized. `Empty` operands claim nothing -- the prim-mask result
/// is empty there too, so the raise is skipped. `a_lit`/`b_lit` are the
/// exact scan-time literal intervals riding the constraint: cells hold
/// only quantized bounds, and the shift/mask rules need the literal
/// (`iv_lsh` keys on a constant shift count).
pub fn arith_interval(
    op: NumOp,
    a: Interval,
    a_lit: Option<ValueRange>,
    b: Option<Interval>,
    b_lit: Option<ValueRange>,
) -> Interval {
    let cv = |h: Interval, lit: Option<ValueRange>| -> Option<crate::opsem::Iv> {
        if let Some(r) = lit {
            return Some(exact_iv(r));
        }
        match h {
            Interval::Empty => None,
            Interval::In(r) => Some(exact_iv(r)),
            Interval::Num | Interval::Any => Some(None),
        }
    };
    let Some(ia) = cv(a, a_lit) else {
        return Interval::Empty;
    };
    let ib = match b.map(|h| cv(h, b_lit)) {
        Some(None) => return Interval::Empty,
        Some(Some(iv)) => Some(iv),
        None => None,
    };
    // Every modeled op except Add coerces to numbers, so an unbounded
    // result is still a number unless an operand admits Add's concat
    // side (an `Any` operand may be a string).
    let unbounded = if op == NumOp::Add && (a == Interval::Any || b == Some(Interval::Any)) {
        Interval::Any
    } else {
        Interval::Num
    };
    match iv_transfer(op, ia, ib, true) {
        Some((lo, hi, _)) => Interval::of_range(lo, hi),
        None => unbounded,
    }
}

/// Result (prim mask, range) for an arith op over operand typesets: the
/// opsem vocabulary at the Likely stance (the optimistic ladder bbv's
/// lowering committed to; every consumer guards or fences). Monotone in
/// both operands (fixpoint-safe).
pub fn arith_transfer(op: NumOp, a: &TypeSet, b: Option<&TypeSet>) -> (Prims, Range) {
    let ob = b.map(opnd);
    crate::opsem::result(op, &opnd(a), ob.as_ref())
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct AbsId(pub u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct ClassId(pub u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct CtxId(pub u32);

/// The distinguished generic context (empty call string), shared by all
/// scripts.
pub const CTX0: CtxId = CtxId(0);

/// A callable value the analysis can name: a compiled script, or one of
/// the builtins it models. Builtins live at the top of the id space so a
/// builtin flows through cells exactly like a scripted callable -- `var
/// Vector = Array` has to carry Array-ness through the aliasing code,
/// which is ordinary analyzed bytecode even though `Array` itself is not.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct FnId(u32);

impl FnId {
    /// Base of the reserved space: everything at or above it is a builtin.
    /// `NATIVE_BASE + idx` is a named native, indexing the solver's
    /// native-name table.
    const NATIVE_BASE: u32 = u32::MAX - 4096;
    /// `Array` itself.
    const ARRAY: u32 = u32::MAX - 64;
    /// `TYPED_ARRAY_BASE + kind` is the typed-array constructor of that
    /// element kind.
    const TYPED_ARRAY_BASE: u32 = u32::MAX - 63;

    /// The `Array` constructor.
    pub const ARRAY_CTOR: FnId = FnId(Self::ARRAY);

    pub const fn script(s: ScriptId) -> FnId {
        FnId(s.get())
    }

    /// The typed-array constructor of element kind `kind`.
    pub fn typed_array_ctor(kind: crate::opsem::TaKind) -> FnId {
        FnId(Self::TYPED_ARRAY_BASE + u32::from(kind.code()))
    }

    /// The named native at `idx` in the solver's native-name table. A
    /// native value flows through cells like any callable; its call result
    /// comes from the spec-derived table (`heap::NATIVE_RESULTS`), or
    /// raises unresolved evidence when unmodeled.
    pub fn native(idx: u32) -> FnId {
        debug_assert!(
            Self::NATIVE_BASE + idx < Self::ARRAY,
            "native id space exhausted"
        );
        FnId(Self::NATIVE_BASE + idx)
    }

    /// Whether this is one of the modeled builtins rather than a script.
    pub const fn is_builtin(self) -> bool {
        self.0 >= Self::NATIVE_BASE
    }

    /// The script behind a scripted callable.
    pub const fn as_script(self) -> Option<ScriptId> {
        if self.is_builtin() {
            None
        } else {
            Some(ScriptId::new(self.0))
        }
    }

    /// The native-name table index of a named native (spec-table call
    /// semantics, as opposed to the Array/typed-array ctors' allocation
    /// semantics).
    pub const fn native_index(self) -> Option<u32> {
        if self.0 >= Self::NATIVE_BASE && self.0 < Self::ARRAY {
            Some(self.0 - Self::NATIVE_BASE)
        } else {
            None
        }
    }

    /// The element kind of a typed-array constructor.
    pub const fn typed_array_kind(self) -> Option<crate::opsem::TaKind> {
        if self.0 >= Self::TYPED_ARRAY_BASE {
            crate::opsem::TaKind::from_code((self.0 - Self::TYPED_ARRAY_BASE) as u8)
        } else {
            None
        }
    }

    /// The raw id, for diagnostics only.
    pub const fn get(self) -> u32 {
        self.0
    }
}

impl std::fmt::Display for FnId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A set of callables, bounded by `BoundedFnSet::MAX`. Past the cap the
/// set is `multi` (megamorphic) and the ids are dropped: it no longer
/// drives call resolution or fact emission. The cap is what keeps the
/// lattice constant-height.
#[derive(Clone, Default, PartialEq, Eq, Debug)]
pub struct BoundedFnSet {
    ids: Vec<FnId>,
    multi: bool,
}

impl BoundedFnSet {
    /// Ids tracked before the set collapses to `multi`.
    pub const MAX: usize = 8;

    pub fn one(f: FnId) -> BoundedFnSet {
        BoundedFnSet {
            ids: vec![f],
            multi: false,
        }
    }

    pub fn is_empty(&self) -> bool {
        !self.multi && self.ids.is_empty()
    }

    pub fn is_multi(&self) -> bool {
        self.multi
    }

    /// Resolved ids (empty when multi).
    pub fn ids(&self) -> &[FnId] {
        &self.ids
    }

    /// `dropped` receives the scripted ids a multi transition discards
    /// (recorded for diagnostics; currently unconsumed).
    pub fn insert(&mut self, f: FnId, dropped: &mut Vec<FnId>) -> bool {
        if self.multi {
            return false;
        }
        match self.ids.binary_search(&f) {
            Ok(_) => false,
            Err(i) => {
                if self.ids.len() == Self::MAX {
                    dropped.extend(self.ids.iter().chain([&f]).filter(|x| !x.is_builtin()));
                    self.ids = Vec::new();
                    self.multi = true;
                } else {
                    self.ids.insert(i, f);
                }
                true
            }
        }
    }

    pub fn set_multi(&mut self, dropped: &mut Vec<FnId>) -> bool {
        if self.multi {
            return false;
        }
        dropped.extend(self.ids.iter().filter(|x| !x.is_builtin()));
        self.ids = Vec::new();
        self.multi = true;
        true
    }

    pub fn join_from(&mut self, o: &BoundedFnSet, dropped: &mut Vec<FnId>) -> bool {
        if o.multi {
            return self.set_multi(dropped);
        }
        let mut changed = false;
        for &f in &o.ids {
            changed |= self.insert(f, dropped);
        }
        changed
    }

    /// The scripted members, as an owned list.
    ///
    /// Owned rather than borrowed on purpose: every caller iterates while
    /// mutating the solver, so a borrowing iterator would not compile. The
    /// sets are at most `MAX` long.
    pub fn scripted(&self) -> Vec<ScriptId> {
        self.ids().iter().filter_map(|f| f.as_script()).collect()
    }

    /// This set with the modeled builtins (the Array and typed-array
    /// constructors, the named natives) dropped.
    ///
    /// Those ids carry allocation or spec-table semantics, never a body the
    /// translator could dispatch to, so every consumer that wants "the
    /// callees this site could actually enter" filters them out first. A
    /// saturated set stays saturated: it has already lost the identities
    /// that would decide.
    pub fn scripted_only(&self, dropped: &mut Vec<FnId>) -> BoundedFnSet {
        let mut out = BoundedFnSet::default();
        if self.is_multi() {
            out.set_multi(dropped);
            return out;
        }
        for &f in self.ids() {
            if !f.is_builtin() {
                out.insert(f, dropped);
            }
        }
        out
    }

    /// Whether joining `self` into `o` would be a no-op.
    pub fn is_subset_of(&self, o: &BoundedFnSet) -> bool {
        if o.multi {
            return true;
        }
        if self.multi {
            return false;
        }
        self.ids.iter().all(|f| o.ids.binary_search(f).is_ok())
    }
}

/// What the lattice join needs to know about one heap abstraction, held
/// by the engine (indexed by [`AbsId`]) and fixed at intern time --
/// order-independence of joins depends on it never changing afterwards.
///
/// The abstraction itself is `heap::Abstraction`, a heap-layer record that
/// keeps growing as the analysis learns; its *contents* are not in either
/// record but in the engine's cell graph, one `CellKey::Field` cell per
/// (abstraction, property name).
#[derive(Clone, Copy, Default, Debug)]
pub struct AbsLabels {
    pub class: Option<ClassId>,
    /// Snapshot abstraction: preferred in a One+One join against a
    /// non-snap alloc (a setup-time allocation flowing into a snapshotted
    /// binding IS the snapshot object; wrong cases cost a guard miss).
    pub snap: bool,
    /// Plain-array abstraction: two array-classed objects meeting union
    /// their site classes (engine-side union-find) instead of joining to
    /// AnyObject: unify-on-meet element nodes, as labels. This is what
    /// keeps a pair of buffers swapped round-robin through a loop from
    /// losing their element type at the swap.
    pub array: bool,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ObjType {
    Empty,
    /// Exactly one abstraction.
    One(AbsId),
    /// Some abstraction of this likely-class.
    ClassAny(ClassId),
    /// Some instance of a *region*: the set of classes that have actually
    /// met somewhere in this program's flow, tracked as a union-find over
    /// classes and labelled here by its root (`Engine::region_root` keeps the
    /// label current, since later meets can move the root). One word, no
    /// cap: a region that grows large simply resolves to a megamorphic
    /// method union, which yields no fact -- the same outcome as
    /// `AnyObject`, so growth degrades smoothly instead of falling off a
    /// cliff.
    ///
    /// Only call-target resolution reads it. A per-field claim must not:
    /// a region is a flow-scoped upper bound on *which classes met*, and
    /// merging the field masks of everything in it produces a claim so
    /// weak it costs more than it buys.
    AnyOf(ClassId),
    /// Any object at all -- no class survived the join.
    AnyObject,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TypeSet {
    pub prims: Prims,
    pub fns: BoundedFnSet,
    pub obj: ObjType,
    /// Meaningful only alongside numeric prim bits; bottom (I32)
    /// otherwise.
    pub range: Range,
    /// Some flow produced this value but the analysis could not say what
    /// (a megamorphic or unresolved call result, an unmodeled builtin or
    /// snapshot value, a read off an unknown receiver). Distinct from an
    /// empty `prims` set, which means nothing ever flowed here at all.
    ///
    /// It propagates like a prim class and blocks every value claim, but
    /// is invisible to fn/obj resolution -- which is why it is a field of
    /// its own rather than a bit in `prims`: it is not a primitive class,
    /// and no emitted fact may carry it. See [`TypeSet::unresolved`].
    pub unknown: bool,
    /// Bounds claim over the Number inhabitants (see [`Interval`]).
    /// Constructors must keep the invariant that a set whose mask admits
    /// numeric-or-unknown values without a known interval carries `Any`
    /// (or `Num`), never `Empty`.
    pub interval: Interval,
}

/// Upper bound on the number of changing raises a single cell can take:
/// 7 prim bits + 9 fn-set growths (8 inserts + multi) + 3 obj raises,
/// plus one One->One snap-preference absorption, plus the array-class
/// union-find label lowerings -- 64 covered all of that. The heap
/// interval adds its ladder ascents: ~36 rungs per bound (magnitudes
/// under 8 exact, then one rung per octave to int32) on each of two
/// bounds, plus the Num/Any rungs, and exact non-ladder bounds from
/// future checked-store clamps sit between them; 768 is the
/// corresponding generous bound.
pub const MAX_CELL_CHANGES: u16 = 768;

impl Default for TypeSet {
    fn default() -> TypeSet {
        TypeSet {
            prims: Prims::EMPTY,
            unknown: false,
            fns: BoundedFnSet::default(),
            obj: ObjType::Empty,
            range: Range::I32,
            interval: Interval::Empty,
        }
    }
}

/// The `interval` a bare prim set supports: numeric classes with no value in
/// hand are unbounded numbers.
fn prims_interval(prims: Prims) -> Interval {
    if prims.intersects(PRIM_INT32 | PRIM_DOUBLE) {
        Interval::Num
    } else {
        Interval::Empty
    }
}

impl TypeSet {
    /// The top of the lattice: every primitive class, every function,
    /// every object, any magnitude. Nothing can be claimed about a value
    /// with this typeset.
    pub fn any() -> TypeSet {
        TypeSet {
            prims: MODELED_PRIMS,
            unknown: true,
            fns: BoundedFnSet {
                ids: Vec::new(),
                multi: true,
            },
            obj: ObjType::AnyObject,
            range: Range::Top,
            interval: Interval::Any,
        }
    }

    /// A value the analysis knows arrived but cannot name: top for the
    /// function and object dimensions, but with an *empty* primitive set
    /// and the `unknown` flag instead of the full primitive set that
    /// [`TypeSet::any`] carries.
    ///
    /// The difference is the whole point. `prims` is evidence: a bit set
    /// there says "a string was actually seen flowing here", and the claim
    /// tiers weigh that evidence when they decide what to predict. Setting
    /// all seven bits for a value nobody could resolve fabricates evidence
    /// that was never observed -- and since the tiers cannot tell a
    /// fabricated string bit from a real one, one unresolved call result
    /// flowing into a field poisons that field's claim as thoroughly as a
    /// genuinely string-valued write would. The `unknown` flag says the
    /// same thing honestly ("something got here, contents unknown"), and
    /// the tiers can then treat it as a claim to make behind a guard
    /// rather than as counter-evidence.
    ///
    /// Used where flow leaves the analysis's sight: escaping functions,
    /// megamorphic and unmodeled calls, reads off receivers that lost
    /// their class.
    pub fn unresolved() -> TypeSet {
        TypeSet {
            prims: Prims::EMPTY,
            unknown: true,
            fns: BoundedFnSet {
                ids: Vec::new(),
                multi: true,
            },
            obj: ObjType::AnyObject,
            range: Range::Top,
            interval: Interval::Any,
        }
    }

    /// Double evidence with no value in hand is arbitrary (Top); int32
    /// evidence is I32 by definition.
    pub fn prim(prims: Prims) -> TypeSet {
        TypeSet {
            prims,
            range: if prims.intersects(PRIM_DOUBLE) {
                Range::Top
            } else {
                Range::I32
            },
            interval: prims_interval(prims),
            ..TypeSet::default()
        }
    }

    /// A cell holding only unresolved evidence (see [`TypeSet::unknown`]).
    pub fn unknown_evidence() -> TypeSet {
        TypeSet {
            unknown: true,
            range: Range::Top,
            interval: Interval::Any,
            ..TypeSet::default()
        }
    }

    /// A numeric mask with a known value interval (snapshot seeds, arith
    /// results). The interval is quantized here -- cells only ever hold
    /// quantized bounds.
    pub fn prim_interval(prims: Prims, range: Range, interval: Interval) -> TypeSet {
        TypeSet {
            prims,
            range,
            interval,
            ..TypeSet::default()
        }
    }

    pub fn fn_one(f: FnId) -> TypeSet {
        TypeSet {
            fns: BoundedFnSet::one(f),
            ..TypeSet::default()
        }
    }

    pub fn obj_one(a: AbsId) -> TypeSet {
        TypeSet {
            obj: ObjType::One(a),
            ..TypeSet::default()
        }
    }

    /// Nothing ever flowed here. Unresolved evidence is not empty: a value
    /// did arrive, the analysis just could not name it.
    pub fn is_empty(&self) -> bool {
        self.prims.is_empty() && !self.unknown && self.fns.is_empty() && self.obj == ObjType::Empty
    }

    /// Monotone join; `meta` maps an abstraction to its (immutable,
    /// assigned-at-creation) class label and snap bit, which is what makes
    /// the join order-independent. `sink` records One+One absorptions
    /// (snap preference): the interval dimension merges the absorbed
    /// loser's cells into the survivor's so One-receiver range
    /// predictions see the loser's writes (dropped fn ids are recorded
    /// too but currently unconsumed). Returns whether `self` grew.
    pub fn join_from(&mut self, o: &TypeSet, meta: &[AbsLabels], sink: &mut JoinSink) -> bool {
        let mut changed = false;
        if !o.prims.subset_of(self.prims) {
            self.prims |= o.prims;
            changed = true;
        }
        if o.unknown && !self.unknown {
            self.unknown = true;
            changed = true;
        }
        changed |= self.fns.join_from(&o.fns, &mut sink.dropped_fns);
        let joined = join_obj(self.obj, o.obj, meta);
        if let (ObjType::One(x), ObjType::One(y)) = (self.obj, o.obj) {
            if x != y {
                if let ObjType::One(z) = joined {
                    sink.snap_absorbs.push((z, if z == x { y } else { x }));
                }
            }
        }
        if joined != self.obj {
            self.obj = joined;
            changed = true;
        }
        if o.range > self.range {
            self.range = o.range;
            changed = true;
        }
        let h = Interval::join(self.interval, o.interval);
        if h != self.interval {
            self.interval = h;
            changed = true;
        }
        changed
    }

    /// The purely-numeric projection: the primitive set, when every value
    /// that reached this cell was a number and nothing else -- no
    /// functions, no objects, and no unresolved evidence.
    ///
    /// This is the gate every numeric claim goes through. `unknown`
    /// disqualifies for the same reason a string bit would: an unresolved
    /// value could have been anything, so a numeric claim over it would be
    /// a guess with no evidence behind it.
    pub fn pure_numeric(&self) -> Option<Prims> {
        if !self.prims.is_empty()
            && self.prims.subset_of(PRIM_INT32 | PRIM_DOUBLE)
            && !self.unknown
            && self.fns.is_empty()
            && self.obj == ObjType::Empty
        {
            Some(self.prims)
        } else {
            None
        }
    }

    /// Exactly one non-numeric primitive class (string, or boolean) and
    /// nothing else: the single-tag claims the guard-at-defs ladder can
    /// validate with one test. Mixed sets stay unclaimed -- a two-tag
    /// dispatch is the generic path's job.
    fn pure_single_prim(&self, prim: Prims) -> bool {
        self.prims == prim && !self.unknown && self.fns.is_empty() && self.obj == ObjType::Empty
    }

    /// The i53 law's contrapositive: double evidence at range Top is
    /// fractional-reachable -- a real runtime double population -- while
    /// I53-ranged double evidence (integral producers) is not.
    pub fn fractional_reachable(&self) -> bool {
        self.prims.intersects(PRIM_DOUBLE) && self.range == Range::Top
    }

    /// String evidence: a real string population flows through the cell.
    pub fn string_reachable(&self) -> bool {
        self.prims.intersects(PRIM_STRING)
    }

    /// [`TypeSet::pure_numeric`] as a claim, plus the double-first hint:
    /// double evidence at range Top is fractional-reachable and therefore
    /// a real runtime double population, while I53 double evidence
    /// (integral producers, such as the accumulating sums of a bignum
    /// kernel) is the dead-path case and must not set the hint.
    /// Unresolved evidence needs no extra fence here: `pure_numeric`
    /// already rejects it, so a surviving `PRIM_DOUBLE` is direct.
    pub fn numeric_claim(&self) -> Option<Claim> {
        let prims = self.pure_numeric()?;
        let claim = Claim::of_prims(prims);
        Some(
            if prims.intersects(PRIM_DOUBLE) && self.range == Range::Top {
                claim.with_double_first()
            } else {
                claim
            },
        )
    }

    /// The full per-site claim tier (guard-at-defs): a purely-numeric
    /// claim (with the double-first hint where fractional-reachable), or
    /// [`Claim::OBJECT`] when every observed value is an object or
    /// function (`unknown` refuses the object claim exactly as it poisons
    /// the numeric one).
    ///
    /// `null`/`undefined` refuse the claim, and that is not conservatism
    /// -- admitting them is a large loss. The claim
    /// is consumed behind a TAG_OBJECT test whose miss arm continues at
    /// the next pc with a bottom value, and for a field the program
    /// explicitly null-checks -- `var packet = this.queue; if (packet ==
    /// null) ...` -- the null case is not an exception, it is half the
    /// control flow. Every list terminator then deopts the rest of the
    /// block. Version counts barely move, so the cost is the arm being
    /// taken, not version growth.
    ///
    /// The type such a field deserves is `null|obj`, which needs no test
    /// at all -- but a TypeDesc is a proof (`is_object_only` elides
    /// receiver tag tests off it), and the analysis only has a prediction.
    /// So a nullable object field's read stays bottom, correctly.
    pub fn site_claim(&self) -> Option<Claim> {
        let claim = self.value_claim()?;
        Some(
            if !claim.is_object() && self.prims.intersects(PRIM_DOUBLE) && self.range == Range::Top
            {
                claim.with_double_first()
            } else {
                claim
            },
        )
    }

    /// [`TypeSet::site_claim`] without the double-first hint: the claim
    /// itself.
    ///
    /// The hint is an arm-*order* hint for a per-site ladder, so a claim
    /// with no ladder behind it -- a per-script formal, whose consumer is
    /// one guard at entry -- takes this one instead.
    pub fn value_claim(&self) -> Option<Claim> {
        if let Some(prims) = self.pure_numeric() {
            let claim = Claim::of_prims(prims);
            // The fractional annotation, exactly as `numeric_claim`: double
            // evidence at range Top means a real fractional population
            // flows through the cell (the i53 law's contrapositive), which
            // is what routes a mixed entry claim to the tolerant
            // number-tag shape instead of the exact int32 one.
            return Some(
                if prims.intersects(PRIM_DOUBLE) && self.range == Range::Top {
                    claim.with_double_first()
                } else {
                    claim
                },
            );
        }
        (self.prims.is_empty()
            && !self.unknown
            && (self.obj != ObjType::Empty || !self.fns.is_empty()))
        .then_some(Claim::OBJECT)
    }

    /// The object claim with nullish tolerance: object-or-nullish and
    /// nothing else. The consumer's per-read tag guard routes the nullish
    /// population to the side arm, so the claim is likely-not-proof like
    /// every other; the payer is the read whose object-only pass arm
    /// kills downstream dead arms (mandreel's heap views: hoisted `var`
    /// declarations put `undefined` in every view gname cell even though
    /// `initHeap` ran before the snapshot, and that evidence alone was
    /// blocking the receiver claim that retires the element string arm).
    pub fn object_claim_nullish(&self) -> Option<Claim> {
        (self.prims.subset_of(PRIM_NULL | PRIM_UNDEFINED)
            && !self.unknown
            && (self.obj != ObjType::Empty || !self.fns.is_empty()))
        .then_some(Claim::OBJECT)
    }

    /// `value_claim` extended with the single-tag string/boolean shapes.
    /// A separate tier on purpose: these claims mint a NEW tag test at the
    /// consuming read, so they belong only where the guard rides an
    /// existing validation (entry claims) or replaces a downstream re-test
    /// (gname/aliased/elem reads). Field and call-result sites stay on
    /// `value_claim`: an un-demanded string/bool claim there is a guard
    /// with no payer.
    pub fn value_claim_full(&self) -> Option<Claim> {
        if self.pure_single_prim(PRIM_STRING) {
            return Some(Claim::of_prims(PRIM_STRING));
        }
        if self.pure_single_prim(PRIM_BOOLEAN) {
            return Some(Claim::of_prims(PRIM_BOOLEAN));
        }
        if self.pure_single_prim(PRIM_SYMBOL) {
            return Some(Claim::of_prims(PRIM_SYMBOL));
        }
        self.value_claim()
    }
}

/// A value that several independent observations have to agree on.
///
/// The lattice is `Unset -> One(v) -> Conflict`, sticky at the top: once
/// two observations disagree the entry never recovers, because a later
/// agreeing observation says nothing about the one that disagreed.
///
/// The analysis reaches for this shape constantly -- which class a site's
/// receiver settled on, which constructor homes a method, which native a
/// call site resolved to, which element kind an array site sees -- and
/// one type states the rule once, instead of each call site improvising
/// its own convention for unset vs. one vs. conflicting.
///
/// `Unset` and `Conflict` are deliberately distinct. "Nothing ever arrived
/// here" and "several things did and they disagreed" are different answers,
/// and only the second is evidence about the program.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum Agreed<V> {
    #[default]
    Unset,
    One(V),
    Conflict,
}

impl<V: PartialEq> Agreed<V> {
    /// Record one observation.
    pub fn observe(&mut self, v: V) {
        match self {
            Agreed::Unset => *self = Agreed::One(v),
            Agreed::One(cur) if *cur == v => {}
            Agreed::One(_) => *self = Agreed::Conflict,
            Agreed::Conflict => {}
        }
    }

    /// The value, while every observation agreed on it.
    pub fn get(&self) -> Option<&V> {
        match self {
            Agreed::One(v) => Some(v),
            _ => None,
        }
    }
}

impl<V: PartialEq + Copy> Agreed<V> {
    pub fn value(&self) -> Option<V> {
        self.get().copied()
    }
}

/// Record one observation into an agreement table.
pub fn observe<K: std::hash::Hash + Eq, V: PartialEq>(
    map: &mut HashMap<K, Agreed<V>>,
    key: K,
    value: V,
) {
    map.entry(key).or_default().observe(value);
}

/// [`Agreed`] over a bounded *set* rather than a single value: it agrees
/// while at most `cap` distinct values arrive and collapses past that.
///
/// Used where several answers are still useful -- a receiver whose classes
/// all live in one region is a fact even though it is not one class -- but
/// an unbounded list is not: past a handful the site is megamorphic and the
/// set says nothing a guard could use.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub enum AgreedSet<V> {
    #[default]
    Unset,
    Some(Vec<V>),
    Conflict,
}

impl<V: PartialEq> AgreedSet<V> {
    /// Record one observed member.
    pub fn observe(&mut self, v: V, cap: usize) {
        match self {
            AgreedSet::Unset => *self = AgreedSet::Some(vec![v]),
            AgreedSet::Some(vs) if vs.contains(&v) => {}
            AgreedSet::Some(vs) if vs.len() < cap => vs.push(v),
            AgreedSet::Some(_) => *self = AgreedSet::Conflict,
            AgreedSet::Conflict => {}
        }
    }

    /// Record an observation that cannot be named, which no set can absorb.
    pub fn conflict(&mut self) {
        *self = AgreedSet::Conflict;
    }

    /// The members, while the set still agrees.
    pub fn get(&self) -> Option<&[V]> {
        match self {
            AgreedSet::Some(vs) => Some(vs),
            _ => None,
        }
    }
}

/// Side-channel of join events the interval channel consumes (see
/// `TypeSet::join_from`).
#[derive(Default)]
pub struct JoinSink {
    /// Scripted fn ids discarded by BoundedFnSet multi transitions: those
    /// scripts may run through the saturated set with unbound arguments.
    pub dropped_fns: Vec<FnId>,
    /// One+One absorptions as (survivor, loser): a One(survivor)
    /// receiver's population silently includes the absorbed loser (its
    /// range predictions may then under-shoot; the runtime conformance
    /// bit absorbs the miss).
    pub snap_absorbs: Vec<(AbsId, AbsId)>,
}

fn class_of(a: AbsId, meta: &[AbsLabels]) -> Option<ClassId> {
    meta.get(a.0 as usize).and_then(|m| m.class)
}

fn is_snap(a: AbsId, meta: &[AbsLabels]) -> bool {
    meta.get(a.0 as usize).is_some_and(|m| m.snap)
}

/// The pure join (no union-find access): region-rescuing joins live in
/// `Engine::join_ts`, which falls back to this and upgrades AnyObject
/// results to AnyOf where both sides carry classes.
pub fn join_obj(a: ObjType, b: ObjType, meta: &[AbsLabels]) -> ObjType {
    use ObjType::*;
    match (a, b) {
        (Empty, x) | (x, Empty) => x,
        (AnyObject, _) | (_, AnyObject) => AnyObject,
        (AnyOf(r), AnyOf(s)) => {
            if r == s {
                AnyOf(r)
            } else {
                AnyObject
            }
        }
        (AnyOf(_), _) | (_, AnyOf(_)) => AnyObject,
        (One(x), One(y)) if x == y => One(x),
        (One(x), One(y)) => {
            // Snap preference (see AbsLabels::snap). Deliberately
            // non-associative in the three-way snap+alloc+alloc case;
            // deterministic under the fifo worklist.
            if is_snap(x, meta) && !is_snap(y, meta) {
                return One(x);
            }
            if is_snap(y, meta) && !is_snap(x, meta) {
                return One(y);
            }
            match (class_of(x, meta), class_of(y, meta)) {
                (Some(c), Some(d)) if c == d => ClassAny(c),
                _ => AnyObject,
            }
        }
        (One(x), ClassAny(c)) | (ClassAny(c), One(x)) => {
            if class_of(x, meta) == Some(c) {
                ClassAny(c)
            } else {
                AnyObject
            }
        }
        (ClassAny(c), ClassAny(d)) => {
            if c == d {
                ClassAny(c)
            } else {
                AnyObject
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Shorthand for an interval bound pair.
    fn iv(lo: i64, hi: i64) -> ValueRange {
        ValueRange::new(lo, hi)
    }

    #[test]
    fn snap_preference() {
        use ObjType::*;
        let meta = vec![
            AbsLabels {
                class: None,
                snap: true,
                array: false,
            },
            AbsLabels::default(),
        ];
        let s = AbsId(0);
        let a = AbsId(1);
        assert_eq!(join_obj(One(s), One(a), &meta), One(s));
        assert_eq!(join_obj(One(a), One(s), &meta), One(s));
        assert_eq!(join_obj(One(s), One(s), &meta), One(s));
    }

    #[test]
    fn obj_join_table() {
        use ObjType::*;
        // abs 0,1 -> class 0; abs 2 -> class 1; abs 3 -> no class
        let cm = |c: Option<ClassId>| AbsLabels {
            class: c,
            snap: false,
            array: false,
        };
        let ac = vec![
            cm(Some(ClassId(0))),
            cm(Some(ClassId(0))),
            cm(Some(ClassId(1))),
            cm(None),
        ];
        let a0 = AbsId(0);
        let a1 = AbsId(1);
        let a2 = AbsId(2);
        let a3 = AbsId(3);
        assert_eq!(join_obj(One(a0), One(a0), &ac), One(a0));
        assert_eq!(join_obj(One(a0), One(a1), &ac), ClassAny(ClassId(0)));
        assert_eq!(join_obj(One(a0), One(a2), &ac), AnyObject);
        assert_eq!(join_obj(One(a0), One(a3), &ac), AnyObject);
        assert_eq!(
            join_obj(One(a0), ClassAny(ClassId(0)), &ac),
            ClassAny(ClassId(0))
        );
        assert_eq!(join_obj(One(a0), ClassAny(ClassId(1)), &ac), AnyObject);
        assert_eq!(
            join_obj(ClassAny(ClassId(0)), ClassAny(ClassId(0)), &ac),
            ClassAny(ClassId(0))
        );
        assert_eq!(
            join_obj(ClassAny(ClassId(0)), ClassAny(ClassId(1)), &ac),
            AnyObject
        );
        assert_eq!(join_obj(Empty, One(a0), &ac), One(a0));
        assert_eq!(join_obj(AnyObject, One(a0), &ac), AnyObject);
    }

    #[test]
    fn arith_ladder() {
        use NumOp::*;
        let i = TypeSet::prim(PRIM_INT32);
        let d = TypeSet::prim(PRIM_DOUBLE);
        let s = TypeSet::prim(PRIM_STRING);
        let id = TypeSet::prim(PRIM_INT32 | PRIM_DOUBLE);
        let si = TypeSet::prim(PRIM_STRING | PRIM_INT32);
        let bl = TypeSet::prim(PRIM_BOOLEAN);
        let o = TypeSet::obj_one(AbsId(0));
        let e = TypeSet::default();
        let m = |t: (Prims, Range)| t.0;
        assert_eq!(arith_transfer(Add, &i, Some(&i)), (PRIM_INT32, Range::I53));
        assert_eq!(
            m(arith_transfer(Add, &i, Some(&d))),
            PRIM_INT32 | PRIM_DOUBLE
        );
        assert_eq!(m(arith_transfer(Add, &d, Some(&d))), PRIM_DOUBLE);
        assert_eq!(arith_transfer(Add, &s, Some(&i)), (PRIM_STRING, Range::Top));
        assert_eq!(
            m(arith_transfer(Add, &si, Some(&i))),
            PRIM_STRING | PRIM_INT32
        );
        assert!(m(arith_transfer(Add, &e, Some(&i))).is_empty());
        assert_eq!(arith_transfer(Sub, &i, Some(&i)), (PRIM_INT32, Range::I53));
        assert_eq!(arith_transfer(Mul, &i, Some(&i)), (PRIM_INT32, Range::I53));
        assert_eq!(
            m(arith_transfer(Mul, &i, Some(&d))),
            PRIM_INT32 | PRIM_DOUBLE
        );
        assert_eq!(
            arith_transfer(Div, &i, Some(&i)),
            (PRIM_INT32 | PRIM_DOUBLE, Range::Top)
        );
        assert_eq!(m(arith_transfer(Div, &d, Some(&d))), PRIM_DOUBLE);
        assert!(m(arith_transfer(Div, &e, Some(&d))).is_empty());
        assert_eq!(arith_transfer(Inc, &i, None), (PRIM_INT32, Range::I53));
        assert_eq!(m(arith_transfer(Inc, &id, None)), PRIM_INT32 | PRIM_DOUBLE);
        assert!(m(arith_transfer(Inc, &e, None)).is_empty());
        assert_eq!(m(arith_transfer(Neg, &i, None)), PRIM_INT32);
        assert_eq!(
            arith_transfer(Sub, &s, Some(&i)),
            (PRIM_INT32 | PRIM_DOUBLE, Range::Top)
        );
        assert_eq!(m(arith_transfer(Sub, &bl, Some(&i))), PRIM_INT32);
        assert_eq!(
            m(arith_transfer(Sub, &o, Some(&i))),
            PRIM_INT32 | PRIM_DOUBLE
        );
        assert_eq!(arith_transfer(Pos, &d, None), (PRIM_DOUBLE, Range::Top));
        assert_eq!(m(arith_transfer(ToNumeric, &i, None)), PRIM_INT32);
        assert_eq!(
            m(arith_transfer(Ursh, &TypeSet::unknown_evidence(), Some(&i))),
            PRIM_INT32 | PRIM_DOUBLE
        );
        // I53 accumulation chains are fixpoint-stable at I53: products and
        // sums of integral operands stay claimable.
        let mut acc = TypeSet::prim(PRIM_INT32 | PRIM_DOUBLE);
        acc.range = Range::I53;
        assert_eq!(
            arith_transfer(Add, &acc, Some(&acc)),
            (PRIM_INT32 | PRIM_DOUBLE, Range::I53)
        );
        assert_eq!(
            arith_transfer(Mul, &acc, Some(&i)),
            (PRIM_INT32 | PRIM_DOUBLE, Range::I53)
        );
        assert_eq!(arith_transfer(Div, &acc, Some(&acc)).1, Range::Top);
    }

    #[test]
    fn fnset_bounds() {
        let fid = |n: u32| FnId::script(ScriptId::new(n));
        let mut s = BoundedFnSet::default();
        let mut dropped = Vec::new();
        for f in 0..8 {
            assert!(s.insert(fid(f), &mut dropped));
        }
        assert_eq!(s.ids().len(), 8);
        assert!(!s.insert(fid(3), &mut dropped));
        assert!(dropped.is_empty());
        assert!(s.insert(fid(100), &mut dropped));
        assert!(s.is_multi());
        assert!(s.ids().is_empty());
        // The multi transition surrendered every id it was tracking plus
        // the trigger: those scripts may now run unbound.
        assert_eq!(dropped, [0, 1, 2, 3, 4, 5, 6, 7, 100].map(fid).to_vec());
        assert!(!s.insert(fid(200), &mut dropped));
    }

    #[test]
    fn join_monotone_bounded() {
        let ac: Vec<AbsLabels> = vec![AbsLabels::default(); 4];
        let mut sink = JoinSink::default();
        let mut t = TypeSet::default();
        let mut changes = 0;
        for step in [
            TypeSet::prim(PRIM_INT32),
            TypeSet::prim(PRIM_DOUBLE),
            TypeSet::fn_one(FnId::script(ScriptId::new(7))),
            TypeSet::obj_one(AbsId(0)),
            TypeSet::obj_one(AbsId(1)),
            TypeSet::any(),
            TypeSet::any(),
        ] {
            if t.join_from(&step, &ac, &mut sink) {
                changes += 1;
            }
        }
        assert!(changes <= MAX_CELL_CHANGES);
        assert_eq!(t, TypeSet::any());
    }

    #[test]
    fn interval_join_is_order_independent() {
        use Interval::*;
        // Quantized-at-creation intervals + hull join: any permutation of
        // any subset must reach the same fixpoint (the shuffle-test
        // pillar, interval component).
        let vals = [
            Empty,
            Any,
            Interval::of_value(0),
            Interval::of_value(1),
            Interval::of_value(-1),
            Interval::of_value(5),
            Interval::of_value(-300),
            Interval::of_range(0, 0xfffffff),
            Interval::of_range(-20, 3),
            Interval::of_range(3, 1 << 40),
        ];
        for &a in &vals {
            for &b in &vals {
                assert_eq!(Interval::join(a, b), Interval::join(b, a));
                for &c in &vals {
                    assert_eq!(
                        Interval::join(Interval::join(a, b), c),
                        Interval::join(a, Interval::join(b, c))
                    );
                }
            }
        }
        assert_eq!(Interval::of_value(5), In(iv(0, 5)));
        assert_eq!(Interval::of_value(-300), In(iv(-512, 0)));
        assert_eq!(Interval::of_range(0, 0xfffffff), In(iv(0, 0xfffffff)));
        assert_eq!(Interval::of_double(3.0), In(iv(0, 3)));
        assert_eq!(Interval::of_double(3.5), Num);
        assert_eq!(Interval::of_double(-0.0), Num);
        assert_eq!(Interval::of_double(f64::NAN), Num);
        // The heap ladder is int32-clipped: wider bounds have no
        // consumer and collapse to the Number rung in one step.
        assert_eq!(Interval::of_range(0, 1 << 33), Num);
        assert_eq!(
            Interval::of_range(0, i32::MAX as i64),
            In(iv(0, i32::MAX as i64))
        );
    }

    #[test]
    fn arith_interval_rules() {
        use Interval::*;
        let m14 = In(iv(0, 0x3fff));
        // The am3 shape: masked digits multiply within int32.
        assert_eq!(
            arith_interval(NumOp::Mul, m14, None, Some(m14), None),
            In(iv(0, (1 << 28) - 1))
        );
        // Exact literal shift count (rides the constraint, not the cell).
        assert_eq!(
            arith_interval(
                NumOp::Rsh,
                In(iv(0, (1 << 28) - 1)),
                None,
                Some(Any),
                Some(ValueRange::new(14, 14))
            ),
            In(iv(0, (1 << 14) - 1))
        );
        // A quantized non-constant shift count proves nothing beyond i32.
        assert_eq!(
            arith_interval(NumOp::Rsh, In(iv(0, 255)), None, Some(In(iv(0, 15))), None),
            In(iv(i32::MIN as i64, i32::MAX as i64))
        );
        // Beyond-int32 arith results collapse to Num; a following mask
        // recovers the bound, which is the multiply-and-mask shape of an
        // integer kernel.
        assert_eq!(
            arith_interval(
                NumOp::Mul,
                In(iv(0, 1 << 26)),
                None,
                Some(In(iv(0, 1 << 26))),
                None
            ),
            Num
        );
        assert_eq!(
            arith_interval(
                NumOp::BitAnd,
                Num,
                None,
                Some(Any),
                Some(ValueRange::new(0x3ffffff, 0x3ffffff))
            ),
            In(iv(0, 0x3ffffff))
        );
        // Bitand against an exact literal mask.
        assert_eq!(
            arith_interval(
                NumOp::BitAnd,
                Any,
                None,
                Some(Any),
                Some(ValueRange::new(0xfffffff, 0xfffffff))
            ),
            In(iv(0, 0xfffffff))
        );
        assert_eq!(arith_interval(NumOp::Div, m14, None, Some(m14), None), Num);
        assert_eq!(
            arith_interval(NumOp::Add, Empty, None, Some(m14), None),
            Empty
        );
        assert_eq!(
            arith_interval(NumOp::Add, In(iv(0, 7)), None, Some(In(iv(0, 7))), None),
            In(iv(0, 15))
        );
        assert_eq!(
            arith_interval(NumOp::Neg, In(iv(0, 7)), None, None, None),
            In(iv(-7, 0))
        );
    }
}
