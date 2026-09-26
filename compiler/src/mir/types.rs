//! The MIR type lattice (MIR.md §2): representation × refinement.
//!
//! A type names both how a value is held (a NaN-boxed `Val`, a raw i32, a
//! managed object reference, a ghost with no runtime form, ...) and what
//! is known about it. Subtyping is pointwise *within* one representation:
//! "boxed, known int32" and "raw i32" are different types, related only
//! by explicit conversion ops.
//!
//! Components split into two classes, and the split is what fences are
//! about (§4):
//! - **invariant** for the value's lifetime: tags, numeric info, object
//!   kind, function script, snapshot singleton, atom identity;
//! - **killable** (heap-dependent): layout claims (identity, `types`,
//!   the constructing state) and ghost facts. [`KillPattern`] names sets
//!   of these, and [`Type::weakened`] drops them.
//!
//! The primitive-class alphabet and numeric intervals are
//! `crate::opsem`'s, so the MIR and the analysis name the same classes.

use crate::ids::{LayoutKey, ScriptId};
use crate::mir::entity::{AtomId, BindingId, FuseId, NativeId, SnapObj};
use crate::opsem::{
    Prims, TaKind, ValueRange, ALL_PRIMS, NUM, PRIM_BIGINT, PRIM_BOOLEAN, PRIM_DOUBLE, PRIM_INT32,
    PRIM_NULL, PRIM_STRING, PRIM_SYMBOL, PRIM_UNDEFINED,
};

pub const I32_MIN: i64 = i32::MIN as i64;
pub const I32_MAX: i64 = i32::MAX as i64;
/// The magnitude bound of `Int`: every integer in `[-2^53, 2^53]` is an
/// exact double, so `Int` arithmetic within it agrees with JS semantics.
pub const INT_LIM: i64 = 1 << 53;

/// A value's possible JS type tags: the seven primitive classes (as
/// `opsem::Prims`), object, and magic. More tags is a weaker claim.
///
/// `magic` covers the engine's magic values (the TDZ sentinel, element
/// holes, generator-closing, ...). They are never JS-visible values, but a
/// baseline frame slot can hold one (`docs/BASELINE.md` §2), so `Val(⊤)`,
/// the boundary type, includes it. Nothing unboxes a magic value, and
/// `guard.tags` without `magic` removes it.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub struct TagSet {
    pub prims: Prims,
    pub object: bool,
    pub magic: bool,
}

impl TagSet {
    pub const NONE: TagSet = TagSet {
        prims: Prims::EMPTY,
        object: false,
        magic: false,
    };
    pub const ALL: TagSet = TagSet {
        prims: ALL_PRIMS,
        object: true,
        magic: true,
    };
    /// Every JS-visible value: all but `magic`.
    pub const JS: TagSet = TagSet {
        prims: ALL_PRIMS,
        object: true,
        magic: false,
    };
    pub const INT32: TagSet = TagSet::prims(PRIM_INT32);
    pub const DOUBLE: TagSet = TagSet::prims(PRIM_DOUBLE);
    pub const NUMBER: TagSet = TagSet::prims(NUM);
    pub const BOOLEAN: TagSet = TagSet::prims(PRIM_BOOLEAN);
    pub const STRING: TagSet = TagSet::prims(PRIM_STRING);
    pub const OBJECT: TagSet = TagSet {
        prims: Prims::EMPTY,
        object: true,
        magic: false,
    };
    pub const MAGIC: TagSet = TagSet {
        prims: Prims::EMPTY,
        object: false,
        magic: true,
    };

    pub const fn prims(prims: Prims) -> TagSet {
        TagSet {
            prims,
            object: false,
            magic: false,
        }
    }

    /// The text-format names, in printing order.
    pub const NAMES: [(&'static str, TagSet); 10] = [
        ("undefined", TagSet::prims(PRIM_UNDEFINED)),
        ("null", TagSet::prims(PRIM_NULL)),
        ("boolean", TagSet::prims(PRIM_BOOLEAN)),
        ("int32", TagSet::prims(PRIM_INT32)),
        ("double", TagSet::prims(PRIM_DOUBLE)),
        ("string", TagSet::prims(PRIM_STRING)),
        ("symbol", TagSet::prims(PRIM_SYMBOL)),
        ("bigint", TagSet::prims(PRIM_BIGINT)),
        ("object", TagSet::OBJECT),
        ("magic", TagSet::MAGIC),
    ];

    pub fn union(self, o: TagSet) -> TagSet {
        TagSet {
            prims: self.prims | o.prims,
            object: self.object || o.object,
            magic: self.magic || o.magic,
        }
    }

    pub fn intersect(self, o: TagSet) -> TagSet {
        TagSet {
            prims: self.prims & o.prims,
            object: self.object && o.object,
            magic: self.magic && o.magic,
        }
    }

    pub fn subset_of(self, o: TagSet) -> bool {
        self.prims.subset_of(o.prims) && (!self.object || o.object) && (!self.magic || o.magic)
    }

    pub fn is_empty(self) -> bool {
        self.prims.is_empty() && !self.object && !self.magic
    }

    /// Nonempty and within `o`: what an infallible unbox requires.
    pub fn is_nonempty_subset_of(self, o: TagSet) -> bool {
        !self.is_empty() && self.subset_of(o)
    }

    pub fn has_number(self) -> bool {
        self.prims.intersects(NUM)
    }

    pub fn has_string(self) -> bool {
        self.prims.intersects(PRIM_STRING)
    }
}

/// What is known about a JS number's value. `range` bounds it (inclusive,
/// integers); `integral` says it has no fractional part and is finite.
/// The two flags are *may* flags: clearing one is a refinement.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct NumInfo {
    pub range: Option<ValueRange>,
    pub integral: bool,
    pub may_neg_zero: bool,
    pub may_nan: bool,
}

impl Default for NumInfo {
    fn default() -> Self {
        NumInfo::TOP
    }
}

impl NumInfo {
    pub const TOP: NumInfo = NumInfo {
        range: None,
        integral: false,
        may_neg_zero: true,
        may_nan: true,
    };

    /// An integer in `[lo, hi]`, never -0 or NaN: what an int32 tag, a raw
    /// `I32` or an `Int` implies.
    pub const fn int(lo: i64, hi: i64) -> NumInfo {
        NumInfo {
            range: Some(ValueRange::new(lo, hi)),
            integral: true,
            may_neg_zero: false,
            may_nan: false,
        }
    }

    /// Exactly the double `x`.
    pub fn exact(x: f64) -> NumInfo {
        let is_int = x.is_finite() && x.fract() == 0.0 && x.abs() <= INT_LIM as f64;
        let neg_zero = x == 0.0 && x.is_sign_negative();
        NumInfo {
            range: (is_int && !neg_zero).then(|| ValueRange::new(x as i64, x as i64)),
            integral: x.is_finite() && x.fract() == 0.0,
            may_neg_zero: neg_zero,
            may_nan: x.is_nan(),
        }
    }

    pub fn le(&self, o: &NumInfo) -> bool {
        let range_ok = match (self.range, o.range) {
            (_, None) => true,
            (None, Some(_)) => false,
            (Some(a), Some(b)) => a.lo >= b.lo && a.hi <= b.hi,
        };
        range_ok
            && (!o.integral || self.integral)
            && (!self.may_neg_zero || o.may_neg_zero)
            && (!self.may_nan || o.may_nan)
    }

    pub fn join(&self, o: &NumInfo) -> NumInfo {
        NumInfo {
            range: match (self.range, o.range) {
                (Some(a), Some(b)) => Some(a.hull(b)),
                _ => None,
            },
            integral: self.integral && o.integral,
            may_neg_zero: self.may_neg_zero || o.may_neg_zero,
            may_nan: self.may_nan || o.may_nan,
        }
    }

    /// The greatest lower bound, or `None` if the two ranges are disjoint
    /// (no number satisfies both).
    pub fn meet(&self, o: &NumInfo) -> Option<NumInfo> {
        let range = match (self.range, o.range) {
            (Some(a), Some(b)) => {
                let (lo, hi) = (a.lo.max(b.lo), a.hi.min(b.hi));
                if lo > hi {
                    return None;
                }
                Some(ValueRange::new(lo, hi))
            }
            (a, b) => a.or(b),
        };
        Some(NumInfo {
            range,
            integral: self.integral || o.integral,
            may_neg_zero: self.may_neg_zero && o.may_neg_zero,
            may_nan: self.may_nan && o.may_nan,
        })
    }

    /// The bounds a raw integer representation can use: `range` clamped to
    /// `[lo, hi]`, or all of it.
    pub fn int_range(&self, lo: i64, hi: i64) -> IRange {
        match self.range {
            Some(r) => IRange::new(r.lo.max(lo), r.hi.min(hi)),
            None => IRange::new(lo, hi),
        }
    }
}

/// An inclusive integer interval, for the raw `I32` and `Int`
/// representations (whose own bounds are the default).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct IRange {
    pub lo: i64,
    pub hi: i64,
}

impl IRange {
    pub const I32: IRange = IRange {
        lo: I32_MIN,
        hi: I32_MAX,
    };
    pub const INT: IRange = IRange {
        lo: -INT_LIM,
        hi: INT_LIM,
    };

    pub const fn new(lo: i64, hi: i64) -> IRange {
        IRange { lo, hi }
    }

    pub fn contains(&self, o: &IRange) -> bool {
        o.lo >= self.lo && o.hi <= self.hi
    }

    pub fn hull(&self, o: &IRange) -> IRange {
        IRange::new(self.lo.min(o.lo), self.hi.max(o.hi))
    }

    pub fn num(&self) -> NumInfo {
        NumInfo::int(self.lo, self.hi)
    }
}

/// An inclusive range of layout keys: what one stamp guard proves (keys of
/// one predictor group are contiguous, `ids::LayoutKey`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct KeyRange {
    pub lo: LayoutKey,
    pub hi: LayoutKey,
}

impl KeyRange {
    pub const fn one(k: LayoutKey) -> KeyRange {
        KeyRange { lo: k, hi: k }
    }

    pub fn contains(&self, o: &KeyRange) -> bool {
        o.lo >= self.lo && o.hi <= self.hi
    }

    pub fn overlaps(&self, o: &KeyRange) -> bool {
        self.lo <= o.hi && o.lo <= self.hi
    }

    pub fn hull(&self, o: &KeyRange) -> KeyRange {
        KeyRange {
            lo: self.lo.min(o.lo),
            hi: self.hi.max(o.hi),
        }
    }

    pub fn keys(&self) -> impl Iterator<Item = LayoutKey> {
        (self.lo.get()..=self.hi.get()).map(LayoutKey::new)
    }
}

/// The object's class (JSClass), which never changes. `Any > Native >`
/// the concrete kinds; a function with a known script is below one with
/// an unknown script.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub enum ObjKind {
    #[default]
    Any,
    Native,
    Plain,
    Array,
    Function(Option<ScriptId>),
    TypedArray(TaKind),
    Arguments,
    Env,
}

impl ObjKind {
    pub fn le(self, o: ObjKind) -> bool {
        match (self, o) {
            (_, ObjKind::Any) => true,
            (ObjKind::Any, _) => false,
            (_, ObjKind::Native) => true,
            (ObjKind::Native, _) => false,
            (ObjKind::Function(_), ObjKind::Function(None)) => true,
            (a, b) => a == b,
        }
    }

    pub fn join(self, o: ObjKind) -> ObjKind {
        if self.le(o) {
            o
        } else if o.le(self) {
            self
        } else if matches!((self, o), (ObjKind::Function(_), ObjKind::Function(_))) {
            ObjKind::Function(None)
        } else if self == ObjKind::Any || o == ObjKind::Any {
            ObjKind::Any
        } else {
            ObjKind::Native
        }
    }
}

/// How much of layout `keys` an object is known to have (MIR.md §2.3).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub enum LayoutState {
    /// A published instance: a stamp guard for `keys` passes on it.
    #[default]
    Published,
    /// Supports exactly the layout's first `n` slots. The common
    /// supertype of a published object and one still under construction.
    Prefix(u32),
    /// Carries the CONSTRUCTING sentinel and has had the first `n`
    /// predicted fields added. A published-K stamp guard would fail on it.
    Constructing(u32),
}

impl LayoutState {
    /// How many leading slots this state supports; `None` is all of them.
    pub fn slots(self) -> Option<u32> {
        match self {
            LayoutState::Published => None,
            LayoutState::Prefix(n) | LayoutState::Constructing(n) => Some(n),
        }
    }

    pub fn le(self, o: LayoutState) -> bool {
        match (self, o) {
            (a, b) if a == b => true,
            // Anything that supports at least `m` slots is a prefix-`m`.
            (a, LayoutState::Prefix(m)) => a.slots().is_none_or(|n| n >= m),
            _ => false,
        }
    }

    pub fn join(self, o: LayoutState) -> LayoutState {
        if self == o {
            return self;
        }
        let n = match (self.slots(), o.slots()) {
            (Some(a), Some(b)) => a.min(b),
            (Some(a), None) | (None, Some(a)) => a,
            (None, None) => unreachable!("two distinct states that are both Published"),
        };
        LayoutState::Prefix(n)
    }
}

/// A claim about an object's layout: its stamp identity is in `keys`, its
/// state is `state`, and (if `types`) the stamp's `TYPES`/`RANGES` bits
/// hold, so its protected fields hold their claimed types (§4.3). `SLOTS`
/// is never in a type: each field op tests it locally.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct LayoutClaim {
    pub keys: KeyRange,
    pub types: bool,
    pub state: LayoutState,
}

impl LayoutClaim {
    pub fn le(&self, o: &LayoutClaim) -> bool {
        o.keys.contains(&self.keys) && (!o.types || self.types) && self.state.le(o.state)
    }

    pub fn join(&self, o: &LayoutClaim) -> LayoutClaim {
        LayoutClaim {
            keys: self.keys.hull(&o.keys),
            types: self.types && o.types,
            state: self.state.join(o.state),
        }
    }
}

/// What is known about an object reference.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub struct ObjInfo {
    pub kind: ObjKind,
    pub singleton: Option<SnapObj>,
    pub layout: Option<LayoutClaim>,
}

impl ObjInfo {
    pub const TOP: ObjInfo = ObjInfo {
        kind: ObjKind::Any,
        singleton: None,
        layout: None,
    };

    pub const fn kind(kind: ObjKind) -> ObjInfo {
        ObjInfo {
            kind,
            singleton: None,
            layout: None,
        }
    }

    pub fn le(&self, o: &ObjInfo) -> bool {
        self.kind.le(o.kind)
            && (o.singleton.is_none() || self.singleton == o.singleton)
            && match (&self.layout, &o.layout) {
                (_, None) => true,
                (None, Some(_)) => false,
                (Some(a), Some(b)) => a.le(b),
            }
    }

    pub fn join(&self, o: &ObjInfo) -> ObjInfo {
        ObjInfo {
            kind: self.kind.join(o.kind),
            singleton: if self.singleton == o.singleton {
                self.singleton
            } else {
                None
            },
            layout: match (&self.layout, &o.layout) {
                (Some(a), Some(b)) => Some(a.join(b)),
                _ => None,
            },
        }
    }

    /// The shallow view of an object claim loaded out of a field (§4.3):
    /// immutable components only. A parent's `TYPES` bit cannot soundly
    /// promise the child's layout identity (§4.6 point 4).
    pub fn shallow(&self) -> ObjInfo {
        ObjInfo {
            layout: None,
            ..*self
        }
    }
}

/// What is known about a string reference.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub struct StrInfo {
    /// The string is exactly this atom.
    pub atom: Option<AtomId>,
}

impl StrInfo {
    pub const TOP: StrInfo = StrInfo { atom: None };

    pub fn le(&self, o: &StrInfo) -> bool {
        o.atom.is_none() || self.atom == o.atom
    }

    pub fn join(&self, o: &StrInfo) -> StrInfo {
        StrInfo {
            atom: if self.atom == o.atom { self.atom } else { None },
        }
    }
}

/// The refinement of a boxed value. Components describe the value only
/// under their tag: `num` when it is a number, `obj` when an object, `str`
/// when a string. Construct through [`VSet::new`], which canonicalizes
/// (components for absent tags are top; `num` absorbs what the tags imply)
/// so structural equality is semantic equality.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct VSet {
    pub tags: TagSet,
    pub num: NumInfo,
    pub obj: ObjInfo,
    pub str: StrInfo,
}

impl VSet {
    pub const TOP: VSet = VSet {
        tags: TagSet::ALL,
        num: NumInfo::TOP,
        obj: ObjInfo::TOP,
        str: StrInfo::TOP,
    };

    pub fn new(tags: TagSet, num: NumInfo, obj: ObjInfo, str: StrInfo) -> VSet {
        let num = if tags.has_number() {
            num.meet(&VSet::implied_num(tags)).unwrap_or(num)
        } else {
            NumInfo::TOP
        };
        VSet {
            tags,
            num,
            obj: if tags.object { obj } else { ObjInfo::TOP },
            str: if tags.has_string() { str } else { StrInfo::TOP },
        }
    }

    pub fn tags(tags: TagSet) -> VSet {
        VSet::new(tags, NumInfo::TOP, ObjInfo::TOP, StrInfo::TOP)
    }

    /// What the number tags alone imply: an int32 tag is an integer in
    /// int32 range that is never -0 (canonical boxing).
    pub fn implied_num(tags: TagSet) -> NumInfo {
        if tags.prims.intersects(NUM) && !tags.prims.intersects(PRIM_DOUBLE) {
            NumInfo::int(I32_MIN, I32_MAX)
        } else {
            NumInfo::TOP
        }
    }

    pub fn le(&self, o: &VSet) -> bool {
        self.tags.subset_of(o.tags)
            && (!self.tags.has_number() || self.num.le(&o.num))
            && (!self.tags.object || self.obj.le(&o.obj))
            && (!self.tags.has_string() || self.str.le(&o.str))
    }

    pub fn join(&self, o: &VSet) -> VSet {
        let pick_num = match (self.tags.has_number(), o.tags.has_number()) {
            (true, true) => self.num.join(&o.num),
            (true, false) => self.num,
            (false, _) => o.num,
        };
        let pick_obj = match (self.tags.object, o.tags.object) {
            (true, true) => self.obj.join(&o.obj),
            (true, false) => self.obj,
            (false, _) => o.obj,
        };
        let pick_str = match (self.tags.has_string(), o.tags.has_string()) {
            (true, true) => self.str.join(&o.str),
            (true, false) => self.str,
            (false, _) => o.str,
        };
        VSet::new(self.tags.union(o.tags), pick_num, pick_obj, pick_str)
    }

    /// Narrow to `tags` (a tag guard's success).
    pub fn restrict(&self, tags: TagSet) -> VSet {
        VSet::new(self.tags.intersect(tags), self.num, self.obj, self.str)
    }
}

/// The kinds of raw interior pointer (§4.4).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum RawKind {
    Elements,
    Slots,
    TaData,
}

/// A ghost fact (§3).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FactKind {
    Fuse(FuseId),
    Binding(BindingId),
    NativeIntact(NativeId),
}

/// A MIR type.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Type {
    /// A boxed JS::Value (wasm i64).
    Val(VSet),
    /// Raw i32: a JS number that is int32-valued, never -0.
    I32(IRange),
    /// Raw i64: a JS number that is integral, `|x| <= 2^53`, never -0.
    Int(IRange),
    /// Raw f64: any JS number.
    F64(NumInfo),
    /// Raw i32 0/1.
    Bool,
    /// Managed reference to a JSObject.
    Obj(ObjInfo),
    /// Managed reference to a JSString.
    Str(StrInfo),
    /// Raw interior pointer: must not be live across a may-GC op.
    Raw(RawKind),
    /// Machine words (lengths, indices, stamp words), not JS values.
    W32,
    W64,
    /// Ghost value, no runtime representation.
    Fact(FactKind),
}

/// A type's representation: subtyping never crosses one.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Repr {
    Val,
    I32,
    Int,
    F64,
    Bool,
    Obj,
    Str,
    Raw,
    W32,
    W64,
    Ghost,
}

/// The machine type a representation lowers to (wasm32 pointers).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Machine {
    I32,
    I64,
    F64,
    None,
}

impl Repr {
    pub fn machine(self) -> Machine {
        match self {
            Repr::Val | Repr::Int | Repr::W64 => Machine::I64,
            Repr::I32 | Repr::Bool | Repr::Obj | Repr::Str | Repr::Raw | Repr::W32 => Machine::I32,
            Repr::F64 => Machine::F64,
            Repr::Ghost => Machine::None,
        }
    }

    /// Managed references the lowering roots across may-GC ops.
    pub fn is_managed(self) -> bool {
        matches!(self, Repr::Val | Repr::Obj | Repr::Str)
    }
}

impl Type {
    pub const VAL_TOP: Type = Type::Val(VSet::TOP);
    pub const I32_TOP: Type = Type::I32(IRange::I32);
    pub const INT_TOP: Type = Type::Int(IRange::INT);
    pub const F64_TOP: Type = Type::F64(NumInfo::TOP);
    pub const OBJ_TOP: Type = Type::Obj(ObjInfo::TOP);
    pub const STR_TOP: Type = Type::Str(StrInfo::TOP);

    pub fn val(tags: TagSet) -> Type {
        Type::Val(VSet::tags(tags))
    }

    pub fn i32_range(lo: i64, hi: i64) -> Type {
        Type::I32(IRange::new(lo.max(I32_MIN), hi.min(I32_MAX)))
    }

    pub fn int_range(lo: i64, hi: i64) -> Type {
        Type::Int(IRange::new(lo.max(-INT_LIM), hi.min(INT_LIM)))
    }

    pub fn repr(&self) -> Repr {
        match self {
            Type::Val(_) => Repr::Val,
            Type::I32(_) => Repr::I32,
            Type::Int(_) => Repr::Int,
            Type::F64(_) => Repr::F64,
            Type::Bool => Repr::Bool,
            Type::Obj(_) => Repr::Obj,
            Type::Str(_) => Repr::Str,
            Type::Raw(_) => Repr::Raw,
            Type::W32 => Repr::W32,
            Type::W64 => Repr::W64,
            Type::Fact(_) => Repr::Ghost,
        }
    }

    /// `Val(⊤)`: what crosses the OPT/GEN boundary (§5).
    pub fn is_val_top(&self) -> bool {
        *self == Type::VAL_TOP
    }

    /// The top of this type's representation.
    pub fn top_of(&self) -> Type {
        match self {
            Type::Val(_) => Type::VAL_TOP,
            Type::I32(_) => Type::I32_TOP,
            Type::Int(_) => Type::INT_TOP,
            Type::F64(_) => Type::F64_TOP,
            Type::Obj(_) => Type::OBJ_TOP,
            Type::Str(_) => Type::STR_TOP,
            t => *t,
        }
    }

    /// The object claim this type carries, boxed or not.
    pub fn obj_info(&self) -> Option<&ObjInfo> {
        match self {
            Type::Obj(o) => Some(o),
            Type::Val(v) if v.tags.object => Some(&v.obj),
            _ => None,
        }
    }

    fn map_obj(&self, f: impl FnOnce(&ObjInfo) -> ObjInfo) -> Type {
        match self {
            Type::Obj(o) => Type::Obj(f(o)),
            Type::Val(v) if v.tags.object => Type::Val(VSet {
                obj: f(&v.obj),
                ..*v
            }),
            t => *t,
        }
    }

    /// Drop the killable object components (§4.3 shallow `TYPES`).
    pub fn shallow(&self) -> Type {
        self.map_obj(ObjInfo::shallow)
    }
}

/// `a <: b`: same representation, pointwise.
pub fn is_subtype(a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::Val(x), Type::Val(y)) => x.le(y),
        (Type::I32(x), Type::I32(y)) | (Type::Int(x), Type::Int(y)) => y.contains(x),
        (Type::F64(x), Type::F64(y)) => x.le(y),
        (Type::Obj(x), Type::Obj(y)) => x.le(y),
        (Type::Str(x), Type::Str(y)) => x.le(y),
        (a, b) => a == b,
    }
}

/// The least upper bound, or `None` across representations.
pub fn join(a: &Type, b: &Type) -> Option<Type> {
    Some(match (a, b) {
        (Type::Val(x), Type::Val(y)) => Type::Val(x.join(y)),
        (Type::I32(x), Type::I32(y)) => Type::I32(x.hull(y)),
        (Type::Int(x), Type::Int(y)) => Type::Int(x.hull(y)),
        (Type::F64(x), Type::F64(y)) => Type::F64(x.join(y)),
        (Type::Obj(x), Type::Obj(y)) => Type::Obj(x.join(y)),
        (Type::Str(x), Type::Str(y)) => Type::Str(x.join(y)),
        (a, b) if a == b => *a,
        _ => return None,
    })
}

/// Classes of killable component (§4.1). A small bitset; see
/// [`KillPattern`] for the optional layout filter.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct KillSet(u8);

impl KillSet {
    pub const NONE: KillSet = KillSet(0);
    /// A layout claim as a whole: identity, `types` and state.
    pub const LAYOUT: KillSet = KillSet(1 << 0);
    /// Only a claim's `TYPES`/`RANGES` bit.
    pub const TYPES: KillSet = KillSet(1 << 1);
    /// The constructing state (a claim weakens to its prefix).
    pub const CONSTRUCTING: KillSet = KillSet(1 << 2);
    pub const FUSE: KillSet = KillSet(1 << 3);
    pub const BINDING: KillSet = KillSet(1 << 4);
    pub const NATIVE: KillSet = KillSet(1 << 5);
    pub const ALL: KillSet = KillSet(0x3f);

    pub const NAMES: [(&'static str, KillSet); 6] = [
        ("layout", KillSet::LAYOUT),
        ("types", KillSet::TYPES),
        ("constructing", KillSet::CONSTRUCTING),
        ("fuse", KillSet::FUSE),
        ("binding", KillSet::BINDING),
        ("native", KillSet::NATIVE),
    ];

    pub const fn union(self, o: KillSet) -> KillSet {
        KillSet(self.0 | o.0)
    }

    pub const fn intersects(self, o: KillSet) -> bool {
        self.0 & o.0 != 0
    }

    pub const fn contains(self, o: KillSet) -> bool {
        self.0 & o.0 == o.0
    }

    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    pub fn minus(self, o: KillSet) -> KillSet {
        KillSet(self.0 & !o.0)
    }
}

impl std::fmt::Debug for KillSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let names: Vec<_> = KillSet::NAMES
            .iter()
            .filter(|(_, k)| self.contains(*k))
            .map(|(n, _)| *n)
            .collect();
        write!(f, "{{{}}}", names.join(","))
    }
}

/// A fence's kill pattern: component classes, optionally restricted (for
/// the layout classes) to claims overlapping a key range.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub struct KillPattern {
    pub set: KillSet,
    pub keys: Option<KeyRange>,
}

impl KillPattern {
    pub const NONE: KillPattern = KillPattern {
        set: KillSet::NONE,
        keys: None,
    };
    pub const ALL: KillPattern = KillPattern {
        set: KillSet::ALL,
        keys: None,
    };

    pub const fn of(set: KillSet) -> KillPattern {
        KillPattern { set, keys: None }
    }

    pub fn is_empty(&self) -> bool {
        self.set.is_empty()
    }

    fn hits_claim(&self, c: &LayoutClaim) -> KillSet {
        if self.keys.is_some_and(|r| !r.overlaps(&c.keys)) {
            return KillSet::NONE;
        }
        let mut hit = KillSet::NONE;
        if self.set.contains(KillSet::LAYOUT) {
            hit = hit.union(KillSet::LAYOUT);
        }
        if self.set.contains(KillSet::TYPES) && c.types {
            hit = hit.union(KillSet::TYPES);
        }
        if self.set.contains(KillSet::CONSTRUCTING)
            && matches!(c.state, LayoutState::Constructing(_))
        {
            hit = hit.union(KillSet::CONSTRUCTING);
        }
        hit
    }

    /// The components of `t` this pattern kills.
    pub fn hits(&self, t: &Type) -> KillSet {
        match t {
            Type::Fact(FactKind::Fuse(_)) if self.set.contains(KillSet::FUSE) => KillSet::FUSE,
            Type::Fact(FactKind::Binding(_)) if self.set.contains(KillSet::BINDING) => {
                KillSet::BINDING
            }
            Type::Fact(FactKind::NativeIntact(_)) if self.set.contains(KillSet::NATIVE) => {
                KillSet::NATIVE
            }
            _ => match t.obj_info().and_then(|o| o.layout.as_ref()) {
                Some(c) => self.hits_claim(c),
                None => KillSet::NONE,
            },
        }
    }

    /// Whether a value of type `t` may not be live across this fence.
    pub fn matches(&self, t: &Type) -> bool {
        !self.hits(t).is_empty()
    }

    /// Whether this pattern kills at least everything `o` does.
    pub fn covers(&self, o: &KillPattern) -> bool {
        self.set.contains(o.set)
            && match (self.keys, o.keys) {
                (None, _) => true,
                (Some(_), None) => o
                    .set
                    .minus(KillSet::FUSE.union(KillSet::BINDING).union(KillSet::NATIVE))
                    .is_empty(),
                (Some(a), Some(b)) => a.contains(&b),
            }
    }
}

impl Type {
    /// The killable component classes this type carries.
    pub fn killable_components(&self) -> KillSet {
        KillPattern::ALL.hits(self)
    }

    /// This type with every component `p` kills removed: the type a value
    /// may carry across the fence (§4.2). Facts cannot be weakened, only
    /// dropped, so a killed fact stays as it is and the caller must not
    /// carry it.
    pub fn weakened(&self, p: &KillPattern) -> Type {
        let hit = p.hits(self);
        if hit.is_empty() {
            return *self;
        }
        self.map_obj(|o| {
            let layout = o.layout.and_then(|c| {
                if hit.contains(KillSet::LAYOUT) {
                    return None;
                }
                let mut c = c;
                if hit.contains(KillSet::TYPES) {
                    c.types = false;
                }
                if hit.contains(KillSet::CONSTRUCTING) {
                    c.state = LayoutState::Prefix(c.state.slots().unwrap_or(0));
                }
                Some(c)
            });
            ObjInfo { layout, ..*o }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lk(k: u32) -> LayoutKey {
        LayoutKey::new(k)
    }

    fn claim(lo: u32, hi: u32, types: bool, state: LayoutState) -> LayoutClaim {
        LayoutClaim {
            keys: KeyRange {
                lo: lk(lo),
                hi: lk(hi),
            },
            types,
            state,
        }
    }

    fn obj(kind: ObjKind, layout: Option<LayoutClaim>) -> Type {
        Type::Obj(ObjInfo {
            kind,
            singleton: None,
            layout,
        })
    }

    #[test]
    fn repr_boundaries() {
        assert!(!is_subtype(&Type::I32_TOP, &Type::VAL_TOP));
        assert!(!is_subtype(&Type::val(TagSet::INT32), &Type::I32_TOP));
        assert!(!is_subtype(&Type::Bool, &Type::I32_TOP));
        assert_eq!(join(&Type::I32_TOP, &Type::F64_TOP), None);
        assert_eq!(Type::Bool.repr().machine(), Type::I32_TOP.repr().machine());
    }

    #[test]
    fn val_subtyping() {
        let i = Type::val(TagSet::INT32);
        let n = Type::val(TagSet::NUMBER);
        assert!(is_subtype(&i, &n));
        assert!(!is_subtype(&n, &i));
        assert!(is_subtype(&n, &Type::VAL_TOP));
        // int32 tags imply integral, no -0, no NaN: so int32 is below an
        // integral number claim even though nobody wrote `integral`.
        let integral = Type::Val(VSet::new(
            TagSet::NUMBER,
            NumInfo {
                integral: true,
                ..NumInfo::TOP
            },
            ObjInfo::TOP,
            StrInfo::TOP,
        ));
        assert!(is_subtype(&i, &integral));
        assert!(!is_subtype(&n, &integral));
        // Ranges.
        let r = |lo, hi| {
            Type::Val(VSet::new(
                TagSet::INT32,
                NumInfo::int(lo, hi),
                ObjInfo::TOP,
                StrInfo::TOP,
            ))
        };
        assert!(is_subtype(&r(0, 9), &r(0, 99)));
        assert!(!is_subtype(&r(0, 99), &r(0, 9)));
        assert_eq!(join(&r(0, 9), &r(50, 99)), Some(r(0, 99)));
        // Canonical form: int32 with no range is the same type as one with
        // the full int32 range spelled out.
        assert_eq!(r(I32_MIN, I32_MAX), i);
    }

    #[test]
    fn val_components_only_under_their_tag() {
        // An object claim on a value that cannot be an object is dropped.
        let v = VSet::new(
            TagSet::INT32,
            NumInfo::TOP,
            ObjInfo::kind(ObjKind::Plain),
            StrInfo::TOP,
        );
        assert_eq!(v.obj, ObjInfo::TOP);
        let plain = Type::Val(VSet::new(
            TagSet::OBJECT,
            NumInfo::TOP,
            ObjInfo::kind(ObjKind::Plain),
            StrInfo::TOP,
        ));
        let plain_or_int = join(&plain, &Type::val(TagSet::INT32)).unwrap();
        assert!(is_subtype(&plain, &plain_or_int));
        assert!(is_subtype(&Type::val(TagSet::INT32), &plain_or_int));
        assert!(!is_subtype(&Type::val(TagSet::OBJECT), &plain_or_int));
    }

    #[test]
    fn obj_kinds() {
        let f = |s| ObjKind::Function(Some(ScriptId::new(s)));
        assert!(f(1).le(ObjKind::Function(None)));
        assert!(f(1).le(ObjKind::Native));
        assert!(!f(1).le(f(2)));
        assert_eq!(f(1).join(f(2)), ObjKind::Function(None));
        assert_eq!(ObjKind::Plain.join(ObjKind::Array), ObjKind::Native);
        assert_eq!(ObjKind::Plain.join(ObjKind::Any), ObjKind::Any);
        assert!(ObjKind::TypedArray(TaKind::Int8).le(ObjKind::Native));
        assert!(!ObjKind::TypedArray(TaKind::Int8).le(ObjKind::TypedArray(TaKind::Uint8)));
    }

    #[test]
    fn layout_claims() {
        let k3 = claim(3, 3, true, LayoutState::Published);
        let k3u = claim(3, 3, false, LayoutState::Published);
        let k35 = claim(3, 5, false, LayoutState::Published);
        assert!(k3.le(&k3u));
        assert!(!k3u.le(&k3));
        assert!(k3.le(&k35));
        assert!(!k35.le(&k3));
        assert_eq!(
            k3.join(&claim(5, 5, true, LayoutState::Published)),
            claim(3, 5, true, LayoutState::Published)
        );
        // An object with a claim is below one without.
        assert!(is_subtype(
            &obj(ObjKind::Plain, Some(k3)),
            &obj(ObjKind::Plain, None)
        ));
        assert!(!is_subtype(
            &obj(ObjKind::Plain, None),
            &obj(ObjKind::Plain, Some(k3u))
        ));
    }

    #[test]
    fn constructing_prefix_rule() {
        let cons = |n| {
            obj(
                ObjKind::Plain,
                Some(claim(3, 3, true, LayoutState::Constructing(n))),
            )
        };
        let prefix = |n| {
            obj(
                ObjKind::Plain,
                Some(claim(3, 3, true, LayoutState::Prefix(n))),
            )
        };
        let published = obj(
            ObjKind::Plain,
            Some(claim(3, 3, true, LayoutState::Published)),
        );
        // Constructing(n) is a K-prefix(n), and a prefix of anything shorter.
        assert!(is_subtype(&cons(2), &prefix(2)));
        assert!(is_subtype(&cons(2), &prefix(1)));
        assert!(!is_subtype(&cons(1), &prefix(2)));
        // ... but never a published K: a stamp guard would fail on it.
        assert!(!is_subtype(&cons(2), &published));
        // Nor a different stage of construction.
        assert!(!is_subtype(&cons(1), &cons(2)));
        assert!(!is_subtype(&cons(2), &cons(1)));
        // A published K supports every prefix.
        assert!(is_subtype(&published, &prefix(2)));
        assert!(!is_subtype(&prefix(2), &published));
        // Joins land on the common prefix.
        assert_eq!(join(&cons(2), &published), Some(prefix(2)));
        assert_eq!(join(&cons(1), &cons(2)), Some(prefix(1)));
        assert_eq!(join(&cons(2), &cons(2)), Some(cons(2)));
    }

    #[test]
    fn shallow_loads() {
        // A field claimed to hold a Plain object of layout K2: the load
        // keeps object-ness and kind, never the layout (§4.3, §4.6).
        let claimed = Type::Val(VSet::new(
            TagSet::OBJECT,
            NumInfo::TOP,
            ObjInfo {
                kind: ObjKind::Plain,
                singleton: None,
                layout: Some(claim(7, 7, true, LayoutState::Published)),
            },
            StrInfo::TOP,
        ));
        let loaded = claimed.shallow();
        let o = loaded.obj_info().unwrap();
        assert_eq!(o.kind, ObjKind::Plain);
        assert_eq!(o.layout, None);
        assert!(is_subtype(&claimed, &loaded));
        assert!(loaded.killable_components().is_empty());
    }

    #[test]
    fn kills_and_weakening() {
        let t = obj(
            ObjKind::Plain,
            Some(claim(3, 3, true, LayoutState::Published)),
        );
        assert_eq!(
            t.killable_components(),
            KillSet::LAYOUT.union(KillSet::TYPES)
        );
        let types = KillPattern::of(KillSet::TYPES);
        assert!(types.matches(&t));
        let w = t.weakened(&types);
        assert!(!types.matches(&w));
        assert!(is_subtype(&t, &w));
        assert!(!w.obj_info().unwrap().layout.unwrap().types);
        let all = t.weakened(&KillPattern::ALL);
        assert_eq!(all, obj(ObjKind::Plain, None));
        // Key filter.
        let other = KillPattern {
            set: KillSet::LAYOUT,
            keys: Some(KeyRange::one(lk(9))),
        };
        assert!(!other.matches(&t));
        // Invariant components are never killable.
        assert!(!KillPattern::ALL.matches(&Type::val(TagSet::INT32)));
        assert!(!KillPattern::ALL.matches(&obj(ObjKind::Function(Some(ScriptId::new(1))), None)));
        // Facts.
        let f = Type::Fact(FactKind::Fuse(FuseId::from_u32(0)));
        assert!(KillPattern::of(KillSet::FUSE).matches(&f));
        assert!(!KillPattern::of(KillSet::BINDING).matches(&f));
        // Constructing weakens to the prefix.
        let c = obj(
            ObjKind::Plain,
            Some(claim(3, 3, true, LayoutState::Constructing(2))),
        );
        let cw = c.weakened(&KillPattern::of(KillSet::CONSTRUCTING));
        assert_eq!(
            cw,
            obj(
                ObjKind::Plain,
                Some(claim(3, 3, true, LayoutState::Prefix(2)))
            )
        );
    }
}
