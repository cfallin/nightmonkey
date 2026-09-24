//! The opcode set (MIR.md §7): per-op signature, result rule, successor
//! shape, and effect summary.
//!
//! Everything here is a function of the opcode, its immediates and its
//! operand *types* (plus the module tables). That is what lets the
//! validator check an op without knowing how it got there, and lets a
//! pass reason about an op it did not create.
//!
//! Terminators that can fail carry their refined outputs to the success
//! edge as *outputs*: the success block's params receive them (see
//! `func::EdgeArg`). [`Sig::outputs`] are the types the op produces; the
//! receiving params may be supertypes.

use crate::ids::{EnvSlot, LayoutKey, Pc, ScriptId};
use crate::mir::entity::{AtomId, BindingId, FuseId, NativeId, SnapObj};
use crate::mir::module::{Module, Region};
use crate::mir::types::{
    is_subtype, join, FactKind, IRange, KeyRange, KillPattern, KillSet, LayoutClaim, LayoutState,
    NumInfo, ObjInfo, ObjKind, RawKind, StrInfo, TagSet, Type, VSet, I32_MAX, I32_MIN, INT_LIM,
};
use crate::opsem::{TaKind, PRIM_BIGINT, PRIM_DOUBLE, PRIM_INT32, PRIM_NULL, PRIM_UNDEFINED};

/// A boxed constant.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ConstVal {
    Undefined,
    Null,
    Bool(bool),
    Int32(i32),
    /// Bits of an f64, so the opcode stays `Eq` (and NaNs round-trip).
    Double(u64),
}

/// The target of an unbox.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum UnboxKind {
    I32,
    F64Num,
    Bool,
    Obj,
    Str,
}

impl UnboxKind {
    pub const ALL: [UnboxKind; 5] = [
        UnboxKind::I32,
        UnboxKind::F64Num,
        UnboxKind::Bool,
        UnboxKind::Obj,
        UnboxKind::Str,
    ];

    pub fn name(self) -> &'static str {
        match self {
            UnboxKind::I32 => "i32",
            UnboxKind::F64Num => "f64num",
            UnboxKind::Bool => "bool",
            UnboxKind::Obj => "obj",
            UnboxKind::Str => "str",
        }
    }

    /// The tags a value must have for this unbox to be infallible.
    pub fn tags(self) -> TagSet {
        match self {
            UnboxKind::I32 => TagSet::INT32,
            UnboxKind::F64Num => TagSet::NUMBER,
            UnboxKind::Bool => TagSet::BOOLEAN,
            UnboxKind::Obj => TagSet::OBJECT,
            UnboxKind::Str => TagSet::STRING,
        }
    }

    /// The raw type unboxing `v` (already within `tags()`) yields.
    fn result(self, v: &VSet) -> Type {
        match self {
            UnboxKind::I32 => Type::I32(v.num.int_range(I32_MIN, I32_MAX)),
            UnboxKind::F64Num => Type::F64(v.num),
            UnboxKind::Bool => Type::Bool,
            UnboxKind::Obj => Type::Obj(v.obj),
            UnboxKind::Str => Type::Str(v.str),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum F64Op {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum BitOp {
    And,
    Or,
    Xor,
    Shl,
    Shr,
}

/// A raw numeric representation, for compares.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum NumRepr {
    I32,
    Int,
    F64,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Cc {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum MathFn {
    Abs,
    Floor,
    Ceil,
    Round,
    Trunc,
    Sqrt,
    Sign,
    Fround,
    Sin,
    Cos,
    Tan,
    Exp,
    Log,
    Min,
    Max,
    Pow,
    Atan2,
}

impl MathFn {
    pub const ALL: [MathFn; 17] = [
        MathFn::Abs,
        MathFn::Floor,
        MathFn::Ceil,
        MathFn::Round,
        MathFn::Trunc,
        MathFn::Sqrt,
        MathFn::Sign,
        MathFn::Fround,
        MathFn::Sin,
        MathFn::Cos,
        MathFn::Tan,
        MathFn::Exp,
        MathFn::Log,
        MathFn::Min,
        MathFn::Max,
        MathFn::Pow,
        MathFn::Atan2,
    ];

    pub fn arity(self) -> usize {
        match self {
            MathFn::Min | MathFn::Max | MathFn::Pow | MathFn::Atan2 => 2,
            _ => 1,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum JsBinop {
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    BitAnd,
    BitOr,
    BitXor,
    Lsh,
    Rsh,
    Ursh,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum JsUnop {
    Neg,
    Pos,
    BitNot,
    Inc,
    Dec,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum JsCc {
    Eq,
    Ne,
    StrictEq,
    StrictNe,
    Lt,
    Le,
    Gt,
    Ge,
}

/// An opcode with its immediates. Operands are `InstData::args`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Opcode {
    // Constants.
    ConstVal(ConstVal),
    ConstI32(i32),
    /// Bits of the f64.
    ConstF64(u64),
    ConstBool(bool),
    ConstObj(SnapObj),
    ConstStr(AtomId),

    // Conversions.
    Box,
    Unbox(UnboxKind),
    I32ToInt,
    I32ToF64,
    IntToF64,
    /// Identity with a declared weaker result type (§4.2). Every op's
    /// result may be declared weaker than its rule; `weaken` is the op
    /// whose only purpose is that.
    Weaken,

    // Guards and checks (terminators: ok, fail).
    GuardUnbox(UnboxKind),
    GuardTags(TagSet),
    GuardKind(ObjKind),
    GuardLayout {
        keys: KeyRange,
        types: bool,
    },
    GuardSingleton(SnapObj),
    GuardScript(ScriptId),
    /// An f64 that is exactly an int32 (not -0) becomes an `I32`.
    F64ToIntExact,
    CheckFuse(FuseId),
    CheckBinding(BindingId),
    CheckNative(NativeId),

    // Control.
    Jump,
    Br,
    /// Dense switch over `0..n`, plus a default.
    Switch(u32),
    Return,
    /// Operands: `this`, `nargs` args, `nlocals` locals, then the operand
    /// stack (the rest). All `Val(⊤)`.
    Exit {
        pc: Pc,
        nargs: u32,
        nlocals: u32,
    },
    ExitThrow {
        pc: Pc,
        nargs: u32,
        nlocals: u32,
    },
    Unreachable,

    // Numeric.
    I32Ovf(ArithOp),
    I32Wrap(ArithOp),
    IntArith(ArithOp),
    F64Arith(F64Op),
    F64Neg,
    I32Bit(BitOp),
    I32Ushr,
    ToInt32,
    Cmp(NumRepr, Cc),
    Math(MathFn),

    // Generic JS ops.
    JsAdd,
    JsBinop(JsBinop),
    JsUnop(JsUnop),
    JsCompare(JsCc),
    JsTypeof,
    JsToBool,
    JsToNumeric,
    JsGetProp(AtomId),
    JsSetProp(AtomId),
    JsGetElem,
    JsSetElem,
    JsGetName(AtomId),

    // Objects.
    LoadField(AtomId),
    StoreField(AtomId),
    InitField(AtomId),
    PublishLayout,
    NewObject(LayoutKey),
    NewArray,
    LoadElem,
    StoreElem,
    LoadTa,
    StoreTa,
    LengthArray,
    LengthString,
    LengthTa,
    ElementsPtr,
    StrCharCodeAt,

    // Globals and environments.
    LoadGName(BindingId),
    StoreGName(BindingId),
    EnvCurrent,
    EnvParent,
    EnvLoad(EnvSlot),
    EnvStore(EnvSlot),

    // Calls. Operands: callee (or new.target pair), `this`, args.
    Call,
    CallDirect,
    Construct,
    CallNative(NativeId),
}

/// What a successor edge means to its terminator.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum SuccRole {
    Target,
    Then,
    Else,
    Case(u32),
    Default,
    Ok,
    Fail,
    OkClean,
    OkDirty,
    Err,
}

impl SuccRole {
    pub fn name(self) -> String {
        match self {
            SuccRole::Target => "target".into(),
            SuccRole::Then => "then".into(),
            SuccRole::Else => "else".into(),
            SuccRole::Case(n) => format!("case{n}"),
            SuccRole::Default => "default".into(),
            SuccRole::Ok => "ok".into(),
            SuccRole::Fail => "fail".into(),
            SuccRole::OkClean => "ok_clean".into(),
            SuccRole::OkDirty => "ok_dirty".into(),
            SuccRole::Err => "err".into(),
        }
    }

    /// Whether this edge may carry the op's outputs.
    pub fn carries_outputs(self) -> bool {
        matches!(self, SuccRole::Ok | SuccRole::OkClean | SuccRole::OkDirty)
    }
}

const OK_FAIL: &[SuccRole] = &[SuccRole::Ok, SuccRole::Fail];
const CLEAN_DIRTY_ERR: &[SuccRole] = &[SuccRole::OkClean, SuccRole::OkDirty, SuccRole::Err];
const OK_ERR: &[SuccRole] = &[SuccRole::Ok, SuccRole::Err];

impl Opcode {
    /// The successor edges this op has, in order. Empty for non-terminators
    /// and for the exiting terminators.
    pub fn roles(&self) -> Vec<SuccRole> {
        use Opcode::*;
        match self {
            Jump => vec![SuccRole::Target],
            Br => vec![SuccRole::Then, SuccRole::Else],
            Switch(n) => (0..*n)
                .map(SuccRole::Case)
                .chain([SuccRole::Default])
                .collect(),
            GuardUnbox(_)
            | GuardTags(_)
            | GuardKind(_)
            | GuardLayout { .. }
            | GuardSingleton(_)
            | GuardScript(_)
            | F64ToIntExact
            | CheckFuse(_)
            | CheckBinding(_)
            | CheckNative(_)
            | I32Ovf(_)
            | LoadElem
            | StoreElem
            | LoadTa
            | StoreTa
            | StrCharCodeAt
            | InitField(_) => OK_FAIL.to_vec(),
            JsAdd | JsBinop(_) | JsUnop(_) | JsCompare(_) | JsToNumeric | JsGetProp(_)
            | JsSetProp(_) | JsGetElem | JsSetElem | LoadField(_) | StoreField(_) | Call
            | CallDirect | Construct | CallNative(_) => CLEAN_DIRTY_ERR.to_vec(),
            // No dynamic effect report: the kill is static, on `ok`.
            JsGetName(_) => OK_ERR.to_vec(),
            _ => vec![],
        }
    }

    pub fn is_terminator(&self) -> bool {
        matches!(
            self,
            Opcode::Return | Opcode::Exit { .. } | Opcode::ExitThrow { .. } | Opcode::Unreachable
        ) || !self.roles().is_empty()
    }

    /// The frame-state split of an exit's operands, if this is one.
    pub fn exit_shape(&self) -> Option<(Pc, u32, u32)> {
        match *self {
            Opcode::Exit { pc, nargs, nlocals } | Opcode::ExitThrow { pc, nargs, nlocals } => {
                Some((pc, nargs, nlocals))
            }
            _ => None,
        }
    }
}

/// An op's typing: the types of its (non-terminator) results and of its
/// (terminator) outputs.
#[derive(Clone, PartialEq, Debug, Default)]
pub struct Sig {
    pub results: Vec<Type>,
    pub outputs: Vec<Type>,
}

impl Sig {
    fn result(t: Type) -> Sig {
        Sig {
            results: vec![t],
            outputs: vec![],
        }
    }

    fn output(t: Type) -> Sig {
        Sig {
            results: vec![],
            outputs: vec![t],
        }
    }

    fn none() -> Sig {
        Sig::default()
    }
}

type SigResult = Result<Sig, String>;

fn arity(args: &[Type], n: usize) -> Result<(), String> {
    if args.len() != n {
        return Err(format!("expected {n} operand(s), got {}", args.len()));
    }
    Ok(())
}

fn val(t: &Type, what: &str) -> Result<VSet, String> {
    match t {
        Type::Val(v) => Ok(*v),
        t => Err(format!(
            "{what}: expected a val, got {}",
            crate::mir::print::type_str(t)
        )),
    }
}

fn obj(t: &Type, what: &str) -> Result<ObjInfo, String> {
    match t {
        Type::Obj(o) => Ok(*o),
        t => Err(format!(
            "{what}: expected an obj, got {}",
            crate::mir::print::type_str(t)
        )),
    }
}

fn i32r(t: &Type, what: &str) -> Result<IRange, String> {
    match t {
        Type::I32(r) => Ok(*r),
        t => Err(format!(
            "{what}: expected an i32, got {}",
            crate::mir::print::type_str(t)
        )),
    }
}

fn want(ok: bool, msg: impl FnOnce() -> String) -> Result<(), String> {
    if ok {
        Ok(())
    } else {
        Err(msg())
    }
}

fn want_kind(o: &ObjInfo, k: ObjKind, what: &str) -> Result<(), String> {
    want(o.kind.le(k), || {
        format!("{what}: expected an object of kind {k:?}, got {:?}", o.kind)
    })
}

/// Interval arithmetic in i128, which no i64 product overflows.
fn arith_range(op: ArithOp, a: IRange, b: IRange) -> (i128, i128) {
    let (al, ah, bl, bh) = (a.lo as i128, a.hi as i128, b.lo as i128, b.hi as i128);
    match op {
        ArithOp::Add => (al + bl, ah + bh),
        ArithOp::Sub => (al - bh, ah - bl),
        ArithOp::Mul => {
            let p = [al * bl, al * bh, ah * bl, ah * bh];
            (*p.iter().min().unwrap(), *p.iter().max().unwrap())
        }
    }
}

fn clamp_range(lo: i128, hi: i128, min: i64, max: i64) -> IRange {
    let lo = lo.clamp(min as i128, max as i128) as i64;
    let hi = hi.clamp(min as i128, max as i128) as i64;
    IRange::new(lo, hi)
}

/// The type a boxed constant has.
pub fn const_val_type(c: ConstVal) -> Type {
    match c {
        ConstVal::Undefined => Type::val(TagSet::prims(PRIM_UNDEFINED)),
        ConstVal::Null => Type::val(TagSet::prims(PRIM_NULL)),
        ConstVal::Bool(_) => Type::val(TagSet::BOOLEAN),
        ConstVal::Int32(n) => Type::Val(VSet::new(
            TagSet::INT32,
            NumInfo::int(n.into(), n.into()),
            ObjInfo::TOP,
            StrInfo::TOP,
        )),
        ConstVal::Double(bits) => Type::Val(VSet::new(
            TagSet::DOUBLE,
            NumInfo::exact(f64::from_bits(bits)),
            ObjInfo::TOP,
            StrInfo::TOP,
        )),
    }
}

/// Boxing is infallible and keeps every refinement.
pub fn box_type(t: &Type) -> Result<Type, String> {
    Ok(match t {
        Type::I32(r) => Type::Val(VSet::new(
            TagSet::INT32,
            r.num(),
            ObjInfo::TOP,
            StrInfo::TOP,
        )),
        // A raw integer or double may box with either number tag.
        Type::Int(r) => Type::Val(VSet::new(
            TagSet::NUMBER,
            r.num(),
            ObjInfo::TOP,
            StrInfo::TOP,
        )),
        Type::F64(n) => Type::Val(VSet::new(TagSet::NUMBER, *n, ObjInfo::TOP, StrInfo::TOP)),
        Type::Bool => Type::val(TagSet::BOOLEAN),
        Type::Obj(o) => Type::Val(VSet::new(TagSet::OBJECT, NumInfo::TOP, *o, StrInfo::TOP)),
        Type::Str(s) => Type::Val(VSet::new(TagSet::STRING, NumInfo::TOP, ObjInfo::TOP, *s)),
        t => {
            return Err(format!(
                "box: cannot box {}",
                crate::mir::print::type_str(t)
            ))
        }
    })
}

/// The claim a field op on a receiver of type `o` relies on: every layout
/// in the claim's key range must have `name`, within the supported
/// prefix. Returns the slot and, per layout, the field's claimed type.
fn field_claims(
    o: &ObjInfo,
    name: AtomId,
    m: &Module,
    what: &str,
) -> Result<(LayoutClaim, Vec<Type>), String> {
    let c = o
        .layout
        .ok_or_else(|| format!("{what}: receiver has no layout claim"))?;
    let mut claims = vec![];
    for k in c.keys.keys() {
        let layout = m
            .layouts
            .get(&k)
            .ok_or_else(|| format!("{what}: layout L{k} is not in the module"))?;
        let (slot, f) = layout
            .field(name)
            .ok_or_else(|| format!("{what}: layout L{k} has no field {}", m.atoms[name]))?;
        if let Some(n) = c.state.slots() {
            want(slot < n as usize, || {
                format!(
                    "{what}: field {} is slot {slot}, beyond the {n}-slot prefix",
                    m.atoms[name]
                )
            })?;
        }
        claims.push(f.claim);
    }
    Ok((c, claims))
}

fn math_result(_f: MathFn) -> Type {
    Type::F64_TOP
}

/// The typing rule for `op` applied to operands of types `args`.
pub fn signature(op: &Opcode, args: &[Type], m: &Module) -> SigResult {
    use Opcode::*;
    let number_or_bigint = TagSet::prims(PRIM_INT32 | PRIM_DOUBLE | PRIM_BIGINT);
    Ok(match op {
        ConstVal(c) => {
            arity(args, 0)?;
            Sig::result(const_val_type(*c))
        }
        ConstI32(n) => {
            arity(args, 0)?;
            Sig::result(Type::I32(IRange::new((*n).into(), (*n).into())))
        }
        ConstF64(bits) => {
            arity(args, 0)?;
            Sig::result(Type::F64(NumInfo::exact(f64::from_bits(*bits))))
        }
        ConstBool(_) => {
            arity(args, 0)?;
            Sig::result(Type::Bool)
        }
        ConstObj(s) => {
            arity(args, 0)?;
            let def = m
                .snap_objs
                .get(*s)
                .ok_or_else(|| format!("const.obj: {s} is not in the module"))?;
            Sig::result(Type::Obj(ObjInfo {
                kind: def.kind,
                singleton: Some(*s),
                layout: None,
            }))
        }
        ConstStr(a) => {
            arity(args, 0)?;
            want(m.atoms.contains(*a), || {
                format!("const.str: {a} is not in the module")
            })?;
            Sig::result(Type::Str(StrInfo { atom: Some(*a) }))
        }

        Box => {
            arity(args, 1)?;
            Sig::result(box_type(&args[0])?)
        }
        Unbox(k) => {
            arity(args, 1)?;
            let v = val(&args[0], "unbox")?;
            want(v.tags.is_nonempty_subset_of(k.tags()), || {
                format!(
                    "unbox.{}: operand {} is not proven to have tags {}",
                    k.name(),
                    crate::mir::print::type_str(&args[0]),
                    crate::mir::print::tags_str(k.tags())
                )
            })?;
            Sig::result(k.result(&v))
        }
        I32ToInt => {
            arity(args, 1)?;
            Sig::result(Type::Int(i32r(&args[0], "i32.to_int")?))
        }
        I32ToF64 => {
            arity(args, 1)?;
            Sig::result(Type::F64(i32r(&args[0], "i32.to_f64")?.num()))
        }
        IntToF64 => {
            arity(args, 1)?;
            match args[0] {
                Type::Int(r) => Sig::result(Type::F64(r.num())),
                _ => return Err("int.to_f64: expected an int".into()),
            }
        }
        Weaken => {
            arity(args, 1)?;
            Sig::result(args[0])
        }

        GuardUnbox(k) => {
            arity(args, 1)?;
            let v = val(&args[0], "guard.unbox")?.restrict(k.tags());
            Sig::output(k.result(&v))
        }
        GuardTags(t) => {
            arity(args, 1)?;
            Sig::output(Type::Val(val(&args[0], "guard.tags")?.restrict(*t)))
        }
        GuardKind(k) => {
            arity(args, 1)?;
            let o = obj(&args[0], "guard.kind")?;
            let kind = if o.kind.le(*k) { o.kind } else { *k };
            Sig::output(Type::Obj(ObjInfo { kind, ..o }))
        }
        GuardLayout { keys, types } => {
            arity(args, 1)?;
            let o = obj(&args[0], "guard.layout")?;
            let new = LayoutClaim {
                keys: *keys,
                types: *types,
                state: LayoutState::Published,
            };
            let layout = match o.layout {
                Some(c) if c.le(&new) => c,
                _ => new,
            };
            Sig::output(Type::Obj(ObjInfo {
                layout: Some(layout),
                ..o
            }))
        }
        GuardSingleton(s) => {
            arity(args, 1)?;
            let o = obj(&args[0], "guard.singleton")?;
            let def = m
                .snap_objs
                .get(*s)
                .ok_or_else(|| format!("guard.singleton: {s} is not in the module"))?;
            Sig::output(Type::Obj(ObjInfo {
                kind: if o.kind.le(def.kind) {
                    o.kind
                } else {
                    def.kind
                },
                singleton: Some(*s),
                ..o
            }))
        }
        GuardScript(s) => {
            arity(args, 1)?;
            let o = obj(&args[0], "guard.script")?;
            Sig::output(Type::Obj(ObjInfo {
                kind: ObjKind::Function(Some(*s)),
                ..o
            }))
        }
        F64ToIntExact => {
            arity(args, 1)?;
            match args[0] {
                Type::F64(n) => Sig::output(Type::I32(n.int_range(I32_MIN, I32_MAX))),
                _ => return Err("f64.to_int_exact: expected an f64".into()),
            }
        }
        CheckFuse(f) => {
            arity(args, 0)?;
            want(m.fuses.contains(*f), || {
                format!("check.fuse: {f} is not in the module")
            })?;
            Sig::output(Type::Fact(FactKind::Fuse(*f)))
        }
        CheckBinding(b) => {
            arity(args, 0)?;
            want(m.bindings.contains(*b), || {
                format!("check.binding: {b} is not in the module")
            })?;
            Sig::output(Type::Fact(FactKind::Binding(*b)))
        }
        CheckNative(n) => {
            arity(args, 0)?;
            want(m.natives.contains(*n), || {
                format!("check.native: {n} is not in the module")
            })?;
            Sig::output(Type::Fact(FactKind::NativeIntact(*n)))
        }

        Jump | Unreachable => {
            arity(args, 0)?;
            Sig::none()
        }
        Br => {
            arity(args, 1)?;
            want(args[0] == Type::Bool, || "br: expected a bool".into())?;
            Sig::none()
        }
        Switch(_) => {
            arity(args, 1)?;
            i32r(&args[0], "switch")?;
            Sig::none()
        }
        Return => {
            arity(args, 1)?;
            val(&args[0], "return")?;
            Sig::none()
        }
        Exit { nargs, nlocals, .. } | ExitThrow { nargs, nlocals, .. } => {
            want(args.len() > (*nargs + *nlocals) as usize, || {
                "exit: fewer operands than this + args + locals".into()
            })?;
            for (i, t) in args.iter().enumerate() {
                val(t, &format!("exit operand {i}"))?;
            }
            Sig::none()
        }

        I32Ovf(a) => {
            arity(args, 2)?;
            let (x, y) = (i32r(&args[0], "i32 arith")?, i32r(&args[1], "i32 arith")?);
            let (lo, hi) = arith_range(*a, x, y);
            Sig::output(Type::I32(clamp_range(lo, hi, I32_MIN, I32_MAX)))
        }
        I32Wrap(a) => {
            arity(args, 2)?;
            let (x, y) = (i32r(&args[0], "i32 arith")?, i32r(&args[1], "i32 arith")?);
            let (lo, hi) = arith_range(*a, x, y);
            let fits = lo >= I32_MIN as i128 && hi <= I32_MAX as i128;
            Sig::result(if fits {
                Type::I32(IRange::new(lo as i64, hi as i64))
            } else {
                Type::I32_TOP
            })
        }
        IntArith(a) => {
            arity(args, 2)?;
            let r = |t: &Type| match t {
                Type::Int(r) => Ok(*r),
                _ => Err("int arith: expected int operands".to_string()),
            };
            let (lo, hi) = arith_range(*a, r(&args[0])?, r(&args[1])?);
            // `Int` arithmetic is only for interval proofs: an op that may
            // leave the exact-double domain is ill-typed, not a wraparound.
            want(lo >= -(INT_LIM as i128) && hi <= INT_LIM as i128, || {
                format!("int arith: result range [{lo}, {hi}] may leave [-2^53, 2^53]")
            })?;
            Sig::result(Type::Int(IRange::new(lo as i64, hi as i64)))
        }
        F64Arith(_) => {
            arity(args, 2)?;
            for t in args {
                want(matches!(t, Type::F64(_)), || {
                    "f64 arith: expected f64 operands".into()
                })?;
            }
            Sig::result(Type::F64_TOP)
        }
        F64Neg => {
            arity(args, 1)?;
            want(matches!(args[0], Type::F64(_)), || {
                "f64.neg: expected an f64".into()
            })?;
            Sig::result(Type::F64_TOP)
        }
        I32Bit(_) => {
            arity(args, 2)?;
            i32r(&args[0], "i32 bitop")?;
            i32r(&args[1], "i32 bitop")?;
            Sig::result(Type::I32_TOP)
        }
        I32Ushr => {
            arity(args, 2)?;
            i32r(&args[0], "i32.ushr")?;
            i32r(&args[1], "i32.ushr")?;
            Sig::result(Type::Int(IRange::new(0, u32::MAX.into())))
        }
        ToInt32 => {
            arity(args, 1)?;
            want(matches!(args[0], Type::F64(_) | Type::Int(_)), || {
                "to_int32: expected an f64 or int".into()
            })?;
            Sig::result(Type::I32_TOP)
        }
        Cmp(r, _) => {
            arity(args, 2)?;
            for t in args {
                let ok = matches!(
                    (r, t),
                    (NumRepr::I32, Type::I32(_))
                        | (NumRepr::Int, Type::Int(_))
                        | (NumRepr::F64, Type::F64(_))
                );
                want(ok, || format!("cmp: operand is not {r:?}"))?;
            }
            Sig::result(Type::Bool)
        }
        Math(f) => {
            arity(args, f.arity())?;
            for t in args {
                want(matches!(t, Type::F64(_)), || {
                    "math: expected f64 operands".into()
                })?;
            }
            Sig::result(math_result(*f))
        }

        JsAdd => {
            arity(args, 2)?;
            val(&args[0], "js.add")?;
            val(&args[1], "js.add")?;
            Sig::output(Type::val(number_or_bigint.union(TagSet::STRING)))
        }
        JsBinop(b) => {
            arity(args, 2)?;
            val(&args[0], "js.binop")?;
            val(&args[1], "js.binop")?;
            Sig::output(Type::val(match b {
                self::JsBinop::Ursh => TagSet::NUMBER,
                self::JsBinop::BitAnd
                | self::JsBinop::BitOr
                | self::JsBinop::BitXor
                | self::JsBinop::Lsh
                | self::JsBinop::Rsh => TagSet::prims(PRIM_INT32 | PRIM_BIGINT),
                _ => number_or_bigint,
            }))
        }
        JsUnop(u) => {
            arity(args, 1)?;
            val(&args[0], "js.unop")?;
            Sig::output(Type::val(match u {
                self::JsUnop::Pos => TagSet::NUMBER,
                _ => number_or_bigint,
            }))
        }
        JsCompare(_) => {
            arity(args, 2)?;
            val(&args[0], "js.compare")?;
            val(&args[1], "js.compare")?;
            Sig::output(Type::Bool)
        }
        JsTypeof => {
            arity(args, 1)?;
            val(&args[0], "js.typeof")?;
            Sig::result(Type::STR_TOP)
        }
        JsToBool => {
            arity(args, 1)?;
            val(&args[0], "js.tobool")?;
            Sig::result(Type::Bool)
        }
        JsToNumeric => {
            arity(args, 1)?;
            val(&args[0], "js.tonumeric")?;
            Sig::output(Type::val(number_or_bigint))
        }
        JsGetProp(_) | JsGetElem | JsSetProp(_) | JsSetElem => {
            let n = match op {
                JsGetProp(_) => 1,
                JsGetElem | JsSetProp(_) => 2,
                _ => 3,
            };
            arity(args, n)?;
            for t in args {
                val(t, "js prop op")?;
            }
            if matches!(op, JsGetProp(_) | JsGetElem) {
                Sig::output(Type::VAL_TOP)
            } else {
                Sig::none()
            }
        }
        JsGetName(_) => {
            arity(args, 0)?;
            Sig::output(Type::VAL_TOP)
        }

        LoadField(name) => {
            arity(args, 1)?;
            let o = obj(&args[0], "load_field")?;
            let (c, claims) = field_claims(&o, *name, m, "load_field")?;
            want(c.types, || {
                "load_field: receiver's layout claim lacks `types`".into()
            })?;
            let mut t = claims[0];
            for c in &claims[1..] {
                t = join(&t, c).ok_or("load_field: field claims disagree in representation")?;
            }
            Sig::output(t.shallow())
        }
        StoreField(name) => {
            arity(args, 2)?;
            let o = obj(&args[0], "store_field")?;
            let (c, claims) = field_claims(&o, *name, m, "store_field")?;
            want(c.types, || {
                "store_field: receiver's layout claim lacks `types`".into()
            })?;
            for claim in &claims {
                want(is_subtype(&args[1], claim), || {
                    format!(
                        "store_field: value {} does not conform to the claim {}",
                        crate::mir::print::type_str(&args[1]),
                        crate::mir::print::type_str(claim)
                    )
                })?;
            }
            Sig::none()
        }
        InitField(name) => {
            arity(args, 2)?;
            let o = obj(&args[0], "init_field")?;
            let c = o.layout.ok_or("init_field: receiver has no layout claim")?;
            let n = match c.state {
                LayoutState::Constructing(n) => n,
                _ => return Err("init_field: receiver is not under construction".into()),
            };
            want(c.keys.lo == c.keys.hi, || {
                "init_field: receiver's layout is not exact".into()
            })?;
            let layout = m
                .layouts
                .get(&c.keys.lo)
                .ok_or_else(|| format!("init_field: layout L{} is not in the module", c.keys.lo))?;
            let f = layout
                .fields
                .get(n as usize)
                .ok_or("init_field: every field is already initialized")?;
            want(f.name == *name, || {
                format!(
                    "init_field: next field is {}, not {}",
                    m.atoms[f.name], m.atoms[*name]
                )
            })?;
            want(is_subtype(&args[1], &f.claim), || {
                "init_field: value does not conform to the field's claim".into()
            })?;
            Sig::output(Type::Obj(ObjInfo {
                layout: Some(LayoutClaim {
                    state: LayoutState::Constructing(n + 1),
                    ..c
                }),
                ..o
            }))
        }
        PublishLayout => {
            arity(args, 1)?;
            let o = obj(&args[0], "publish_layout")?;
            let c = o
                .layout
                .ok_or("publish_layout: receiver has no layout claim")?;
            let n = match c.state {
                LayoutState::Constructing(n) => n,
                _ => return Err("publish_layout: receiver is not under construction".into()),
            };
            let layout = m.layouts.get(&c.keys.lo).ok_or_else(|| {
                format!("publish_layout: layout L{} is not in the module", c.keys.lo)
            })?;
            want(
                c.keys.lo == c.keys.hi && n as usize == layout.fields.len(),
                || "publish_layout: not every field is initialized".into(),
            )?;
            Sig::result(Type::Obj(ObjInfo {
                layout: Some(LayoutClaim {
                    state: LayoutState::Published,
                    ..c
                }),
                ..o
            }))
        }
        NewObject(k) => {
            arity(args, 0)?;
            want(m.layouts.contains_key(k), || {
                format!("new_object: layout L{k} is not in the module")
            })?;
            Sig::result(Type::Obj(ObjInfo {
                kind: ObjKind::Plain,
                singleton: None,
                layout: Some(LayoutClaim {
                    keys: KeyRange::one(*k),
                    types: true,
                    state: LayoutState::Constructing(0),
                }),
            }))
        }
        NewArray => {
            arity(args, 1)?;
            i32r(&args[0], "new_array")?;
            Sig::result(Type::Obj(ObjInfo::kind(ObjKind::Array)))
        }
        LoadElem | StoreElem => {
            arity(args, if *op == LoadElem { 2 } else { 3 })?;
            want_kind(&obj(&args[0], "elem op")?, ObjKind::Native, "elem op")?;
            i32r(&args[1], "elem op index")?;
            if *op == LoadElem {
                Sig::output(Type::VAL_TOP)
            } else {
                val(&args[2], "store_elem value")?;
                Sig::none()
            }
        }
        LoadTa | StoreTa => {
            arity(args, if *op == LoadTa { 2 } else { 3 })?;
            let o = obj(&args[0], "typed array op")?;
            let k = match o.kind {
                ObjKind::TypedArray(k) => k,
                _ => {
                    return Err(
                        "typed array op: receiver is not a typed array of known kind".into(),
                    )
                }
            };
            i32r(&args[1], "typed array op index")?;
            if *op == LoadTa {
                Sig::output(match (k, k.proven_range()) {
                    (TaKind::Float32 | TaKind::Float64, _) => Type::F64_TOP,
                    (TaKind::Uint32, Some((lo, hi))) => Type::Int(IRange::new(lo, hi)),
                    (_, Some((lo, hi))) => Type::I32(IRange::new(lo, hi)),
                    (_, None) => Type::I32_TOP,
                })
            } else {
                want(
                    matches!(args[2], Type::I32(_) | Type::Int(_) | Type::F64(_)),
                    || "store_ta: value must be a raw number".into(),
                )?;
                Sig::none()
            }
        }
        LengthArray => {
            arity(args, 1)?;
            want_kind(
                &obj(&args[0], "length.array")?,
                ObjKind::Array,
                "length.array",
            )?;
            Sig::result(Type::Int(IRange::new(0, u32::MAX.into())))
        }
        LengthString => {
            arity(args, 1)?;
            want(matches!(args[0], Type::Str(_)), || {
                "length.string: expected a str".into()
            })?;
            Sig::result(Type::I32(IRange::new(0, (1 << 30) - 2)))
        }
        LengthTa => {
            arity(args, 1)?;
            let o = obj(&args[0], "length.ta")?;
            want(matches!(o.kind, ObjKind::TypedArray(_)), || {
                "length.ta: expected a typed array".into()
            })?;
            Sig::result(Type::Int(IRange::new(0, INT_LIM)))
        }
        ElementsPtr => {
            arity(args, 1)?;
            want_kind(
                &obj(&args[0], "elements_ptr")?,
                ObjKind::Native,
                "elements_ptr",
            )?;
            Sig::result(Type::Raw(RawKind::Elements))
        }
        StrCharCodeAt => {
            arity(args, 2)?;
            want(matches!(args[0], Type::Str(_)), || {
                "str.char_code_at: expected a str".into()
            })?;
            i32r(&args[1], "str.char_code_at index")?;
            Sig::output(Type::I32(IRange::new(0, 0xffff)))
        }

        LoadGName(b) | StoreGName(b) => {
            let def = m
                .bindings
                .get(*b)
                .ok_or_else(|| format!("gname op: {b} is not in the module"))?;
            want(
                !args.is_empty() && args[0] == Type::Fact(FactKind::Binding(*b)),
                || format!("gname op: first operand must be the fact.binding({b}) ghost"),
            )?;
            if let LoadGName(_) = op {
                arity(args, 1)?;
                Sig::result(def.claim)
            } else {
                arity(args, 2)?;
                want(is_subtype(&args[1], &def.claim), || {
                    "store_gname: value does not conform to the binding's claim".into()
                })?;
                Sig::none()
            }
        }
        EnvCurrent => {
            arity(args, 0)?;
            Sig::result(Type::Obj(ObjInfo::kind(ObjKind::Env)))
        }
        EnvParent => {
            arity(args, 1)?;
            want_kind(&obj(&args[0], "env.parent")?, ObjKind::Env, "env.parent")?;
            Sig::result(Type::Obj(ObjInfo::kind(ObjKind::Env)))
        }
        EnvLoad(_) => {
            arity(args, 1)?;
            want_kind(&obj(&args[0], "env.load")?, ObjKind::Env, "env.load")?;
            Sig::result(Type::VAL_TOP)
        }
        EnvStore(_) => {
            arity(args, 2)?;
            want_kind(&obj(&args[0], "env.store")?, ObjKind::Env, "env.store")?;
            val(&args[1], "env.store value")?;
            Sig::none()
        }

        Call | Construct => {
            want(args.len() >= 2, || "call: expected callee and this".into())?;
            for t in args {
                val(t, "call operand")?;
            }
            Sig::output(if *op == Construct {
                Type::OBJ_TOP
            } else {
                Type::VAL_TOP
            })
        }
        CallDirect => {
            want(args.len() >= 2, || {
                "call_direct: expected callee and this".into()
            })?;
            let o = obj(&args[0], "call_direct callee")?;
            want(matches!(o.kind, ObjKind::Function(Some(_))), || {
                "call_direct: callee's script is not known".into()
            })?;
            for t in &args[1..] {
                val(t, "call operand")?;
            }
            Sig::output(Type::VAL_TOP)
        }
        CallNative(n) => {
            want(m.natives.contains(*n), || {
                format!("call_native: {n} is not in the module")
            })?;
            want(!args.is_empty(), || "call_native: expected this".into())?;
            for t in args {
                val(t, "call operand")?;
            }
            Sig::output(Type::VAL_TOP)
        }
    })
}

/// The effect-flags contribution of an op (`bbv/abi.rs` names the bits).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub struct FlagBits(u8);

impl FlagBits {
    pub const NONE: FlagBits = FlagBits(0);
    pub const MUT_THIS: FlagBits = FlagBits(1);
    pub const MUT_OTHER: FlagBits = FlagBits(2);
    pub const STAMPS: FlagBits = FlagBits(4);
    pub const BIND: FlagBits = FlagBits(8);
    pub const ALL: FlagBits = FlagBits(15);

    pub const fn union(self, o: FlagBits) -> FlagBits {
        FlagBits(self.0 | o.0)
    }

    pub const fn bits(self) -> u8 {
        self.0
    }
}

/// How an op contributes to the flow-carried flags word (§6).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FlagsEffect {
    Bits(FlagBits),
    /// Whatever the helper reports at runtime (at most `ALL`).
    Dynamic,
    /// The callee's returned flags.
    Callee,
}

/// Where an op's kill pattern applies, which follows from its shape.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum KillSite {
    /// The op kills nothing.
    None,
    /// A single-successor op: a fence at the op itself.
    Op,
    /// On the `ok` edge (and the `err` edge): a static kill.
    OkEdge,
    /// On the `ok_dirty` edge (and `err`) only: a dynamic kill.
    DirtyEdge,
}

/// An op's effect summary.
#[derive(Clone, PartialEq, Debug)]
pub struct Effects {
    pub reads: Vec<Region>,
    pub writes: Vec<Region>,
    pub may_gc: bool,
    pub may_run_js: bool,
    pub may_throw: bool,
    pub kill: KillPattern,
    pub flags: FlagsEffect,
}

impl Effects {
    pub const PURE: Effects = Effects {
        reads: vec![],
        writes: vec![],
        may_gc: false,
        may_run_js: false,
        may_throw: false,
        kill: KillPattern::NONE,
        flags: FlagsEffect::Bits(FlagBits::NONE),
    };

    /// Arbitrary JS may run: every region, every killable component.
    fn generic(flags: FlagsEffect) -> Effects {
        Effects {
            reads: vec![Region::Unknown],
            writes: vec![Region::Unknown],
            may_gc: true,
            may_run_js: true,
            may_throw: true,
            kill: KillPattern::ALL,
            flags,
        }
    }

    pub fn is_pure(&self) -> bool {
        *self == Effects::PURE
    }
}

impl Opcode {
    /// Where this op's kill pattern (if any) applies.
    pub fn kill_site(&self, fx: &Effects) -> KillSite {
        if fx.kill.is_empty() {
            return KillSite::None;
        }
        let roles = self.roles();
        if roles.contains(&SuccRole::OkDirty) {
            KillSite::DirtyEdge
        } else if roles.contains(&SuccRole::Ok) {
            KillSite::OkEdge
        } else {
            KillSite::Op
        }
    }
}

/// The field region an access through a receiver of type `o` touches:
/// specific when a layout claim proves the receiver's class, the
/// `Field(*, name)` wildcard otherwise.
fn field_region(o: Option<&ObjInfo>, name: AtomId) -> Region {
    Region::Field {
        name,
        keys: o.and_then(|o| o.layout).map(|c| c.keys),
    }
}

/// The elements root a receiver's layout claim proves, if every layout in
/// its range names the same one.
fn elements_root(o: Option<&ObjInfo>, m: &Module) -> Option<crate::ids::RegionRoot> {
    let c = o?.layout?;
    let mut root = None;
    for k in c.keys.keys() {
        let r = m.layouts.get(&k)?.elements?;
        if root.is_some_and(|x| x != r) {
            return None;
        }
        root = Some(r);
    }
    root
}

/// The effect summary of `op` on operands of types `args`. Total: an
/// ill-typed op gets the summary its opcode implies with wildcard regions.
pub fn effects(op: &Opcode, args: &[Type], m: &Module) -> Effects {
    use Opcode::*;
    let recv = args.first().and_then(|t| t.obj_info());
    let mut fx = Effects::PURE;
    match op {
        JsAdd | JsBinop(_) | JsUnop(_) | JsCompare(_) | JsToNumeric | JsGetProp(_)
        | JsSetProp(_) | JsGetElem | JsSetElem => return Effects::generic(FlagsEffect::Dynamic),
        JsGetName(_) => return Effects::generic(FlagsEffect::Bits(FlagBits::ALL)),
        Call | CallDirect | Construct | CallNative(_) => {
            return Effects::generic(FlagsEffect::Callee)
        }
        LoadField(name) => {
            // SLOTS is tested locally; the IC arm may GC and reports dirt.
            fx.reads = vec![field_region(recv, *name)];
            fx.may_gc = true;
            fx.may_throw = true;
            fx.kill = KillPattern::ALL;
            fx.flags = FlagsEffect::Dynamic;
        }
        StoreField(name) => {
            // Not a fence for `types` (§4.3): the value conforms by type.
            // The IC arm (add transition) reports dirt dynamically.
            fx.writes = vec![field_region(recv, *name)];
            fx.may_gc = true;
            fx.may_throw = true;
            fx.kill = KillPattern::ALL;
            fx.flags = FlagsEffect::Dynamic;
        }
        InitField(name) => {
            fx.writes = vec![field_region(recv, *name)];
            fx.may_gc = true;
            fx.flags = FlagsEffect::Bits(FlagBits::MUT_THIS);
        }
        PublishLayout => {
            fx.kill = KillPattern::of(KillSet::CONSTRUCTING);
        }
        NewObject(_) | NewArray => fx.may_gc = true,
        LoadElem => fx.reads = vec![Region::Elements(elements_root(recv, m))],
        StoreElem => {
            fx.writes = vec![Region::Elements(elements_root(recv, m))];
            fx.flags = FlagsEffect::Bits(FlagBits::MUT_OTHER);
        }
        LoadTa | StoreTa => {
            let r = match recv.map(|o| o.kind) {
                Some(ObjKind::TypedArray(k)) => Region::TypedArrayData(k),
                _ => Region::Unknown,
            };
            if *op == LoadTa {
                fx.reads = vec![r, Region::TypedArrayLength];
            } else {
                fx.reads = vec![Region::TypedArrayLength];
                fx.writes = vec![r];
                fx.flags = FlagsEffect::Bits(FlagBits::MUT_OTHER);
            }
        }
        LengthArray => fx.reads = vec![Region::ArrayLength(elements_root(recv, m))],
        LengthTa => fx.reads = vec![Region::TypedArrayLength],
        ElementsPtr => fx.reads = vec![Region::Elements(elements_root(recv, m))],
        // Reading a rope's chars flattens it, which allocates.
        StrCharCodeAt => fx.may_gc = true,
        LoadGName(b) => fx.reads = vec![Region::Global(*b)],
        StoreGName(b) => {
            fx.writes = vec![Region::Global(*b)];
            fx.kill = KillPattern::of(KillSet::FUSE);
            fx.flags = FlagsEffect::Bits(FlagBits::BIND);
        }
        EnvLoad(s) => fx.reads = vec![Region::Env(*s)],
        EnvStore(s) => {
            fx.writes = vec![Region::Env(*s)];
            fx.flags = FlagsEffect::Bits(FlagBits::MUT_OTHER);
        }
        _ => {}
    }
    fx
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::module::{FieldDef, Layout};

    fn m() -> Module {
        let mut m = Module::default();
        let x = m.intern_atom(&crate::ids::JsString::from("x"));
        let o = m.intern_atom(&crate::ids::JsString::from("o"));
        m.layouts.insert(
            LayoutKey::new(3),
            Layout {
                fields: vec![
                    FieldDef {
                        name: x,
                        claim: Type::val(TagSet::INT32),
                    },
                    FieldDef {
                        name: o,
                        claim: Type::Val(VSet::new(
                            TagSet::OBJECT,
                            NumInfo::TOP,
                            ObjInfo {
                                kind: ObjKind::Plain,
                                singleton: None,
                                layout: Some(LayoutClaim {
                                    keys: KeyRange::one(LayoutKey::new(4)),
                                    types: true,
                                    state: LayoutState::Published,
                                }),
                            },
                            StrInfo::TOP,
                        )),
                    },
                ],
                elements: None,
            },
        );
        m
    }

    fn k3(types: bool) -> Type {
        Type::Obj(ObjInfo {
            kind: ObjKind::Plain,
            singleton: None,
            layout: Some(LayoutClaim {
                keys: KeyRange::one(LayoutKey::new(3)),
                types,
                state: LayoutState::Published,
            }),
        })
    }

    #[test]
    fn every_opcode_has_a_shape() {
        // Terminators with successors, exiting terminators, and plain ops
        // are disjoint, and the kill site follows from the shape.
        let m = m();
        let ops = [
            Opcode::Jump,
            Opcode::GuardTags(TagSet::INT32),
            Opcode::Call,
            Opcode::JsGetName(AtomId::from_u32(0)),
            Opcode::StoreGName(BindingId::from_u32(0)),
            Opcode::Box,
        ];
        let sites: Vec<_> = ops
            .iter()
            .map(|op| op.kill_site(&effects(op, &[], &m)))
            .collect();
        assert_eq!(
            sites,
            [
                KillSite::None,
                KillSite::None,
                KillSite::DirtyEdge,
                KillSite::OkEdge,
                KillSite::Op,
                KillSite::None
            ]
        );
        assert!(Opcode::Return.is_terminator());
        assert!(!Opcode::Box.is_terminator());
    }

    #[test]
    fn unbox_requires_proof() {
        let m = m();
        let n = Type::val(TagSet::NUMBER);
        assert!(signature(&Opcode::Unbox(UnboxKind::I32), &[n], &m).is_err());
        assert!(signature(&Opcode::Unbox(UnboxKind::F64Num), &[n], &m).is_ok());
        let g = signature(&Opcode::GuardUnbox(UnboxKind::I32), &[n], &m).unwrap();
        assert_eq!(g.outputs, vec![Type::I32_TOP]);
        let b = signature(&Opcode::Box, &[Type::i32_range(0, 9)], &m).unwrap();
        let u = signature(&Opcode::Unbox(UnboxKind::I32), &b.results, &m).unwrap();
        assert_eq!(u.results, vec![Type::i32_range(0, 9)]);
    }

    #[test]
    fn arith_ranges() {
        let m = m();
        let s = signature(
            &Opcode::I32Ovf(ArithOp::Add),
            &[Type::i32_range(0, 10), Type::i32_range(-5, 5)],
            &m,
        )
        .unwrap();
        assert_eq!(s.outputs, vec![Type::i32_range(-5, 15)]);
        let big = Type::int_range(0, 1 << 52);
        assert!(signature(&Opcode::IntArith(ArithOp::Add), &[big, big], &m).is_ok());
        assert!(signature(&Opcode::IntArith(ArithOp::Mul), &[big, big], &m).is_err());
    }

    #[test]
    fn field_ops_follow_the_claim() {
        let m = m();
        let x = AtomId::from_u32(0);
        let o = AtomId::from_u32(1);
        let s = signature(&Opcode::LoadField(x), &[k3(true)], &m).unwrap();
        assert_eq!(s.outputs, vec![Type::val(TagSet::INT32)]);
        // Shallow: the child's layout claim is not carried.
        let s = signature(&Opcode::LoadField(o), &[k3(true)], &m).unwrap();
        assert_eq!(s.outputs[0].obj_info().unwrap().layout, None);
        assert_eq!(s.outputs[0].obj_info().unwrap().kind, ObjKind::Plain);
        // Without `types`, no load.
        assert!(signature(&Opcode::LoadField(x), &[k3(false)], &m).is_err());
        // Stores require conformance.
        assert!(signature(
            &Opcode::StoreField(x),
            &[k3(true), Type::val(TagSet::INT32)],
            &m
        )
        .is_ok());
        assert!(signature(
            &Opcode::StoreField(x),
            &[k3(true), Type::val(TagSet::NUMBER)],
            &m
        )
        .is_err());
    }
}
