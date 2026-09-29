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
    /// The TDZ sentinel (`JS_UNINITIALIZED_LEXICAL`), a magic value: what an
    /// uninitialized `let`/`const` binding holds.
    Uninitialized,
    /// Any valid value: an exit operand for a frame slot that is dead at
    /// the exit's pc (§5.1's liveness pruning). The lowering leaves such a
    /// slot as the frame already has it.
    Dead,
    /// The `this` placeholder of a `new` (`JS_IS_CONSTRUCTING`), a magic
    /// value.
    IsConstructing,
    /// An array literal's elision (`JS_ELEMENTS_HOLE`), a magic value.
    Hole,
}

/// `RtOp::PushEnv` kinds.
pub const ENV_LEXICAL: u32 = 0;
pub const ENV_CLASS_BODY: u32 = 1;
pub const ENV_VAR: u32 = 2;

/// `RtOp::Check` kinds.
pub const CHECK_OBJ_COERCIBLE: u32 = 0;
pub const CHECK_CLASS_HERITAGE: u32 = 1;
pub const CHECK_THIS: u32 = 2;
pub const CHECK_THIS_REINIT: u32 = 3;

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

/// The generic operations `js.rt` runs through their runtime helpers,
/// with their operands (all boxed).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum RtOp {
    /// `lhs instanceof rhs` -> boolean.
    Instanceof,
    /// `key in obj` -> boolean.
    In,
    /// `obj.hasOwnProperty(key)` (the `HasOwn` op), `key, obj` -> boolean.
    HasOwn,
    /// `delete obj.name` -> boolean (strict or not).
    DelProp(AtomId, bool),
    /// `delete obj[key]` -> boolean.
    DelElem(bool),
    /// `{}` -> object.
    NewObject,
    /// `new Array(len)` for a literal of `len` elements -> object.
    NewArray(u32),
    /// Define own property `name` of `obj` to `v`, with the attributes.
    InitProp(AtomId, u32),
    /// Define own element `key` of `obj` to `v`, with the attributes.
    /// Its attrs, and whether the store owes the array stamp's RANGES
    /// claim a clear (`ranges`: a claim applies and the value is not
    /// proven inside it).
    InitElem(u32, bool),
    /// ToPropertyKey (a string, a symbol or an int32) -> val.
    ToPropertyKey,
    /// The regexp literal the script's gcthing `index` names, cloned ->
    /// object.
    RegExp(u32),
    /// Define getter/setter `name` of `obj` to `f` (`kind`: 1 setter,
    /// 2 hidden).
    InitPropGetSet(AtomId, u32),
    /// Self-hosted intrinsic `name` (`GetIntrinsic`) -> value.
    Intrinsic(AtomId),
    /// Global `name` for `typeof` (`GetGName` before `Typeof`): an unbound
    /// name is undefined, not a ReferenceError -> value.
    GetNameTypeof(AtomId),
    /// For-in's property iterator over `v` (`Iter`) -> object.
    Iter,
    /// A check of `v` that throws or does nothing (`CheckObjCoercible`,
    /// `CheckClassHeritage`, `CheckThis`: `CHECK_*`).
    Check(u32),
    /// Name function `fun` by key `name` (`SetFunName`, the prefix kind).
    SetFunName(u32),
    /// The global `this` (`GlobalThis`) -> object.
    GlobalThis,
    /// The BigInt literal at the script's gcthing index (`BigInt`) -> value.
    BigInt(u32),
    /// Set `obj`'s prototype to `proto` (`MutateProto`, `__proto__:` in a
    /// literal).
    MutateProto,
    /// `#x in obj` style checks (`CheckPrivateField`: condition, kind),
    /// `obj, key` -> boolean.
    CheckPrivateField(u32, u32),
    /// Throw unless `v` is an object (`CheckIsObj`, the message kind).
    CheckIsObj(u32),
    /// Close iterator `it` (`CloseIter`, the completion kind): calls its
    /// `return`.
    CloseIter(u32),
    /// A spread call's argument array, or undefined when the spread value
    /// is not a packed array whose iteration is intact
    /// (`OptimizeSpreadCall`) -> value.
    OptimizeSpreadCall,
    /// `f(...arr)` / `new f(...arr)` (`SpreadCall`/`SpreadNew`: whether it
    /// constructs): `callee, this, arr, new.target` -> value.
    SpreadCall(u32),
    /// A scope's environment over the frame's (`PushLexicalEnv`,
    /// `PushClassBodyEnv`, `PushVarEnv`: `ENV_*`, the scope's pc) ->
    /// object; `env.set` makes it the frame's.
    PushEnv(u32, u32),
    /// A `with` environment over the frame's wrapping `v` (`EnterWith`,
    /// its pc) -> object.
    EnterWith(u32),
    /// A copy of the frame's block environment (`FreshenLexicalEnv`,
    /// `RecreateLexicalEnv` with 1: fresh bindings) -> object.
    FreshenEnv(u32),
    /// A name read through the frame's environment chain (`GetName`; 1 for
    /// `typeof`, where unbound is undefined) -> value.
    GetName(AtomId, u32),
    /// The environment a later `js.rt.setname` stores `name` into, from the
    /// frame's chain (`BindName`, `BindUnqualifiedName` with 1) -> object.
    BindName(AtomId, u32),
    /// `delete name` through the frame's chain (`DelName`) -> boolean.
    DelName(AtomId),
    /// The frame's variable environment (`BindVar`) -> object.
    BindVar,
    /// `env.name = v` for an environment `BindName` found (`SetName`,
    /// strict): `env, v`.
    SetName(AtomId, bool),
    /// A computed-key accessor in a literal or class (`InitElemGetter`
    /// and kin: bit 0 setter, bit 1 hidden): `obj, key, fn`.
    InitElemGetSet(u32),
    /// The home object's prototype (`SuperBase`: home) -> value.
    SuperBase,
    /// The constructor's parent (`SuperFun`: callee) -> value.
    SuperFun,
    /// `super.name` (`GetPropSuper`): `recv, base` -> value.
    GetPropSuper(AtomId),
    /// `super[key]` (`GetElemSuper`): `recv, key, base` -> value.
    GetElemSuper,
    /// `super.name = v` (`SetPropSuper`, strict): `recv, base, v` -> v.
    SetPropSuper(AtomId, bool),
    /// `super[key] = v` (`SetElemSuper`, strict): `recv, key, base, v` -> v.
    SetElemSuper(bool),
    /// Set method `f`'s home object (`InitHomeObject`): `f, home`.
    InitHomeObject,
    /// A class constructor with prototype `proto` (`FunWithProto`, the
    /// function gcthing), closing over the frame's environment -> object.
    FunWithProto(u32),
    /// A derived constructor's result (`CheckReturn`): `this, rval` ->
    /// value (throws for a non-object, non-undefined rval or an
    /// uninitialized `this`).
    CheckReturn,
    /// Register a `using` resource with the frame's environment
    /// (`AddDisposable`, the hint): `v, method, needs_closure`.
    AddDisposable(u32),
    /// The frame's environment's disposal list, taken
    /// (`TakeDisposeCapability`) -> value.
    TakeDisposeCapability,
    /// `SuppressedError(e, suppressed)` (`CreateSuppressedError`) -> object.
    CreateSuppressedError,
    /// `name` read from environment `env` a `BindName` found
    /// (`GetBoundName`): `env` -> value.
    GetBoundName(AtomId),
    /// An object with prototype `proto` (`ObjWithProto`) -> object.
    ObjWithProto,
    /// A fresh private name (`NewPrivateName`) -> symbol.
    NewPrivateName(AtomId),
    /// `import(spec, opts)` (`DynamicImport`) -> object.
    DynamicImport,
    /// A direct eval with spread arguments (`SpreadEval`, its pc):
    /// `callee, this, arr` -> value.
    SpreadEval(u32),
    /// A generator object for the frame's callee and environment
    /// (`Generator`) -> object.
    CreateGenerator,
    /// Mark generator `g` finished (`FinalYieldRval`): `g`.
    GenFinal,
    /// Raise a `throw`/`return` resumption (`CheckResumeKind` with a kind
    /// other than next; always fails): `v, g, kind`. A return stages `v`
    /// as the frame's rval.
    GenCheckResume,
    /// `AsyncAwait`/`AsyncResolve` (1 for resolve): `v, g` -> value.
    AsyncAwait(u32),
    /// `AsyncReject`: `reason, stack, g` -> value.
    AsyncReject,
    /// `CanSkipAwait`: `v` -> boolean.
    CanSkipAwait,
    /// `MaybeExtractAwaitValue`: `v, can_skip` -> value.
    MaybeExtractAwait,
    /// Resume generator `g` with `v` and resume kind `k` (`Resume`) -> value.
    Resume,
    /// `ToString` of v -> string.
    ToString,
    /// Well-known symbol `code` (`JSOp::Symbol`) -> symbol.
    Symbol(u32),
    /// Builtin object `kind` (`JSOp::BuiltinObject`) -> object.
    BuiltinObject(u32),
}

impl RtOp {
    /// The op with its atoms renamed by `f` (an inlined callee's, into
    /// the caller's table). Exhaustive, with no wildcard: a new variant
    /// carrying an atom must say how it maps.
    pub fn map_atoms(self, f: impl Fn(AtomId) -> AtomId) -> RtOp {
        use RtOp::*;
        match self {
            DelProp(a, s) => DelProp(f(a), s),
            InitProp(a, t) => InitProp(f(a), t),
            InitPropGetSet(a, k) => InitPropGetSet(f(a), k),
            Intrinsic(a) => Intrinsic(f(a)),
            GetNameTypeof(a) => GetNameTypeof(f(a)),
            GetName(a, t) => GetName(f(a), t),
            BindName(a, k) => BindName(f(a), k),
            DelName(a) => DelName(f(a)),
            SetName(a, s) => SetName(f(a), s),
            GetPropSuper(a) => GetPropSuper(f(a)),
            SetPropSuper(a, s) => SetPropSuper(f(a), s),
            GetBoundName(a) => GetBoundName(f(a)),
            NewPrivateName(a) => NewPrivateName(f(a)),
            op @ (Instanceof | In | HasOwn | DelElem(_) | NewObject | NewArray(_) | InitElem(..)
            | ToPropertyKey | RegExp(_) | Iter | Check(_) | SetFunName(_) | GlobalThis | BigInt(_)
            | MutateProto | CheckPrivateField(..) | CheckIsObj(_) | CloseIter(_) | OptimizeSpreadCall
            | SpreadCall(_) | PushEnv(..) | EnterWith(_) | FreshenEnv(_) | BindVar | InitElemGetSet(_)
            | SuperBase | SuperFun | GetElemSuper | SetElemSuper(_) | InitHomeObject | FunWithProto(_)
            | CheckReturn | AddDisposable(_) | TakeDisposeCapability | CreateSuppressedError
            | ObjWithProto | DynamicImport | SpreadEval(_) | CreateGenerator | GenFinal | GenCheckResume
            | AsyncAwait(_) | AsyncReject | CanSkipAwait | MaybeExtractAwait | Resume | ToString | Symbol(_)
            | BuiltinObject(_)) => op,
        }
    }
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
        slots: bool,
    },
    /// An object under construction for layout `key` (MIR.md §2.3): its
    /// word carries the CONSTRUCTING sentinel with `key`'s early key, and
    /// SLOTS (and TYPES if `types`), and it has exactly `n` slots, so
    /// `key`'s first `n` fields (`constructing(n)`).
    GuardCtor {
        key: LayoutKey,
        n: u32,
        types: bool,
    },
    GuardSingleton(SnapObj),
    GuardScript(ScriptId),
    /// An f64 that is exactly an int32 (not -0) becomes an `I32`.
    F64ToIntExact,
    /// An `int` known to be int32 (T: fails outside int32's range).
    IntToI32,
    CheckFuse(FuseId),
    /// The binding's slot is resolved against the global object's live
    /// shape (and, with `write`, is a writable data property).
    CheckBinding(BindingId, bool),
    CheckNative(NativeId),

    // Control.
    Jump,
    Br,
    /// Dense switch over `0..n`, plus a default.
    Switch(u32),
    Return,
    /// Operands: `this`, `nargs` args, `nlocals` locals, the rval, then
    /// the operand stack (the rest). All `Val(⊤)`.
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
    /// Suspend the generator at a yield (`InitialYield`, `Yield`, `Await`
    /// at `pc`, resume index `index`): an exit's operands (the frame at
    /// `pc`, whose stack ends with the generator, below it the yielded
    /// value unless `initial`). The lowering writes the frame, saves it
    /// into the generator (baseline's `gen_suspend`) and returns the
    /// yielded value (the generator for `initial`). A resume enters the
    /// function's `Resume` root for `index`.
    GenSuspend {
        pc: Pc,
        index: u32,
        nargs: u32,
        nlocals: u32,
        initial: bool,
    },
    /// Whether `v` is the generator-closing magic (`IsGenClosing`) -> bool.
    IsGenClosing,
    /// An exit from an inlined callee's code (§5.5), with an `exit`'s
    /// operands for the callee's frame: finish the callee in its baseline
    /// body from `pc` (with its exception pending if `throw`), and take
    /// `ok` with its result or `err` with its exception.
    ExitInline {
        pc: Pc,
        nargs: u32,
        nlocals: u32,
        throw: bool,
    },
    /// Write the inlined callee's frame (§5.5) from `callee, this, args`
    /// (the callee's formals, padded), its other slots as its prologue
    /// would. The instruction's frame is the callee's.
    InlineEnter,
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
    /// `typeof v == type` (or `!=`), the operand byte of `JSOp::TypeofEq`
    /// (`js::TypeofEqOperand`): a leaf.
    JsTypeofEq(u8),
    /// `v === c` for the constant the operand of `JSOp::StrictConstantEq`
    /// encodes (`js::ConstantCompareOperand`): a leaf.
    JsConstantStrictEq(u16),
    /// Formal `n` of the frame's mapped `arguments` object (which the
    /// entry made): `ArgumentsObject::arg`, a leaf.
    ArgsMapped(u32),
    /// Set formal `n` of the frame's mapped `arguments` object: a leaf.
    ArgsMappedSet(u32),
    JsToBool,
    JsToNumeric,
    JsGetProp(AtomId),
    /// Strict-mode (`true`) or sloppy assignment.
    JsSetProp(AtomId, bool),
    JsGetElem,
    /// Strictness, and the RANGES duty (as `InitElem`'s).
    JsSetElem(bool, bool),
    JsGetName(AtomId),
    /// Sloppy-mode `this` that is not an object: the global `this` for
    /// null/undefined, a wrapper object for a primitive.
    JsBoxThis,
    /// The binding object for an unqualified global assignment
    /// (`BindUnqualifiedGName`).
    JsBindGName(AtomId),
    /// `env.name = v` for a global or name assignment (`SetGName`), strict
    /// or sloppy.
    JsSetName(AtomId, bool),
    /// A generic operation through its runtime helper (see [`RtOp`]).
    JsRt(RtOp),
    /// The function's (unmapped) arguments object: the frame's cached
    /// one, else a new one, cached. Only in the function's own frame.
    ArgsObject,
    /// A rest-parameter array of the actuals past the first `n`.
    RestArray(u32),
    /// The actual argument count, an i32.
    ArgsLength,
    /// The frame's `new.target` (the op's frame: an inlined construct's
    /// frame holds its own) -> value.
    FrameNewTarget,
    /// The frame's callee (`Callee`) -> value.
    FrameCallee,
    /// For-in: the iterator's next property name, or the NO_ITER magic
    /// when it is exhausted (`MoreIter`; advances the iterator).
    IterMore,
    /// Whether a value is the NO_ITER magic (`IsNoIter`) -> bool.
    IterIsDone,
    /// For-in: close the iterator (`EndIter`).
    IterEnd,
    /// Whether `v` iterates as a packed array with the iteration protocol
    /// intact (`OptimizeGetIterator`) -> bool.
    IterOptimizable,
    /// Actual argument `args[0]` (an i32 index below the count).
    ActualArg,
    /// Actual argument `k`, or undefined if there are not that many.
    ActualArgOr(u32),
    /// Whether boxed `args[0]` is the builtin in cell `k` (the runtime's
    /// pristine-builtin cells, e.g. `Function.prototype.apply`).
    JsIsBuiltin(u32),
    /// `target.apply(this, arguments)` forwarding the frame's own actuals
    /// (operands `apply`, `target`, `this`), through the runtime.
    ApplyFwd,
    /// `throw args[0]`: the only successor is `err`.
    JsThrow,
    /// Write `args[0]` (a `Val`, or an i32, f64 or bool, stored as the
    /// Value it is) to baseline frame slot `k` (0 `this`, then the
    /// formals, the locals, the rval): the write-through that keeps the
    /// frame's copy of every formal, local and rval equal to the slot's
    /// value, so exits need not carry them (§5.1).
    FrameStore(u32),
    /// A closure of the script's inner function `index` (a gcthing index)
    /// over environment `args[0]` (`Lambda`).
    JsLambda(u32),

    // Objects.
    LoadField(AtomId),
    StoreField(AtomId),
    InitField(AtomId),
    PublishLayout,
    NewObject(LayoutKey),
    NewArray,
    LoadElem,
    /// The RANGES duty (as `InitElem`'s).
    StoreElem(bool),
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
    /// The callee of the function environment `hops` links up the frame's
    /// chain (`EnvCallee`, `super` in an arrow or eval) -> object.
    EnvCallee(u32),
    /// The script's object gcthing `index` (`Object`, `CallSiteObj`: a
    /// template or singleton, not a copy) -> object.
    ObjectLit(u32),
    /// Make environment `e` (boxed) the frame's current one: a scope's
    /// entry (write-through, as baseline's frame keeps it).
    EnvSet,
    /// Make the frame's current environment's enclosing one current: a
    /// scope's exit (`PopLexicalEnv`, `LeaveWith`).
    EnvPop,
    EnvParent,
    EnvLoad(EnvSlot),
    EnvStore(EnvSlot),

    // Calls. Operands: callee (or new.target pair), `this`, args.
    Call,
    /// A call of an iterator method (`CallIter`): `call`, whose uncallable
    /// callee throws the iterator protocol's error.
    CallIter,
    /// A direct `eval` (`Eval`/`StrictEval` at pc): `call`'s operands; the
    /// code runs in the frame's environment.
    CallEval(u32),
    CallDirect,
    /// `new`: operands callee, `this` (the IS_CONSTRUCTING magic), args,
    /// new.target. The site's sized-allocation slot count and early stamp
    /// word (`bbv::construct_nslots`/`construct_alloc_word`).
    Construct(u32, u32),
    /// The `this` of a construct (`callee, new.target`): a fresh object
    /// sized `nslots` and seeded with the alloc word, as a direct construct
    /// makes it (the site's construct cell, else `create_this`).
    CreateThis(u32, u32),
    /// Whether function `f` is a constructor (its flags): an arrow
    /// function or a method is not.
    FnIsCtor,
    /// Whether object `o` emulates `undefined` (`document.all`): what
    /// loose equality with null or undefined asks of an object.
    ObjEmulatesUndef,
    /// Advance boxed `v`'s prefix-stamped object to its full layout key
    /// when its bits and shape allow (the module's restamp descriptor
    /// `i`): the two-phase restamp at an init delegate's or fill script's
    /// returns, or after a fill sequence's last add.
    Restamp(u32),
    /// Write class word `w` into a freshly allocated object literal or
    /// array (`lit_stamps_in`, `array_stamp_in`): nothing can have read
    /// the old word, and the claims it seeds hold vacuously.
    StampFresh(u32),
    /// A layout constructor's first stamp of its completed `this`
    /// (layout, field count, kept bits): a no-op unless `this` is an
    /// object of this constructor still under construction.
    CtorStamp(u32, u32, u32),
    /// `publish_layout` at its earliest point (MIR.md §2.3): the same
    /// stamp before a call made while `this` may still be under
    /// construction (`ctor_publish`), only for an object carrying this
    /// constructor's own early key (an unkeyed one waits for the return).
    CtorPublish(u32, u32, u32),
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
            | GuardCtor { .. }
            | GuardSingleton(_)
            | GuardScript(_)
            | F64ToIntExact
            | IntToI32
            | CheckFuse(_)
            | CheckBinding(..)
            | CheckNative(_)
            | I32Ovf(_)
            | LoadElem
            | StoreElem(_)
            | LoadTa
            | StoreTa
            | StrCharCodeAt
            | InitField(_) => OK_FAIL.to_vec(),
            JsAdd | JsBinop(_) | JsUnop(_) | JsCompare(_) | JsToNumeric | JsGetProp(_)
            | JsSetProp(..) | JsGetElem | JsSetElem(..) | JsBoxThis | JsBindGName(_)
            | JsSetName(..) | LoadField(_) | StoreField(_) | Call | CallIter | CallEval(_) | CallDirect | Construct(..)
            | CallNative(_) | JsGetName(_) | CreateThis(..) => CLEAN_DIRTY_ERR.to_vec(),
            // Clean if the callee's baseline rest demoted nothing.
            ExitInline { .. } => CLEAN_DIRTY_ERR.to_vec(),
            // Allocations: no kill, so no effect report.
            JsLambda(_) => OK_ERR.to_vec(),
            JsRt(_) | ApplyFwd => CLEAN_DIRTY_ERR.to_vec(),
            ArgsObject | RestArray(_) => OK_ERR.to_vec(),
            JsThrow => vec![SuccRole::Err],
            _ => vec![],
        }
    }

    pub fn is_terminator(&self) -> bool {
        matches!(
            self,
            Opcode::Return
                | Opcode::Exit { .. }
                | Opcode::ExitThrow { .. }
                | Opcode::GenSuspend { .. }
                | Opcode::Unreachable
        ) || !self.roles().is_empty()
    }

    /// The frame-state split of the operands of an exit, a throw or an
    /// inline exit.
    pub fn frame_operands(&self) -> Option<(Pc, u32, u32)> {
        match *self {
            Opcode::ExitInline { pc, nargs, nlocals, .. } | Opcode::GenSuspend { pc, nargs, nlocals, .. } => {
                Some((pc, nargs, nlocals))
            }
            _ => self.exit_shape(),
        }
    }

    /// The frame-state split of an exit's operands, if this is one: an
    /// op that leaves the function for its own baseline body.
    pub fn exit_shape(&self) -> Option<(Pc, u32, u32)> {
        match *self {
            Opcode::Exit { pc, nargs, nlocals } | Opcode::ExitThrow { pc, nargs, nlocals } => {
                Some((pc, nargs, nlocals))
            }
            _ => None,
        }
    }
}

/// An exit's (or onramp root's) operands split into the frame's parts.
#[derive(Clone, Copy, Debug)]
pub struct FrameParts<'a, T> {
    pub this: &'a T,
    pub args: &'a [T],
    pub locals: &'a [T],
    pub rval: &'a T,
    pub stack: &'a [T],
}

/// Split `ops` (`this`, args, locals, rval, stack) by `nargs` and
/// `nlocals`; `None` if there are too few.
pub fn frame_parts<T>(ops: &[T], nargs: u32, nlocals: u32) -> Option<FrameParts<'_, T>> {
    let (na, nl) = (nargs as usize, nlocals as usize);
    if ops.len() < 2 + na + nl {
        return None;
    }
    Some(FrameParts {
        this: &ops[0],
        args: &ops[1..1 + na],
        locals: &ops[1 + na..1 + na + nl],
        rval: &ops[1 + na + nl],
        stack: &ops[2 + na + nl..],
    })
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
        ConstVal::Uninitialized | ConstVal::IsConstructing | ConstVal::Hole => Type::val(TagSet::MAGIC),
        ConstVal::Dead => Type::VAL_TOP,
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
        // A predicted field (at its slot), or a typed field with no slot
        // prediction (an access finds it through an IC).
        match layout.field(name) {
            Some((slot, f)) => {
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
            None => {
                let f = layout
                    .named_field(name)
                    .ok_or_else(|| format!("{what}: layout L{k} has no field {}", m.atoms[name]))?;
                want(c.state == LayoutState::Published, || {
                    format!("{what}: slotless field {} under construction", m.atoms[name])
                })?;
                claims.push(f.claim);
            }
        }
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
        GuardLayout { keys, types, slots } => {
            arity(args, 1)?;
            let o = obj(&args[0], "guard.layout")?;
            let new = LayoutClaim {
                keys: *keys,
                types: *types,
                slots: *slots,
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
        GuardCtor { key, n, types } => {
            arity(args, 1)?;
            let o = obj(&args[0], "guard.ctor")?;
            Sig::output(Type::Obj(ObjInfo {
                layout: Some(LayoutClaim {
                    keys: KeyRange::one(*key),
                    types: *types,
                    slots: true,
                    state: LayoutState::Constructing(*n),
                }),
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
        IntToI32 => {
            arity(args, 1)?;
            match args[0] {
                Type::Int(r) => Sig::output(Type::I32(clamp_range(r.lo.into(), r.hi.into(), I32_MIN, I32_MAX))),
                _ => return Err("int.to_i32: expected an int".into()),
            }
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
        CheckBinding(b, _) => {
            arity(args, 0)?;
            want(m.bindings.contains(*b), || {
                format!("check.binding: {b} is not in the module")
            })?;
            Sig::output(Type::Fact(FactKind::Binding(*b)))
        }
        // The callee is native `n` (its pristine JSNative).
        CheckNative(n) => {
            arity(args, 1)?;
            val(&args[0], "check.native callee")?;
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
        InlineEnter => {
            want(args.len() >= 2, || "inline.enter: expected callee and this".into())?;
            Sig::none()
        }
        ExitInline { nargs, nlocals, .. } => {
            want(frame_parts(args, *nargs, *nlocals).is_some(), || {
                "exit.inline: fewer operands than this + args + locals + rval".into()
            })?;
            for (i, t) in args.iter().enumerate() {
                if !matches!(t, Type::Val(_)) {
                    box_type(t).map_err(|e| format!("exit.inline operand {i}: {e}"))?;
                }
            }
            Sig::output(Type::VAL_TOP)
        }
        Exit { nargs, nlocals, .. } | ExitThrow { nargs, nlocals, .. } | GenSuspend { nargs, nlocals, .. } => {
            want(frame_parts(args, *nargs, *nlocals).is_some(), || {
                "exit: fewer operands than this + args + locals + rval".into()
            })?;
            // Any boxable representation: the lowering boxes each operand
            // once per exit shape (§5.1), not once per exit.
            for (i, t) in args.iter().enumerate() {
                if !matches!(t, Type::Val(_)) {
                    box_type(t).map_err(|e| format!("exit operand {i}: {e}"))?;
                }
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
            // No string or object operand (whose ToPrimitive might give a
            // string): no concatenation.
            let strish = TagSet::STRING.union(TagSet::OBJECT);
            if free_of(&args[0], strish) && free_of(&args[1], strish) {
                Sig::output(Type::val(if no_bigint(args) { TagSet::NUMBER } else { number_or_bigint }))
            } else {
                Sig::output(Type::val(number_or_bigint.union(TagSet::STRING)))
            }
        }
        JsBinop(b) => {
            arity(args, 2)?;
            val(&args[0], "js.binop")?;
            val(&args[1], "js.binop")?;
            let nb = no_bigint(args);
            Sig::output(Type::val(match b {
                self::JsBinop::Ursh => TagSet::NUMBER,
                self::JsBinop::BitAnd
                | self::JsBinop::BitOr
                | self::JsBinop::BitXor
                | self::JsBinop::Lsh
                | self::JsBinop::Rsh if nb => TagSet::INT32,
                self::JsBinop::BitAnd
                | self::JsBinop::BitOr
                | self::JsBinop::BitXor
                | self::JsBinop::Lsh
                | self::JsBinop::Rsh => TagSet::prims(PRIM_INT32 | PRIM_BIGINT),
                _ if nb => TagSet::NUMBER,
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
            Sig::result(Type::val(TagSet::STRING))
        }
        JsRt(r) => {
            let (n, out) = match r {
                RtOp::Instanceof | RtOp::In | RtOp::HasOwn | RtOp::DelElem(_) => {
                    (2, Some(Type::val(TagSet::BOOLEAN)))
                }
                RtOp::DelProp(..) => (1, Some(Type::val(TagSet::BOOLEAN))),
                RtOp::NewObject | RtOp::NewArray(_) => (0, Some(Type::val(TagSet::OBJECT))),
                RtOp::InitProp(..) => (2, None),
                RtOp::InitElem(..) => (3, None),
                RtOp::ToPropertyKey => (1, Some(Type::VAL_TOP)),
                RtOp::RegExp(_) => (0, Some(Type::val(TagSet::OBJECT))),
                RtOp::InitPropGetSet(..) => (2, None),
                RtOp::Intrinsic(_) | RtOp::GetNameTypeof(_) => (0, Some(Type::VAL_TOP)),
                RtOp::Iter => (1, Some(Type::val(TagSet::OBJECT))),
                RtOp::Check(_) => (1, None),
                RtOp::SetFunName(_) | RtOp::MutateProto => (2, None),
                RtOp::GlobalThis => (0, Some(Type::val(TagSet::OBJECT))),
                RtOp::BigInt(_) => (0, Some(Type::VAL_TOP)),
                RtOp::CheckPrivateField(..) => (2, Some(Type::val(TagSet::BOOLEAN))),
                RtOp::CheckIsObj(_) | RtOp::CloseIter(_) => (1, None),
                RtOp::OptimizeSpreadCall => (1, Some(Type::VAL_TOP)),
                RtOp::PushEnv(..) | RtOp::FreshenEnv(_) | RtOp::BindName(..) | RtOp::BindVar => {
                    (0, Some(Type::val(TagSet::OBJECT)))
                }
                RtOp::EnterWith(_) => (1, Some(Type::val(TagSet::OBJECT))),
                RtOp::GetName(..) => (0, Some(Type::VAL_TOP)),
                RtOp::DelName(_) => (0, Some(Type::val(TagSet::BOOLEAN))),
                RtOp::SetName(..) => (2, None),
                RtOp::InitElemGetSet(_) => (3, None),
                RtOp::SuperBase | RtOp::SuperFun => (1, Some(Type::VAL_TOP)),
                RtOp::GetPropSuper(_) | RtOp::CheckReturn => (2, Some(Type::VAL_TOP)),
                RtOp::GetElemSuper | RtOp::SetPropSuper(..) => (3, Some(Type::VAL_TOP)),
                RtOp::SetElemSuper(_) => (4, Some(Type::VAL_TOP)),
                RtOp::InitHomeObject => (2, None),
                RtOp::AddDisposable(_) => (3, None),
                RtOp::TakeDisposeCapability => (0, Some(Type::VAL_TOP)),
                RtOp::CreateSuppressedError | RtOp::DynamicImport => (2, Some(Type::val(TagSet::OBJECT))),
                RtOp::GetBoundName(_) => (1, Some(Type::VAL_TOP)),
                RtOp::ObjWithProto => (1, Some(Type::val(TagSet::OBJECT))),
                RtOp::NewPrivateName(_) => (0, Some(Type::val(TagSet::prims(crate::opsem::PRIM_SYMBOL)))),
                RtOp::SpreadEval(_) => (3, Some(Type::VAL_TOP)),
                RtOp::CreateGenerator => (0, Some(Type::val(TagSet::OBJECT))),
                RtOp::GenFinal => (1, None),
                RtOp::GenCheckResume => (3, None),
                RtOp::AsyncAwait(_) | RtOp::MaybeExtractAwait => (2, Some(Type::VAL_TOP)),
                RtOp::AsyncReject | RtOp::Resume => (3, Some(Type::VAL_TOP)),
                RtOp::CanSkipAwait => (1, Some(Type::val(TagSet::BOOLEAN))),
                RtOp::FunWithProto(_) => (1, Some(Type::val(TagSet::OBJECT))),
                RtOp::SpreadCall(0) => (4, Some(Type::VAL_TOP)),
                RtOp::SpreadCall(_) => (4, Some(Type::val(TagSet::OBJECT))),
                RtOp::ToString => (1, Some(Type::val(TagSet::STRING))),
                RtOp::Symbol(_) => (0, Some(Type::val(TagSet::prims(crate::opsem::PRIM_SYMBOL)))),
                RtOp::BuiltinObject(_) => (0, Some(Type::val(TagSet::OBJECT))),
            };
            arity(args, n)?;
            for t in args {
                val(t, "js.rt operand")?;
            }
            match out {
                Some(t) => Sig::output(t),
                None => Sig::none(),
            }
        }
        JsThrow => {
            arity(args, 1)?;
            val(&args[0], "js.throw")?;
            Sig::none()
        }
        ArgsObject | RestArray(_) => {
            arity(args, 0)?;
            Sig::output(Type::val(TagSet::OBJECT))
        }
        ArgsLength => {
            arity(args, 0)?;
            Sig::result(Type::I32(IRange::new(0, i64::from(i32::MAX))))
        }
        FrameNewTarget => {
            arity(args, 0)?;
            Sig::result(Type::VAL_TOP)
        }
        FrameCallee => {
            arity(args, 0)?;
            Sig::result(Type::val(TagSet::OBJECT))
        }
        IterMore => {
            arity(args, 1)?;
            val(&args[0], "iter.more")?;
            Sig::result(Type::VAL_TOP)
        }
        IsGenClosing => {
            arity(args, 1)?;
            val(&args[0], "is_gen_closing")?;
            Sig::result(Type::Bool)
        }
        IterIsDone => {
            arity(args, 1)?;
            val(&args[0], "iter.done")?;
            Sig::result(Type::Bool)
        }
        IterEnd => {
            arity(args, 1)?;
            val(&args[0], "iter.end")?;
            Sig::none()
        }
        IterOptimizable => {
            arity(args, 1)?;
            val(&args[0], "iter.optimizable")?;
            Sig::result(Type::Bool)
        }
        ActualArg => {
            arity(args, 1)?;
            i32r(&args[0], "args.actual")?;
            Sig::result(Type::VAL_TOP)
        }
        ActualArgOr(_) => {
            arity(args, 0)?;
            Sig::result(Type::VAL_TOP)
        }
        JsIsBuiltin(_) => {
            arity(args, 1)?;
            val(&args[0], "js.is_builtin")?;
            Sig::result(Type::Bool)
        }
        ApplyFwd => {
            arity(args, 3)?;
            for t in args {
                val(t, "js.apply_fwd operand")?;
            }
            Sig::output(Type::VAL_TOP)
        }
        JsToBool => {
            arity(args, 1)?;
            val(&args[0], "js.tobool")?;
            Sig::result(Type::Bool)
        }
        JsTypeofEq(_) | JsConstantStrictEq(_) => {
            arity(args, 1)?;
            val(&args[0], "js leaf compare")?;
            Sig::result(Type::Bool)
        }
        ArgsMapped(_) => {
            arity(args, 0)?;
            Sig::result(Type::VAL_TOP)
        }
        ArgsMappedSet(_) => {
            arity(args, 1)?;
            val(&args[0], "args.mapped_set")?;
            Sig::none()
        }
        JsToNumeric => {
            arity(args, 1)?;
            val(&args[0], "js.tonumeric")?;
            Sig::output(Type::val(number_or_bigint))
        }
        JsGetProp(_) | JsGetElem | JsSetProp(..) | JsSetElem(..) => {
            let n = match op {
                JsGetProp(_) => 1,
                JsGetElem | JsSetProp(..) => 2,
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
        JsBoxThis => {
            arity(args, 1)?;
            val(&args[0], "js.box_this")?;
            Sig::output(Type::val(TagSet::OBJECT))
        }
        JsBindGName(_) => {
            arity(args, 0)?;
            Sig::output(Type::val(TagSet::OBJECT))
        }
        FrameStore(_) => {
            arity(args, 1)?;
            want(
                matches!(args[0], Type::Val(_) | Type::I32(_) | Type::F64(_) | Type::Bool | Type::Obj(_)),
                || "frame.store: expected a val, i32, f64, bool or obj".into(),
            )?;
            Sig::none()
        }
        CreateThis(..) => {
            arity(args, 2)?;
            val(&args[0], "create_this callee")?;
            val(&args[1], "create_this new.target")?;
            Sig::output(Type::val(TagSet::OBJECT))
        }
        FnIsCtor => {
            arity(args, 1)?;
            obj(&args[0], "fn.is_ctor")?;
            Sig::result(Type::Bool)
        }
        ObjEmulatesUndef => {
            arity(args, 1)?;
            obj(&args[0], "obj.emulates_undef")?;
            Sig::result(Type::Bool)
        }
        Restamp(_) => {
            arity(args, 1)?;
            val(&args[0], "restamp")?;
            Sig::none()
        }
        StampFresh(_) => {
            arity(args, 1)?;
            val(&args[0], "stamp.fresh")?;
            Sig::none()
        }
        CtorStamp(..) | CtorPublish(..) => {
            arity(args, 1)?;
            val(&args[0], "ctor.stamp")?;
            Sig::none()
        }
        JsLambda(_) => {
            arity(args, 1)?;
            want_kind(&obj(&args[0], "js.lambda")?, ObjKind::Env, "js.lambda")?;
            Sig::output(Type::val(TagSet::OBJECT))
        }
        JsSetName(..) => {
            arity(args, 2)?;
            val(&args[0], "js.setname env")?;
            val(&args[1], "js.setname value")?;
            Sig::none()
        }

        LoadField(name) => {
            arity(args, 1)?;
            let o = obj(&args[0], "load_field")?;
            let (c, claims) = field_claims(&o, *name, m, "load_field")?;
            // `types` backs a field's claim: without it (the identity
            // alone) the value is any `Val`, to be guarded at the def.
            if !c.types {
                return Ok(Sig::output(Type::VAL_TOP));
            }
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
            // Without `types` there is no claim to keep: any value, and
            // the store's own check maintains the bits (§4.3).
            if !c.types {
                val(&args[1], "store_field value")?;
                return Ok(Sig::none());
            }
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
                .ok_or("init_field: every field is already initialized")?
                .as_ref()
                .ok_or("init_field: the next field is not described")?;
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
                    slots: true,
                    state: LayoutState::Constructing(0),
                }),
            }))
        }
        NewArray => {
            arity(args, 1)?;
            i32r(&args[0], "new_array")?;
            Sig::result(Type::Obj(ObjInfo::kind(ObjKind::Array)))
        }
        LoadElem | StoreElem(_) => {
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
            // A wasm32 engine's typed arrays are shorter than 2^31.
            Sig::result(Type::I32(IRange::new(0, I32_MAX)))
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
        EnvCallee(_) | ObjectLit(_) => {
            arity(args, 0)?;
            Sig::result(Type::val(TagSet::OBJECT))
        }
        EnvSet => {
            arity(args, 1)?;
            val(&args[0], "env.set")?;
            Sig::none()
        }
        EnvPop => {
            arity(args, 0)?;
            Sig::none()
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

        Call | CallIter | CallEval(_) | Construct(..) => {
            want(args.len() >= 2, || "call: expected callee and this".into())?;
            for t in args {
                val(t, "call operand")?;
            }
            Sig::output(if matches!(op, Construct(..)) {
                Type::val(TagSet::OBJECT)
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
/// Whether value type `t` has none of `tags`.
fn free_of(t: &Type, tags: TagSet) -> bool {
    match t {
        Type::Val(v) => v.tags.intersect(tags).is_empty(),
        _ => false,
    }
}

/// Whether a numeric operator on `args` cannot yield a BigInt: that needs
/// both operands BigInt after ToNumeric, and one that is no BigInt and no
/// object (whose valueOf might give one) makes the result a Number, or a
/// TypeError for mixing.
fn no_bigint(args: &[Type]) -> bool {
    let big = TagSet::prims(PRIM_BIGINT).union(TagSet::OBJECT);
    args.iter().any(|t| free_of(t, big))
}

pub fn effects(op: &Opcode, args: &[Type], m: &Module) -> Effects {
    use Opcode::*;
    let recv = args.first().and_then(|t| t.obj_info());
    let mut fx = Effects::PURE;
    match op {
        JsAdd | JsBinop(_) | JsUnop(_) | JsCompare(_) | JsToNumeric | JsGetProp(_)
        | JsSetProp(..) | JsGetElem | JsSetElem(..) | JsBoxThis | JsBindGName(_) | JsSetName(..) => {
            return Effects::generic(FlagsEffect::Dynamic)
        }
        JsGetName(_) => return Effects::generic(FlagsEffect::Dynamic),
        JsRt(_) => return Effects::generic(FlagsEffect::Dynamic),
        ApplyFwd => return Effects::generic(FlagsEffect::Callee),
        // Allocations: they run no JS and change no class word (a GC moves
        // objects but keeps their words), so they kill nothing.
        ArgsObject | RestArray(_) | JsLambda(_) => {
            fx.may_gc = true;
            fx.may_throw = true;
        }
        JsThrow => return Effects::generic(FlagsEffect::Bits(FlagBits::ALL)),
        // `.prototype` of the callee: generic, reported.
        CreateThis(..) => return Effects::generic(FlagsEffect::Dynamic),
        // Writes the class word of an object no guard can have proven.
        CtorStamp(..) | CtorPublish(..) => {
            fx.writes = vec![Region::Unknown];
            fx.flags = FlagsEffect::Bits(FlagBits::MUT_THIS);
        }
        // The object is fresh: no fact about its word exists yet.
        StampFresh(_) => fx.flags = FlagsEffect::Bits(FlagBits::MUT_THIS),
        // Advances a prefix key to its full one: slots stay put, so a
        // fact about the prefix stays true; a prefix-key guard just misses.
        Restamp(_) => {
            fx.writes = vec![Region::Unknown];
            fx.flags = FlagsEffect::Bits(FlagBits::MUT_OTHER);
        }
        // The rest of the callee, in baseline: anything.
        ExitInline { .. } => return Effects::generic(FlagsEffect::Dynamic),
        Call | CallIter | CallEval(_) | CallDirect | Construct(..) | CallNative(_) => {
            return Effects::generic(FlagsEffect::Callee)
        }
        // The atom's string: its lowering calls a may-GC helper.
        ConstStr(_) => fx.may_gc = true,
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
        ArgsMapped(_) => fx.reads = vec![Region::Unknown],
        ArgsMappedSet(_) => {
            fx.writes = vec![Region::Unknown];
            fx.flags = FlagsEffect::Bits(FlagBits::MUT_OTHER);
        }
        StoreElem(_) => {
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
        // The iterator's own state, which nothing else reads.
        IterMore | IterEnd => {
            fx.reads = vec![Region::Unknown];
            fx.writes = vec![Region::Unknown];
        }
        // The value's shape and the realm's iteration fuses.
        IterOptimizable => fx.reads = vec![Region::Unknown],
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
        // The frame's current environment, which a scope's entry and exit
        // replace.
        EnvCurrent | EnvCallee(_) => fx.reads = vec![Region::FrameEnv],
        EnvSet => fx.writes = vec![Region::FrameEnv],
        EnvPop => {
            fx.reads = vec![Region::FrameEnv];
            fx.writes = vec![Region::FrameEnv];
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
                    Some(FieldDef {
                        name: x,
                        claim: Type::val(TagSet::INT32),
                    }),
                    Some(FieldDef {
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
                                    slots: true,
                                    state: LayoutState::Published,
                                }),
                            },
                            StrInfo::TOP,
                        )),
                    }),
                ],
                named: vec![],
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
                slots: true,
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
                KillSite::DirtyEdge,
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
    fn magic_is_boundary_only() {
        // `Val(⊤)` includes magic values (a frame slot can hold one):
        // nothing unboxes it, and a tag guard without `magic` removes it.
        let m = m();
        assert!(TagSet::MAGIC.subset_of(VSet::TOP.tags));
        let js = Type::val(TagSet::JS);
        assert!(is_subtype(&js, &Type::VAL_TOP));
        assert!(!is_subtype(&Type::VAL_TOP, &js));
        let g = signature(&Opcode::GuardTags(TagSet::JS), &[Type::VAL_TOP], &m).unwrap();
        assert_eq!(g.outputs, vec![js]);
        for k in UnboxKind::ALL {
            assert!(signature(&Opcode::Unbox(k), &[Type::val(TagSet::MAGIC)], &m).is_err());
            let g = signature(&Opcode::GuardUnbox(k), &[Type::VAL_TOP], &m).unwrap();
            assert!(!matches!(g.outputs[0], Type::Val(v) if v.tags.magic));
        }
        // Boxing never yields magic.
        let b = signature(&Opcode::Box, &[Type::I32_TOP], &m).unwrap();
        assert!(!matches!(b.results[0], Type::Val(v) if v.tags.magic));
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
        // Without `types`, the identity alone: any val.
        let s = signature(&Opcode::LoadField(x), &[k3(false)], &m).unwrap();
        assert_eq!(s.outputs, vec![Type::VAL_TOP]);
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
