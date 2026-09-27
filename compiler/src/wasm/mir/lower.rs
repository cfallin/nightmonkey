//! Lowering a MIR function to its own waffle function (MIR.md §9).
//!
//! The body has the shared `night_abi_sig2` signature and is the script's
//! table entry; the script's baseline body is a separate function that the
//! exits call (`docs/BASELINE.md` §7).
//!
//! - **Values.** Each MIR value becomes at most one waffle value per point:
//!   `Val` and `Int` are i64, `F64` is f64, the rest i32, and ghosts
//!   (`Fact`) vanish. Blocks map one to one, plus internal blocks for the
//!   ops that branch.
//! - **Reducibility (§5.4).** A function with onramp roots may be
//!   irreducible; waffle's backend makes it reducible by duplication.
//! - **Rooting (§4.4).** Before a may-GC helper call, every managed value
//!   (`Val`, `Obj`, `Str`) live across it is stored, boxed, to the
//!   NightStack just above the padded formals, and the helper's `top` is
//!   passed above them. Afterwards each is reloaded into a fresh waffle
//!   value. So the waffle value standing for a managed MIR value differs
//!   from path to path, and every managed value live into a block enters
//!   it as a waffle block param (a *carried* value), passed along each
//!   edge from the current mapping.
//! - **Exits (§5.1).** An exit writes the whole baseline frame (`this`,
//!   formals, locals, rval, stack, and the fixed slots), stores its resume
//!   word, calls the baseline body with `ARGC_RESUME_BIT`, and returns
//!   what it returns.
//! - **Effects.** Every body reports `FLAGS_ALL`, and a generic op always
//!   takes its `ok_dirty` edge; accurate flags come with M5.

use std::collections::{BTreeMap, BTreeSet};

use waffle::entity::EntityRef;
use waffle::{
    Block, BlockTarget, Func, FunctionBody, MemoryArg, Module, Operator, Terminator, Type, Value,
    ValueDef,
};

use crate::ids::Pc;
use crate::mir;
use crate::mir::func::{Edge, EdgeArg, RootKind};
use crate::mir::ops::{
    frame_parts, ArithOp, BitOp, Cc, ConstVal, F64Op, JsBinop, JsCc, JsUnop, MathFn, NumRepr,
    Opcode, UnboxKind,
};
use crate::mir::types::{Machine, TagSet, Type as MType};
use crate::opsem::{
    PRIM_BIGINT, PRIM_BOOLEAN, PRIM_DOUBLE, PRIM_INT32, PRIM_NULL, PRIM_STRING, PRIM_SYMBOL,
    PRIM_UNDEFINED,
};
use crate::wasm::baseline::layout::{
    FrameLayout, ResumeMode, ResumeWord, ARGC_FLAGS, ARGC_ONRAMP_BIT, ARGC_RESUME_BIT, ERR_DEOPT,
};
use crate::wasm::bbv::abi::{
    BINOP_BITAND, BINOP_BITNOT, BINOP_BITOR, BINOP_BITXOR, BINOP_DEC, BINOP_DIV, BINOP_INC,
    BINOP_LSH, BINOP_MOD, BINOP_MUL, BINOP_RSH, BINOP_SUB, BINOP_URSH, CLASS_WORD_SHALLOW,
    CLASS_WORD_RANGES, CLASS_WORD_SENTINEL, CLASS_WORD_SLOTS, EARLY_KEY_MAX, EARLY_KEY_SHIFT, IC_SET_ABSSLOT,
    IC_SET_RECVSHAPE, IC_SET_SLOTENC, IC_TRANS_ABSSLOT, IC_TRANS_INLINE_HOPS, IC_TRANS_NEWSHAPE,
    IC_TRANS_OLDSHAPE, IC_TRANS_PROTO0, IC_TRANS_PROTO_HOPS, IC_TRANS_PROTO_ROW_BYTES,
    IC_TRANS_ROW_OFF, IC_TRANS_SLOTOFF, BASESHAPE_PROTO_OFFSET, IOF_CELL_ADDR_PLACEHOLDER,
    IOF_CELL_GEN, IOF_CELL_SLOTENC, CONSTRUCT_CELL_ADDR_PLACEHOLDER, CONSTRUCT_CELL_CTORSHAPE,
    CONSTRUCT_CELL_GEN, CONSTRUCT_CELL_PROTOPTR, CONSTRUCT_CELL_PROTOSLOTENC, NURSERY_HEADER_BYTES,
    IC_WAY_HOLDERPTR, IC_WAY_MONO_OFF, IC_WAY_RECVSHAPE,
    IC_WAY_ADDR_PLACEHOLDER, NATIVE_SLOTS_OFFSET, SHAPE_BASESHAPE_OFFSET, BASESHAPE_CLASP_OFFSET,
    BASESCRIPT_NIGHTFUNCINDEX_OFFSET, FUNC_FLAGS_SLOT_OFFSET, FUNCTION_FLAGS_CONSTRUCTOR, FUNC_ENV_SLOT_OFFSET, FUNC_SCRIPT_SLOT_OFFSET,
    SHAPE_FIXED_SLOTS_MASK_BITS, SHAPE_FIXED_SLOTS_SHIFT, JSCONTEXT_REALM_OFFSET,
    REALM_GLOBAL_OFFSET, CHUNK_STORE_BUFFER_OFFSET, CMP_EQ, CMP_GE, CMP_GT, CMP_LE, CMP_LT, CMP_NE, CMP_STRICTEQ, CMP_STRICTNE,
    ELEMENTS_FLAGS_BACK, ELEMENTS_FROZEN_FLAG, ELEMENTS_INITLEN_BACK, FIXED_SLOTS_BASE, FLAGS_ALL, OBJ_CLASS_IDX_OFFSET, OBJ_ELEMENTS_OFFSET,
    JSCONTEXT_ZONE_OFFSET, NOT_CHUNK_MASK, SHAPE_IMMUTABLE_FLAGS_OFFSET, SHAPE_IS_NATIVE_BIT,
    SHAPE_OFFSET, VAL_GCTHING_TAG_MIN, ZONE_NEEDS_BARRIER_OFFSET,
};
use crate::wasm::translate::{
    AtomTable, Helpers, INLINE_IC_STRIDE, MAGIC_IS_CONSTRUCTING, MAGIC_UNINITIALIZED_LEXICAL, TAG_BIGINT_HI, TAG_BOOLEAN, TAG_CLEAR,
    TAG_INT32, TAG_MAGIC, TAG_NULL, TAG_OBJECT, TAG_STRING, TAG_SYMBOL, TAG_UNDEFINED,
};

type R<T> = Result<T, String>;

/// Whether `new` of a compiled constructor calls it directly.
const DIRECT_CONSTRUCT: bool = true;

/// Whether global binding writes get their inline arm.
const INLINE_GNAME_SETS: bool = true;

const UNDEF: u64 = TAG_UNDEFINED << 32;

/// The onramp backoff an exit leaves in the frame (`FrameLayout::backoff`).
const ONRAMP_BACKOFF: u32 = 32;

/// `JS::GenericNaN()`'s bits.
const CANONICAL_NAN_BITS: u64 = 0x7FF8_0000_0000_0000;

/// A lowered MIR function.
pub struct Lowered {
    pub body: FunctionBody,
    /// Adapter-offset placeholders of direct calls.
    pub body_off_patches: Vec<Value>,
    /// `Call` placeholders for the script's baseline body, one per exit.
    pub baseline_calls: Vec<Value>,
    /// Property-IC way-address placeholders, with their row offsets.
    pub prop_ic_patches: Vec<(Value, u32)>,
    /// `instanceof` cell placeholders, with their rows (+1).
    pub iof_cell_patches: Vec<(Value, u32)>,
    pub construct_cell_patches: Vec<(Value, u32)>,
}

/// The resume words `f`'s exits and throws carry: the set the baseline
/// body must accept (`docs/BASELINE.md` §4).
pub fn resume_words(f: &mir::Func) -> Vec<ResumeWord> {
    let mut out = BTreeSet::new();
    for (_, d) in f.insts.iter() {
        let mode = match d.op {
            Opcode::Exit { .. } => ResumeMode::Continue,
            Opcode::ExitThrow { .. } => ResumeMode::Throw,
            _ => continue,
        };
        let (pc, _, _) = d.op.exit_shape().unwrap();
        out.insert(ResumeWord { pc, mode });
    }
    out.into_iter().collect()
}

/// The resume words of the exits and throws reachable from `root`: where
/// an activation entered there can resume baseline.
pub fn resume_words_from(f: &mir::Func, root: mir::Block) -> Vec<ResumeWord> {
    let mut seen = BTreeSet::new();
    let mut work = vec![root];
    let mut out = BTreeSet::new();
    while let Some(b) = work.pop() {
        if !seen.insert(b) {
            continue;
        }
        work.extend(f.succs(b));
        if let Some(t) = f.terminator(b) {
            let op = f.insts[t].op;
            if let Some((pc, _, _)) = op.exit_shape() {
                let mode = if matches!(op, Opcode::Exit { .. }) {
                    ResumeMode::Continue
                } else {
                    ResumeMode::Throw
                };
                out.insert(ResumeWord { pc, mode });
            }
        }
    }
    out.into_iter().collect()
}

/// The waffle type a MIR type lowers to (`None` for a ghost).
fn machine(t: &MType) -> Option<Type> {
    match t.repr().machine() {
        Machine::I32 => Some(Type::I32),
        Machine::I64 => Some(Type::I64),
        Machine::F64 => Some(Type::F64),
        Machine::None => None,
    }
}

/// An exit operand's representation, as far as boxing it goes: exits
/// whose operands agree on these share an exit hub.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum BoxKind {
    Val,
    I32,
    Int,
    F64,
    Bool,
    Obj,
    Str,
}

impl BoxKind {
    fn of(t: &MType) -> R<BoxKind> {
        Ok(match t {
            MType::Val(_) => BoxKind::Val,
            MType::I32(_) => BoxKind::I32,
            MType::Int(_) => BoxKind::Int,
            MType::F64(_) => BoxKind::F64,
            MType::Bool => BoxKind::Bool,
            MType::Obj(_) => BoxKind::Obj,
            MType::Str(_) => BoxKind::Str,
            t => return Err(format!("exit: cannot box {}", mir::print::type_str(t))),
        })
    }
}

fn is_managed(t: &MType) -> bool {
    t.repr().is_managed()
}

struct Lower<'a> {
    h: Helpers,
    f: &'a mir::Func,
    layout: FrameLayout,
    body: FunctionBody,
    cur: Block,
    cx: Value,
    sp: Value,
    /// The base of the frame's variable region (locals, fixed slots,
    /// operands) and of everything MIR places above it: `sp`, or past the
    /// actuals beyond the formals for a script that reads its actuals
    /// (`FrameLayout::rebase_vp`).
    vp: Value,
    /// `argc` without its flag bits.
    argc: Value,
    retval_out: Value,
    script_param: Value,
    new_target: Value,
    blocks: BTreeMap<mir::Block, Block>,
    live_in: BTreeMap<mir::Block, BTreeSet<mir::Value>>,
    /// Per block: the managed live-ins that enter as waffle params (after
    /// the block's own params), in order.
    carried: BTreeMap<mir::Block, Vec<mir::Value>>,
    /// The waffle value standing for each MIR value at the emission point.
    vmap: BTreeMap<mir::Value, Value>,
    /// Where the rooting slots start, in bytes above `sp`: past the whole
    /// baseline frame, at its deepest operand stack.
    root_base: u32,
    /// The baseline frame's deepest operand stack.
    max_depth: u32,
    /// With inlined callees (§5.5): the rooting area's size in slots (the
    /// most managed values live anywhere), and per frame id its base and
    /// end offsets from `sp` and its layout. Frame 0 is the function's;
    /// its end is the rooting area's.
    inline: bool,
    root_slots: u32,
    frame_off: Vec<u32>,
    frame_end: Vec<u32>,
    frame_layouts: Vec<FrameLayout>,
    /// The frame of the instruction being lowered.
    cur_frame: u32,
    baseline_calls: Vec<Value>,
    /// The stress mode's period (`Options::mir_stress`); 0 = off.
    stress: u32,
    /// Whether the function has onramp roots, and (if so) the entry's
    /// test of `ARGC_ONRAMP_BIT`, which says how this activation began.
    has_onramps: bool,
    onramp_flag: Value,
    mm: &'a mir::Module,
    atoms: &'a mut AtomTable,
    /// Adapter-offset placeholders (`Outcome::Compiled::body_off_patches`).
    body_off_patches: Vec<Value>,
    /// Property-IC way-address placeholders (`Outcome::Compiled::prop_ic_patches`).
    prop_ic_patches: Vec<(Value, u32)>,
    /// `instanceof` cell placeholders (`Outcome::Compiled::iof_cell_patches`).
    iof_cell_patches: Vec<(Value, u32)>,
    /// Construct cell placeholders (bbv's per-site cell).
    construct_cell_patches: Vec<(Value, u32)>,
    /// The census helper, when exits are counted (`--mir-exit-census`).
    exit_census: Option<Func>,
    ctor_stamp: Option<[u32; 3]>,
    ctor_restamp: Option<[u32; 7]>,
    /// One exit hub per frame shape (`exit_hub`).
    exit_hubs: BTreeMap<Vec<Option<BoxKind>>, Block>,
    strict: bool,
    plain_env: bool,
    own_env: bool,
    forward_resume: bool,
    /// The syntactic global binding (`TranslateCtx::syn_gnames`) each
    /// global name read names, for its inline arms.
    gname_bids: BTreeMap<mir::entity::AtomId, u32>,
    /// Each global name with a fused literal (`fused_gnames`), which an
    /// inline write must keep.
    gname_fused: BTreeMap<mir::entity::AtomId, crate::wasm::translate::FusedGname>,
    /// Each property name's predicted (layout stamp key, byte offset)
    /// pairs (`layout_addpred_in`), for the inline add arm.
    add_preds: BTreeMap<mir::entity::AtomId, Vec<(u32, u32)>>,
}

/// Per-script lowering choices besides the function itself.
#[derive(Clone, Copy, Default)]
pub struct LowerOpts {
    /// The stress mode's period (`Options::mir_stress`); 0 = off.
    pub stress: u32,
    /// Count every exit (`--mir-exit-census`).
    pub exit_census: bool,
    /// A layout constructor's ctor-exit stamp arguments (layout, field
    /// count, kept bits), as baseline's `Gen::ctor_stamp`.
    pub ctor_stamp: Option<[u32; 3]>,
    /// An init delegate's restamp arguments (`bbv::restamp_args`).
    pub ctor_restamp: Option<[u32; 7]>,
    /// Strict-mode code: a field store's generic fallback throws on failure.
    pub strict: bool,
    /// The activation's environment is its callee's (`baseline::env_is_plain`).
    pub plain_env: bool,
    /// The activation makes its own environment (a call object, a named
    /// lambda's scope) at entry, fixed from then on: `env_setup`.
    pub own_env: bool,
    /// The script may be inlined: its entry forwards a resume to its
    /// baseline body (§5.5).
    pub forward_resume: bool,
}

/// Lower `f` (a function of `mm`, whose baseline frame is `layout`) into a
/// new body of `m`.
pub fn lower<'a>(
    m: &mut Module,
    h: Helpers,
    mm: &'a mir::Module,
    atoms: &'a mut AtomTable,
    f: &'a mir::Func,
    layout: FrameLayout,
    max_depth: u32,
    o: LowerOpts,
    gname_bids: BTreeMap<mir::entity::AtomId, u32>,
    gname_fused: BTreeMap<mir::entity::AtomId, crate::wasm::translate::FusedGname>,
    add_preds: BTreeMap<mir::entity::AtomId, Vec<(u32, u32)>>,
) -> R<Lowered> {
    let body = FunctionBody::new(m, h.night_abi_sig2);
    let entry = body.entry;
    let p = |i: usize| body.blocks[entry].params[i].1;
    let (cx, sp, argc, retval_out, script_param, new_target) = (p(0), p(1), p(2), p(3), p(4), p(5));
    // Rooting slots and callee frames go above the whole baseline frame,
    // which therefore always holds valid Values (a fresh entry initializes
    // it): an exit can leave a dead slot as it is.
    let root_base = layout.operand(max_depth);
    let mut l = Lower {
        h,
        f,
        layout,
        body,
        cur: entry,
        cx,
        sp,
        vp: sp,
        argc,
        retval_out,
        script_param,
        new_target,
        blocks: BTreeMap::new(),
        live_in: BTreeMap::new(),
        carried: BTreeMap::new(),
        vmap: BTreeMap::new(),
        root_base,
        max_depth,
        inline: !f.inline_frames.is_empty(),
        root_slots: 0,
        frame_off: vec![0],
        frame_end: vec![root_base],
        frame_layouts: vec![layout],
        cur_frame: 0,
        baseline_calls: vec![],
        stress: o.stress,
        has_onramps: f.roots.iter().any(|r| r.kind != RootKind::Entry),
        onramp_flag: argc,
        mm,
        atoms,
        body_off_patches: vec![],
        prop_ic_patches: vec![],
        iof_cell_patches: vec![],
        construct_cell_patches: vec![],
        exit_census: if o.exit_census { h.census } else { None },
        ctor_stamp: o.ctor_stamp,
        ctor_restamp: o.ctor_restamp,
        exit_hubs: BTreeMap::new(),
        strict: o.strict,
        plain_env: o.plain_env,
        own_env: o.own_env,
        forward_resume: o.forward_resume,
        gname_bids,
        gname_fused,
        add_preds,
    };
    l.run()?;
    Ok(Lowered {
        body: l.body,
        body_off_patches: l.body_off_patches,
        baseline_calls: l.baseline_calls,
        prop_ic_patches: l.prop_ic_patches,
        iof_cell_patches: l.iof_cell_patches,
        construct_cell_patches: l.construct_cell_patches,
    })
}

impl<'a> Lower<'a> {
    // --- waffle primitives ---------------------------------------------------

    fn push_val(&mut self, def: ValueDef) -> Value {
        let v = self.body.add_value(def);
        self.body.append_to_block(self.cur, v);
        v
    }

    fn op(&mut self, op: Operator, args: &[Value], ty: Option<Type>) -> Value {
        let args = self.body.arg_pool.from_iter(args.iter().copied());
        let tys = match ty {
            Some(t) => self.body.single_type_list(t),
            None => Default::default(),
        };
        self.push_val(ValueDef::Operator(op, args, tys))
    }

    fn i32c(&mut self, value: u32) -> Value {
        self.op(Operator::I32Const { value }, &[], Some(Type::I32))
    }

    fn i64c(&mut self, value: u64) -> Value {
        self.op(Operator::I64Const { value }, &[], Some(Type::I64))
    }

    fn f64c(&mut self, value: u64) -> Value {
        self.op(Operator::F64Const { value }, &[], Some(Type::F64))
    }

    fn un(&mut self, op: Operator, a: Value, t: Type) -> Value {
        self.op(op, &[a], Some(t))
    }

    fn bin(&mut self, op: Operator, a: Value, b: Value, t: Type) -> Value {
        self.op(op, &[a, b], Some(t))
    }

    fn select(&mut self, t: Type, a: Value, b: Value, cond: Value) -> Value {
        self.op(Operator::TypedSelect { ty: t }, &[a, b, cond], Some(t))
    }

    fn mem(&self, align: u32, offset: u32) -> MemoryArg {
        MemoryArg {
            align,
            offset,
            memory: self.h.mem,
        }
    }

    fn load_i64(&mut self, addr: Value, offset: u32) -> Value {
        let m = self.mem(3, offset);
        self.un(Operator::I64Load { memory: m }, addr, Type::I64)
    }

    fn store_i64(&mut self, addr: Value, offset: u32, v: Value) {
        let m = self.mem(3, offset);
        self.op(Operator::I64Store { memory: m }, &[addr, v], None);
    }

    fn store_i32(&mut self, addr: Value, offset: u32, v: Value) {
        let m = self.mem(2, offset);
        self.op(Operator::I32Store { memory: m }, &[addr, v], None);
    }

    fn add_off(&mut self, addr: Value, off: u32) -> Value {
        if off == 0 {
            return addr;
        }
        let k = self.i32c(off);
        self.bin(Operator::I32Add, addr, k, Type::I32)
    }

    fn call(&mut self, f: Func, args: &[Value], rets: &[Type]) -> Value {
        let args = self.body.arg_pool.from_iter(args.iter().copied());
        let tys = self.body.type_pool.from_iter(rets.iter().copied());
        self.push_val(ValueDef::Operator(
            Operator::Call { function_index: f },
            args,
            tys,
        ))
    }

    fn call1(&mut self, f: Func, args: &[Value], ret: Type) -> Value {
        self.call(f, args, &[ret])
    }

    fn terminate(&mut self, t: Terminator) {
        self.body.set_terminator(self.cur, t);
    }

    fn cond_br(&mut self, cond: Value, if_true: BlockTarget, if_false: BlockTarget) {
        self.terminate(Terminator::CondBr {
            cond,
            if_true,
            if_false,
        });
    }

    fn ret(&mut self, err: Value) {
        let flags = self.i32c(FLAGS_ALL);
        self.terminate(Terminator::Return {
            values: vec![err, flags],
        });
    }

    // --- boxing ------------------------------------------------------------------

    fn tag_of(&mut self, v: Value) -> Value {
        let sh = self.i64c(32);
        let hi = self.bin(Operator::I64ShrU, v, sh, Type::I64);
        self.un(Operator::I32WrapI64, hi, Type::I32)
    }

    fn tag_is(&mut self, tag: Value, t: u32) -> Value {
        let k = self.i32c(t);
        self.bin(Operator::I32Eq, tag, k, Type::I32)
    }

    fn box_tagged(&mut self, tag: u64, payload: Value) -> Value {
        let p = self.un(Operator::I64ExtendI32U, payload, Type::I64);
        let t = self.i64c(tag << 32);
        self.bin(Operator::I64Or, t, p, Type::I64)
    }

    /// Box an f64 as `NumberValue` does: an int32 when it is one exactly
    /// (not -0), else a double, with NaN canonicalized.
    fn box_number(&mut self, x: Value) -> Value {
        let i = self.un(Operator::I32TruncSatF64S, x, Type::I32);
        let back = self.un(Operator::F64ConvertI32S, i, Type::F64);
        let exact = self.bin(Operator::F64Eq, back, x, Type::I32);
        let bits = self.un(Operator::I64ReinterpretF64, x, Type::I64);
        let negz = self.i64c(1 << 63);
        let not_negz = self.bin(Operator::I64Ne, bits, negz, Type::I32);
        let is_int = self.bin(Operator::I32And, exact, not_negz, Type::I32);
        let nan = self.bin(Operator::F64Ne, x, x, Type::I32);
        let canon = self.i64c(CANONICAL_NAN_BITS);
        let dbl = self.select(Type::I64, canon, bits, nan);
        let int = self.box_tagged(TAG_INT32, i);
        self.select(Type::I64, int, dbl, is_int)
    }

    /// A value of type `t` (lowered as `v`) as a boxed Value.
    fn boxed(&mut self, t: &MType, v: Value) -> R<Value> {
        Ok(match t {
            MType::Val(_) => v,
            MType::I32(_) => self.box_tagged(TAG_INT32, v),
            MType::Bool => self.box_tagged(TAG_BOOLEAN, v),
            MType::Obj(_) => self.box_tagged(TAG_OBJECT, v),
            MType::Str(_) => self.box_tagged(TAG_STRING, v),
            MType::F64(_) => self.box_number(v),
            MType::Int(_) => {
                let x = self.un(Operator::F64ConvertI64S, v, Type::F64);
                self.box_number(x)
            }
            t => return Err(format!("box: cannot box {}", mir::print::type_str(t))),
        })
    }

    /// The inverse of `boxed` for the managed representations.
    fn unboxed_managed(&mut self, t: &MType, v: Value) -> Value {
        match t {
            MType::Val(_) => v,
            _ => self.un(Operator::I32WrapI64, v, Type::I32),
        }
    }

    /// A number Value (int32 or double) as an f64.
    fn to_f64(&mut self, v: Value) -> Value {
        let tag = self.tag_of(v);
        let is_int = self.tag_is(tag, TAG_INT32 as u32);
        let low = self.un(Operator::I32WrapI64, v, Type::I32);
        let fi = self.un(Operator::F64ConvertI32S, low, Type::F64);
        let fd = self.un(Operator::F64ReinterpretI64, v, Type::F64);
        self.select(Type::F64, fi, fd, is_int)
    }

    /// JS ToInt32 of an f64: its integer part modulo 2^32. `x - trunc(x /
    /// 2^32) * 2^32` is exact for every finite `x` (scaling by a power of
    /// two is exact, and the difference fits `x`'s precision), and brings
    /// it within (-2^32, 2^32), where a saturating i64 truncation and a
    /// wrap finish the job. NaN and the infinities come out as NaN, which
    /// truncates to 0, as ToInt32 wants.
    fn to_int32(&mut self, x: Value) -> Value {
        let two32 = self.f64c(4294967296f64.to_bits());
        let q = self.bin(Operator::F64Div, x, two32, Type::F64);
        let qt = self.un(Operator::F64Trunc, q, Type::F64);
        let m = self.bin(Operator::F64Mul, qt, two32, Type::F64);
        let r = self.bin(Operator::F64Sub, x, m, Type::F64);
        let i = self.un(Operator::I64TruncSatF64S, r, Type::I64);
        self.un(Operator::I32WrapI64, i, Type::I32)
    }

    /// Whether `v`'s tag is in `tags`.
    fn has_tags(&mut self, v: Value, tags: TagSet) -> Value {
        let tag = self.tag_of(v);
        let mut acc: Option<Value> = None;
        let mut or = |l: &mut Self, c: Value| {
            acc = Some(match acc {
                Some(a) => l.bin(Operator::I32Or, a, c, Type::I32),
                None => c,
            });
        };
        let singles = [
            (PRIM_INT32, TAG_INT32 as u32),
            (PRIM_BOOLEAN, TAG_BOOLEAN as u32),
            (PRIM_UNDEFINED, TAG_UNDEFINED as u32),
            (PRIM_NULL, TAG_NULL as u32),
            (PRIM_STRING, TAG_STRING as u32),
            (PRIM_SYMBOL, TAG_SYMBOL as u32),
            (PRIM_BIGINT, TAG_BIGINT_HI),
        ];
        for (prim, t) in singles {
            if tags.prims.intersects(prim) {
                let c = self.tag_is(tag, t);
                or(self, c);
            }
        }
        if tags.prims.intersects(PRIM_DOUBLE) {
            let k = self.i32c(TAG_CLEAR);
            let c = self.bin(Operator::I32LtU, tag, k, Type::I32);
            or(self, c);
        }
        if tags.object {
            let c = self.tag_is(tag, TAG_OBJECT as u32);
            or(self, c);
        }
        if tags.magic {
            let c = self.tag_is(tag, TAG_MAGIC as u32);
            or(self, c);
        }
        match acc {
            Some(a) => a,
            None => self.i32c(0),
        }
    }

    // --- the MIR side ----------------------------------------------------------

    fn ty(&self, v: mir::Value) -> MType {
        self.f.values[v].ty
    }

    fn get(&self, v: mir::Value) -> R<Value> {
        self.vmap
            .get(&v)
            .copied()
            .ok_or_else(|| format!("lowering: {v} has no value here"))
    }

    fn args(&self, inst: mir::Inst) -> R<Vec<Value>> {
        self.f.insts[inst]
            .args
            .iter()
            .map(|&v| self.get(v))
            .collect()
    }

    /// Blocks reachable from a root.
    /// The reachable blocks in reverse postorder from the roots.
    fn rpo(&self) -> Vec<mir::Block> {
        let mut seen = BTreeSet::new();
        let mut post = vec![];
        for r in &self.f.roots {
            if !seen.insert(r.block) {
                continue;
            }
            let mut stack = vec![(r.block, self.f.succs(r.block), 0usize)];
            while let Some((b, succs, i)) = stack.last_mut() {
                if *i < succs.len() {
                    let s = succs[*i];
                    *i += 1;
                    if seen.insert(s) {
                        let ss = self.f.succs(s);
                        stack.push((s, ss, 0));
                    }
                } else {
                    post.push(*b);
                    stack.pop();
                }
            }
        }
        post.reverse();
        post
    }

    fn reachable(&self) -> BTreeSet<mir::Block> {
        let mut seen = BTreeSet::new();
        let mut work: Vec<mir::Block> = self.f.roots.iter().map(|r| r.block).collect();
        while let Some(b) = work.pop() {
            if seen.insert(b) {
                work.extend(self.f.succs(b));
            }
        }
        seen
    }

    fn liveness(&mut self, blocks: &BTreeSet<mir::Block>) {
        let f = self.f;
        let edge_uses = |inst: mir::Inst| -> Vec<mir::Value> {
            f.insts[inst]
                .succs
                .iter()
                .flat_map(|e| e.args.iter())
                .filter_map(|a| match a {
                    EdgeArg::Value(v) => Some(*v),
                    EdgeArg::Out(_) => None,
                })
                .collect()
        };
        let mut changed = true;
        while changed {
            changed = false;
            for &b in blocks.iter().rev() {
                let mut live: BTreeSet<mir::Value> = BTreeSet::new();
                for s in f.succs(b) {
                    if let Some(l) = self.live_in.get(&s) {
                        live.extend(l.iter().copied());
                    }
                }
                for &inst in f.blocks[b].insts.iter().rev() {
                    for r in &f.insts[inst].results {
                        live.remove(r);
                    }
                    live.extend(f.insts[inst].args.iter().copied());
                    live.extend(edge_uses(inst));
                }
                for p in &f.blocks[b].params {
                    live.remove(p);
                }
                live.retain(|&v| machine(&f.values[v].ty).is_some());
                if self.live_in.get(&b) != Some(&live) {
                    self.live_in.insert(b, live);
                    changed = true;
                }
            }
        }
    }

    fn run(&mut self) -> R<()> {
        let f = self.f;
        let reach = self.reachable();
        self.liveness(&reach);
        if self.inline {
            self.inline_layout(&reach);
        }
        // Waffle blocks: the block's own params, then its carried values.
        for &b in &f.layout {
            if !reach.contains(&b) {
                continue;
            }
            let wb = self.body.add_block();
            for &p in &f.blocks[b].params {
                if let Some(t) = machine(&self.ty(p)) {
                    self.body.add_blockparam(wb, t);
                }
            }
            let carried: Vec<mir::Value> = self.live_in[&b]
                .iter()
                .copied()
                .filter(|&v| is_managed(&self.ty(v)))
                .collect();
            for &v in &carried {
                self.body.add_blockparam(wb, machine(&self.ty(v)).unwrap());
            }
            self.carried.insert(b, carried);
            self.blocks.insert(b, wb);
        }
        self.entry()?;
        // In reverse postorder, so a block's dominators, which define the
        // unmanaged values it uses directly, are lowered before it.
        for b in self.rpo() {
            self.cur = self.blocks[&b];
            let wparams: Vec<Value> = self.body.blocks[self.cur]
                .params
                .iter()
                .map(|&(_, v)| v)
                .collect();
            let mut k = 0;
            for &p in &f.blocks[b].params {
                if machine(&self.ty(p)).is_some() {
                    self.vmap.insert(p, wparams[k]);
                    k += 1;
                }
            }
            for &v in &self.carried[&b].clone() {
                self.vmap.insert(v, wparams[k]);
                k += 1;
            }
            for &inst in &f.blocks[b].insts {
                self.inst(inst)?;
            }
        }
        Ok(())
    }

    /// The entry. Under `ARGC_ONRAMP_BIT` (baseline at a loop header),
    /// enter the onramp root the resume word names, with its params read
    /// from the baseline frame. Otherwise, pad the formals the caller did
    /// not pass with undefined (the frame below the rooting slots must hold
    /// valid Values), then enter the entry root with callee, `this` and the
    /// formals.
    fn entry(&mut self) -> R<()> {
        if self.forward_resume {
            // An inlined copy's exit finishes the call in baseline through
            // this entry (§5.5): hand the frame, as it is, to the baseline
            // body.
            let rb = self.i32c(ARGC_RESUME_BIT);
            let resume = self.bin(Operator::I32And, self.argc, rb, Type::I32);
            let (fwd, rest) = (self.body.add_block(), self.body.add_block());
            self.cond_br(resume, Self::to(fwd), Self::to(rest));
            self.cur = fwd;
            let argc = self.argc;
            self.tail_to_baseline(argc);
            self.cur = rest;
        }
        let bit = self.i32c(ARGC_ONRAMP_BIT);
        self.onramp_flag = self.bin(Operator::I32And, self.argc, bit, Type::I32);
        let flags = self.i32c(!ARGC_FLAGS);
        self.argc = self.bin(Operator::I32And, self.argc, flags, Type::I32);
        if self.layout.rebase_vp {
            // Past the actuals beyond the formals, as baseline's `vp`.
            let n = self.i32c(self.layout.nargs);
            let extra = self.bin(Operator::I32Sub, self.argc, n, Type::I32);
            let more = self.bin(Operator::I32GtU, self.argc, n, Type::I32);
            let zero = self.i32c(0);
            let extra = self.select(Type::I32, extra, zero, more);
            let eight = self.i32c(8);
            let bytes = self.bin(Operator::I32Mul, extra, eight, Type::I32);
            self.vp = self.bin(Operator::I32Add, self.sp, bytes, Type::I32);
        }
        let onramps: Vec<(Pc, mir::Block)> = self
            .f
            .roots
            .iter()
            .filter_map(|r| match r.kind {
                RootKind::Onramp(pc) => Some((pc, r.block)),
                RootKind::Entry => None,
            })
            .collect();
        if !onramps.is_empty() {
            let disp = self.body.add_block();
            let fresh = self.body.add_block();
            self.cond_br(self.onramp_flag, Self::to(disp), Self::to(fresh));
            self.cur = disp;
            let word = self.load_i32(self.vp, self.layout.resume());
            for (pc, root) in onramps {
                let w = ResumeWord {
                    pc,
                    mode: ResumeMode::Continue,
                };
                let k = self.i32c(w.encode() as u32);
                let hit = self.bin(Operator::I32Eq, word, k, Type::I32);
                let (yes, no) = (self.body.add_block(), self.body.add_block());
                self.cond_br(hit, Self::to(yes), Self::to(no));
                self.cur = yes;
                self.enter_onramp(pc, root)?;
                self.cur = no;
            }
            self.terminate(Terminator::Unreachable);
            self.cur = fresh;
        }
        let root = self
            .f
            .roots
            .iter()
            .find(|r| r.kind == RootKind::Entry)
            .ok_or("lowering: no entry root")?
            .block;
        let undef = self.i64c(UNDEF);
        let mut vals = vec![
            self.load_i64(self.sp, FrameLayout::CALLEE),
            self.load_i64(self.sp, FrameLayout::THIS),
        ];
        for i in 0..self.layout.nargs {
            let off = self.layout.arg(i);
            let cur = self.load_i64(self.sp, off);
            let iv = self.i32c(i);
            let keep = self.bin(Operator::I32LtU, iv, self.argc, Type::I32);
            let v = self.select(Type::I64, cur, undef, keep);
            self.store_i64(self.sp, off, v);
            vals.push(v);
        }
        // The rest of the baseline frame, as its prologue would set it: the
        // GC traces it (it is below every `top` MIR publishes), and exits
        // leave dead slots as they find them.
        let l = self.layout;
        let vp = self.vp;
        for j in 0..l.nlocals {
            self.store_i64(vp, l.local(j), undef);
        }
        for off in [l.args_obj(), l.rval()] {
            self.store_i64(vp, off, undef);
        }
        // The environment: the callee's own, or none (§5.1).
        let env = if self.plain_env {
            let callee = self.load_i64(self.sp, 0);
            let f = self.un(Operator::I32WrapI64, callee, Type::I32);
            self.load_i64(f, FUNC_ENV_SLOT_OFFSET)
        } else {
            undef
        };
        self.store_i64(vp, l.env(), env);
        self.store_i64(vp, l.new_target(), self.new_target);
        let zero = self.i64c(TAG_INT32 << 32);
        self.store_i64(vp, l.resume(), zero);
        self.store_i64(vp, l.backoff(), zero);
        for k in 0..self.max_depth {
            self.store_i64(vp, l.operand(k), undef);
        }
        self.init_root_area();
        if self.own_env {
            // Every slot is valid: the GC may run. Failing, the throw has
            // no handler (baseline's prologue: pc 0, depth 0).
            let top = self.add_off(self.vp, self.top_off(0));
            let script = self.script_ptr();
            let ok = self.call1(self.h.env_setup, &[self.cx, top, self.sp, script], Type::I32);
            let (made, fail) = (self.body.add_block(), self.body.add_block());
            self.cond_br(ok, Self::to(made), Self::to(fail));
            self.cur = fail;
            let one = self.i32c(1);
            self.ret(one);
            self.cur = made;
            let env = self.load_i64(top, 0);
            self.store_i64(vp, l.env(), env);
        }
        let params = self.f.blocks[root].params.clone();
        if params.len() != vals.len() {
            return Err("lowering: the entry root's params are not the frame".into());
        }
        let mut args = vec![];
        for (&p, &v) in params.iter().zip(&vals) {
            let t = self.ty(p);
            if machine(&t).is_some() {
                args.push(self.unboxed_managed(&t, v));
            }
        }
        let b = self.blocks[&root];
        self.terminate(Terminator::Br {
            target: BlockTarget { block: b, args },
        });
        Ok(())
    }

    /// Enter onramp root `root` (loop header `pc`) with the baseline
    /// frame's state at `pc`: `this`, formals, locals, rval and the
    /// operand stack.
    fn enter_onramp(&mut self, pc: Pc, root: mir::Block) -> R<()> {
        let l = self.layout;
        let (sp, vp) = (self.sp, self.vp);
        let depth = *self
            .f
            .frame
            .depths
            .get(&pc)
            .ok_or("lowering: no depth at an onramp")?;
        let mut vals = vec![self.load_i64(sp, FrameLayout::THIS)];
        for i in 0..l.nargs {
            vals.push(self.load_i64(sp, l.arg(i)));
        }
        for j in 0..l.nlocals {
            vals.push(self.load_i64(vp, l.local(j)));
        }
        vals.push(self.load_i64(vp, l.rval()));
        for k in 0..depth {
            vals.push(self.load_i64(vp, l.operand(k)));
        }
        // Baseline's operand slots above its current depth are stale; MIR's
        // rooting `top` covers them, so make them valid.
        let undef = self.i64c(UNDEF);
        for k in depth..self.max_depth {
            self.store_i64(vp, l.operand(k), undef);
        }
        self.init_root_area();
        if vals.len() != self.f.blocks[root].params.len() {
            return Err("lowering: an onramp root's params are not the frame".into());
        }
        let block = self.blocks[&root];
        self.terminate(Terminator::Br {
            target: BlockTarget { block, args: vals },
        });
        Ok(())
    }

    fn to(block: Block) -> BlockTarget {
        BlockTarget {
            block,
            args: vec![],
        }
    }

    fn load_i32(&mut self, addr: Value, offset: u32) -> Value {
        let m = self.mem(2, offset);
        self.un(Operator::I32Load { memory: m }, addr, Type::I32)
    }

    /// The waffle target for MIR edge `e`, with `outs` standing for the
    /// terminator's outputs.
    fn target(&mut self, e: &Edge, outs: &[Value]) -> R<BlockTarget> {
        let block = *self
            .blocks
            .get(&e.block)
            .ok_or_else(|| format!("lowering: {} is unreachable", e.block))?;
        let mut args = vec![];
        let params = self.f.blocks[e.block].params.clone();
        for (a, &p) in e.args.iter().zip(&params) {
            if machine(&self.ty(p)).is_none() {
                continue;
            }
            args.push(match *a {
                EdgeArg::Value(v) => self.get(v)?,
                EdgeArg::Out(k) => *outs
                    .get(k as usize)
                    .ok_or_else(|| format!("lowering: no output %{k}"))?,
            });
        }
        for v in self.carried[&e.block].clone() {
            args.push(self.get(v)?);
        }
        Ok(BlockTarget { block, args })
    }

    /// Branch to MIR edge `e` from a fresh block, returning that block's
    /// target (for a `CondBr` arm that must carry args).
    fn edge(&mut self, inst: mir::Inst, k: usize, outs: &[Value]) -> R<BlockTarget> {
        let e = self.f.insts[inst].succs[k].clone();
        self.target(&e, outs)
    }

    // --- rooting -------------------------------------------------------------------

    /// The managed values live across terminator `inst` (into any
    /// successor), in a fixed order.
    fn live_across(&self, inst: mir::Inst) -> Vec<mir::Value> {
        let d = &self.f.insts[inst];
        let mut s: BTreeSet<mir::Value> = BTreeSet::new();
        for e in &d.succs {
            if let Some(l) = self.live_in.get(&e.block) {
                s.extend(l.iter().copied());
            }
            for a in &e.args {
                if let EdgeArg::Value(v) = a {
                    s.insert(*v);
                }
            }
        }
        s.into_iter().filter(|&v| is_managed(&self.ty(v))).collect()
    }

    /// The managed values live across non-terminator `inst`: live after it,
    /// other than its results.
    fn live_after(&self, inst: mir::Inst) -> Vec<mir::Value> {
        let f = self.f;
        let b = f
            .layout
            .iter()
            .copied()
            .find(|&b| f.blocks[b].insts.contains(&inst))
            .expect("inst in a block");
        let mut live: BTreeSet<mir::Value> = BTreeSet::new();
        for s in f.succs(b) {
            if let Some(l) = self.live_in.get(&s) {
                live.extend(l.iter().copied());
            }
        }
        for &i in f.blocks[b].insts.iter().rev() {
            if i == inst {
                break;
            }
            let d = &f.insts[i];
            for r in &d.results {
                live.remove(r);
            }
            live.extend(d.args.iter().copied());
            for e in &d.succs {
                for a in &e.args {
                    if let EdgeArg::Value(v) = a {
                        live.insert(*v);
                    }
                }
            }
        }
        for r in &f.insts[inst].results {
            live.remove(r);
        }
        live.into_iter()
            .filter(|&v| is_managed(&self.ty(v)))
            .collect()
    }

    /// Call may-GC helper `f(cx, top, args...)` with every value in `live`
    /// rooted, reloading them afterwards. Returns the helper's i32 status
    /// and the boxed result it wrote at `top`.
    fn gc_call(&mut self, f: Func, args: &[Value], live: &[mir::Value]) -> R<(Value, Value)> {
        self.spill(live)?;
        let top_off = self.top_off(live.len());
        let top = self.add_off(self.vp, top_off);
        let mut full = vec![self.cx, top];
        full.extend_from_slice(args);
        let ok = self.call1(f, &full, Type::I32);
        self.reload(live)?;
        let result = self.load_i64(self.vp, top_off);
        Ok((ok, result))
    }

    /// The first free byte above everything this instruction's frame
    /// chain holds, as an offset from `sp`: where a helper's out-slot and
    /// GC scan limit, and a real call's frame, go. Without inlined
    /// callees, just past the `live` rooting slots; with them, past the
    /// instruction's own inline frame (the rooting area, of fixed size,
    /// sits below every inline frame).
    fn top_off(&self, live: usize) -> u32 {
        if self.inline {
            self.frame_end[self.cur_frame as usize]
        } else {
            self.root_base + 8 * u32::try_from(live).unwrap()
        }
    }

    /// Lay out the rooting area and the inline frames (§5.5). The area
    /// holds at most the managed values live into a block plus those
    /// defined in it; each inline frame sits at its parent's end.
    fn inline_layout(&mut self, reach: &BTreeSet<mir::Block>) {
        let f = self.f;
        let mut r = 0usize;
        for &b in &f.layout {
            if !reach.contains(&b) {
                continue;
            }
            let mut n = self.live_in[&b].iter().filter(|&&v| is_managed(&self.ty(v))).count();
            n += f.blocks[b].params.iter().filter(|&&v| is_managed(&self.ty(v))).count();
            for &inst in &f.blocks[b].insts {
                n += f.insts[inst].results.iter().filter(|&&v| is_managed(&self.ty(v))).count();
            }
            r = r.max(n);
        }
        self.root_slots = u32::try_from(r).unwrap();
        self.frame_end[0] = self.root_base + 8 * self.root_slots;
        for fr in &f.inline_frames {
            let lay = FrameLayout {
                nargs: fr.shape.formals,
                nlocals: fr.shape.locals,
                rebase_vp: false,
            };
            let off = self.frame_end[fr.parent as usize];
            self.frame_off.push(off);
            self.frame_end.push(off + lay.top(fr.max_depth + 3));
            self.frame_layouts.push(lay);
        }
    }

    /// Make the rooting area valid Values: with inline frames, helpers'
    /// GC scan limit lies above it whatever is live.
    fn init_root_area(&mut self) {
        if !self.inline {
            return;
        }
        let undef = self.i64c(UNDEF);
        for i in 0..self.root_slots {
            self.store_i64(self.vp, self.root_base + 8 * i, undef);
        }
    }

    /// Store `live` (managed values), boxed, to the rooting slots.
    fn spill(&mut self, live: &[mir::Value]) -> R<()> {
        for (i, &v) in live.iter().enumerate() {
            let t = self.ty(v);
            let w = self.get(v)?;
            let b = self.boxed(&t, w)?;
            let off = self.root_base + 8 * u32::try_from(i).unwrap();
            self.store_i64(self.vp, off, b);
        }
        Ok(())
    }

    /// Reload `live` from the rooting slots (a GC may have moved them).
    fn reload(&mut self, live: &[mir::Value]) -> R<()> {
        for (i, &v) in live.iter().enumerate() {
            let t = self.ty(v);
            let off = self.root_base + 8 * u32::try_from(i).unwrap();
            let raw = self.load_i64(self.vp, off);
            let w = self.unboxed_managed(&t, raw);
            self.vmap.insert(v, w);
        }
        Ok(())
    }

    // --- instructions ------------------------------------------------------------------

    fn def(&mut self, inst: mir::Inst, v: Value) {
        let r = self.f.insts[inst].results[0];
        self.vmap.insert(r, v);
    }

    fn inst(&mut self, inst: mir::Inst) -> R<()> {
        self.cur_frame = self.f.inst_frame[inst];
        let d = self.f.insts[inst].clone();
        let a = self.args(inst)?;
        let at = |i: usize| self.f.values[d.args[i]].ty;
        match d.op {
            Opcode::ConstVal(c) => {
                let bits = match c {
                    ConstVal::Undefined => UNDEF,
                    ConstVal::Null => TAG_NULL << 32,
                    ConstVal::Bool(b) => (TAG_BOOLEAN << 32) | u64::from(b),
                    ConstVal::Int32(n) => (TAG_INT32 << 32) | u64::from(n as u32),
                    ConstVal::Double(bits) => bits,
                    ConstVal::Uninitialized => (TAG_MAGIC << 32) | MAGIC_UNINITIALIZED_LEXICAL,
                    ConstVal::IsConstructing => (TAG_MAGIC << 32) | MAGIC_IS_CONSTRUCTING,
                    ConstVal::Dead => UNDEF,
                };
                let v = self.i64c(bits);
                self.def(inst, v);
            }
            Opcode::ConstI32(n) => {
                let v = self.i32c(n as u32);
                self.def(inst, v);
            }
            Opcode::ConstF64(bits) => {
                let v = self.f64c(bits);
                self.def(inst, v);
            }
            Opcode::ConstBool(b) => {
                let v = self.i32c(u32::from(b));
                self.def(inst, v);
            }
            Opcode::Box => {
                let v = self.boxed(&at(0), a[0])?;
                self.def(inst, v);
            }
            Opcode::Unbox(k) => {
                let v = match k {
                    UnboxKind::F64Num => self.to_f64(a[0]),
                    _ => self.un(Operator::I32WrapI64, a[0], Type::I32),
                };
                self.def(inst, v);
            }
            Opcode::Weaken => self.def(inst, a[0]),
            Opcode::I32ToInt => {
                let v = self.un(Operator::I64ExtendI32S, a[0], Type::I64);
                self.def(inst, v);
            }
            Opcode::I32ToF64 => {
                let v = self.un(Operator::F64ConvertI32S, a[0], Type::F64);
                self.def(inst, v);
            }
            Opcode::IntToF64 => {
                let v = self.un(Operator::F64ConvertI64S, a[0], Type::F64);
                self.def(inst, v);
            }
            Opcode::I32Wrap(op) => {
                let o = match op {
                    ArithOp::Add => Operator::I32Add,
                    ArithOp::Sub => Operator::I32Sub,
                    ArithOp::Mul => Operator::I32Mul,
                };
                let v = self.bin(o, a[0], a[1], Type::I32);
                self.def(inst, v);
            }
            Opcode::IntArith(op) => {
                let o = match op {
                    ArithOp::Add => Operator::I64Add,
                    ArithOp::Sub => Operator::I64Sub,
                    ArithOp::Mul => Operator::I64Mul,
                };
                let v = self.bin(o, a[0], a[1], Type::I64);
                self.def(inst, v);
            }
            Opcode::F64Arith(op) => {
                let o = match op {
                    F64Op::Add => Operator::F64Add,
                    F64Op::Sub => Operator::F64Sub,
                    F64Op::Mul => Operator::F64Mul,
                    F64Op::Div => Operator::F64Div,
                    F64Op::Mod => return Err("lowering: f64.mod".into()),
                };
                let v = self.bin(o, a[0], a[1], Type::F64);
                self.def(inst, v);
            }
            Opcode::F64Neg => {
                let v = self.un(Operator::F64Neg, a[0], Type::F64);
                self.def(inst, v);
            }
            Opcode::I32Bit(op) => {
                let o = match op {
                    BitOp::And => Operator::I32And,
                    BitOp::Or => Operator::I32Or,
                    BitOp::Xor => Operator::I32Xor,
                    // Wasm masks shift counts to 5 bits, as JS does.
                    BitOp::Shl => Operator::I32Shl,
                    BitOp::Shr => Operator::I32ShrS,
                };
                let v = self.bin(o, a[0], a[1], Type::I32);
                self.def(inst, v);
            }
            Opcode::I32Ushr => {
                let r = self.bin(Operator::I32ShrU, a[0], a[1], Type::I32);
                let v = self.un(Operator::I64ExtendI32U, r, Type::I64);
                self.def(inst, v);
            }
            Opcode::Cmp(repr, cc) => {
                use Operator::*;
                let o = match (repr, cc) {
                    (NumRepr::I32, Cc::Eq) => I32Eq,
                    (NumRepr::I32, Cc::Ne) => I32Ne,
                    (NumRepr::I32, Cc::Lt) => I32LtS,
                    (NumRepr::I32, Cc::Le) => I32LeS,
                    (NumRepr::I32, Cc::Gt) => I32GtS,
                    (NumRepr::I32, Cc::Ge) => I32GeS,
                    (NumRepr::Int, Cc::Eq) => I64Eq,
                    (NumRepr::Int, Cc::Ne) => I64Ne,
                    (NumRepr::Int, Cc::Lt) => I64LtS,
                    (NumRepr::Int, Cc::Le) => I64LeS,
                    (NumRepr::Int, Cc::Gt) => I64GtS,
                    (NumRepr::Int, Cc::Ge) => I64GeS,
                    (NumRepr::F64, Cc::Eq) => F64Eq,
                    (NumRepr::F64, Cc::Ne) => F64Ne,
                    (NumRepr::F64, Cc::Lt) => F64Lt,
                    (NumRepr::F64, Cc::Le) => F64Le,
                    (NumRepr::F64, Cc::Gt) => F64Gt,
                    (NumRepr::F64, Cc::Ge) => F64Ge,
                };
                let v = self.bin(o, a[0], a[1], Type::I32);
                self.def(inst, v);
            }
            Opcode::Math(MathFn::Abs) => {
                let v = self.un(Operator::F64Abs, a[0], Type::F64);
                self.def(inst, v);
            }
            Opcode::ToInt32 => {
                let x = match at(0) {
                    MType::Int(_) => self.un(Operator::F64ConvertI64S, a[0], Type::F64),
                    _ => a[0],
                };
                let v = self.to_int32(x);
                self.def(inst, v);
            }
            Opcode::JsToBool => {
                let v = self.to_bool(a[0]);
                self.def(inst, v);
            }

            // --- terminators ---
            Opcode::Jump => {
                let t = self.edge(inst, 0, &[])?;
                self.terminate(Terminator::Br { target: t });
            }
            Opcode::Br => {
                let (t, e) = (self.edge(inst, 0, &[])?, self.edge(inst, 1, &[])?);
                self.cond_br(a[0], t, e);
            }
            Opcode::Switch(n) => {
                let mut targets = vec![];
                for k in 0..n as usize {
                    targets.push(self.edge(inst, k, &[])?);
                }
                let default = self.edge(inst, n as usize, &[])?;
                self.terminate(Terminator::Select {
                    value: a[0],
                    targets,
                    default,
                });
            }
            Opcode::Return => {
                if let Some([layout, nfields, keep]) = self.ctor_stamp {
                    // `this` as the caller passed it: MIR never writes it.
                    let thisv = self.load_i64(self.sp, FrameLayout::THIS);
                    let (l, n, k) = (self.i32c(layout), self.i32c(nfields), self.i32c(keep));
                    self.call(self.h.ctor_stamp, &[thisv, l, n, k], &[]);
                }
                if let Some(r) = self.ctor_restamp {
                    let mut args = vec![self.load_i64(self.sp, FrameLayout::THIS)];
                    for x in r {
                        args.push(self.i32c(x));
                    }
                    self.call(self.h.ctor_restamp, &args, &[]);
                }
                self.store_i64(self.retval_out, 0, a[0]);
                let z = self.i32c(0);
                self.ret(z);
            }
            Opcode::Unreachable => self.terminate(Terminator::Unreachable),
            Opcode::Exit { pc, nargs, nlocals } | Opcode::ExitThrow { pc, nargs, nlocals } => {
                let mode = if matches!(d.op, Opcode::Exit { .. }) {
                    ResumeMode::Continue
                } else {
                    ResumeMode::Throw
                };
                let dead: Vec<bool> = d
                    .args
                    .iter()
                    .map(|&v| {
                        matches!(
                            self.f.values[v].def,
                            mir::func::ValueDef::Result(i, _)
                                if self.f.insts[i].op == Opcode::ConstVal(ConstVal::Dead)
                        )
                    })
                    .collect();
                let tys: Vec<MType> = d.args.iter().map(|&v| self.ty(v)).collect();
                self.exit(ResumeWord { pc, mode }, &a, &tys, &dead, nargs, nlocals)?;
            }
            Opcode::GuardUnbox(k) => {
                let v = a[0];
                let tag = self.tag_of(v);
                let (cond, out) = match k {
                    UnboxKind::I32 => {
                        let c = self.tag_is(tag, TAG_INT32 as u32);
                        (c, self.un(Operator::I32WrapI64, v, Type::I32))
                    }
                    UnboxKind::F64Num => {
                        let k = self.i32c(TAG_INT32 as u32);
                        let c = self.bin(Operator::I32LeU, tag, k, Type::I32);
                        (c, self.to_f64(v))
                    }
                    UnboxKind::Bool => {
                        let c = self.tag_is(tag, TAG_BOOLEAN as u32);
                        (c, self.un(Operator::I32WrapI64, v, Type::I32))
                    }
                    UnboxKind::Obj => {
                        let c = self.tag_is(tag, TAG_OBJECT as u32);
                        (c, self.un(Operator::I32WrapI64, v, Type::I32))
                    }
                    UnboxKind::Str => {
                        let c = self.tag_is(tag, TAG_STRING as u32);
                        (c, self.un(Operator::I32WrapI64, v, Type::I32))
                    }
                };
                self.guard(inst, cond, &[out])?;
            }
            Opcode::GuardTags(t) => {
                let c = self.has_tags(a[0], t);
                self.guard(inst, c, &[a[0]])?;
            }
            Opcode::F64ToIntExact => {
                let x = a[0];
                let i = self.un(Operator::I32TruncSatF64S, x, Type::I32);
                let back = self.un(Operator::F64ConvertI32S, i, Type::F64);
                let exact = self.bin(Operator::F64Eq, back, x, Type::I32);
                let bits = self.un(Operator::I64ReinterpretF64, x, Type::I64);
                let negz = self.i64c(1 << 63);
                let not_negz = self.bin(Operator::I64Ne, bits, negz, Type::I32);
                let ok = self.bin(Operator::I32And, exact, not_negz, Type::I32);
                self.guard(inst, ok, &[i])?;
            }
            Opcode::I32Ovf(op) => {
                let (x, y) = (a[0], a[1]);
                let (r, ok) = match op {
                    ArithOp::Add | ArithOp::Sub => {
                        let (o, wide) = if op == ArithOp::Add {
                            (Operator::I32Add, Operator::I64Add)
                        } else {
                            (Operator::I32Sub, Operator::I64Sub)
                        };
                        let r = self.bin(o, x, y, Type::I32);
                        let x64 = self.un(Operator::I64ExtendI32S, x, Type::I64);
                        let y64 = self.un(Operator::I64ExtendI32S, y, Type::I64);
                        let w = self.bin(wide, x64, y64, Type::I64);
                        let r64 = self.un(Operator::I64ExtendI32S, r, Type::I64);
                        (r, self.bin(Operator::I64Eq, w, r64, Type::I32))
                    }
                    ArithOp::Mul => {
                        let x64 = self.un(Operator::I64ExtendI32S, x, Type::I64);
                        let y64 = self.un(Operator::I64ExtendI32S, y, Type::I64);
                        let w = self.bin(Operator::I64Mul, x64, y64, Type::I64);
                        let r = self.un(Operator::I32WrapI64, w, Type::I32);
                        let r64 = self.un(Operator::I64ExtendI32S, r, Type::I64);
                        let fits = self.bin(Operator::I64Eq, w, r64, Type::I32);
                        // A zero product with a negative operand is -0.
                        let zero = self.un(Operator::I32Eqz, r, Type::I32);
                        let xy = self.bin(Operator::I32Or, x, y, Type::I32);
                        let z = self.i32c(0);
                        let neg = self.bin(Operator::I32LtS, xy, z, Type::I32);
                        let negz = self.bin(Operator::I32And, zero, neg, Type::I32);
                        let not_negz = self.un(Operator::I32Eqz, negz, Type::I32);
                        (r, self.bin(Operator::I32And, fits, not_negz, Type::I32))
                    }
                };
                self.guard(inst, ok, &[r])?;
            }
            Opcode::JsAdd
            | Opcode::JsBinop(_)
            | Opcode::JsUnop(_)
            | Opcode::JsCompare(_)
            | Opcode::JsToNumeric => {
                self.numeric_fast_arms(inst, &d.op, &a)?;
                self.js_op(inst, &d.op, &a)?
            }
            Opcode::JsTypeofEq(k) => {
                // A leaf: no GC, no JS.
                let kv = self.i32c(u32::from(k));
                let f = self.h.typeof_eq;
                let v = self.call1(f, &[self.cx, a[0], kv], Type::I32);
                self.def(inst, v);
            }
            Opcode::JsConstantStrictEq(k) => {
                // A leaf: no GC, no JS.
                let kv = self.i32c(u32::from(k));
                let f = self.h.constant_strict_eq;
                let v = self.call1(f, &[self.cx, a[0], kv], Type::I32);
                self.def(inst, v);
            }
            // The activation's environment is fixed (§5.1): the frame's env
            // slot, which the fresh entry (or baseline, before an onramp)
            // set, and which is rooted with the frame.
            Opcode::EnvCurrent => {
                let fid = self.cur_frame as usize;
                let env = self.load_i64(self.vp, self.frame_off[fid] + self.frame_layouts[fid].env());
                let p = self.un(Operator::I32WrapI64, env, Type::I32);
                self.def(inst, p);
            }
            // `EnvironmentObject::ENCLOSING_ENV_SLOT`, always fixed.
            Opcode::EnvParent => {
                let env = self.load_i64(a[0], FIXED_SLOTS_BASE);
                let p = self.un(Operator::I32WrapI64, env, Type::I32);
                self.def(inst, p);
            }
            Opcode::EnvLoad(slot) => {
                let addr = self.slot_addr(a[0], slot.get());
                let v = self.load_i64(addr, 0);
                self.def(inst, v);
            }
            Opcode::EnvStore(slot) => {
                // A leaf with its barriers: `setAliasedBinding` zero hops up.
                let env = self.box_tagged(TAG_OBJECT, a[0]);
                let (z, s) = (self.i32c(0), self.i32c(slot.get()));
                self.call(self.h.set_aliased, &[self.cx, env, z, s, a[1]], &[]);
            }
            Opcode::FrameStore(k) => {
                let fid = self.cur_frame as usize;
                let l = self.frame_layouts[fid];
                let (nargs, nlocals) = (l.nargs, l.nlocals);
                let off = self.frame_off[fid]
                    + match k {
                        0 => FrameLayout::THIS,
                        k if k <= nargs => l.arg(k - 1),
                        k if k <= nargs + nlocals => l.local(k - 1 - nargs),
                        _ => l.rval(),
                    };
                // The Value it is. A double goes in as a double (NaN made
                // canonical, as any boxed double must be), not re-tagged
                // as an int32: `box_number` is not needed for validity.
                let v = match at(0) {
                    MType::F64(_) => {
                        let bits = self.un(Operator::I64ReinterpretF64, a[0], Type::I64);
                        let nan = self.bin(Operator::F64Ne, a[0], a[0], Type::I32);
                        let canon = self.i64c(CANONICAL_NAN_BITS);
                        self.select(Type::I64, canon, bits, nan)
                    }
                    t => self.boxed(&t, a[0])?,
                };
                // `this` and the formals sit below the actuals (`sp`); the
                // rest of the function's frame, and inline frames, at `vp`.
                let base = if fid == 0 && k <= nargs { self.sp } else { self.vp };
                self.store_i64(base, off, v);
            }
            Opcode::JsLambda(index) => {
                let env = self.box_tagged(TAG_OBJECT, a[0]);
                let script = self.script_ptr();
                let i = self.i32c(index);
                let live = self.live_across(inst);
                let (ok, r) = self.gc_call(self.h.lambda, &[env, script, i], &live)?;
                let t = self.edge(inst, 0, &[r])?;
                let e = self.edge(inst, 1, &[])?;
                self.cond_br(ok, t, e);
            }
            Opcode::JsGetName(name) => {
                // `ok` and `err` (a static kill): not a clean/dirty op.
                if let Some(&bid) = self.gname_bids.get(&name) {
                    self.gname_fast_arms(inst, bid)?;
                }
                let at = self.atom(name);
                let z = self.i32c(0);
                let live = self.live_across(inst);
                let (ok, r) = self.gc_call(self.h.get_gname, &[at, z], &live)?;
                let t = self.edge(inst, 0, &[r])?;
                let e = self.edge(inst, 1, &[])?;
                self.cond_br(ok, t, e);
            }
            Opcode::JsGetProp(name) => {
                // The site's inline cache (as bbv's fact-free reads): the
                // shared probe `night_ic_get` (own and holder ways, then
                // the megamorphic table) takes `ok_clean` on a hit; a miss
                // runs the generic get and fills the site's ways.
                let at = self.atom(name);
                let cache = self.atoms.next_prop_cache();
                let way_base = self.i32c(IC_WAY_ADDR_PLACEHOLDER);
                self.prop_ic_patches.push((way_base, cache * INLINE_IC_STRIDE));
                let probe = self.body.add_block();
                self.get_ic_way0(inst, a[0], way_base, probe)?;
                self.cur = probe;
                let r = self.call(self.h.ic_get_poly, &[a[0], at, way_base], &[Type::I64]);
                let tag = self.tag_of(r);
                let miss = self.tag_is(tag, TAG_MAGIC as u32);
                let slow = self.body.add_block();
                let t = self.edge(inst, 0, &[r])?;
                self.cond_br(miss, Self::to(slow), t);
                self.cur = slow;
                let c = self.i32c(cache);
                self.js_call(inst, self.h.get_prop_ic_miss, &[a[0], at, c], false)?;
            }
            Opcode::JsSetProp(name, strict) => {
                // The site's inline cache, way 0 only: an overwrite of the
                // own slot the way describes, taking `ok_clean`. A miss
                // runs the generic set and fills the way.
                let at = self.atom(name);
                let cache = self.atoms.next_prop_cache();
                let way = self.i32c(IC_WAY_ADDR_PLACEHOLDER);
                self.prop_ic_patches.push((way, cache * INLINE_IC_STRIDE));
                let (trans, slow) = (self.body.add_block(), self.body.add_block());
                self.set_ic_way0(inst, a[0], a[1], way, trans)?;
                self.cur = trans;
                self.set_ic_trans(inst, name, a[0], a[1], way, slow)?;
                self.cur = slow;
                let (c, sv) = (self.i32c(cache), self.i32c(u32::from(strict)));
                self.js_call(inst, self.h.set_prop_ic_miss, &[a[0], at, a[1], c, sv], false)?;
            }
            Opcode::JsGetElem => {
                // An in-bounds, non-hole dense element of a native object
                // inline (as baseline does), taking `ok_clean`; everything
                // else through the helper.
                let slow = self.body.add_block();
                let v = self.dense_element(a[0], a[1], slow);
                let t = self.edge(inst, 0, &[v])?;
                self.terminate(Terminator::Br { target: t });
                self.cur = slow;
                self.js_call(inst, self.h.get_element, &[a[0], a[1]], false)?;
            }
            Opcode::JsSetElem(strict) => {
                // An in-bounds overwrite of a non-hole dense element inline,
                // taking `ok_clean`: an own writable data property unless
                // the elements are frozen. The store bypasses the engine,
                // so it also requires no RANGES on the object's word.
                let num = matches!(self.ty(d.args[2]), MType::Val(s) if s.tags.subset_of(TagSet::NUMBER));
                let slow = self.body.add_block();
                let (obj, elements, idx, addr, _) = self.dense_slot(a[0], a[1], slow);
                let back = self.i32c(ELEMENTS_FLAGS_BACK);
                let header = self.bin(Operator::I32Sub, elements, back, Type::I32);
                let flags = self.load_i32(header, 0);
                let fz = self.i32c(ELEMENTS_FROZEN_FLAG);
                let frozen = self.bin(Operator::I32And, flags, fz, Type::I32);
                let w = self.load_i32(obj, OBJ_CLASS_IDX_OFFSET);
                let rb = self.i32c(CLASS_WORD_RANGES);
                let ranges = self.bin(Operator::I32And, w, rb, Type::I32);
                let bad = self.bin(Operator::I32Or, frozen, ranges, Type::I32);
                let good = self.un(Operator::I32Eqz, bad, Type::I32);
                self.check(good, slow);
                if !num {
                    self.pre_barrier(addr, 0);
                }
                self.store_i64(addr, 0, a[2]);
                if !num {
                    let f = self.h.post_write_barrier_elem;
                    self.post_barrier(f, obj, idx, a[2]);
                }
                let t = self.edge(inst, 0, &[])?;
                self.terminate(Terminator::Br { target: t });
                self.cur = slow;
                let sv = self.i32c(u32::from(strict));
                self.js_call(inst, self.h.set_element, &[a[0], a[1], a[2], sv], false)?;
            }
            Opcode::Call => self.js_call_op(inst, &a)?,
            Opcode::GuardScript(sid) => {
                // The callee is a function of `sid`'s script, which is
                // compiled (§5.5): its class is a function class, its
                // script slot is that script (a native's slot never is),
                // and the script has a table index.
                let addr = *self
                    .mm
                    .script_addrs
                    .get(&sid)
                    .ok_or("lowering: guard.script without the script's address")?;
                let shape = self.load_i32(a[0], SHAPE_OFFSET);
                let base = self.load_i32(shape, SHAPE_BASESHAPE_OFFSET);
                let clasp = self.load_i32(base, BASESHAPE_CLASP_OFFSET);
                let slot = self.i32c(self.h.fn_class_slot);
                let fn_class = self.load_i32(slot, 0);
                let ext_class = self.load_i32(slot, 4);
                let is_fn = self.bin(Operator::I32Eq, clasp, fn_class, Type::I32);
                let is_ext = self.bin(Operator::I32Eq, clasp, ext_class, Type::I32);
                let is_function = self.bin(Operator::I32Or, is_fn, is_ext, Type::I32);
                let (fun_b, fail_b) = (self.body.add_block(), self.body.add_block());
                self.cond_br(is_function, Self::to(fun_b), Self::to(fail_b));
                self.cur = fun_b;
                let script = self.load_i32(a[0], FUNC_SCRIPT_SLOT_OFFSET);
                let want = self.i32c(addr);
                let same = self.bin(Operator::I32Eq, script, want, Type::I32);
                let idx_addr = self.i32c(addr);
                let idx = self.load_i32(idx_addr, BASESCRIPT_NIGHTFUNCINDEX_OFFSET);
                let z = self.i32c(0);
                let compiled = self.bin(Operator::I32Ne, idx, z, Type::I32);
                let ok = self.bin(Operator::I32And, same, compiled, Type::I32);
                let t = self.edge(inst, 0, &[a[0]])?;
                let e = self.edge(inst, 1, &[])?;
                self.cond_br(ok, t, e);
                self.cur = fail_b;
                let e = self.edge(inst, 1, &[])?;
                self.terminate(Terminator::Br { target: e });
            }
            Opcode::InlineEnter => self.inline_enter(&d, &a)?,
            Opcode::JsRt(r) => {
                use crate::mir::ops::RtOp;
                let h = self.h;
                let z = self.i32c(0);
                let (f, args) = match r {
                    RtOp::Instanceof => {
                        let cell = self.i32c(IOF_CELL_ADDR_PLACEHOLDER);
                        let idx = self.atoms.next_iof_cell();
                        self.iof_cell_patches.push((cell, idx + 1));
                        self.instanceof_arms(inst, a[0], a[1], cell)?;
                        (h.instanceof_, vec![a[0], a[1], cell])
                    }
                    RtOp::In => (h.in_, vec![a[0], a[1]]),
                    RtOp::HasOwn => (h.has_own, vec![a[0], a[1]]),
                    RtOp::DelProp(name, strict) => {
                        let (at, sv) = (self.atom(name), self.i32c(u32::from(strict)));
                        (h.del_prop, vec![a[0], at, sv])
                    }
                    RtOp::DelElem(strict) => {
                        let sv = self.i32c(u32::from(strict));
                        (h.del_elem, vec![a[0], a[1], sv])
                    }
                    RtOp::NewObject => (h.new_object, vec![z]),
                    RtOp::NewArray(len) => {
                        let lv = self.i32c(len);
                        (h.new_array, vec![lv, z])
                    }
                    RtOp::InitProp(name, attrs) => {
                        let (at, av, none) = (self.atom(name), self.i32c(attrs), self.i32c(u32::MAX));
                        (h.init_prop, vec![a[0], at, a[1], av, none])
                    }
                    RtOp::InitElem(attrs) => {
                        let av = self.i32c(attrs);
                        (h.init_elem, vec![a[0], a[1], a[2], av])
                    }
                };
                self.js_call(inst, f, &args, false)?;
            }
            Opcode::JsThrow => {
                // The helper sets the pending exception and always fails.
                // It may GC (capturing the stack): root what its throw exit
                // reads.
                let live = self.live_across(inst);
                self.spill(&live)?;
                let top_off = self.top_off(live.len());
                let top = self.add_off(self.vp, top_off);
                self.call(self.h.throw, &[self.cx, top, a[0]], &[]);
                self.reload(&live)?;
                let e = self.edge(inst, 0, &[])?;
                self.terminate(Terminator::Br { target: e });
            }
            Opcode::ArgsObject => {
                // The frame caches it, as baseline does, so both tiers
                // (and repeated reads) see one object.
                let l = self.layout;
                let cached = self.load_i64(self.vp, l.args_obj());
                let tag = self.tag_of(cached);
                let undef = self.tag_is(tag, TAG_UNDEFINED as u32);
                let (build, have) = (self.body.add_block(), self.body.add_block());
                self.cond_br(undef, Self::to(build), Self::to(have));
                self.cur = have;
                let t = self.edge(inst, 0, &[cached])?;
                self.terminate(Terminator::Br { target: t });
                self.cur = build;
                let live = self.live_across(inst);
                // With an environment, the runtime is given it, as
                // baseline's prologue does: a mapped object in a function
                // with a call object records it (`MaybeForwardToCallObject`).
                let (ok, r) = if self.plain_env || self.own_env {
                    let env = self.load_i64(self.vp, l.env());
                    self.gc_call(self.h.arguments_env, &[self.sp, self.argc, env], &live)?
                } else {
                    self.gc_call(self.h.arguments_, &[self.sp, self.argc], &live)?
                };
                let (store, e) = (self.body.add_block(), self.edge(inst, 1, &[])?);
                self.cond_br(ok, Self::to(store), e);
                self.cur = store;
                self.store_i64(self.vp, l.args_obj(), r);
                let t = self.edge(inst, 0, &[r])?;
                self.terminate(Terminator::Br { target: t });
            }
            Opcode::RestArray(n) => {
                let live = self.live_across(inst);
                let nv = self.i32c(n);
                let (ok, r) = self.gc_call(self.h.rest, &[self.sp, self.argc, nv], &live)?;
                let t = self.edge(inst, 0, &[r])?;
                let e = self.edge(inst, 1, &[])?;
                self.cond_br(ok, t, e);
            }
            Opcode::ArgsLength => self.def(inst, self.argc),
            Opcode::ActualArgOr(k) => {
                let v = self.load_i64(self.sp, FrameLayout::ARGS + 8 * k);
                let kv = self.i32c(k);
                let have = self.bin(Operator::I32LtU, kv, self.argc, Type::I32);
                let undef = self.i64c(UNDEF);
                let r = self.select(Type::I64, v, undef, have);
                self.def(inst, r);
            }
            Opcode::JsIsBuiltin(k) => {
                let cell = self.i32c(self.h.builtin_cells_base + 8 * k);
                let bits = self.load_i64(cell, 0);
                let r = self.bin(Operator::I64Eq, a[0], bits, Type::I32);
                self.def(inst, r);
            }
            Opcode::ApplyFwd => {
                self.js_call(inst, self.h.apply_fwd, &[a[0], a[1], a[2], self.sp, self.argc], false)?;
            }
            Opcode::ActualArg => {
                let eight = self.i32c(8);
                let off = self.bin(Operator::I32Mul, a[0], eight, Type::I32);
                let addr = self.bin(Operator::I32Add, self.sp, off, Type::I32);
                let v = self.load_i64(addr, FrameLayout::ARGS);
                self.def(inst, v);
            }
            Opcode::JsTypeof => {
                // A leaf: the type's name is an atom.
                let v = self.call(self.h.typeof_, &[self.cx, a[0]], &[Type::I64]);
                self.def(inst, v);
            }
            Opcode::ExitInline { pc, nargs, nlocals, throw } => {
                self.exit_inline(inst, &d, &a, pc, nargs, nlocals, throw)?
            }
            Opcode::Construct(nslots, word) => {
                // The frame `[callee, this, args…, new.target]` above the
                // rooting slots, then the runtime's construct (it creates
                // `this` sized and seeded for the site, and runs the
                // constructor). The result lands at the frame's top.
                let live = self.live_across(inst);
                self.spill(&live)?;
                let frame = self.top_off(live.len());
                for (k, &v) in a.iter().enumerate() {
                    self.store_i64(self.vp, frame + 8 * u32::try_from(k).unwrap(), v);
                }
                let argc = u32::try_from(a.len() - 3).unwrap();
                let top_off = frame + 8 * u32::try_from(a.len()).unwrap();
                let base = self.add_off(self.vp, frame);
                let top = self.add_off(self.vp, top_off);
                let (callee, new_target) = (a[0], a[a.len() - 1]);
                let join = self.body.add_block();
                let ok_p = self.body.add_blockparam(join, Type::I32);
                let res_p = self.body.add_blockparam(join, Type::I64);
                // Direct: a compiled constructor gets its `this` from
                // `create_this` (sized and stamped for the site) and runs
                // by a direct call, with no trip through the engine's
                // construct (bbv's direct construct, without its inline
                // allocation cell).
                const HEADROOM: u32 = 64 * 1024;
                let (funcidx, script) = self.classify(callee);
                let z = self.i32c(0);
                let compiled = self.bin(Operator::I32Ne, funcidx, z, Type::I32);
                let limit_addr = self.i32c(self.h.night_stack_limit_base);
                let limit = self.load_i32(limit_addr, 0);
                let hi = self.add_off(top, HEADROOM);
                let fits = self.bin(Operator::I32LeU, hi, limit, Type::I32);
                let maybe = self.bin(Operator::I32And, compiled, fits, Type::I32);
                let enabled = self.i32c(u32::from(DIRECT_CONSTRUCT));
                let maybe = self.bin(Operator::I32And, maybe, enabled, Type::I32);
                let (chk, generic) = (self.body.add_block(), self.body.add_block());
                self.cond_br(maybe, Self::to(chk), Self::to(generic));
                self.cur = chk;
                let fun = self.un(Operator::I32WrapI64, callee, Type::I32);
                let flags = self.load_i32(fun, FUNC_FLAGS_SLOT_OFFSET);
                let cbit = self.i32c(FUNCTION_FLAGS_CONSTRUCTOR);
                let is_ctor = self.bin(Operator::I32And, flags, cbit, Type::I32);
                let direct = self.body.add_block();
                self.cond_br(is_ctor, Self::to(direct), Self::to(generic));
                self.cur = direct;
                let made = self.construct_this(top, callee, new_target, nslots, word);
                let call_b = self.body.add_block();
                let undef = self.i64c(UNDEF);
                self.cond_br(
                    made,
                    Self::to(call_b),
                    BlockTarget {
                        block: join,
                        args: vec![made, undef],
                    },
                );
                self.cur = call_b;
                let thisv = self.load_i64(top, 0);
                self.store_i64(base, FrameLayout::THIS, thisv);
                // `create_this` may GC: the frame's copies are current, the
                // operands from before it are not.
                let new_target = self.load_i64(base, 8 * (argc + 2));
                let off = self.i32c(u32::MAX);
                self.body_off_patches.push(off);
                let body_idx = self.bin(Operator::I32Sub, funcidx, off, Type::I32);
                let av = self.i32c(argc);
                let args = self
                    .body
                    .arg_pool
                    .from_iter([self.cx, base, av, top, script, new_target, body_idx].into_iter());
                let tys = self.body.type_pool.from_iter([Type::I32, Type::I32].into_iter());
                let call = self.push_val(ValueDef::Operator(
                    Operator::CallIndirect {
                        sig_index: self.h.night_abi_sig2,
                        table_index: self.h.indirect_table,
                    },
                    args,
                    tys,
                ));
                let err = self.push_val(ValueDef::PickOutput(call, 0, Type::I32));
                let ok_d = self.un(Operator::I32Eqz, err, Type::I32);
                // The constructor's result if an object, else its `this`
                // (reread: the GC updates the frame).
                let r = self.load_i64(top, 0);
                let rt = self.tag_of(r);
                let obj = self.tag_is(rt, TAG_OBJECT as u32);
                let th = self.load_i64(base, FrameLayout::THIS);
                let res = self.select(Type::I64, r, th, obj);
                self.terminate(Terminator::Br {
                    target: BlockTarget {
                        block: join,
                        args: vec![ok_d, res],
                    },
                });
                self.cur = generic;
                let (av, nv, wv) = (self.i32c(argc), self.i32c(nslots), self.i32c(word));
                let ok = self.call1(self.h.construct, &[self.cx, top, base, av, nv, wv], Type::I32);
                let r = self.load_i64(top, 0);
                self.terminate(Terminator::Br {
                    target: BlockTarget {
                        block: join,
                        args: vec![ok, r],
                    },
                });
                self.cur = join;
                self.reload(&live)?;
                let t = self.edge(inst, 1, &[res_p])?;
                let e = self.edge(inst, 2, &[])?;
                self.cond_br(ok_p, t, e);
            }
            Opcode::GuardLayout { keys, types } => {
                // The stamp word (`JSObject*+4`): identity is layout key + 1
                // in the low 16 bits; TYPES is the SHALLOW bit (§4.3).
                let w = self.load_i32(a[0], OBJ_CLASS_IDX_OFFSET);
                let m = self.i32c(0xFFFF);
                let id = self.bin(Operator::I32And, w, m, Type::I32);
                let lo = self.i32c(keys.lo.get() + 1);
                let mut ok = if keys.lo == keys.hi {
                    self.bin(Operator::I32Eq, id, lo, Type::I32)
                } else {
                    let rel = self.bin(Operator::I32Sub, id, lo, Type::I32);
                    let span = self.i32c(keys.hi.get() - keys.lo.get());
                    self.bin(Operator::I32LeU, rel, span, Type::I32)
                };
                if types {
                    let bit = self.i32c(CLASS_WORD_SHALLOW);
                    let t = self.bin(Operator::I32And, w, bit, Type::I32);
                    let z = self.i32c(0);
                    let t = self.bin(Operator::I32Ne, t, z, Type::I32);
                    ok = self.bin(Operator::I32And, ok, t, Type::I32);
                }
                self.guard(inst, ok, &[a[0]])?;
            }
            Opcode::CheckFuse(fuse) => {
                let addr = self.mm.fuses[fuse].addr;
                if addr == 0 {
                    return Err(format!("lowering: {fuse} has no fuse word"));
                }
                let base = self.i32c(addr);
                let w = self.load_i32(base, 0);
                let one = self.i32c(1);
                let ok = self.bin(Operator::I32Eq, w, one, Type::I32);
                self.guard(inst, ok, &[])?;
            }
            Opcode::LoadField(name) => self.field_op(inst, name, a[0], None)?,
            Opcode::StoreField(name) => self.field_op(inst, name, a[0], Some(a[1]))?,
            Opcode::JsBoxThis => {
                self.js_call(inst, self.h.box_nonstrict_this, &[a[0]], false)?;
            }
            Opcode::JsBindGName(name) => {
                let at = self.atom(name);
                self.js_call(inst, self.h.bind_unqualified_gname, &[at], false)?;
            }
            Opcode::JsSetName(name, strict) => {
                if let Some(&bid) = self.gname_bids.get(&name).filter(|_| INLINE_GNAME_SETS) {
                    let fused = self.gname_fused.get(&name).copied();
                    self.gname_set_arms(inst, bid, a[1], fused)?;
                }
                let at = self.atom(name);
                let sv = self.i32c(u32::from(strict));
                self.js_call(inst, self.h.set_name, &[a[0], at, a[1], sv], false)?;
            }
            Opcode::ConstStr(name) => {
                // The atom's string, through the (may-GC) helper, with the
                // values live past this instruction rooted.
                let at = self.atom(name);
                let live = self.live_after(inst);
                let (_ok, r) = self.gc_call(self.h.string, &[at], &live)?;
                let v = self.un(Operator::I32WrapI64, r, Type::I32);
                self.def(inst, v);
            }
            op => {
                return Err(format!(
                    "lowering: {} is not lowered yet",
                    mir::print::mnemonic(&op)
                ))
            }
        }
        Ok(())
    }

    /// A fallible check: `ok` to the `ok` edge with `outs`, else `fail`.
    /// Under the stress mode, a guard whose failure exits also fails
    /// whenever the stress helper says so. (One whose failure merges back,
    /// a tag test, must keep its meaning.)
    fn guard(&mut self, inst: mir::Inst, ok: Value, outs: &[Value]) -> R<()> {
        let fail_blk = self.f.insts[inst].succs[1].block;
        let exits = self
            .f
            .terminator(fail_blk)
            .is_some_and(|t| self.f.insts[t].op.exit_shape().is_some());
        let ok = if self.stress == 0 || !exits {
            ok
        } else {
            let n = self.i32c(self.stress);
            let fail = self.call1(self.h.mir_stress, &[n], Type::I32);
            let pass = self.un(Operator::I32Eqz, fail, Type::I32);
            self.bin(Operator::I32And, ok, pass, Type::I32)
        };
        let t = self.edge(inst, 0, outs)?;
        let f = self.edge(inst, 1, &[])?;
        self.cond_br(ok, t, f);
        Ok(())
    }

    /// A generic JS op through its helper (`ok_clean`, `ok_dirty`, `err`).
    /// With no dynamic effect report yet, success takes `ok_dirty`, which
    /// is always sound.
    fn js_op(&mut self, inst: mir::Inst, op: &Opcode, a: &[Value]) -> R<()> {
        let h = self.h;
        let (f, args): (Func, Vec<Value>) = match *op {
            Opcode::JsAdd => (h.add, vec![a[0], a[1]]),
            Opcode::JsBinop(b) => {
                let kind = match b {
                    JsBinop::Sub => BINOP_SUB,
                    JsBinop::Mul => BINOP_MUL,
                    JsBinop::Div => BINOP_DIV,
                    JsBinop::Mod => BINOP_MOD,
                    JsBinop::BitAnd => BINOP_BITAND,
                    JsBinop::BitOr => BINOP_BITOR,
                    JsBinop::BitXor => BINOP_BITXOR,
                    JsBinop::Lsh => BINOP_LSH,
                    JsBinop::Rsh => BINOP_RSH,
                    JsBinop::Ursh => BINOP_URSH,
                    JsBinop::Pow => return self.js_call(inst, h.pow, &[a[0], a[1]], false),
                };
                let k = self.i32c(kind);
                (h.binop, vec![k, a[0], a[1]])
            }
            Opcode::JsUnop(u) => match u {
                JsUnop::Neg => (h.neg, vec![a[0]]),
                JsUnop::Pos => (h.pos, vec![a[0]]),
                JsUnop::BitNot | JsUnop::Inc | JsUnop::Dec => {
                    let kind = match u {
                        JsUnop::BitNot => BINOP_BITNOT,
                        JsUnop::Inc => BINOP_INC,
                        _ => BINOP_DEC,
                    };
                    let k = self.i32c(kind);
                    (h.binop, vec![k, a[0], a[0]])
                }
            },
            Opcode::JsCompare(cc) => {
                if matches!(cc, JsCc::Eq | JsCc::Ne | JsCc::StrictEq | JsCc::StrictNe) {
                    self.equality_fast_arm(inst, cc, a[0], a[1])?;
                }
                let kind = match cc {
                    JsCc::Eq => CMP_EQ,
                    JsCc::Ne => CMP_NE,
                    JsCc::StrictEq => CMP_STRICTEQ,
                    JsCc::StrictNe => CMP_STRICTNE,
                    JsCc::Lt => CMP_LT,
                    JsCc::Le => CMP_LE,
                    JsCc::Gt => CMP_GT,
                    JsCc::Ge => CMP_GE,
                };
                let k = self.i32c(kind);
                return self.js_call(inst, h.compare, &[k, a[0], a[1]], true);
            }
            Opcode::JsToNumeric => (h.tonumeric, vec![a[0]]),
            _ => unreachable!(),
        };
        self.js_call(inst, f, &args, false)
    }

    /// The inline arms of a read of syntactic global binding `bid` (bbv's
    /// `emit_get_gname_inline_guarded`), each taking the op's `ok` edge:
    /// the binding's value-fuse cell while armed; else its cached slot row
    /// while the global's shape is the one the row was resolved against;
    /// else the resolve leaf (no GC) and the slot. Falls through to the
    /// generic helper when the binding is not cacheable (lexicals, TDZ).
    fn gname_fast_arms(&mut self, inst: mir::Inst, bid: u32) -> R<()> {
        let vals = self.i32c(self.h.global_vals_base + 16 * bid);
        let fw = self.load_i32(vals, 8);
        let one = self.i32c(1);
        let armed = self.bin(Operator::I32Eq, fw, one, Type::I32);
        let (hit_b, slots_b) = (self.body.add_block(), self.body.add_block());
        self.cond_br(armed, Self::to(hit_b), Self::to(slots_b));
        self.cur = hit_b;
        let v = self.load_i64(vals, 0);
        let t = self.edge(inst, 0, &[v])?;
        self.terminate(Terminator::Br { target: t });

        self.cur = slots_b;
        let base = self.i32c(self.h.global_slots_base);
        let entry0 = self.load_i32(base, 8 * bid);
        let shape0 = self.load_i32(base, 8 * bid + 4);
        let resolved0 = self.bin(Operator::I32And, entry0, one, Type::I32);
        let realm = self.load_i32(self.cx, JSCONTEXT_REALM_OFFSET);
        let global = self.load_i32(realm, REALM_GLOBAL_OFFSET);
        let live = self.load_i32(global, SHAPE_OFFSET);
        let same = self.bin(Operator::I32Eq, shape0, live, Type::I32);
        let hit = self.bin(Operator::I32And, resolved0, same, Type::I32);
        let use_b = self.body.add_block();
        let entry = self.body.add_blockparam(use_b, Type::I32);
        let resolve_b = self.body.add_block();
        self.cond_br(hit, BlockTarget { block: use_b, args: vec![entry0] }, Self::to(resolve_b));

        self.cur = resolve_b;
        let b = self.i32c(bid);
        let entry1 = self.call1(self.h.resolve_global_slot_guarded, &[self.cx, b], Type::I32);
        let resolved1 = self.bin(Operator::I32And, entry1, one, Type::I32);
        let slow = self.body.add_block();
        self.cond_br(resolved1, BlockTarget { block: use_b, args: vec![entry1] }, Self::to(slow));

        // The entry: bit 1 selects the dynamic slots, `entry & !7` is the
        // byte offset from that base (past the fixed-slot header when
        // fixed).
        self.cur = use_b;
        let sh = self.bin(Operator::I32ShrU, entry, one, Type::I32);
        let dynamic = self.bin(Operator::I32And, sh, one, Type::I32);
        let m = self.i32c(!7);
        let idx8 = self.bin(Operator::I32And, entry, m, Type::I32);
        let z = self.i32c(0);
        let fb = self.i32c(FIXED_SLOTS_BASE);
        let add = self.select(Type::I32, z, fb, dynamic);
        let off = self.bin(Operator::I32Add, idx8, add, Type::I32);
        let slots = self.load_i32(global, NATIVE_SLOTS_OFFSET);
        let slot_base = self.select(Type::I32, slots, global, dynamic);
        let addr = self.bin(Operator::I32Add, slot_base, off, Type::I32);
        let v = self.load_i64(addr, 0);
        let t = self.edge(inst, 0, &[v])?;
        self.terminate(Terminator::Br { target: t });
        self.cur = slow;
        Ok(())
    }

    /// The inline arm of a write to syntactic global binding `bid` (bbv's
    /// `emit_set_name_inline_guarded`), taking `ok_clean`: with the
    /// binding's slot row resolved against the global's live shape (or
    /// re-resolved by the leaf) and writable, store `val` with barriers,
    /// then keep the binding's value fuse, the bind epoch and a fused
    /// literal's fuse as the generic store would. Falls through to the
    /// helper otherwise (accessors, lexicals, read-only, undeclared).
    fn gname_set_arms(
        &mut self,
        inst: mir::Inst,
        bid: u32,
        val: Value,
        fused: Option<crate::wasm::translate::FusedGname>,
    ) -> R<()> {
        let base = self.i32c(self.h.global_slots_base);
        let entry0 = self.load_i32(base, 8 * bid);
        let shape0 = self.load_i32(base, 8 * bid + 4);
        let one = self.i32c(1);
        let two = self.i32c(2);
        let writable = |l: &mut Self, e: Value| {
            let r = l.bin(Operator::I32And, e, one, Type::I32);
            let sh = l.bin(Operator::I32ShrU, e, two, Type::I32);
            let w = l.bin(Operator::I32And, sh, one, Type::I32);
            l.bin(Operator::I32And, r, w, Type::I32)
        };
        let rw0 = writable(self, entry0);
        let realm = self.load_i32(self.cx, JSCONTEXT_REALM_OFFSET);
        let global = self.load_i32(realm, REALM_GLOBAL_OFFSET);
        let live = self.load_i32(global, SHAPE_OFFSET);
        let same = self.bin(Operator::I32Eq, shape0, live, Type::I32);
        let hit = self.bin(Operator::I32And, rw0, same, Type::I32);
        let use_b = self.body.add_block();
        let entry = self.body.add_blockparam(use_b, Type::I32);
        let resolve_b = self.body.add_block();
        self.cond_br(hit, BlockTarget { block: use_b, args: vec![entry0] }, Self::to(resolve_b));
        self.cur = resolve_b;
        let b = self.i32c(bid);
        let entry1 = self.call1(self.h.resolve_global_slot_guarded, &[self.cx, b], Type::I32);
        let rw1 = writable(self, entry1);
        let slow = self.body.add_block();
        self.cond_br(rw1, BlockTarget { block: use_b, args: vec![entry1] }, Self::to(slow));

        self.cur = use_b;
        // Entry: bit 1 selects the dynamic slots, `entry & !7` is the byte
        // offset from that base, `entry >> 3` the slot index within it.
        let sh = self.bin(Operator::I32ShrU, entry, one, Type::I32);
        let dynamic = self.bin(Operator::I32And, sh, one, Type::I32);
        let m = self.i32c(!7);
        let idx8 = self.bin(Operator::I32And, entry, m, Type::I32);
        let z = self.i32c(0);
        let fb = self.i32c(FIXED_SLOTS_BASE);
        let add = self.select(Type::I32, z, fb, dynamic);
        let off = self.bin(Operator::I32Add, idx8, add, Type::I32);
        let slots = self.load_i32(global, NATIVE_SLOTS_OFFSET);
        let slot_base = self.select(Type::I32, slots, global, dynamic);
        let addr = self.bin(Operator::I32Add, slot_base, off, Type::I32);
        self.pre_barrier(addr, 0);
        self.store_i64(addr, 0, val);
        let three = self.i32c(3);
        let idx = self.bin(Operator::I32ShrU, entry, three, Type::I32);
        let flags = self.load_i32(live, SHAPE_IMMUTABLE_FLAGS_OFFSET);
        let fs = self.i32c(SHAPE_FIXED_SLOTS_SHIFT);
        let nf = self.bin(Operator::I32ShrU, flags, fs, Type::I32);
        let fm = self.i32c(SHAPE_FIXED_SLOTS_MASK_BITS);
        let nfixed = self.bin(Operator::I32And, nf, fm, Type::I32);
        let idx_plus = self.bin(Operator::I32Add, idx, nfixed, Type::I32);
        let abs = self.select(Type::I32, idx_plus, idx, dynamic);
        self.post_barrier(self.h.post_write_barrier, global, abs, val);
        // The binding's value fuse (`gGlobalVals[bid]`): an armed cell whose
        // value changes mirrors a non-GC value in place, and otherwise is
        // unarmed with the re-arm left to the runtime (bbv's
        // `emit_blow_binding_value_fuse`).
        let vals = self.i32c(self.h.global_vals_base + 16 * bid);
        let fw = self.load_i32(vals, 8);
        let armed = self.bin(Operator::I32Eq, fw, one, Type::I32);
        let old = self.load_i64(vals, 0);
        let changed = self.bin(Operator::I64Ne, old, val, Type::I32);
        let blow = self.bin(Operator::I32And, armed, changed, Type::I32);
        let (blow_b, cont) = (self.body.add_block(), self.body.add_block());
        self.cond_br(blow, Self::to(blow_b), Self::to(cont));
        self.cur = blow_b;
        let tag = self.tag_of(val);
        let st = self.i32c(TAG_STRING as u32);
        let is_gc = self.bin(Operator::I32GeU, tag, st, Type::I32);
        let (gc_b, plain_b) = (self.body.add_block(), self.body.add_block());
        self.cond_br(is_gc, Self::to(gc_b), Self::to(plain_b));
        self.cur = plain_b;
        self.store_i64(vals, 0, val);
        self.terminate(Terminator::Br { target: Self::to(cont) });
        self.cur = gc_b;
        let z = self.i32c(0);
        self.store_i32(vals, 8, z);
        let b = self.i32c(bid);
        self.call(self.h.binding_written, &[b], &[]);
        self.terminate(Terminator::Br { target: Self::to(cont) });
        self.cur = cont;
        // The bind epoch.
        let slot = self.i32c(self.h.strlit_slot + crate::region_shape::STRLIT_BIND_EPOCH_ADDR_OFF);
        let ep = self.load_i32(slot, 0);
        let e = self.load_i32(ep, 0);
        let e1 = self.bin(Operator::I32Add, e, one, Type::I32);
        self.store_i32(ep, 0, e1);
        // A fused literal's fuse: the literal arms it, anything else blows
        // it.
        if let Some(fg) = fused {
            let fa = self.i32c(fg.fuse_addr);
            let f = self.load_i32(fa, 0);
            let lit = self.i64c(fg.boxed);
            let neq = self.bin(Operator::I64Ne, val, lit, Type::I32);
            let z = self.i32c(0);
            let is_zero = self.bin(Operator::I32Eq, f, z, Type::I32);
            let armed = self.select(Type::I32, one, f, is_zero);
            let nf = self.select(Type::I32, two, armed, neq);
            self.store_i32(fa, 0, nf);
        }
        let t = self.edge(inst, 0, &[])?;
        self.terminate(Terminator::Br { target: t });
        self.cur = slow;
        Ok(())
    }

    /// The inline arms of a generic numeric op, as baseline's (and the
    /// portable baseline interpreter's) are: all-int32 operands, then all
    /// numbers as doubles, each taking `ok_clean` with the boxed result (a
    /// bool for a compare); otherwise falls through to the helper. Without
    /// them MIR would run code whose types it does not know slower than
    /// baseline does. Emits nothing for an op with no arm.
    fn numeric_fast_arms(&mut self, inst: mir::Inst, op: &Opcode, a: &[Value]) -> R<()> {
        use Operator as O;
        #[derive(Clone, Copy)]
        enum Int {
            Checked(O, O),
            Mul,
            Plain(O),
            Mod,
            Ursh,
            Step(O, u32),
            Neg,
            BitNot,
            Same,
            Cmp(O),
        }
        #[derive(Clone, Copy)]
        enum Num {
            Bin(O),
            Step(O),
            Neg,
            Same,
            Cmp(O),
        }
        let (n, int, num): (usize, Option<Int>, Option<Num>) = match *op {
            Opcode::JsAdd => (2, Some(Int::Checked(O::I32Add, O::I64Add)), Some(Num::Bin(O::F64Add))),
            Opcode::JsBinop(b) => match b {
                JsBinop::Sub => (2, Some(Int::Checked(O::I32Sub, O::I64Sub)), Some(Num::Bin(O::F64Sub))),
                JsBinop::Mul => (2, Some(Int::Mul), Some(Num::Bin(O::F64Mul))),
                JsBinop::Div => (2, None, Some(Num::Bin(O::F64Div))),
                // Double `%` is fmod, which Wasm lacks.
                JsBinop::Mod => (2, Some(Int::Mod), None),
                JsBinop::BitAnd => (2, Some(Int::Plain(O::I32And)), None),
                JsBinop::BitOr => (2, Some(Int::Plain(O::I32Or)), None),
                JsBinop::BitXor => (2, Some(Int::Plain(O::I32Xor)), None),
                // Wasm masks shift counts to 5 bits, as JS does.
                JsBinop::Lsh => (2, Some(Int::Plain(O::I32Shl)), None),
                JsBinop::Rsh => (2, Some(Int::Plain(O::I32ShrS)), None),
                JsBinop::Ursh => (2, Some(Int::Ursh), None),
                JsBinop::Pow => return Ok(()),
            },
            Opcode::JsUnop(u) => match u {
                JsUnop::Inc => (1, Some(Int::Step(O::I32Add, i32::MAX as u32)), Some(Num::Step(O::F64Add))),
                JsUnop::Dec => (1, Some(Int::Step(O::I32Sub, i32::MIN as u32)), Some(Num::Step(O::F64Sub))),
                JsUnop::Neg => (1, Some(Int::Neg), Some(Num::Neg)),
                JsUnop::BitNot => (1, Some(Int::BitNot), None),
                JsUnop::Pos => (1, Some(Int::Same), Some(Num::Same)),
            },
            Opcode::JsToNumeric => (1, Some(Int::Same), Some(Num::Same)),
            Opcode::JsCompare(cc) => {
                let (i, f) = match cc {
                    JsCc::Lt => (O::I32LtS, O::F64Lt),
                    JsCc::Le => (O::I32LeS, O::F64Le),
                    JsCc::Gt => (O::I32GtS, O::F64Gt),
                    JsCc::Ge => (O::I32GeS, O::F64Ge),
                    _ => return Ok(()),
                };
                (2, Some(Int::Cmp(i)), Some(Num::Cmp(f)))
            }
            _ => return Ok(()),
        };
        let ops = &a[..n];
        let slow = self.body.add_block();
        let num_b = if num.is_some() { self.body.add_block() } else { slow };
        if let Some(int) = int {
            let mut all = self.i32c(1);
            for &v in ops {
                let t = self.tag_of(v);
                let is = self.tag_is(t, TAG_INT32 as u32);
                all = self.bin(O::I32And, all, is, Type::I32);
            }
            let int_b = self.body.add_block();
            self.cond_br(all, Self::to(int_b), Self::to(num_b));
            self.cur = int_b;
            let x = self.un(O::I32WrapI64, ops[0], Type::I32);
            let y = if n == 2 { self.un(O::I32WrapI64, ops[1], Type::I32) } else { x };
            let one = self.i32c(1);
            let (r, ok) = match int {
                Int::Checked(o, wide) => {
                    let r = self.bin(o, x, y, Type::I32);
                    let x64 = self.un(O::I64ExtendI32S, x, Type::I64);
                    let y64 = self.un(O::I64ExtendI32S, y, Type::I64);
                    let w = self.bin(wide, x64, y64, Type::I64);
                    let r64 = self.un(O::I64ExtendI32S, r, Type::I64);
                    (r, self.bin(O::I64Eq, w, r64, Type::I32))
                }
                Int::Mul => {
                    let x64 = self.un(O::I64ExtendI32S, x, Type::I64);
                    let y64 = self.un(O::I64ExtendI32S, y, Type::I64);
                    let w = self.bin(O::I64Mul, x64, y64, Type::I64);
                    let r = self.un(O::I32WrapI64, w, Type::I32);
                    let r64 = self.un(O::I64ExtendI32S, r, Type::I64);
                    let fits = self.bin(O::I64Eq, w, r64, Type::I32);
                    // A zero product with a negative operand is -0.
                    let zero = self.un(O::I32Eqz, r, Type::I32);
                    let xy = self.bin(O::I32Or, x, y, Type::I32);
                    let z = self.i32c(0);
                    let neg = self.bin(O::I32LtS, xy, z, Type::I32);
                    let negz = self.bin(O::I32And, zero, neg, Type::I32);
                    let not_negz = self.un(O::I32Eqz, negz, Type::I32);
                    (r, self.bin(O::I32And, fits, not_negz, Type::I32))
                }
                Int::Plain(o) => (self.bin(o, x, y, Type::I32), one),
                // A non-negative dividend and a positive divisor: the
                // result is the unsigned remainder, never -0.
                Int::Mod => {
                    let z = self.i32c(0);
                    let xn = self.bin(O::I32GeS, x, z, Type::I32);
                    let yp = self.bin(O::I32GtS, y, z, Type::I32);
                    let ok = self.bin(O::I32And, xn, yp, Type::I32);
                    // The divisor is forced to 1 off the arm, so the
                    // remainder never traps.
                    let d = self.select(Type::I32, y, one, yp);
                    (self.bin(O::I32RemU, x, d, Type::I32), ok)
                }
                // Only a result below 2^31 is an int32.
                Int::Ursh => {
                    let r = self.bin(O::I32ShrU, x, y, Type::I32);
                    let z = self.i32c(0);
                    (r, self.bin(O::I32GeS, r, z, Type::I32))
                }
                Int::Step(o, limit) => {
                    let l = self.i32c(limit);
                    let ok = self.bin(O::I32Ne, x, l, Type::I32);
                    (self.bin(o, x, one, Type::I32), ok)
                }
                // Neg of 0 is -0 and of INT32_MIN overflows.
                Int::Neg => {
                    let z = self.i32c(0);
                    let min = self.i32c(i32::MIN as u32);
                    let nz = self.bin(O::I32Ne, x, z, Type::I32);
                    let nm = self.bin(O::I32Ne, x, min, Type::I32);
                    let ok = self.bin(O::I32And, nz, nm, Type::I32);
                    (self.bin(O::I32Sub, z, x, Type::I32), ok)
                }
                Int::BitNot => {
                    let m1 = self.i32c(u32::MAX);
                    (self.bin(O::I32Xor, x, m1, Type::I32), one)
                }
                Int::Same => (x, one),
                Int::Cmp(o) => (self.bin(o, x, y, Type::I32), one),
            };
            let out = if matches!(int, Int::Cmp(_)) { r } else { self.box_tagged(TAG_INT32, r) };
            let t = self.edge(inst, 0, &[out])?;
            self.cond_br(ok, t, Self::to(num_b));
        } else {
            self.terminate(Terminator::Br { target: Self::to(num_b) });
        }
        if let Some(num) = num {
            self.cur = num_b;
            let mut all = self.i32c(1);
            for &v in ops {
                let t = self.tag_of(v);
                let int = self.tag_is(t, TAG_INT32 as u32);
                let clear = self.i32c(TAG_CLEAR);
                let dbl = self.bin(O::I32LtU, t, clear, Type::I32);
                let is = self.bin(O::I32Or, int, dbl, Type::I32);
                all = self.bin(O::I32And, all, is, Type::I32);
            }
            let go = self.body.add_block();
            self.cond_br(all, Self::to(go), Self::to(slow));
            self.cur = go;
            let x = self.to_f64(ops[0]);
            let y = if n == 2 { self.to_f64(ops[1]) } else { x };
            let out = match num {
                Num::Bin(o) => {
                    let r = self.bin(o, x, y, Type::F64);
                    self.box_number(r)
                }
                Num::Step(o) => {
                    let one = self.f64c(1f64.to_bits());
                    let r = self.bin(o, x, one, Type::F64);
                    self.box_number(r)
                }
                Num::Neg => {
                    let r = self.un(O::F64Neg, x, Type::F64);
                    self.box_number(r)
                }
                Num::Same => ops[0],
                Num::Cmp(o) => self.bin(o, x, y, Type::I32),
            };
            let t = self.edge(inst, 0, &[out])?;
            self.terminate(Terminator::Br { target: t });
        }
        self.cur = slow;
        Ok(())
    }

    /// Whether an object that emulates `undefined` (`document.all`) may
    /// exist: the runtime's fuse word, nonzero once one's class is seen.
    fn dda_possible(&mut self) -> Value {
        let slot = self.i32c(self.h.dda_fuse_addr_slot);
        let addr = self.load_i32(slot, 0);
        self.load_i32(addr, 0)
    }

    /// ToBoolean of boxed `v`, inline for int32, boolean, null, undefined
    /// and (while no object emulates `undefined`) objects; the leaf helper
    /// otherwise.
    fn to_bool(&mut self, v: Value) -> Value {
        let join = self.body.add_block();
        let r = self.body.add_blockparam(join, Type::I32);
        let tag = self.tag_of(v);
        let low = self.un(Operator::I32WrapI64, v, Type::I32);
        // int32 and boolean: the payload.
        let int = self.tag_is(tag, TAG_INT32 as u32);
        let boolean = self.tag_is(tag, TAG_BOOLEAN as u32);
        let payload = self.bin(Operator::I32Or, int, boolean, Type::I32);
        let nz = self.i32c(0);
        let low_t = self.bin(Operator::I32Ne, low, nz, Type::I32);
        let next = self.body.add_block();
        self.cond_br(payload, BlockTarget { block: join, args: vec![low_t] }, Self::to(next));
        self.cur = next;
        let null = self.tag_is(tag, TAG_NULL as u32);
        let undef = self.tag_is(tag, TAG_UNDEFINED as u32);
        let nullish = self.bin(Operator::I32Or, null, undef, Type::I32);
        let zero = self.i32c(0);
        let next = self.body.add_block();
        self.cond_br(nullish, BlockTarget { block: join, args: vec![zero] }, Self::to(next));
        self.cur = next;
        let obj = self.tag_is(tag, TAG_OBJECT as u32);
        let (obj_blk, slow) = (self.body.add_block(), self.body.add_block());
        self.cond_br(obj, Self::to(obj_blk), Self::to(slow));
        self.cur = obj_blk;
        let dda = self.dda_possible();
        let one = self.i32c(1);
        self.cond_br(dda, Self::to(slow), BlockTarget { block: join, args: vec![one] });
        self.cur = slow;
        // A leaf: no GC, no JS.
        let t = self.call1(self.h.to_boolean, &[self.cx, v], Type::I32);
        self.terminate(Terminator::Br { target: BlockTarget { block: join, args: vec![t] } });
        self.cur = join;
        r
    }

    /// The inline arm of an equality compare, taking `ok_clean` with the
    /// result where the operands decide it by their bits: strictly, when
    /// neither is a double, string or BigInt (so equal values have equal
    /// bits); loosely, when both are int32s or both booleans, or both are
    /// null, undefined or an object while no object emulates `undefined`
    /// (then null and undefined are equal to each other and nothing else,
    /// and objects by identity). Otherwise falls through to the helper.
    fn equality_fast_arm(&mut self, inst: mir::Inst, cc: JsCc, a: Value, b: Value) -> R<()> {
        let (ta, tb) = (self.tag_of(a), self.tag_of(b));
        let bits_eq = self.bin(Operator::I64Eq, a, b, Type::I32);
        let fast = self.body.add_block();
        let slow = self.body.add_block();
        let r = match cc {
            JsCc::StrictEq | JsCc::StrictNe => {
                // int32, boolean, undefined, null (consecutive tags), symbol
                // or object.
                let simple = |l: &mut Self, t: Value| {
                    let lo = l.i32c(TAG_INT32 as u32);
                    let rel = l.bin(Operator::I32Sub, t, lo, Type::I32);
                    let three = l.i32c(3);
                    let prim = l.bin(Operator::I32LeU, rel, three, Type::I32);
                    let sym = l.tag_is(t, TAG_SYMBOL as u32);
                    let obj = l.tag_is(t, TAG_OBJECT as u32);
                    let x = l.bin(Operator::I32Or, prim, sym, Type::I32);
                    l.bin(Operator::I32Or, x, obj, Type::I32)
                };
                let (sa, sb) = (simple(self, ta), simple(self, tb));
                let both = self.bin(Operator::I32And, sa, sb, Type::I32);
                self.cond_br(both, Self::to(fast), Self::to(slow));
                self.cur = fast;
                bits_eq
            }
            _ => {
                let same = self.bin(Operator::I32Eq, ta, tb, Type::I32);
                let int = self.tag_is(ta, TAG_INT32 as u32);
                let boolean = self.tag_is(ta, TAG_BOOLEAN as u32);
                let ib = self.bin(Operator::I32Or, int, boolean, Type::I32);
                let same_ib = self.bin(Operator::I32And, same, ib, Type::I32);
                let nullish = |l: &mut Self, t: Value| {
                    let null = l.tag_is(t, TAG_NULL as u32);
                    let undef = l.tag_is(t, TAG_UNDEFINED as u32);
                    l.bin(Operator::I32Or, null, undef, Type::I32)
                };
                let (na, nb) = (nullish(self, ta), nullish(self, tb));
                let oa = self.tag_is(ta, TAG_OBJECT as u32);
                let ob = self.tag_is(tb, TAG_OBJECT as u32);
                let ka = self.bin(Operator::I32Or, na, oa, Type::I32);
                let kb = self.bin(Operator::I32Or, nb, ob, Type::I32);
                let both_k = self.bin(Operator::I32And, ka, kb, Type::I32);
                let (ib_blk, k_blk) = (self.body.add_block(), self.body.add_block());
                self.cond_br(same_ib, Self::to(ib_blk), Self::to(k_blk));
                self.cur = ib_blk;
                self.terminate(Terminator::Br { target: Self::to(fast) });
                self.cur = k_blk;
                let dda_blk = self.body.add_block();
                self.cond_br(both_k, Self::to(dda_blk), Self::to(slow));
                self.cur = dda_blk;
                let dda = self.dda_possible();
                self.cond_br(dda, Self::to(slow), Self::to(fast));
                self.cur = fast;
                let both_n = self.bin(Operator::I32And, na, nb, Type::I32);
                self.bin(Operator::I32Or, bits_eq, both_n, Type::I32)
            }
        };
        let r = if matches!(cc, JsCc::Ne | JsCc::StrictNe) {
            self.un(Operator::I32Eqz, r, Type::I32)
        } else {
            r
        };
        let t = self.edge(inst, 0, &[r])?;
        self.terminate(Terminator::Br { target: t });
        self.cur = slow;
        Ok(())
    }

    /// Call `f` rooted; on success take `ok_dirty` with the result (its
    /// boolean payload if `bool_out`), else `err`.
    fn js_call(&mut self, inst: mir::Inst, f: Func, args: &[Value], bool_out: bool) -> R<()> {
        let live = self.live_across(inst);
        let (ok, result) = self.gc_call(f, args, &live)?;
        let out = if bool_out {
            self.un(Operator::I32WrapI64, result, Type::I32)
        } else {
            result
        };
        let t = self.edge(inst, 1, &[out])?;
        let e = self.edge(inst, 2, &[])?;
        self.cond_br(ok, t, e);
        Ok(())
    }

    /// `load_field`/`store_field` (§4.3): with the stamp's SLOTS bit set,
    /// the field is in its predicted fixed slot, accessed directly (the
    /// `ok_clean` edge). Otherwise the generic property helper does it,
    /// staying in MIR (`ok_dirty`, or `err`). A store takes the fixed slot
    /// only where it keeps the stamp's bits true (see below), with GC
    /// barriers unless the value is a number.
    fn field_op(
        &mut self,
        inst: mir::Inst,
        name: mir::entity::AtomId,
        obj: Value,
        val: Option<Value>,
    ) -> R<()> {
        let recv_ty = self.ty(self.f.insts[inst].args[0]);
        let keys = recv_ty
            .obj_info()
            .and_then(|o| o.layout)
            .ok_or("lowering: a field op without a layout claim")?
            .keys;
        let slot = self
            .mm
            .layouts
            .get(&keys.lo)
            .and_then(|l| l.field(name))
            .ok_or("lowering: a field op on an undescribed field")?
            .0;
        let slot = u32::try_from(slot).unwrap();
        let off = FIXED_SLOTS_BASE + 8 * slot;
        // A store of anything but a number: may overwrite or write a GC
        // thing (barriers), and would falsify a TYPES claim.
        let num = val.is_some()
            && matches!(self.ty(self.f.insts[inst].args[1]), MType::Val(s) if s.tags.subset_of(TagSet::NUMBER));
        let w = self.load_i32(obj, OBJ_CLASS_IDX_OFFSET);
        let fast_ok = if val.is_none() {
            let bit = self.i32c(CLASS_WORD_SLOTS);
            self.bin(Operator::I32And, w, bit, Type::I32)
        } else {
            // A store keeps the object's validity bits true only if it
            // cannot break them: TYPES survives a number store only (a
            // MIR claim may rest on it; the engine maintains it), and
            // RANGES, consumed checklessly but by no MIR claim, is dropped
            // on the way (`drop_ranges`).
            let mask = CLASS_WORD_SLOTS | if num { 0 } else { CLASS_WORD_SHALLOW };
            let m = self.i32c(mask);
            let bits = self.bin(Operator::I32And, w, m, Type::I32);
            let want = self.i32c(CLASS_WORD_SLOTS);
            self.bin(Operator::I32Eq, bits, want, Type::I32)
        };
        let (fast, slow) = (self.body.add_block(), self.body.add_block());
        self.cond_br(fast_ok, Self::to(fast), Self::to(slow));

        self.cur = fast;
        let outs = match val {
            None => vec![self.load_i64(obj, off)],
            Some(v) => {
                self.clear_bits(obj, w, CLASS_WORD_RANGES);
                if !num {
                    self.pre_barrier(obj, off);
                }
                self.store_i64(obj, off, v);
                if !num {
                    let s = self.i32c(slot);
                    self.post_barrier(self.h.post_write_barrier, obj, s, v);
                }
                vec![]
            }
        };
        let t = self.edge(inst, 0, &outs)?;
        self.terminate(Terminator::Br { target: t });

        self.cur = slow;
        let boxed = self.box_tagged(TAG_OBJECT, obj);
        let at = self.atom(name);
        let live = self.live_across(inst);
        let (ok, r) = match val {
            None => self.gc_call(self.h.get_property, &[boxed, at], &live)?,
            Some(v) => {
                let strict = self.i32c(u32::from(self.strict));
                self.gc_call(self.h.set_property, &[boxed, at, v, strict], &live)?
            }
        };
        let outs = if val.is_none() { vec![r] } else { vec![] };
        let t = self.edge(inst, 1, &outs)?;
        let e = self.edge(inst, 2, &[])?;
        self.cond_br(ok, t, e);
        Ok(())
    }

    /// The incremental pre-write barrier on the slot at `obj + off`: while
    /// the zone is marking, mark the value about to be overwritten.
    fn pre_barrier(&mut self, addr: Value, off: u32) {
        let zone = self.load_i32(self.cx, JSCONTEXT_ZONE_OFFSET);
        let flag = self.load_i32(zone, ZONE_NEEDS_BARRIER_OFFSET);
        let (marking, cont) = (self.body.add_block(), self.body.add_block());
        self.cond_br(flag, Self::to(marking), Self::to(cont));
        self.cur = marking;
        let old = self.load_i64(addr, off);
        self.call(self.h.pre_write_barrier, &[old], &[]);
        self.terminate(Terminator::Br { target: Self::to(cont) });
        self.cur = cont;
    }

    /// The generational post-write barrier for storing boxed `v` into slot
    /// or element `slot` of `obj`: a nursery GC thing into a tenured object
    /// is recorded in the store buffer by `helper` (the slot or element
    /// form).
    fn post_barrier(&mut self, helper: Func, obj: Value, slot: Value, v: Value) {
        let cont = self.body.add_block();
        let mask = self.i32c(NOT_CHUNK_MASK);
        let chunk = self.bin(Operator::I32And, obj, mask, Type::I32);
        let owner_sb = self.load_i32(chunk, CHUNK_STORE_BUFFER_OFFSET);
        let tenured = self.body.add_block();
        self.cond_br(owner_sb, Self::to(cont), Self::to(tenured));
        self.cur = tenured;
        let tag = self.tag_of(v);
        let min = self.i32c(VAL_GCTHING_TAG_MIN);
        let is_gc = self.bin(Operator::I32GeU, tag, min, Type::I32);
        let gc = self.body.add_block();
        self.cond_br(is_gc, Self::to(gc), Self::to(cont));
        self.cur = gc;
        let cell = self.un(Operator::I32WrapI64, v, Type::I32);
        let chunk = self.bin(Operator::I32And, cell, mask, Type::I32);
        let sb = self.load_i32(chunk, CHUNK_STORE_BUFFER_OFFSET);
        let record = self.body.add_block();
        self.cond_br(sb, Self::to(record), Self::to(cont));
        self.cur = record;
        let owner = self.box_tagged(TAG_OBJECT, obj);
        self.call(helper, &[owner, slot, v], &[]);
        self.terminate(Terminator::Br { target: Self::to(cont) });
        self.cur = cont;
    }

    /// A get IC's way 0 inline (bbv's `emit_get_ic_inline_arms`, one way):
    /// with `recv` an object of the way's shape, the value from its own
    /// fixed slot, or through the way's holder (a prototype method) while
    /// the holder keeps its shape, taking `ok_clean`; else `probe`.
    fn get_ic_way0(&mut self, inst: mir::Inst, recv: Value, way: Value, probe: Block) -> R<()> {
        let tag = self.tag_of(recv);
        let is_obj = self.tag_is(tag, TAG_OBJECT as u32);
        self.check(is_obj, probe);
        let obj = self.un(Operator::I32WrapI64, recv, Type::I32);
        let shape = self.load_i32(obj, SHAPE_OFFSET);
        let wshape = self.load_i32(way, IC_WAY_RECVSHAPE);
        let hit = self.bin(Operator::I32Eq, shape, wshape, Type::I32);
        self.check(hit, probe);
        let moff = self.load_i32(way, IC_WAY_MONO_OFF);
        let (own, tail) = (self.body.add_block(), self.body.add_block());
        self.cond_br(moff, Self::to(own), Self::to(tail));
        self.cur = own;
        let addr = self.bin(Operator::I32Add, obj, moff, Type::I32);
        let v = self.load_i64(addr, 0);
        let t = self.edge(inst, 0, &[v])?;
        self.terminate(Terminator::Br { target: t });
        self.cur = tail;
        let hp = self.load_i32(way, IC_WAY_HOLDERPTR);
        let chs = self.load_i32(way, IC_WAY_HOLDERPTR + 4);
        let enc = self.load_i32(way, IC_WAY_HOLDERPTR + 8);
        let base = self.select(Type::I32, hp, obj, hp);
        let live = self.load_i32(base, SHAPE_OFFSET);
        let same = self.bin(Operator::I32Eq, live, chs, Type::I32);
        self.check(same, probe);
        let one = self.i32c(1);
        let dynamic = self.bin(Operator::I32And, enc, one, Type::I32);
        let not1 = self.i32c(!1);
        let off = self.bin(Operator::I32And, enc, not1, Type::I32);
        let slots = self.load_i32(base, NATIVE_SLOTS_OFFSET);
        let sb = self.select(Type::I32, slots, base, dynamic);
        let addr = self.bin(Operator::I32Add, sb, off, Type::I32);
        let v = self.load_i64(addr, 0);
        let t = self.edge(inst, 0, &[v])?;
        self.terminate(Terminator::Br { target: t });
        Ok(())
    }

    /// A set IC's way 0 (`bbv`'s `emit_set_prop_ic_inline` without its
    /// transition and megamorphic arms): with `recv` an object of the
    /// way's shape, store `val` to the slot the way names and take
    /// `ok_clean`; else branch to `slow`. The store bypasses the engine's
    /// choke, so it also requires the object's word to carry no bit it
    /// could falsify: RANGES never, TYPES unless `val` is a number.
    fn set_ic_way0(&mut self, inst: mir::Inst, recv: Value, val: Value, way: Value, slow: Block) -> R<()> {
        let num = matches!(self.ty(self.f.insts[inst].args[1]), MType::Val(s) if s.tags.subset_of(TagSet::NUMBER));
        let tag = self.tag_of(recv);
        let is_obj = self.tag_is(tag, TAG_OBJECT as u32);
        self.check(is_obj, slow);
        let obj = self.un(Operator::I32WrapI64, recv, Type::I32);
        let shape = self.load_i32(obj, SHAPE_OFFSET);
        let cached = self.load_i32(way, IC_SET_RECVSHAPE);
        let hit = self.bin(Operator::I32Eq, shape, cached, Type::I32);
        self.check(hit, slow);
        let w = self.load_i32(obj, OBJ_CLASS_IDX_OFFSET);
        self.check_store_bits(obj, w, num, slow);
        // The slot: `enc & 1` selects the dynamic slots over the object,
        // `enc & !1` is the byte offset from that base.
        let enc = self.load_i32(way, IC_SET_SLOTENC);
        let one = self.i32c(1);
        let dynamic = self.bin(Operator::I32And, enc, one, Type::I32);
        let not1 = self.i32c(!1);
        let off = self.bin(Operator::I32And, enc, not1, Type::I32);
        let slots = self.load_i32(obj, NATIVE_SLOTS_OFFSET);
        let base = self.op(Operator::Select, &[slots, obj, dynamic], Some(Type::I32));
        let addr = self.bin(Operator::I32Add, base, off, Type::I32);
        if !num {
            self.pre_barrier(addr, 0);
        }
        self.store_i64(addr, 0, val);
        if !num {
            let abs = self.load_i32(way, IC_SET_ABSSLOT);
            self.post_barrier(self.h.post_write_barrier, obj, abs, val);
        }
        let t = self.edge(inst, 0, &[])?;
        self.terminate(Terminator::Br { target: t });
        Ok(())
    }

    /// The address of native object `obj`'s slot `slot`: a fixed slot if
    /// the shape has that many, else a dynamic one.
    fn slot_addr(&mut self, obj: Value, slot: u32) -> Value {
        let shape = self.load_i32(obj, SHAPE_OFFSET);
        let flags = self.load_i32(shape, SHAPE_IMMUTABLE_FLAGS_OFFSET);
        let sh = self.i32c(SHAPE_FIXED_SLOTS_SHIFT);
        let n = self.bin(Operator::I32ShrU, flags, sh, Type::I32);
        let m = self.i32c(SHAPE_FIXED_SLOTS_MASK_BITS);
        let nfixed = self.bin(Operator::I32And, n, m, Type::I32);
        let s = self.i32c(slot);
        let fixed = self.bin(Operator::I32LtU, s, nfixed, Type::I32);
        let base = self.i32c(FIXED_SLOTS_BASE);
        let fixed_base = self.bin(Operator::I32Add, obj, base, Type::I32);
        let fixed_addr = self.i32c(8 * slot);
        let fixed_addr = self.bin(Operator::I32Add, fixed_base, fixed_addr, Type::I32);
        let slots = self.load_i32(obj, NATIVE_SLOTS_OFFSET);
        let rel = self.bin(Operator::I32Sub, s, nfixed, Type::I32);
        let eight = self.i32c(8);
        let off = self.bin(Operator::I32Mul, rel, eight, Type::I32);
        let dyn_addr = self.bin(Operator::I32Add, slots, off, Type::I32);
        self.op(Operator::Select, &[fixed_addr, dyn_addr, fixed], Some(Type::I32))
    }

    /// The script's `JSScript*`, re-derived from the callee (a rooted frame
    /// slot), as baseline's `script_ptr`.
    fn script_ptr(&mut self) -> Value {
        let fid = self.cur_frame as usize;
        let callee = if fid == 0 {
            self.load_i64(self.sp, FrameLayout::CALLEE)
        } else {
            self.load_i64(self.vp, self.frame_off[fid] + FrameLayout::CALLEE)
        };
        let f = self.un(Operator::I32WrapI64, callee, Type::I32);
        self.load_i32(f, FUNC_SCRIPT_SLOT_OFFSET)
    }

    /// A set IC's add-transition row replayed inline (bbv's add arm, in its
    /// sound subset): `recv` an object of the row's pre-add shape, the
    /// row's prototype hops unchanged (the first two live, deeper ones
    /// none), and the add unable to falsify the object's class-word bits.
    /// That holds when it has no SLOTS, or lands where one of the name's
    /// predicted (layout key, offset) pairs says; with no RANGES; and no
    /// TYPES unless the value is a number. Then store the fresh slot, swap
    /// the shape word and take `ok_clean`; else branch to `slow` (the
    /// helper keeps the bits itself).
    fn set_ic_trans(
        &mut self,
        inst: mir::Inst,
        name: mir::entity::AtomId,
        recv: Value,
        val: Value,
        way: Value,
        slow: Block,
    ) -> R<()> {
        let num = matches!(self.ty(self.f.insts[inst].args[1]), MType::Val(s) if s.tags.subset_of(TagSet::NUMBER));
        let tag = self.tag_of(recv);
        let is_obj = self.tag_is(tag, TAG_OBJECT as u32);
        self.check(is_obj, slow);
        let obj = self.un(Operator::I32WrapI64, recv, Type::I32);
        let row = self.add_off(way, IC_TRANS_ROW_OFF);
        let shape = self.load_i32(obj, SHAPE_OFFSET);
        let old = self.load_i32(row, IC_TRANS_OLDSHAPE);
        let m_old = self.bin(Operator::I32Eq, old, shape, Type::I32);
        self.check(m_old, slow);
        let slot_off = self.load_i32(row, IC_TRANS_SLOTOFF);
        self.check(slot_off, slow);
        for n in 0..IC_TRANS_PROTO_HOPS {
            let p = self.load_i32(row, IC_TRANS_PROTO0 + IC_TRANS_PROTO_ROW_BYTES * n);
            let empty = self.un(Operator::I32Eqz, p, Type::I32);
            let ok = if n < IC_TRANS_INLINE_HOPS {
                let want = self.load_i32(row, IC_TRANS_PROTO0 + IC_TRANS_PROTO_ROW_BYTES * n + 4);
                // An empty hop's load reads the null page's first word:
                // only its `empty` matters.
                let live = self.load_i32(p, SHAPE_OFFSET);
                let same = self.bin(Operator::I32Eq, live, want, Type::I32);
                self.bin(Operator::I32Or, empty, same, Type::I32)
            } else {
                empty
            };
            self.check(ok, slow);
        }
        // The class word.
        let w = self.load_i32(obj, OBJ_CLASS_IDX_OFFSET);
        self.check_store_bits(obj, w, num, slow);
        let sb = self.i32c(CLASS_WORD_SLOTS);
        let slots = self.bin(Operator::I32And, w, sb, Type::I32);
        let (keyed, go) = (self.body.add_block(), self.body.add_block());
        self.cond_br(slots, Self::to(keyed), Self::to(go));
        self.cur = keyed;
        let preds = self.add_preds.get(&name).cloned().unwrap_or_default();
        if preds.is_empty() {
            self.terminate(Terminator::Br { target: Self::to(slow) });
        } else {
            // The live layout key: the early key under the CONSTRUCTING
            // sentinel, else the stamped identity (they are disjoint).
            let ksh = self.i32c(EARLY_KEY_SHIFT);
            let kraw = self.bin(Operator::I32ShrU, w, ksh, Type::I32);
            let km = self.i32c(EARLY_KEY_MAX);
            let k_sent = self.bin(Operator::I32And, kraw, km, Type::I32);
            let m16 = self.i32c(0xFFFF);
            let k_idx = self.bin(Operator::I32And, w, m16, Type::I32);
            let k = self.bin(Operator::I32Or, k_sent, k_idx, Type::I32);
            let mut hit = self.i32c(0);
            for (key, off) in preds {
                let kv = self.i32c(key);
                let ke = self.bin(Operator::I32Eq, k, kv, Type::I32);
                let ov = self.i32c(off);
                let oe = self.bin(Operator::I32Eq, slot_off, ov, Type::I32);
                let both = self.bin(Operator::I32And, ke, oe, Type::I32);
                hit = self.bin(Operator::I32Or, hit, both, Type::I32);
            }
            self.cond_br(hit, Self::to(go), Self::to(slow));
        }
        self.cur = go;
        let addr = self.bin(Operator::I32Add, obj, slot_off, Type::I32);
        self.store_i64(addr, 0, val);
        let new_s = self.load_i32(row, IC_TRANS_NEWSHAPE);
        self.store_i32(obj, SHAPE_OFFSET, new_s);
        if !num {
            let abs = self.load_i32(row, IC_TRANS_ABSSLOT);
            self.post_barrier(self.h.post_write_barrier, obj, abs, val);
        }
        let t = self.edge(inst, 0, &[])?;
        self.terminate(Terminator::Br { target: t });
        Ok(())
    }

    /// An inline store's duty to the receiver's class word `w`: RANGES is
    /// consumed checklessly, but by no MIR claim, so it is dropped here
    /// rather than sent to the engine; TYPES survives a number store, and
    /// a non-number one clears it only on an object still under
    /// construction (the CONSTRUCTING sentinel: no guard can have proven
    /// it, so no claim rests on it); on a published one it goes to
    /// `slow`, where the engine keeps the bit.
    fn check_store_bits(&mut self, obj: Value, w: Value, num: bool, slow: Block) {
        if !num {
            let m = self.i32c(CLASS_WORD_SHALLOW | CLASS_WORD_SENTINEL);
            let bits = self.bin(Operator::I32And, w, m, Type::I32);
            let pub_shallow = self.i32c(CLASS_WORD_SHALLOW);
            let bad = self.bin(Operator::I32Eq, bits, pub_shallow, Type::I32);
            let ok = self.un(Operator::I32Eqz, bad, Type::I32);
            self.check(ok, slow);
        }
        let mask = CLASS_WORD_RANGES | if num { 0 } else { CLASS_WORD_SHALLOW };
        self.clear_bits(obj, w, mask);
    }

    /// Clear `mask`'s bits of `obj`'s class word `w`, if any is set.
    fn clear_bits(&mut self, obj: Value, w: Value, mask: u32) {
        let m = self.i32c(mask);
        let bits = self.bin(Operator::I32And, w, m, Type::I32);
        let (clr, done) = (self.body.add_block(), self.body.add_block());
        self.cond_br(bits, Self::to(clr), Self::to(done));
        self.cur = clr;
        let keep = self.i32c(!mask);
        let nw = self.bin(Operator::I32And, w, keep, Type::I32);
        self.store_i32(obj, OBJ_CLASS_IDX_OFFSET, nw);
        self.terminate(Terminator::Br { target: Self::to(done) });
        self.cur = done;
    }

    /// The construct `this` for a direct construct (bbv's
    /// `emit_construct_this`): with the site's cell describing the callee
    /// (its shape, under the live IC generation) and its live `.prototype`
    /// still the cached one, a nursery bump of the cached empty `this`;
    /// else `create_this`, which also fills the cell. Leaves `this` at
    /// `top` and returns the ok flag (1 on the bump path).
    fn construct_this(
        &mut self,
        top: Value,
        callee: Value,
        new_target: Value,
        nslots: u32,
        word: u32,
    ) -> Value {
        let cell = self.i32c(CONSTRUCT_CELL_ADDR_PLACEHOLDER);
        let idx = self.atoms.next_construct_cell();
        self.construct_cell_patches.push((cell, idx + 1));
        let done = self.body.add_block();
        let ok_p = self.body.add_blockparam(done, Type::I32);
        let slow = self.body.add_block();
        let cptr = self.un(Operator::I32WrapI64, callee, Type::I32);
        let ashape = self.load_i32(cell, 0);
        let cshape = self.load_i32(cell, CONSTRUCT_CELL_CTORSHAPE);
        let cgen = self.load_i32(cell, CONSTRUCT_CELL_GEN);
        let live_shape = self.load_i32(cptr, SHAPE_OFFSET);
        let gen_addr = self.i32c(self.h.prop_ic_gen_base);
        let live_gen = self.load_i32(gen_addr, 0);
        let z = self.i32c(0);
        let filled = self.bin(Operator::I32Ne, ashape, z, Type::I32);
        let s_ok = self.bin(Operator::I32Eq, cshape, live_shape, Type::I32);
        let g_ok = self.bin(Operator::I32Eq, cgen, live_gen, Type::I32);
        let hit = self.bin(Operator::I32And, filled, s_ok, Type::I32);
        let hit = self.bin(Operator::I32And, hit, g_ok, Type::I32);
        self.check(hit, slow);
        // A reassigned `.prototype` keeps the callee's shape.
        let enc = self.load_i32(cell, CONSTRUCT_CELL_PROTOSLOTENC);
        let one = self.i32c(1);
        let dynamic = self.bin(Operator::I32And, enc, one, Type::I32);
        let not1 = self.i32c(!1);
        let off = self.bin(Operator::I32And, enc, not1, Type::I32);
        let slots = self.load_i32(cptr, NATIVE_SLOTS_OFFSET);
        let sb = self.select(Type::I32, slots, cptr, dynamic);
        let addr = self.bin(Operator::I32Add, sb, off, Type::I32);
        let pval = self.load_i64(addr, 0);
        let pt = self.tag_of(pval);
        let p_obj = self.tag_is(pt, TAG_OBJECT as u32);
        let pptr = self.un(Operator::I32WrapI64, pval, Type::I32);
        let cproto = self.load_i32(cell, CONSTRUCT_CELL_PROTOPTR);
        let p_eq = self.bin(Operator::I32Eq, pptr, cproto, Type::I32);
        let p_ok = self.bin(Operator::I32And, p_obj, p_eq, Type::I32);
        self.check(p_ok, slow);
        // Room in the nursery, then bump and fill the header.
        let posp_slot = self.i32c(self.h.nursery_pos_slot);
        let posp = self.load_i32(posp_slot, 0);
        let pos = self.load_i32(posp, 0);
        let total = self.load_i32(cell, 4);
        let newpos = self.bin(Operator::I32Add, pos, total, Type::I32);
        let endp_slot = self.i32c(self.h.nursery_end_slot);
        let endp = self.load_i32(endp_slot, 0);
        let end = self.load_i32(endp, 0);
        let fits = self.bin(Operator::I32LeU, newpos, end, Type::I32);
        self.check(fits, slow);
        self.store_i32(posp, 0, newpos);
        let hdr = self.load_i32(cell, 16);
        self.store_i32(pos, 0, hdr);
        let hb = self.i32c(NURSERY_HEADER_BYTES);
        let obj = self.bin(Operator::I32Add, pos, hb, Type::I32);
        self.store_i32(obj, SHAPE_OFFSET, ashape);
        let wv = self.i32c(word);
        self.store_i32(obj, OBJ_CLASS_IDX_OFFSET, wv);
        let slotsw = self.load_i32(cell, 8);
        self.store_i32(obj, NATIVE_SLOTS_OFFSET, slotsw);
        let elemsw = self.load_i32(cell, 12);
        self.store_i32(obj, OBJ_ELEMENTS_OFFSET, elemsw);
        let payload = self.un(Operator::I64ExtendI32U, obj, Type::I64);
        let tag = self.i64c(TAG_OBJECT << 32);
        let this_v = self.bin(Operator::I64Or, payload, tag, Type::I64);
        self.store_i64(top, 0, this_v);
        let one = self.i32c(1);
        self.terminate(Terminator::Br {
            target: BlockTarget {
                block: done,
                args: vec![one],
            },
        });
        self.cur = slow;
        let (nv, wv) = (self.i32c(nslots), self.i32c(word));
        let made = self.call1(
            self.h.create_this,
            &[self.cx, top, callee, new_target, nv, cell, wv],
            Type::I32,
        );
        self.terminate(Terminator::Br {
            target: BlockTarget {
                block: done,
                args: vec![made],
            },
        });
        self.cur = done;
        ok_p
    }

    /// `lhs instanceof rhs` inline (bbv's `emit_instanceof`), taking
    /// `ok_clean`: with the site's cell describing `rhs` (its shape, under
    /// the live IC generation), read its `.prototype` from the cached slot
    /// and walk `lhs`'s prototype chain (bounded) for it. Anything else
    /// falls through to the helper, which also fills the cell.
    fn instanceof_arms(&mut self, inst: mir::Inst, lhs: Value, rhs: Value, cell: Value) -> R<()> {
        let slow = self.body.add_block();
        let rt = self.tag_of(rhs);
        let r_obj = self.tag_is(rt, TAG_OBJECT as u32);
        self.check(r_obj, slow);
        let rptr = self.un(Operator::I32WrapI64, rhs, Type::I32);
        let rshape = self.load_i32(rptr, SHAPE_OFFSET);
        let cshape = self.load_i32(cell, 0);
        let cgen = self.load_i32(cell, IOF_CELL_GEN);
        let gen_addr = self.i32c(self.h.prop_ic_gen_base);
        let live_gen = self.load_i32(gen_addr, 0);
        let s_ok = self.bin(Operator::I32Eq, rshape, cshape, Type::I32);
        let g_ok = self.bin(Operator::I32Eq, cgen, live_gen, Type::I32);
        let hit = self.bin(Operator::I32And, s_ok, g_ok, Type::I32);
        self.check(hit, slow);
        // The live `.prototype`, from the cached slot.
        let enc = self.load_i32(cell, IOF_CELL_SLOTENC);
        let one = self.i32c(1);
        let dynamic = self.bin(Operator::I32And, enc, one, Type::I32);
        let not1 = self.i32c(!1);
        let off = self.bin(Operator::I32And, enc, not1, Type::I32);
        let slots = self.load_i32(rptr, NATIVE_SLOTS_OFFSET);
        let sb = self.select(Type::I32, slots, rptr, dynamic);
        let addr = self.bin(Operator::I32Add, sb, off, Type::I32);
        let pval = self.load_i64(addr, 0);
        let pt = self.tag_of(pval);
        let p_obj = self.tag_is(pt, TAG_OBJECT as u32);
        self.check(p_obj, slow);
        let pptr = self.un(Operator::I32WrapI64, pval, Type::I32);
        let (t_b, f_b) = (self.body.add_block(), self.body.add_block());
        let lt = self.tag_of(lhs);
        let l_obj = self.tag_is(lt, TAG_OBJECT as u32);
        let lptr = self.un(Operator::I32WrapI64, lhs, Type::I32);
        let walk = self.body.add_block();
        let cur = self.body.add_blockparam(walk, Type::I32);
        let depth = self.body.add_blockparam(walk, Type::I32);
        let d0 = self.i32c(crate::constants::IOF_WALK_DEPTH);
        // A primitive is never an instance.
        self.cond_br(
            l_obj,
            BlockTarget {
                block: walk,
                args: vec![lptr, d0],
            },
            Self::to(f_b),
        );
        self.cur = walk;
        let ws = self.load_i32(cur, SHAPE_OFFSET);
        let wb = self.load_i32(ws, SHAPE_BASESHAPE_OFFSET);
        let proto = self.load_i32(wb, BASESHAPE_PROTO_OFFSET);
        let found = self.bin(Operator::I32Eq, proto, pptr, Type::I32);
        let wa = self.body.add_block();
        self.cond_br(found, Self::to(t_b), Self::to(wa));
        // A TaggedProto below 2 is null (0: not an instance) or lazy (1).
        self.cur = wa;
        let two = self.i32c(2);
        let low = self.bin(Operator::I32LtU, proto, two, Type::I32);
        let (wb2, wc) = (self.body.add_block(), self.body.add_block());
        self.cond_br(low, Self::to(wb2), Self::to(wc));
        self.cur = wb2;
        let z = self.i32c(0);
        let is_null = self.bin(Operator::I32Eq, proto, z, Type::I32);
        self.cond_br(is_null, Self::to(f_b), Self::to(slow));
        self.cur = wc;
        let z = self.i32c(0);
        let spent = self.bin(Operator::I32Eq, depth, z, Type::I32);
        let next = self.body.add_block();
        self.cond_br(spent, Self::to(slow), Self::to(next));
        self.cur = next;
        let one = self.i32c(1);
        let nd = self.bin(Operator::I32Sub, depth, one, Type::I32);
        self.terminate(Terminator::Br {
            target: BlockTarget {
                block: walk,
                args: vec![proto, nd],
            },
        });
        for (b, v) in [(t_b, 1u64), (f_b, 0u64)] {
            self.cur = b;
            let r = self.i64c((TAG_BOOLEAN << 32) | v);
            let t = self.edge(inst, 0, &[r])?;
            self.terminate(Terminator::Br { target: t });
        }
        self.cur = slow;
        Ok(())
    }

    /// Branch to `fail` unless `cond`.
    fn check(&mut self, cond: Value, fail: Block) {
        let cont = self.body.add_block();
        self.cond_br(cond, Self::to(cont), Self::to(fail));
        self.cur = cont;
    }

    /// Element `key` of `recv` (both boxed) when `recv` is a native object,
    /// `key` an int32, and the element an initialized, non-hole dense one;
    /// else branches to `fail`. Pure reads: a typed array's dense
    /// initializedLength is 0, and a proxy fails the native check first.
    fn dense_element(&mut self, recv: Value, key: Value, fail: Block) -> Value {
        self.dense_slot(recv, key, fail).4
    }

    /// `dense_element`'s checks, returning the object, its elements, the
    /// index, the element's address and its value.
    fn dense_slot(&mut self, recv: Value, key: Value, fail: Block) -> (Value, Value, Value, Value, Value) {
        let tag = self.tag_of(recv);
        let is_obj = self.tag_is(tag, TAG_OBJECT as u32);
        let ktag = self.tag_of(key);
        let is_int = self.tag_is(ktag, TAG_INT32 as u32);
        let both = self.bin(Operator::I32And, is_obj, is_int, Type::I32);
        self.check(both, fail);
        let obj = self.un(Operator::I32WrapI64, recv, Type::I32);
        let shape = self.load_i32(obj, SHAPE_OFFSET);
        let flags = self.load_i32(shape, SHAPE_IMMUTABLE_FLAGS_OFFSET);
        let bit = self.i32c(SHAPE_IS_NATIVE_BIT);
        let native = self.bin(Operator::I32And, flags, bit, Type::I32);
        self.check(native, fail);
        let elements = self.load_i32(obj, OBJ_ELEMENTS_OFFSET);
        let back = self.i32c(ELEMENTS_INITLEN_BACK);
        let header = self.bin(Operator::I32Sub, elements, back, Type::I32);
        let initlen = self.load_i32(header, 0);
        let idx = self.un(Operator::I32WrapI64, key, Type::I32);
        let in_bounds = self.bin(Operator::I32LtU, idx, initlen, Type::I32);
        self.check(in_bounds, fail);
        let eight = self.i32c(8);
        let off = self.bin(Operator::I32Mul, idx, eight, Type::I32);
        let addr = self.bin(Operator::I32Add, elements, off, Type::I32);
        let v = self.load_i64(addr, 0);
        let vtag = self.tag_of(v);
        let hole = self.tag_is(vtag, TAG_MAGIC as u32);
        let not_hole = self.un(Operator::I32Eqz, hole, Type::I32);
        self.check(not_hole, fail);
        (obj, elements, idx, addr, v)
    }

    /// The helpers' atom id for MIR atom `a`, as an i32 constant.
    fn atom(&mut self, a: mir::entity::AtomId) -> Value {
        let id = self.atoms.intern_chars(self.mm.atoms[a].chars());
        self.i32c(id)
    }

    /// A JS call (`callee`, `this`, args; all boxed). The callee's frame
    /// is written just above the rooting slots, and the call enters a
    /// compiled callee's body directly when it can (`call_indirect`, as
    /// baseline's calls do: JS call depth is then bounded by the
    /// NightStack, not the native stack), else the generic helper. The
    /// result is at the frame's top. Success takes `ok_dirty`.
    fn js_call_op(&mut self, inst: mir::Inst, ops: &[Value]) -> R<()> {
        /// Headroom a compiled body may use past its actuals (the runtime
        /// entries' `kNightStackHeadroomSlots`).
        const HEADROOM: u32 = 64 * 1024;
        let live = self.live_across(inst);
        self.spill(&live)?;
        let frame = self.top_off(live.len());
        for (k, &v) in ops.iter().enumerate() {
            self.store_i64(self.vp, frame + 8 * u32::try_from(k).unwrap(), v);
        }
        let argc = u32::try_from(ops.len() - 2).unwrap();
        let top_off = frame + 8 * (argc + 2);
        let base = self.add_off(self.vp, frame);
        let top = self.add_off(self.vp, top_off);
        let z = self.i32c(0);
        let (funcidx, script) = self.classify(ops[0]);
        let limit_addr = self.i32c(self.h.night_stack_limit_base);
        let limit = self.load_i32(limit_addr, 0);
        let hi = self.add_off(top, HEADROOM);
        let fits = self.bin(Operator::I32LeU, hi, limit, Type::I32);
        let compiled = self.bin(Operator::I32Ne, funcidx, z, Type::I32);
        let direct = self.bin(Operator::I32And, compiled, fits, Type::I32);
        let (direct_b, generic_b, join) = (
            self.body.add_block(),
            self.body.add_block(),
            self.body.add_block(),
        );
        let ok = self.body.add_blockparam(join, Type::I32);
        self.cond_br(direct, Self::to(direct_b), Self::to(generic_b));

        self.cur = direct_b;
        let argc_v = self.i32c(argc);
        let undef = self.i64c(UNDEF);
        // Bodies sit `N` table slots below their adapters (`wasm/mod.rs`).
        let off = self.i32c(u32::MAX);
        self.body_off_patches.push(off);
        let body_idx = self.bin(Operator::I32Sub, funcidx, off, Type::I32);
        let args = self
            .body
            .arg_pool
            .from_iter([self.cx, base, argc_v, top, script, undef, body_idx].into_iter());
        let tys = self
            .body
            .type_pool
            .from_iter([Type::I32, Type::I32].into_iter());
        let call = self.push_val(ValueDef::Operator(
            Operator::CallIndirect {
                sig_index: self.h.night_abi_sig2,
                table_index: self.h.indirect_table,
            },
            args,
            tys,
        ));
        let err = self.push_val(ValueDef::PickOutput(call, 0, Type::I32));
        let ok_direct = self.un(Operator::I32Eqz, err, Type::I32);
        self.terminate(Terminator::Br {
            target: BlockTarget {
                block: join,
                args: vec![ok_direct],
            },
        });

        self.cur = generic_b;
        let argc_v = self.i32c(argc);
        let ok_generic = self.call1(self.h.call, &[self.cx, top, base, argc_v], Type::I32);
        self.terminate(Terminator::Br {
            target: BlockTarget {
                block: join,
                args: vec![ok_generic],
            },
        });

        self.cur = join;
        self.reload(&live)?;
        let result = self.load_i64(self.vp, top_off);
        let t = self.edge(inst, 1, &[result])?;
        let e = self.edge(inst, 2, &[])?;
        self.cond_br(ok, t, e);
        Ok(())
    }

    /// `night_call_classify` of boxed `callee`: its funcref-table index (0
    /// when not compiled or not a scripted function) and its `JSScript*`.
    fn classify(&mut self, callee: Value) -> (Value, Value) {
        let z = self.i32c(0);
        let args = self.body.arg_pool.from_iter([callee, z, z].into_iter());
        let tys = self
            .body
            .type_pool
            .from_iter([Type::I32, Type::I32, Type::I32].into_iter());
        let cls = self.push_val(ValueDef::Operator(
            Operator::Call {
                function_index: self.h.call_classify,
            },
            args,
            tys,
        ));
        let funcidx = self.push_val(ValueDef::PickOutput(cls, 0, Type::I32));
        let script = self.push_val(ValueDef::PickOutput(cls, 1, Type::I32));
        (funcidx, script)
    }

    /// `inline.enter` (§5.5): the inlined callee's frame, as its
    /// prologue would write it, from `callee, this, formals`. Every slot
    /// up to the frame's end is made a valid Value: helpers' GC scan limit
    /// inside the callee is that end.
    fn inline_enter(&mut self, d: &mir::func::InstData, a: &[Value]) -> R<()> {
        let fid = self.cur_frame as usize;
        let (base, l) = (self.frame_off[fid], self.frame_layouts[fid]);
        let max_depth = self.f.inline_frames[fid - 1].max_depth;
        if a.len() != 2 + l.nargs as usize {
            return Err("lowering: inline.enter needs callee, this and every formal".into());
        }
        let mut boxed = vec![];
        for (&v, &mv) in a.iter().zip(&d.args) {
            let t = self.ty(mv);
            boxed.push(self.boxed(&t, v)?);
        }
        // Inline frames are placed from `vp`.
        let sp = self.vp;
        self.store_i64(sp, base + FrameLayout::CALLEE, boxed[0]);
        self.store_i64(sp, base + FrameLayout::THIS, boxed[1]);
        for i in 0..l.nargs {
            self.store_i64(sp, base + l.arg(i), boxed[2 + i as usize]);
        }
        let undef = self.i64c(UNDEF);
        for j in 0..l.nlocals {
            self.store_i64(sp, base + l.local(j), undef);
        }
        // The callee's own environment: what its prologue loads, for a
        // script whose activation has none of its own (the only kind
        // inlined).
        let fun = self.un(Operator::I32WrapI64, boxed[0], Type::I32);
        let env = self.load_i64(fun, FUNC_ENV_SLOT_OFFSET);
        self.store_i64(sp, base + l.env(), env);
        self.store_i64(sp, base + l.args_obj(), undef);
        self.store_i64(sp, base + l.new_target(), undef);
        self.store_i64(sp, base + l.rval(), undef);
        let zero = self.i64c(TAG_INT32 << 32);
        self.store_i64(sp, base + l.resume(), zero);
        self.store_i64(sp, base + l.backoff(), zero);
        for k in 0..max_depth + 3 {
            self.store_i64(sp, base + l.operand(k), undef);
        }
        Ok(())
    }

    /// `exit.inline` (§5.5): finish the inlined callee in its baseline
    /// body from `pc`. Write the operands the frame does not already hold
    /// (write-through keeps the formals, locals and rval), the resume
    /// word, then call the callee's entry with `ARGC_RESUME_BIT` on its
    /// frame. The caller continues on `ok` with the callee's result, or on
    /// `err`.
    #[allow(clippy::too_many_arguments)]
    fn exit_inline(
        &mut self,
        inst: mir::Inst,
        d: &mir::func::InstData,
        a: &[Value],
        pc: Pc,
        nargs: u32,
        nlocals: u32,
        throw: bool,
    ) -> R<()> {
        let fid = self.cur_frame as usize;
        let (base, end, l) = (self.frame_off[fid], self.frame_end[fid], self.frame_layouts[fid]);
        let mut ops = vec![];
        for (&v, &mv) in a.iter().zip(&d.args) {
            let dead = matches!(
                self.f.values[mv].def,
                mir::func::ValueDef::Result(i, _)
                    if self.f.insts[i].op == Opcode::ConstVal(ConstVal::Dead)
            );
            ops.push(if dead {
                None
            } else {
                let t = self.ty(mv);
                Some(self.boxed(&t, v)?)
            });
        }
        let fp = frame_parts(&ops, nargs, nlocals).ok_or("lowering: malformed exit.inline")?;
        // Inline frames are placed from `vp`.
        let sp = self.vp;
        if let Some(v) = *fp.this {
            self.store_i64(sp, base + FrameLayout::THIS, v);
        }
        for (i, v) in fp.args.iter().enumerate() {
            if let Some(v) = *v {
                self.store_i64(sp, base + l.arg(u32::try_from(i).unwrap()), v);
            }
        }
        for (j, v) in fp.locals.iter().enumerate() {
            if let Some(v) = *v {
                self.store_i64(sp, base + l.local(u32::try_from(j).unwrap()), v);
            }
        }
        if let Some(v) = *fp.rval {
            self.store_i64(sp, base + l.rval(), v);
        }
        for (k, v) in fp.stack.iter().enumerate() {
            if let Some(v) = *v {
                self.store_i64(sp, base + l.operand(u32::try_from(k).unwrap()), v);
            }
        }
        let mode = if throw {
            ResumeMode::Throw
        } else {
            ResumeMode::Continue
        };
        let w = ResumeWord { pc, mode };
        let word = self.i64c((TAG_INT32 << 32) | u64::from(w.encode() as u32));
        self.store_i64(sp, base + l.resume(), word);
        let backoff = self.i64c((TAG_INT32 << 32) | u64::from(ONRAMP_BACKOFF));
        self.store_i64(sp, base + l.backoff(), backoff);
        // The call, rooted: the caller's managed values live across it.
        let live = self.live_across(inst);
        self.spill(&live)?;
        let callee = self.load_i64(sp, base + FrameLayout::CALLEE);
        let (funcidx, script) = self.classify(callee);
        let off = self.i32c(u32::MAX);
        self.body_off_patches.push(off);
        let body_idx = self.bin(Operator::I32Sub, funcidx, off, Type::I32);
        let frame = self.add_off(sp, base);
        let top = self.add_off(sp, end);
        let argc = self.i32c(nargs | ARGC_RESUME_BIT);
        let undef = self.i64c(UNDEF);
        let args = self
            .body
            .arg_pool
            .from_iter([self.cx, frame, argc, top, script, undef, body_idx].into_iter());
        let tys = self.body.type_pool.from_iter([Type::I32, Type::I32].into_iter());
        let call = self.push_val(ValueDef::Operator(
            Operator::CallIndirect {
                sig_index: self.h.night_abi_sig2,
                table_index: self.h.indirect_table,
            },
            args,
            tys,
        ));
        let err = self.push_val(ValueDef::PickOutput(call, 0, Type::I32));
        self.reload(&live)?;
        let result = self.load_i64(sp, end);
        let ok = self.un(Operator::I32Eqz, err, Type::I32);
        let t = self.edge(inst, 0, &[result])?;
        let e = self.edge(inst, 1, &[])?;
        self.cond_br(ok, t, e);
        Ok(())
    }

    /// Leave MIR at `w` with the frame state `ops` (this, formals,
    /// locals, rval, stack; of types `tys`, `dead` ones left as the frame
    /// has them): a branch to the function's exit hub for this shape of
    /// frame, carrying the resume word and the operands as they are.
    fn exit(
        &mut self,
        w: ResumeWord,
        ops: &[Value],
        tys: &[MType],
        dead: &[bool],
        nargs: u32,
        nlocals: u32,
    ) -> R<()> {
        if let Some(census) = self.exit_census {
            static NEXT: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
            let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            crate::diag_line!(
                "night: mir exit {id} sid#{} pc {} {:?}",
                self.f.script,
                w.pc,
                w.mode
            );
            let (k, i) = (
                self.i32c(crate::options::MIR_EXIT_CENSUS_KIND),
                self.i32c(id),
            );
            self.call1(census, &[k, i], Type::I32);
        }
        let mut shape = Vec::with_capacity(ops.len());
        for (t, &d) in tys.iter().zip(dead) {
            shape.push(if d { None } else { Some(BoxKind::of(t)?) });
        }
        let hub = match self.exit_hubs.get(&shape) {
            Some(&b) => b,
            None => {
                let b = self.exit_hub(&shape, tys, nargs, nlocals)?;
                self.exit_hubs.insert(shape.clone(), b);
                b
            }
        };
        let mut args = vec![self.i32c(w.encode() as u32)];
        args.extend(ops.iter().zip(dead).filter(|(_, &d)| !d).map(|(&v, _)| v));
        self.terminate(Terminator::Br {
            target: BlockTarget { block: hub, args },
        });
        Ok(())
    }

    /// The exit hub for frames of `shape` (§5.1): its params are the
    /// resume word and the live operands in their own representations. It
    /// boxes each once, writes the baseline frame, then runs the baseline
    /// body from there (or returns DEOPT to an onramping baseline caller).
    /// One hub serves every exit of the same shape, so a function's exit
    /// code grows with its distinct frame shapes, not with its exits.
    fn exit_hub(&mut self, shape: &[Option<BoxKind>], tys: &[MType], nargs: u32, nlocals: u32) -> R<Block> {
        let saved = self.cur;
        let hub = self.body.add_block();
        let word = self.body.add_blockparam(hub, Type::I32);
        let mut raw = vec![];
        for (k, t) in shape.iter().zip(tys) {
            if k.is_some() {
                let m = machine(t).ok_or("lowering: an exit operand without a representation")?;
                raw.push(Some(self.body.add_blockparam(hub, m)));
            } else {
                raw.push(None);
            }
        }
        self.cur = hub;
        let mut boxed = vec![];
        for (v, t) in raw.iter().zip(tys) {
            boxed.push(match v {
                Some(v) => Some(self.boxed(t, *v)?),
                None => None,
            });
        }
        let fp = frame_parts(&boxed, nargs, nlocals).ok_or("lowering: malformed exit")?;
        let (sp, vp) = (self.sp, self.vp);
        let l = self.layout;
        // A dead operand's slot keeps the frame's (valid) value.
        if let Some(v) = *fp.this {
            self.store_i64(sp, FrameLayout::THIS, v);
        }
        for (i, v) in fp.args.iter().enumerate() {
            if let Some(v) = *v {
                self.store_i64(sp, l.arg(u32::try_from(i).unwrap()), v);
            }
        }
        for (j, v) in fp.locals.iter().enumerate() {
            if let Some(v) = *v {
                self.store_i64(vp, l.local(u32::try_from(j).unwrap()), v);
            }
        }
        if let Some(v) = *fp.rval {
            self.store_i64(vp, l.rval(), v);
        }
        for (k, v) in fp.stack.iter().enumerate() {
            if let Some(v) = *v {
                self.store_i64(vp, l.operand(u32::try_from(k).unwrap()), v);
            }
        }
        // The fixed slots MIR does not keep current. The env slot is fixed
        // for the activation, and the arguments-object slot holds the one
        // `args.object` made, if any (the fresh entry cleared it).
        self.store_i64(vp, l.new_target(), self.new_target);
        let w64 = self.un(Operator::I64ExtendI32U, word, Type::I64);
        let tag = self.i64c(TAG_INT32 << 32);
        let wv = self.bin(Operator::I64Or, w64, tag, Type::I64);
        self.store_i64(vp, l.resume(), wv);
        // Baseline waits this many loop-header visits before it tries an
        // onramp again, so it makes progress from here.
        let backoff = self.i64c((TAG_INT32 << 32) | u64::from(ONRAMP_BACKOFF));
        self.store_i64(vp, l.backoff(), backoff);
        if self.has_onramps {
            // Entered by an onramp: the baseline caller resumes itself.
            let (deopt, call_blk) = (self.body.add_block(), self.body.add_block());
            self.cond_br(self.onramp_flag, Self::to(deopt), Self::to(call_blk));
            self.cur = deopt;
            let d = self.i32c(ERR_DEOPT);
            self.ret(d);
            self.cur = call_blk;
        }
        let bit = self.i32c(ARGC_RESUME_BIT);
        let argc = self.bin(Operator::I32Or, self.argc, bit, Type::I32);
        self.tail_to_baseline(argc);
        self.cur = saved;
        Ok(hub)
    }

    /// Run this script's baseline body on the frame at `sp` with `argc`
    /// (resume and onramp bits included), and return its result.
    fn tail_to_baseline(&mut self, argc: Value) {
        let call = self.call(
            Func::invalid(),
            &[
                self.cx,
                self.sp,
                argc,
                self.retval_out,
                self.script_param,
                self.new_target,
            ],
            &[Type::I32, Type::I32],
        );
        self.baseline_calls.push(call);
        let err = self.push_val(ValueDef::PickOutput(call, 0, Type::I32));
        let eff = self.push_val(ValueDef::PickOutput(call, 1, Type::I32));
        self.terminate(Terminator::Return {
            values: vec![err, eff],
        });
    }
}
