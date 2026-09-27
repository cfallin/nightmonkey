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
//! - **Rooting (§4.4).** A managed value (`Val`, `Obj`, `Str`) that may be
//!   live across a may-GC call has a home slot in the rooting area, above
//!   baseline's fixed frame and locals; values never live at once share
//!   one. Every may-GC call's GC scan covers the whole area, initialized
//!   at entry. Before a call, each live managed value its slot does not
//!   hold yet is stored, boxed; SSA values do not change and the GC
//!   updates slots in place, so it stays stored across later calls. After
//!   a call, register copies are dropped, and a value is reloaded where
//!   next used. Where each managed value is (register, slot, or both) is
//!   tracked along the emission; a block's entry state is decided from
//!   its incoming edges, each of which gets its own waffle block to bring
//!   the value there (`enter_block`, `conform`). Unmanaged values are
//!   never rooted.
//! - **Frame.** Formals, locals and rval stay in their own
//!   representations (no write-through, except a mapped `arguments`'s
//!   formals); exits write them.
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

use crate::ids::{Pc, ScriptId};
use crate::mir;
use crate::mir::func::{Edge, EdgeArg, RootKind};
use crate::mir::ops::{
    frame_parts, ArithOp, BitOp, Cc, ConstVal, F64Op, JsBinop, JsCc, JsUnop, MathFn, NumRepr,
    Opcode, UnboxKind,
};
use crate::mir::types::{Machine, ObjKind, TagSet, Type as MType};
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
    CLASS_WORD_RANGES, CLASS_WORD_SENTINEL, CLASS_WORD_SLOTS, SHAPE_SMALL_SLOTSPAN_MASK_BITS,
    SHAPE_SMALL_SLOTSPAN_SHIFT, TA_DATA_PAYLOAD_OFFSET, TA_LENGTH_PAYLOAD_OFFSET, ELEMENTS_LENGTH_BACK,
    ELEMENTS_CAPACITY_BACK, ELEMENTS_PUSH_BAIL_MASK, ELEMENTS_HEADER_BYTES, ALLOC_CELL_ADDR_PLACEHOLDER,
    STRING_LENGTH_OFFSET, STRING_FLAGS_OFFSET, STRING_CHARS_OFFSET, STRING_LINEAR_BIT,
    STRING_INLINE_CHARS_BIT, STRING_LATIN1_CHARS_BIT, CALL_CELL_ADDR_PLACEHOLDER, CALL_CELL_FUNCIDX,
    CALL_CELL_SCRIPT, EARLY_KEY_MAX, EARLY_KEY_SHIFT, IC_SET_ABSSLOT,
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
    AtomTable, Helpers, APPEND_CACHE_ENTRY_BYTES, APPEND_CACHE_SIZE, BC_ARR_POP, BC_ARR_PUSH,
    ELEMENTS_POP_BAIL_MASK, INLINE_IC_STRIDE, MAGIC_IS_CONSTRUCTING, MAGIC_UNINITIALIZED_LEXICAL, TAG_BIGINT_HI, TAG_BOOLEAN, TAG_CLEAR,
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
    pub call_cell_patches: Vec<(Value, u32)>,
    pub alloc_cell_patches: Vec<(Value, u32)>,
    /// Per mnemonic: how many instructions, and the wasm values they
    /// lowered to (`--dump-opsize`).
    pub opsize: BTreeMap<String, (u32, u32)>,
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
    /// The waffle value standing for each MIR value at the emission point:
    /// for a managed value, its register copy, if it has a valid one (a
    /// may-GC call invalidates them).
    vmap: BTreeMap<mir::Value, Value>,
    /// Rooting (see the module doc): each managed value that may be live
    /// across a may-GC call has a home slot in the rooting area, which
    /// starts at `root_base` and holds `nslots` slots; `slotted` is the set
    /// of values whose home slot holds them at the emission point.
    root_base: u32,
    home: BTreeMap<mir::Value, u32>,
    nslots: u32,
    slotted: BTreeSet<mir::Value>,
    /// Home slots that may hold a value no longer live: cleared at the
    /// next may-GC call, which must not keep it alive (a `WeakRef`'s
    /// target, say).
    dirty: BTreeSet<u32>,
    /// Per (frame, slot): the value a `frame.store` put there, along the
    /// emission path; a store of the same value again is dropped.
    framed: BTreeMap<(u32, u32), mir::Value>,
    /// The builder's retaining frame stores before the next instruction:
    /// emitted where that instruction can GC (`root`), not before it.
    pending_retain: Vec<((u32, u32), mir::Value)>,
    /// The MIR block being lowered.
    cur_mblock: mir::Block,
    /// Whether the emission point is on a helper's slow path: its edges'
    /// managed values are reloaded on the edge rather than at their uses.
    cold: bool,
    /// Edges into blocks not entered yet, and each entered block's entry
    /// state (`enter_block`).
    pending: BTreeMap<mir::Block, Vec<PendingEdge>>,
    plans: BTreeMap<mir::Block, Vec<(mir::Value, Loc, bool)>>,
    entry_dirty: BTreeMap<mir::Block, BTreeSet<u32>>,
    rpo_index: BTreeMap<mir::Block, usize>,
    preds: BTreeMap<mir::Block, Vec<mir::Block>>,
    /// Per block: the managed values that may have been live across a
    /// may-GC call since their definition, at its end.
    crossed_out: BTreeMap<mir::Block, BTreeSet<mir::Value>>,
    /// With inlined callees (§5.5): per frame id its base and end offsets
    /// from `sp` and its layout. Frame 0 is the function's, ending past
    /// the rooting area; each inline frame sits at its parent's end. A
    /// may-GC call's scan limit is its frame's end.
    inline: bool,
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
    /// Call value cell placeholders (bbv's per-site cell; 0: the trash row).
    call_cell_patches: Vec<(Value, u32)>,
    alloc_cell_patches: Vec<(Value, u32)>,
    opsize: BTreeMap<String, (u32, u32)>,
    /// The census helper, when exits are counted (`--mir-exit-census`).
    exit_census: Option<Func>,
    /// The census helper, when blocks are counted (`--block-census`).
    block_census: Option<Func>,
    ctor_restamp: Option<[u32; 7]>,
    /// One exit hub per frame shape (`exit_hub`).
    exit_hubs: BTreeMap<Vec<Option<BoxKind>>, Block>,
    /// One `exit.inline` hub per inline frame: its entry and last blocks,
    /// its site-index param and call status, and each site's tail
    /// (`exit_inline`).
    inline_hubs: BTreeMap<u32, (Block, Block, Value, Value, Vec<Block>)>,
    strict: bool,
    plain_env: bool,
    own_env: bool,
    forward_resume: bool,
    mapped_formals: bool,
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

/// An edge into a block not entered yet: its own waffle block, filled in
/// when the block's entry state is decided, with the edge's explicit
/// args and where each managed live-in of the target is along it (its
/// register copy, if valid; whether its home slot holds it).
struct PendingEdge {
    tb: Block,
    args: Vec<Value>,
    snap: BTreeMap<mir::Value, (Option<Value>, bool)>,
    dirty: BTreeSet<u32>,
    framed: BTreeMap<(u32, u32), mir::Value>,
    cold: bool,
}

/// Where a managed live-in of a block is on entry.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Loc {
    /// In a register: a waffle param of the block.
    Param,
    /// In a register, the same waffle value along every edge.
    Direct(Value),
    /// Only in its home slot.
    Slot,
}

/// Per-script lowering choices besides the function itself.
#[derive(Clone, Copy, Default)]
pub struct LowerOpts {
    /// The stress mode's period (`Options::mir_stress`); 0 = off.
    pub stress: u32,
    /// Count every exit (`--mir-exit-census`).
    pub exit_census: bool,
    /// Count every MIR block's executions (`--block-census`).
    pub block_census: bool,
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
    /// The script's formals are a mapped `arguments`'s, which may write
    /// them behind MIR's back: their frame stores are never dropped.
    pub mapped_formals: bool,
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
    o: LowerOpts,
    gname_bids: BTreeMap<mir::entity::AtomId, u32>,
    gname_fused: BTreeMap<mir::entity::AtomId, crate::wasm::translate::FusedGname>,
    add_preds: BTreeMap<mir::entity::AtomId, Vec<(u32, u32)>>,
) -> R<Lowered> {
    let body = FunctionBody::new(m, h.night_abi_sig2);
    let entry = body.entry;
    let p = |i: usize| body.blocks[entry].params[i].1;
    let (cx, sp, argc, retval_out, script_param, new_target) = (p(0), p(1), p(2), p(3), p(4), p(5));
    // Rooting slots and callee frames go above baseline's fixed frame and
    // locals, which therefore always hold valid Values (a fresh entry
    // initializes them): an exit can leave a dead one as it is. They
    // overlap baseline's operand slots, which MIR never reads while it
    // runs (an onramp reads them before anything is spilled, an exit
    // writes every one below its depth), so those are not initialized:
    // a helper's GC scan stops at the spilled roots.
    let root_base = layout.operand(0);
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
        vmap: BTreeMap::new(),
        root_base,
        home: BTreeMap::new(),
        nslots: 0,
        slotted: BTreeSet::new(),
        dirty: BTreeSet::new(),
        framed: BTreeMap::new(),
        pending_retain: vec![],
        cur_mblock: mir::Block::from_u32(0),
        cold: false,
        pending: BTreeMap::new(),
        plans: BTreeMap::new(),
        entry_dirty: BTreeMap::new(),
        rpo_index: BTreeMap::new(),
        preds: BTreeMap::new(),
        crossed_out: BTreeMap::new(),
        inline: !f.inline_frames.is_empty(),
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
        call_cell_patches: vec![],
        alloc_cell_patches: vec![],
        opsize: BTreeMap::new(),
        exit_census: if o.exit_census { h.census } else { None },
        block_census: if o.block_census { h.census } else { None },
        ctor_restamp: o.ctor_restamp,
        exit_hubs: BTreeMap::new(),
        inline_hubs: BTreeMap::new(),
        strict: o.strict,
        plain_env: o.plain_env,
        own_env: o.own_env,
        forward_resume: o.forward_resume,
        mapped_formals: o.mapped_formals,
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
        call_cell_patches: l.call_cell_patches,
        alloc_cell_patches: l.alloc_cell_patches,
        opsize: l.opsize,
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

    /// `v` in a register at the emission point: a managed value only in
    /// its home slot is loaded (without recording the copy, which is valid
    /// only on this path).
    fn value_here(&mut self, v: mir::Value) -> R<Value> {
        if let Some(&w) = self.vmap.get(&v) {
            return Ok(w);
        }
        if self.slotted.contains(&v) {
            return self.load_home(v);
        }
        Err(format!("lowering: {v} has no value here"))
    }

    /// Load managed `v` from its home slot, unboxed to its representation.
    fn load_home(&mut self, v: mir::Value) -> R<Value> {
        let off = self.home_off(v)?;
        let raw = self.load_i64(self.vp, off);
        let t = self.ty(v);
        Ok(self.unboxed_managed(&t, raw))
    }

    fn home_off(&self, v: mir::Value) -> R<u32> {
        let k = self
            .home
            .get(&v)
            .ok_or_else(|| format!("lowering: {v} is live across a may-GC call but has no home slot"))?;
        Ok(self.root_base + 8 * k)
    }

    /// The instruction's operands, at its start (which dominates all of its
    /// code): a value only in its home slot is loaded, and the copy kept
    /// until the next may-GC call.
    fn args(&mut self, inst: mir::Inst) -> R<Vec<Value>> {
        let vs = self.f.insts[inst].args.clone();
        let mut out = vec![];
        for v in vs {
            let w = self.value_here(v)?;
            self.vmap.insert(v, w);
            out.push(w);
        }
        Ok(out)
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
        let order = self.rpo();
        for (i, &b) in order.iter().enumerate() {
            self.rpo_index.insert(b, i);
            for s in f.succs(b) {
                self.preds.entry(s).or_default().push(b);
            }
        }
        self.homes(&reach, &order);
        self.frame_end[0] = self.root_base + 8 * self.nslots;
        if self.inline {
            self.inline_layout();
        }
        // Waffle blocks with the block's own params; its managed live-ins
        // are placed when it is entered.
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
            self.blocks.insert(b, wb);
        }
        self.entry()?;
        // In reverse postorder, so a block's dominators, which define the
        // unmanaged values it uses directly, are lowered before it.
        for b in order {
            self.cur_mblock = b;
            self.enter_block(b)?;
            if let Some(census) = self.block_census {
                static NEXT: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
                let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let ops: Vec<String> = f.blocks[b].insts.iter().map(|&i| mir::print::mnemonic(&f.insts[i].op)).collect();
                crate::diag_line!("night: mir block {id} sid#{} {b} {}", self.f.script, ops.join(" "));
                let (k, i) = (self.i32c(crate::options::MIR_BLOCK_CENSUS_KIND), self.i32c(id));
                self.call1(census, &[k, i], Type::I32);
            }
            for &inst in &f.blocks[b].insts {
                self.cold = false;
                // Retaining stores still pending at a terminator that
                // cannot GC (an inlined call's entry): the GC points are
                // past the block, so they are written here.
                if !self.pending_retain.is_empty()
                    && !self.f.insts[inst].succs.is_empty()
                    && !self.may_gc(inst)
                {
                    self.flush_retain(None)?;
                    self.pending_retain.clear();
                }
                let before = self.body.values.len();
                self.inst(inst)?;
                if self.may_gc(inst) {
                    self.pending_retain.clear();
                }
                let e = self
                    .opsize
                    .entry(mir::print::mnemonic(&f.insts[inst].op))
                    .or_default();
                e.0 += 1;
                e.1 += u32::try_from(self.body.values.len() - before).unwrap();
            }
        }
        if let Some((b, _)) = self.pending.iter().find(|(_, v)| !v.is_empty()) {
            return Err(format!("lowering: an edge into {b} was never placed"));
        }
        // Each `exit.inline` hub continues at its site's tail.
        for (_, last, site, err, tails) in std::mem::take(&mut self.inline_hubs).into_values() {
            let targets: Vec<BlockTarget> = tails
                .iter()
                .map(|&t| BlockTarget {
                    block: t,
                    args: vec![err],
                })
                .collect();
            let default = targets[0].clone();
            self.body.set_terminator(
                last,
                Terminator::Select {
                    value: site,
                    targets,
                    default,
                },
            );
        }
        waffle::passes::empty_blocks::run(&mut self.body);
        Ok(())
    }

    /// The frame stores in the loop through header `h` (the blocks between
    /// it and its back-edge sources `later`), per (frame, slot), and the
    /// inline frames the loop enters.
    fn loop_frame_writes(
        &self,
        h: mir::Block,
        later: &[mir::Block],
    ) -> (BTreeMap<(u32, u32), BTreeSet<mir::Value>>, BTreeSet<u32>) {
        let f = self.f;
        let mut fwd: BTreeSet<mir::Block> = BTreeSet::new();
        let mut work = vec![h];
        while let Some(b) = work.pop() {
            if fwd.insert(b) {
                work.extend(f.succs(b));
            }
        }
        let mut body: BTreeSet<mir::Block> = BTreeSet::new();
        let mut work: Vec<mir::Block> = later.to_vec();
        while let Some(b) = work.pop() {
            if fwd.contains(&b) && body.insert(b) && b != h {
                work.extend(self.preds.get(&b).cloned().unwrap_or_default());
            }
        }
        let mut stores: BTreeMap<(u32, u32), BTreeSet<mir::Value>> = BTreeMap::new();
        let mut entered = BTreeSet::new();
        for b in body {
            for &i in &f.blocks[b].insts {
                match f.insts[i].op {
                    Opcode::FrameStore(k) => {
                        stores.entry((f.inst_frame[i], k)).or_default().insert(f.insts[i].args[0]);
                    }
                    Opcode::InlineEnter => {
                        entered.insert(f.inst_frame[i]);
                    }
                    _ => {}
                }
            }
        }
        (stores, entered)
    }

    /// Whether `inst` may call something that GCs (a superset of where the
    /// lowering roots: any op with an `err` or `ok_dirty` edge).
    fn may_gc(&self, inst: mir::Inst) -> bool {
        use mir::ops::SuccRole;
        let op = &self.f.insts[inst].op;
        op.roles().iter().any(|r| matches!(r, SuccRole::Err | SuccRole::OkDirty))
    }

    /// Home slots: every managed value live across a may-GC instruction
    /// gets one, shared among values never live at once. In SSA two
    /// values interfere iff one is live at the other's definition, so
    /// coloring in definition order (reverse postorder, which respects
    /// dominance) against the colored values live there is enough. Also
    /// computes `crossed_out`.
    fn homes(&mut self, reach: &BTreeSet<mir::Block>, order: &[mir::Block]) {
        let f = self.f;
        let managed = |v: mir::Value| is_managed(&f.values[v].ty);
        // Per block: the managed values live after each may-GC instruction,
        // and the values live after each definition (block params first).
        let mut cand: BTreeSet<mir::Value> = BTreeSet::new();
        let mut crossed_gen: BTreeMap<mir::Block, BTreeSet<mir::Value>> = BTreeMap::new();
        let mut def_live: Vec<(mir::Block, usize, mir::Value, Vec<mir::Value>)> = vec![];
        for &b in reach {
            let mut live: BTreeSet<mir::Value> = BTreeSet::new();
            for s in f.succs(b) {
                if let Some(l) = self.live_in.get(&s) {
                    live.extend(l.iter().copied());
                }
            }
            let insts = &f.blocks[b].insts;
            for (k, &i) in insts.iter().enumerate().rev() {
                let d = &f.insts[i];
                for e in &d.succs {
                    for a in &e.args {
                        if let EdgeArg::Value(v) = a {
                            live.insert(*v);
                        }
                    }
                }
                for &r in &d.results {
                    live.remove(&r);
                }
                if self.may_gc(i) {
                    let g = crossed_gen.entry(b).or_default();
                    for &v in live.iter().filter(|&&v| managed(v)) {
                        cand.insert(v);
                        g.insert(v);
                    }
                }
                for &r in &d.results {
                    if managed(r) {
                        let mut l: Vec<mir::Value> = live.iter().copied().filter(|&v| managed(v)).collect();
                        l.push(r);
                        def_live.push((b, k + 1, r, l));
                    }
                }
                live.extend(d.args.iter().copied());
            }
            for &p in &f.blocks[b].params {
                if managed(p) {
                    let l: Vec<mir::Value> = live.iter().copied().filter(|&v| managed(v)).collect();
                    def_live.push((b, 0, p, l));
                }
            }
        }
        // Color in definition order.
        let pos: BTreeMap<mir::Block, usize> = order.iter().enumerate().map(|(i, &b)| (b, i)).collect();
        def_live.sort_by_key(|&(b, k, v, _)| (pos.get(&b).copied().unwrap_or(usize::MAX), k, v));
        let mut n = 0u32;
        for (_, _, v, live) in def_live {
            if !cand.contains(&v) {
                continue;
            }
            let used: BTreeSet<u32> = live
                .iter()
                .filter(|&&u| u != v)
                .filter_map(|u| self.home.get(u).copied())
                .collect();
            let c = (0..).find(|c| !used.contains(c)).unwrap();
            n = n.max(c + 1);
            self.home.insert(v, c);
        }
        self.nslots = n;
        // What may have crossed a may-GC call, forward to a fixpoint.
        let mut changed = true;
        while changed {
            changed = false;
            for &b in order {
                let mut out: BTreeSet<mir::Value> = BTreeSet::new();
                for p in self.preds.get(&b).cloned().unwrap_or_default() {
                    if let Some(c) = self.crossed_out.get(&p) {
                        out.extend(c.iter().copied());
                    }
                }
                if let Some(g) = crossed_gen.get(&b) {
                    out.extend(g.iter().copied());
                }
                if self.crossed_out.get(&b) != Some(&out) {
                    self.crossed_out.insert(b, out);
                    changed = true;
                }
            }
        }
    }

    /// Enter block `b`: decide where each managed live-in is on entry from
    /// the edges already made into it (every one but back edges), fill
    /// those edges' blocks, and set the emission state.
    ///
    /// A value that may cross a may-GC call before a later (back) edge
    /// reaches `b` enters only in its home slot, so a loop stores it once,
    /// before it. Otherwise it enters in a register if every edge has one
    /// (a param, unless every edge has the same value) or if every edge
    /// but a helper's slow path does (which reloads it); else only in its
    /// home slot, stored along the edges that have not stored it.
    fn enter_block(&mut self, b: mir::Block) -> R<()> {
        let f = self.f;
        let wb = self.blocks[&b];
        self.cur = wb;
        let pend = self.pending.remove(&b).unwrap_or_default();
        let me = self.rpo_index[&b];
        let later: Vec<mir::Block> = self
            .preds
            .get(&b)
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .filter(|p| self.rpo_index.get(p).is_some_and(|&i| i >= me))
            .collect();
        let live: Vec<mir::Value> = self.live_in[&b].iter().copied().filter(|&v| is_managed(&self.ty(v))).collect();
        let mut plan = vec![];
        for &v in &live {
            let at = |p: &PendingEdge| p.snap.get(&v).copied().unwrap_or((None, false));
            let all_reg = pend.iter().all(|p| at(p).0.is_some());
            let all_slot = pend.iter().all(|p| at(p).1);
            let crossed_later = later
                .iter()
                .any(|p| self.crossed_out.get(p).is_some_and(|c| c.contains(&v)));
            let hot: Vec<&PendingEdge> = pend.iter().filter(|p| !p.cold).collect();
            let loc = if crossed_later && self.home.contains_key(&v) {
                Loc::Slot
            } else if all_reg && !pend.is_empty() {
                let first = at(&pend[0]).0;
                if later.is_empty() && pend.iter().all(|p| at(p).0 == first) {
                    Loc::Direct(first.unwrap())
                } else {
                    Loc::Param
                }
            } else if !hot.is_empty() && hot.iter().all(|p| at(p).0.is_some()) {
                Loc::Param
            } else {
                Loc::Slot
            };
            let entry_slotted = loc == Loc::Slot || (!pend.is_empty() && all_slot);
            plan.push((v, loc, entry_slotted));
        }
        for &(v, loc, _) in &plan {
            if loc == Loc::Param {
                self.body.add_blockparam(wb, machine(&self.ty(v)).unwrap());
            }
        }
        self.plans.insert(b, plan.clone());
        let dirty: BTreeSet<u32> = pend.iter().flat_map(|p| p.dirty.iter().copied()).collect();
        // What the frame holds on every edge. Where back edges are still
        // to come, only slots the loop never stores a different value into
        // (nor enters their inline frame), which the back edges then agree
        // on.
        let mut framed = pend.first().map(|p| p.framed.clone()).unwrap_or_default();
        for p in pend.iter().skip(1) {
            framed.retain(|k, v| p.framed.get(k) == Some(v));
        }
        if !later.is_empty() {
            let (stores, entered) = self.loop_frame_writes(b, &later);
            framed.retain(|k, v| !entered.contains(&k.0) && stores.get(k).is_none_or(|s| s.iter().all(|w| w == v)));
        }
        self.entry_dirty.insert(b, dirty.clone());
        for p in pend {
            self.conform(b, p)?;
        }
        // The emission state.
        self.cur = wb;
        let wparams: Vec<Value> = self.body.blocks[wb].params.iter().map(|&(_, v)| v).collect();
        let mut k = 0;
        for &p in &f.blocks[b].params {
            if machine(&self.ty(p)).is_some() {
                self.vmap.insert(p, wparams[k]);
                k += 1;
            }
        }
        self.slotted.clear();
        self.dirty = dirty;
        self.framed = framed;
        self.pending_retain.clear();
        for (v, loc, es) in plan {
            match loc {
                Loc::Param => {
                    self.vmap.insert(v, wparams[k]);
                    k += 1;
                }
                Loc::Direct(w) => {
                    self.vmap.insert(v, w);
                }
                Loc::Slot => {
                    self.vmap.remove(&v);
                }
            }
            if es {
                self.slotted.insert(v);
            }
        }
        self.cold = false;
        Ok(())
    }

    /// Fill edge `p` into entered block `b`: bring each managed live-in to
    /// where `b` expects it, then branch.
    fn conform(&mut self, b: mir::Block, p: PendingEdge) -> R<()> {
        let saved = self.cur;
        self.cur = p.tb;
        let mut args = p.args;
        for (v, loc, es) in self.plans[&b].clone() {
            let (reg, sl) = p.snap.get(&v).copied().unwrap_or((None, false));
            let lost = || format!("lowering: {v} is live into {b} but has no value on an edge");
            if (loc == Loc::Slot || es) && !sl {
                let r = reg.ok_or_else(lost)?;
                let t = self.ty(v);
                let boxed = self.boxed(&t, r)?;
                let off = self.home_off(v)?;
                self.store_i64(self.vp, off, boxed);
            }
            match loc {
                Loc::Param => {
                    let r = match reg {
                        Some(r) => r,
                        None if sl => self.load_home(v)?,
                        None => return Err(lost()),
                    };
                    args.push(r);
                }
                Loc::Direct(w) => {
                    if reg != Some(w) {
                        return Err(format!("lowering: {v} enters {b} as two values"));
                    }
                }
                Loc::Slot => {}
            }
        }
        // A slot this edge may have left a dead value in, which the block
        // does not know to clear (a back edge): clear it here, unless it
        // holds a value the block keeps in it.
        let kept: BTreeSet<u32> = self.plans[&b]
            .iter()
            .filter(|&&(_, loc, es)| loc == Loc::Slot || es)
            .filter_map(|(v, _, _)| self.home.get(v).copied())
            .collect();
        let extra: Vec<u32> = p
            .dirty
            .iter()
            .copied()
            .filter(|s| !self.entry_dirty[&b].contains(s) && !kept.contains(s))
            .collect();
        if !extra.is_empty() {
            let undef = self.i64c(UNDEF);
            for s in extra {
                self.store_i64(self.vp, self.root_base + 8 * s, undef);
            }
        }
        let wb = self.blocks[&b];
        self.terminate(Terminator::Br {
            target: BlockTarget { block: wb, args },
        });
        self.cur = saved;
        Ok(())
    }

    /// An edge into MIR block `b` with explicit waffle args `args`, from
    /// the emission point: its own waffle block, filled now if `b` has been
    /// entered (a back edge), else when it is.
    fn edge_into(&mut self, b: mir::Block, args: Vec<Value>) -> R<BlockTarget> {
        let tb = self.body.add_block();
        let mut snap = BTreeMap::new();
        if let Some(l) = self.live_in.get(&b) {
            for &v in l {
                if is_managed(&self.ty(v)) {
                    snap.insert(v, (self.vmap.get(&v).copied(), self.slotted.contains(&v)));
                }
            }
        }
        let p = PendingEdge {
            tb,
            args,
            snap,
            dirty: self.dirty.clone(),
            framed: self.framed.clone(),
            cold: self.cold,
        };
        if self.plans.contains_key(&b) {
            self.conform(b, p)?;
        } else {
            self.pending.entry(b).or_default().push(p);
        }
        Ok(Self::to(tb))
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
            // The GC updated the frame, not the values read from it before.
            vals = vec![
                self.load_i64(self.sp, FrameLayout::CALLEE),
                self.load_i64(self.sp, FrameLayout::THIS),
            ];
            for i in 0..self.layout.nargs {
                vals.push(self.load_i64(self.sp, self.layout.arg(i)));
            }
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
        let t = self.edge_into(root, args)?;
        self.terminate(Terminator::Br { target: t });
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
        if vals.len() != self.f.blocks[root].params.len() {
            return Err("lowering: an onramp root's params are not the frame".into());
        }
        // After reading the operands: the rooting area overlaps them.
        self.init_root_area();
        let t = self.edge_into(root, vals)?;
        self.terminate(Terminator::Br { target: t });
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
        if !self.blocks.contains_key(&e.block) {
            return Err(format!("lowering: {} is unreachable", e.block));
        }
        let mut args = vec![];
        let params = self.f.blocks[e.block].params.clone();
        for (a, &p) in e.args.iter().zip(&params) {
            if machine(&self.ty(p)).is_none() {
                continue;
            }
            args.push(match *a {
                EdgeArg::Value(v) => self.value_here(v)?,
                EdgeArg::Out(k) => *outs
                    .get(k as usize)
                    .ok_or_else(|| format!("lowering: no output %{k}"))?,
            });
        }
        self.edge_into(e.block, args)
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

    /// Call may-GC helper `f(cx, top, args...)` with every value in `live`
    /// rooted, reloading them afterwards. Returns the helper's i32 status
    /// and the boxed result it wrote at `top`.
    fn gc_call(&mut self, f: Func, args: &[Value], live: &[mir::Value]) -> R<(Value, Value)> {
        self.root(live)?;
        let top_off = self.top_off(live.len());
        let top = self.add_off(self.vp, top_off);
        let mut full = vec![self.cx, top];
        full.extend_from_slice(args);
        let ok = self.call1(f, &full, Type::I32);
        self.after_gc(live);
        // A helper's slow path: its edges reload what their targets keep
        // in registers.
        self.cold = true;
        let result = self.load_i64(self.vp, top_off);
        Ok((ok, result))
    }

    /// The first free byte above everything this instruction's frame
    /// chain holds, as an offset from `sp`: where a helper's out-slot and
    /// GC scan limit, and a real call's frame, go. That is past the
    /// instruction's own frame, which is past the rooting area and every
    /// enclosing inline frame. (`live` no longer matters: kept for the
    /// callers' shape.)
    fn top_off(&self, _live: usize) -> u32 {
        self.frame_end[self.cur_frame as usize]
    }

    /// Lay out the inline frames (§5.5): each at its parent's end, the
    /// function's own frame ending past the rooting area.
    fn inline_layout(&mut self) {
        for fr in &self.f.inline_frames {
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

    /// Make the rooting area valid Values: every may-GC call's scan covers
    /// all of it, whatever is live.
    fn init_root_area(&mut self) {
        if self.nslots == 0 {
            return;
        }
        let undef = self.i64c(UNDEF);
        for i in 0..self.nslots {
            self.store_i64(self.vp, self.root_base + 8 * i, undef);
        }
    }

    /// Write the pending retaining stores (the locals' values, into the
    /// frame the GC sees: a value stays alive while its local holds it, as
    /// in baseline), but not where both it and what the frame slot holds
    /// are rooted anyway, in `live` (so in their home slots). Returns the
    /// stores made.
    fn flush_retain(&mut self, live: Option<&[mir::Value]>) -> R<u32> {
        let mut stores = 0;
        for (key, v) in self.pending_retain.clone() {
            if self.framed.get(&key) == Some(&v) {
                continue;
            }
            if let Some(live) = live {
                if live.contains(&v) && self.framed.get(&key).is_some_and(|o| live.contains(o)) {
                    continue;
                }
            }
            let (fid, k) = key;
            let f = fid as usize;
            let l = self.frame_layouts[f];
            let (nargs, nlocals) = (l.nargs, l.nlocals);
            let off = self.frame_off[f]
                + match k {
                    0 => FrameLayout::THIS,
                    k if k <= nargs => l.arg(k - 1),
                    k if k <= nargs + nlocals => l.local(k - 1 - nargs),
                    _ => l.rval(),
                };
            let w = self.value_here(v)?;
            let t = self.ty(v);
            let b = self.boxed(&t, w)?;
            let base = if fid == 0 && k <= nargs { self.sp } else { self.vp };
            self.store_i64(base, off, b);
            self.framed.insert(key, v);
            stores += 1;
        }
        Ok(stores)
    }

    /// Before a may-GC call: store each of `live` (managed values live
    /// across it) that its home slot does not hold yet. A stored value
    /// stays stored (SSA values do not change, and the GC updates the slot
    /// in place), so repeated calls store it once.
    fn root(&mut self, live: &[mir::Value]) -> R<()> {
        let mut stores = self.flush_retain(Some(live))?;
        for &v in live {
            if self.slotted.contains(&v) {
                continue;
            }
            stores += 1;
            let t = self.ty(v);
            let w = self.get(v)?;
            let b = self.boxed(&t, w)?;
            let off = self.home_off(v)?;
            self.store_i64(self.vp, off, b);
            self.slotted.insert(v);
        }
        // Slots holding what is live now; any other written slot may hold
        // a dead value, which the GC must not see.
        let holding: BTreeSet<u32> = live.iter().filter_map(|v| self.home.get(v).copied()).collect();
        let stale: Vec<u32> = self.dirty.difference(&holding).copied().collect();
        if !stale.is_empty() {
            let undef = self.i64c(UNDEF);
            for s in &stale {
                self.store_i64(self.vp, self.root_base + 8 * s, undef);
            }
            stores += u32::try_from(stale.len()).unwrap();
        }
        self.dirty = holding;
        self.slotted.retain(|v| live.contains(v));
        let e = self.opsize.entry("(root sites / stores)".into()).or_default();
        e.0 += 1;
        e.1 += stores;
        Ok(())
    }

    /// After a may-GC call: `live`'s register copies may point to moved
    /// objects; each is reloaded from its home slot where next used.
    fn after_gc(&mut self, live: &[mir::Value]) {
        for v in live {
            self.vmap.remove(v);
        }
    }

    // --- instructions ------------------------------------------------------------------

    fn def(&mut self, inst: mir::Inst, v: Value) {
        let r = self.f.insts[inst].results[0];
        self.vmap.insert(r, v);
    }

    fn inst(&mut self, inst: mir::Inst) -> R<()> {
        self.cur_frame = self.f.inst_frame[inst];
        let d = self.f.insts[inst].clone();
        if let Opcode::FrameStore(k) = d.op {
            let key = (self.cur_frame, k);
            let aliased = self.mapped_formals && self.cur_frame == 0 && k >= 1 && k <= self.layout.nargs;
            if !aliased {
                // A retaining store (the builder's `retain_locals`): held
                // for the next instruction's GC points.
                if self.framed.get(&key) != Some(&d.args[0]) {
                    self.pending_retain.push((key, d.args[0]));
                }
                return Ok(());
            }
        }
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
                        // Branches, not one flag: the product fits, and
                        // only a zero one (rare) tests for -0 (a negative
                        // operand).
                        let x64 = self.un(Operator::I64ExtendI32S, x, Type::I64);
                        let y64 = self.un(Operator::I64ExtendI32S, y, Type::I64);
                        let w = self.bin(Operator::I64Mul, x64, y64, Type::I64);
                        let r = self.un(Operator::I32WrapI64, w, Type::I32);
                        let r64 = self.un(Operator::I64ExtendI32S, r, Type::I64);
                        let fits = self.bin(Operator::I64Eq, w, r64, Type::I32);
                        let (nz, zero, ok_b, fail_b) = (
                            self.body.add_block(),
                            self.body.add_block(),
                            self.body.add_block(),
                            self.body.add_block(),
                        );
                        self.cond_br(fits, Self::to(nz), Self::to(fail_b));
                        self.cur = nz;
                        self.cond_br(r, Self::to(ok_b), Self::to(zero));
                        self.cur = zero;
                        let xy = self.bin(Operator::I32Or, x, y, Type::I32);
                        let z = self.i32c(0);
                        let neg = self.bin(Operator::I32LtS, xy, z, Type::I32);
                        self.cond_br(neg, Self::to(fail_b), Self::to(ok_b));
                        self.cur = fail_b;
                        let f = self.edge(inst, 1, &[])?;
                        self.terminate(Terminator::Br { target: f });
                        self.cur = ok_b;
                        (r, self.i32c(1))
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
            Opcode::ArgsMapped(n) | Opcode::ArgsMappedSet(n) => {
                // The entry made the object (mapped scripts are not
                // inlined: the frame is the function's own).
                let obj = self.load_i64(self.vp, self.layout.args_obj());
                let i = self.i32c(n);
                if let Opcode::ArgsMapped(_) = d.op {
                    let v = self.call1(self.h.get_mapped_arg, &[obj, i], Type::I64);
                    self.def(inst, v);
                } else {
                    self.call(self.h.set_mapped_arg, &[obj, i, a[0]], &[]);
                }
            }
            Opcode::JsTypeofEq(k) => {
                // A leaf: no GC, no JS.
                let kv = self.i32c(u32::from(k));
                let f = self.h.typeof_eq;
                let v = self.call1(f, &[self.cx, a[0], kv], Type::I32);
                self.def(inst, v);
            }
            Opcode::JsConstantStrictEq(k) => {
                // `ConstantStrictEqual` inline (bbv's): the operand's type
                // byte, then its payload.
                let v = self.constant_strict_eq(a[0], k);
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
                // `setAliasedBinding` zero hops up, inline: the slot store
                // with its barriers.
                let addr = self.slot_addr(a[0], slot.get());
                self.pre_barrier(addr, 0);
                self.store_i64(addr, 0, a[1]);
                let s = self.i32c(slot.get());
                self.post_barrier(self.h.post_write_barrier, a[0], s, a[1]);
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
                let nm = String::from_utf16_lossy(self.mm.atoms[name].chars());
                if nm == "charCodeAt" || nm == "charAt" {
                    // A string's pristine char method, while String.prototype
                    // is untouched (bbv's char-op read): the cached native.
                    let cell = if nm == "charCodeAt" { self.h.str_ccat_cell } else { self.h.str_cat_cell };
                    let ic = self.body.add_block();
                    let tag = self.tag_of(a[0]);
                    let is_str = self.tag_is(tag, TAG_STRING as u32);
                    let fslot = self.i32c(self.h.str_fuse_addr_slot);
                    let faddr = self.load_i32(fslot, 0);
                    let fword = self.load_i32(faddr, 0);
                    let intact = self.un(Operator::I32Eqz, fword, Type::I32);
                    let c = self.i32c(cell);
                    let bits = self.load_i64(c, 0);
                    let z = self.i64c(0);
                    let armed = self.bin(Operator::I64Ne, bits, z, Type::I32);
                    let ok = self.bin(Operator::I32And, is_str, intact, Type::I32);
                    let ok = self.bin(Operator::I32And, ok, armed, Type::I32);
                    let hit = self.body.add_block();
                    self.cond_br(ok, Self::to(hit), Self::to(ic));
                    self.cur = hit;
                    let t = self.edge(inst, 0, &[bits])?;
                    self.terminate(Terminator::Br { target: t });
                    self.cur = ic;
                }
                if self.mm.atoms[name].chars() == "length".encode_utf16().collect::<Vec<u16>>().as_slice() {
                    // Not a slot: a string's or an array's own word.
                    let ic = self.body.add_block();
                    self.length_arms(inst, a[0], ic)?;
                    self.cur = ic;
                }
                let probe = self.body.add_block();
                self.get_ic_ways(inst, a[0], way_base, cache * INLINE_IC_STRIDE, probe)?;
                self.cur = probe;
                let r = self.call(self.h.ic_get_poly, &[a[0], at, way_base], &[Type::I64]);
                let tag = self.tag_of(r);
                let miss = self.tag_is(tag, TAG_MAGIC as u32);
                let slow = self.body.add_block();
                let t = self.edge(inst, 0, &[r])?;
                self.cond_br(miss, Self::to(slow), t);
                self.cur = slow;
                if let Some(census) = self.exit_census {
                    static NEXT: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
                    let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    crate::diag_line!(
                        "night: mir getmiss {id} sid#{} {}",
                        self.f.script,
                        String::from_utf16_lossy(self.mm.atoms[name].chars())
                    );
                    let (k, i) = (
                        self.i32c(crate::options::MIR_GET_MISS_CENSUS_KIND),
                        self.i32c(id),
                    );
                    self.call1(census, &[k, i], Type::I32);
                }
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
            Opcode::GuardKind(ObjKind::Native) => {
                let shape = self.load_i32(a[0], SHAPE_OFFSET);
                let flags = self.load_i32(shape, SHAPE_IMMUTABLE_FLAGS_OFFSET);
                let bit = self.i32c(SHAPE_IS_NATIVE_BIT);
                let native = self.bin(Operator::I32And, flags, bit, Type::I32);
                self.guard(inst, native, &[a[0]])?;
            }
            Opcode::GuardKind(ObjKind::TypedArray(k)) => {
                // The class is the kind's typed-array class (bbv's
                // `ta_clasp_eq`).
                let shape = self.load_i32(a[0], SHAPE_OFFSET);
                let base = self.load_i32(shape, SHAPE_BASESHAPE_OFFSET);
                let clasp = self.load_i32(base, BASESHAPE_CLASP_OFFSET);
                let cslot = self.i32c(self.h.ta_class_base + 4 * (u32::from(k.code()) - 1));
                let want = self.load_i32(cslot, 0);
                let ok = self.bin(Operator::I32Eq, clasp, want, Type::I32);
                self.guard(inst, ok, &[a[0]])?;
            }
            Opcode::LoadTa | Opcode::StoreTa => {
                // An in-bounds element (a detached array has length 0);
                // else `fail`.
                let k = match self.ty(d.args[0]) {
                    MType::Obj(o) => match o.kind {
                        ObjKind::TypedArray(k) => k,
                        _ => return Err("lowering: typed array op without a kind".into()),
                    },
                    _ => return Err("lowering: typed array op without a kind".into()),
                };
                let fail = self.body.add_block();
                let len = self.load_i32(a[0], TA_LENGTH_PAYLOAD_OFFSET);
                let ok = self.bin(Operator::I32LtU, a[1], len, Type::I32);
                self.check(ok, fail);
                let data = self.load_i32(a[0], TA_DATA_PAYLOAD_OFFSET);
                let sh = k.log2_bytes();
                let addr = if sh == 0 {
                    self.bin(Operator::I32Add, data, a[1], Type::I32)
                } else {
                    let s = self.i32c(sh);
                    let off = self.bin(Operator::I32Shl, a[1], s, Type::I32);
                    self.bin(Operator::I32Add, data, off, Type::I32)
                };
                use crate::opsem::TaKind as K;
                let outs = if d.op == Opcode::LoadTa {
                    let m = self.mem(sh, 0);
                    let v = match k {
                        K::Int8 => self.un(Operator::I32Load8S { memory: m }, addr, Type::I32),
                        K::Uint8 | K::Uint8Clamped => self.un(Operator::I32Load8U { memory: m }, addr, Type::I32),
                        K::Int16 => self.un(Operator::I32Load16S { memory: m }, addr, Type::I32),
                        K::Uint16 => self.un(Operator::I32Load16U { memory: m }, addr, Type::I32),
                        K::Int32 => self.un(Operator::I32Load { memory: m }, addr, Type::I32),
                        K::Uint32 => return Err("lowering: load_ta of a Uint32Array".into()),
                        K::Float32 | K::Float64 => {
                            let d = if k == K::Float32 {
                                let f = self.un(Operator::F32Load { memory: m }, addr, Type::F32);
                                self.un(Operator::F64PromoteF32, f, Type::F64)
                            } else {
                                self.un(Operator::F64Load { memory: m }, addr, Type::F64)
                            };
                            // Any NaN as the canonical one: a boxed double
                            // must not look like a tag.
                            let nan = self.bin(Operator::F64Ne, d, d, Type::I32);
                            let c = self.f64c(f64::NAN.to_bits());
                            self.select(Type::F64, c, d, nan)
                        }
                    };
                    vec![v]
                } else {
                    let m = self.mem(sh, 0);
                    let v = a[2];
                    match k {
                        K::Int8 | K::Uint8 => {
                            self.op(Operator::I32Store8 { memory: m }, &[addr, v], None);
                        }
                        K::Int16 | K::Uint16 => {
                            self.op(Operator::I32Store16 { memory: m }, &[addr, v], None);
                        }
                        K::Int32 | K::Uint32 => {
                            self.op(Operator::I32Store { memory: m }, &[addr, v], None);
                        }
                        K::Float32 => {
                            let f = self.un(Operator::F32DemoteF64, v, Type::F32);
                            self.op(Operator::F32Store { memory: m }, &[addr, f], None);
                        }
                        K::Float64 => {
                            self.op(Operator::F64Store { memory: m }, &[addr, v], None);
                        }
                        K::Uint8Clamped => {
                            // An int32 clamped to 0..=255.
                            let z = self.i32c(0);
                            let neg = self.bin(Operator::I32LtS, v, z, Type::I32);
                            let lo = self.select(Type::I32, z, v, neg);
                            let hi = self.i32c(255);
                            let big = self.bin(Operator::I32GtS, lo, hi, Type::I32);
                            let c = self.select(Type::I32, hi, lo, big);
                            self.op(Operator::I32Store8 { memory: m }, &[addr, c], None);
                        }
                    }
                    vec![]
                };
                let t = self.edge(inst, 0, &outs)?;
                self.terminate(Terminator::Br { target: t });
                self.cur = fail;
                let f = self.edge(inst, 1, &[])?;
                self.terminate(Terminator::Br { target: f });
            }
            Opcode::LoadElem => {
                // An in-bounds, non-hole dense element; else `fail`.
                let fail = self.body.add_block();
                let (_, v) = self.elem_addr(a[0], a[1], fail, true);
                let t = self.edge(inst, 0, &[v.unwrap()])?;
                self.terminate(Terminator::Br { target: t });
                self.cur = fail;
                let f = self.edge(inst, 1, &[])?;
                self.terminate(Terminator::Br { target: f });
            }
            Opcode::StoreElem => {
                // An in-bounds overwrite of a non-hole dense element of
                // unfrozen elements (an own writable data property); else
                // `fail`. RANGES, consumed by no MIR claim, is dropped.
                let num = matches!(self.ty(d.args[2]), MType::Val(s) if s.tags.subset_of(TagSet::NUMBER));
                let fail = self.body.add_block();
                let (addr, _) = self.elem_addr(a[0], a[1], fail, true);
                let elements = self.load_i32(a[0], OBJ_ELEMENTS_OFFSET);
                let back = self.i32c(ELEMENTS_FLAGS_BACK);
                let header = self.bin(Operator::I32Sub, elements, back, Type::I32);
                let flags = self.load_i32(header, 0);
                let fz = self.i32c(ELEMENTS_FROZEN_FLAG);
                let frozen = self.bin(Operator::I32And, flags, fz, Type::I32);
                let thawed = self.un(Operator::I32Eqz, frozen, Type::I32);
                self.check(thawed, fail);
                let w = self.load_i32(a[0], OBJ_CLASS_IDX_OFFSET);
                self.clear_bits(a[0], w, CLASS_WORD_RANGES);
                if !num {
                    self.pre_barrier(addr, 0);
                }
                self.store_i64(addr, 0, a[2]);
                if !num {
                    let f = self.h.post_write_barrier_elem;
                    self.post_barrier(f, a[0], a[1], a[2]);
                }
                let t = self.edge(inst, 0, &[])?;
                self.terminate(Terminator::Br { target: t });
                self.cur = fail;
                let f = self.edge(inst, 1, &[])?;
                self.terminate(Terminator::Br { target: f });
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
            Opcode::CreateThis(nslots, word) => {
                // May GC: root what is live across it.
                let live = self.live_across(inst);
                self.root(&live)?;
                let top_off = self.top_off(live.len());
                let top = self.add_off(self.vp, top_off);
                let ok = self.construct_this(top, a[0], a[1], nslots, word);
                self.after_gc(&live);
                let r = self.load_i64(self.vp, top_off);
                let t = self.edge(inst, 0, &[r])?;
                let e = self.edge(inst, 1, &[])?;
                self.cond_br(ok, t, e);
            }
            Opcode::ObjEmulatesUndef => {
                // Only while some object's class emulates `undefined` (the
                // runtime's fuse) can one be falsy; the leaf says.
                let (yes, no, join) = (self.body.add_block(), self.body.add_block(), self.body.add_block());
                let r = self.body.add_blockparam(join, Type::I32);
                let dda = self.dda_possible();
                self.cond_br(dda, Self::to(yes), Self::to(no));
                self.cur = no;
                let z = self.i32c(0);
                self.terminate(Terminator::Br { target: BlockTarget { block: join, args: vec![z] } });
                self.cur = yes;
                let boxed = self.box_tagged(TAG_OBJECT, a[0]);
                let t = self.call1(self.h.to_boolean, &[self.cx, boxed], Type::I32);
                let f = self.un(Operator::I32Eqz, t, Type::I32);
                self.terminate(Terminator::Br { target: BlockTarget { block: join, args: vec![f] } });
                self.cur = join;
                self.def(inst, r);
            }
            Opcode::FnIsCtor => {
                let flags = self.load_i32(a[0], FUNC_FLAGS_SLOT_OFFSET);
                let cbit = self.i32c(FUNCTION_FLAGS_CONSTRUCTOR);
                let c = self.bin(Operator::I32And, flags, cbit, Type::I32);
                let z = self.i32c(0);
                let v = self.bin(Operator::I32Ne, c, z, Type::I32);
                self.def(inst, v);
            }
            Opcode::CtorStamp(layout, nfields, keep) => self.ctor_stamp_inline(a[0], layout, nfields, keep),
            Opcode::JsRt(r) => {
                use crate::mir::ops::RtOp;
                let h = self.h;
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
                    RtOp::NewObject => {
                        let cell = self.alloc_inline(inst, None)?;
                        (h.new_object, vec![cell])
                    }
                    RtOp::NewArray(len) => {
                        let cell = self.alloc_inline(inst, Some(len))?;
                        let lv = self.i32c(len);
                        (h.new_array, vec![lv, cell])
                    }
                    RtOp::InitProp(name, attrs) => {
                        let site = if attrs == crate::wasm::bbv::abi::INIT_ATTR_ENUMERATE {
                            self.init_prop_inline(inst, a[0], a[1])?
                        } else {
                            u32::MAX
                        };
                        let (at, av, sv) = (self.atom(name), self.i32c(attrs), self.i32c(site));
                        (h.init_prop, vec![a[0], at, a[1], av, sv])
                    }
                    RtOp::InitElem(attrs) => {
                        let key = self.f.insts[inst].args[1];
                        let index = match self.f.values[key].def {
                            mir::func::ValueDef::Result(i, _) => match self.f.insts[i].op {
                                Opcode::ConstVal(ConstVal::Int32(n)) => u32::try_from(n).ok(),
                                _ => None,
                            },
                            _ => None,
                        };
                        match index {
                            Some(i)
                                if attrs == crate::wasm::bbv::abi::INIT_ATTR_ENUMERATE
                                    && i < crate::constants::INLINE_INIT_ELEM_CAP =>
                            {
                                self.init_elem_inline(inst, a[0], i, a[2])?
                            }
                            _ => {}
                        }
                        let av = self.i32c(attrs);
                        (h.init_elem, vec![a[0], a[1], a[2], av])
                    }
                    RtOp::ToPropertyKey => (h.to_property_key, vec![a[0]]),
                    RtOp::RegExp(idx) => {
                        let script = self.script_ptr();
                        let iv = self.i32c(idx);
                        (h.regexp, vec![script, iv])
                    }
                    RtOp::InitPropGetSet(name, kind) => {
                        let (at, kv) = (self.atom(name), self.i32c(kind));
                        (h.init_prop_getset, vec![a[0], at, a[1], kv])
                    }
                };
                self.js_call(inst, f, &args, false)?;
            }
            Opcode::JsThrow => {
                // The helper sets the pending exception and always fails.
                // It may GC (capturing the stack): root what its throw exit
                // reads.
                let live = self.live_across(inst);
                self.root(&live)?;
                let top_off = self.top_off(live.len());
                let top = self.add_off(self.vp, top_off);
                self.call(self.h.throw, &[self.cx, top, a[0]], &[]);
                self.after_gc(&live);
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
                // `new Array()` (bbv's bump arm): the pristine Array
                // constructor, as its own new.target, makes what `[]` does.
                if a.len() == 3 && self.names_atom("Array") {
                    let (callee, nt) = (a[0], a[2]);
                    let is_arr = self.builtin_is(callee, crate::wasm::translate::BC_ARRAY_CTOR);
                    let same = self.bin(Operator::I64Eq, callee, nt, Type::I32);
                    let m = self.bin(Operator::I32And, is_arr, same, Type::I32);
                    let (arr, other) = (self.body.add_block(), self.body.add_block());
                    self.cond_br(m, Self::to(arr), Self::to(other));
                    self.cur = arr;
                    // The helper's reload rebinds the live values on its
                    // path only.
                    let saved = (self.vmap.clone(), self.slotted.clone(), self.dirty.clone(), self.framed.clone());
                    let cell = self.alloc_inline(inst, Some(0))?;
                    let lv = self.i32c(0);
                    let live = self.live_across(inst);
                    let (ok, r) = self.gc_call(self.h.new_array, &[lv, cell], &live)?;
                    let t = self.edge(inst, 1, &[r])?;
                    let e = self.edge(inst, 2, &[])?;
                    self.cond_br(ok, t, e);
                    (self.vmap, self.slotted, self.dirty, self.framed) = saved;
                    self.cur = other;
                }
                // The frame `[callee, this, args…, new.target]` above the
                // rooting slots, then the runtime's construct (it creates
                // `this` sized and seeded for the site, and runs the
                // constructor). The result lands at the frame's top.
                let live = self.live_across(inst);
                self.root(&live)?;
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
                self.after_gc(&live);
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
                if let Some(&bid) = self.gname_bids.get(&name) {
                    self.gname_bind_arms(inst, bid)?;
                }
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
                // The atom itself, from the startup-filled atom table (a
                // pinned atom never moves), as bbv's `emit_string_literal`:
                // one load, no allocation.
                let id = self.atoms.intern_chars(self.mm.atoms[name].chars());
                let slot = self.i32c(self.h.atom_table_slot);
                let tbl = self.load_i32(slot, 0);
                let v = self.load_i32(tbl, 4 * id);
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

    /// The inline arm of binding syntactic global name `bid` (bbv's
    /// `emit_bind_gname_inline`): with the binding's slot row resolved
    /// against the global's live shape (or re-resolved by the leaf), the
    /// binding object is the global object, taking `ok_clean`. Falls
    /// through to the helper otherwise.
    fn gname_bind_arms(&mut self, inst: mir::Inst, bid: u32) -> R<()> {
        let base = self.i32c(self.h.global_slots_base);
        let entry0 = self.load_i32(base, 8 * bid);
        let shape0 = self.load_i32(base, 8 * bid + 4);
        let one = self.i32c(1);
        let resolved0 = self.bin(Operator::I32And, entry0, one, Type::I32);
        let realm = self.load_i32(self.cx, JSCONTEXT_REALM_OFFSET);
        let global = self.load_i32(realm, REALM_GLOBAL_OFFSET);
        let live = self.load_i32(global, SHAPE_OFFSET);
        let same = self.bin(Operator::I32Eq, shape0, live, Type::I32);
        let hit = self.bin(Operator::I32And, resolved0, same, Type::I32);
        let (hit_b, resolve_b, slow) = (self.body.add_block(), self.body.add_block(), self.body.add_block());
        self.cond_br(hit, Self::to(hit_b), Self::to(resolve_b));
        self.cur = resolve_b;
        let b = self.i32c(bid);
        let entry1 = self.call1(self.h.resolve_global_slot_guarded, &[self.cx, b], Type::I32);
        let resolved1 = self.bin(Operator::I32And, entry1, one, Type::I32);
        self.cond_br(resolved1, Self::to(hit_b), Self::to(slow));
        self.cur = hit_b;
        let g = self.box_tagged(TAG_OBJECT, global);
        let t = self.edge(inst, 0, &[g])?;
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

    /// A get IC's inline ways (bbv's `emit_get_ic_inline_arms`): with
    /// `recv` an object whose shape one of the site's ways names (way 0 at
    /// `way0`, the rest `INLINE_IC_WAY_BYTES` apart from its row offset
    /// `way_off`), the value from its own fixed slot, or through the way's
    /// holder (a prototype method) while the holder keeps its shape,
    /// taking `ok_clean`; else `probe`.
    fn get_ic_ways(&mut self, inst: mir::Inst, recv: Value, way0: Value, way_off: u32, probe: Block) -> R<()> {
        use crate::region_shape::{INLINE_IC_WAYS, INLINE_IC_WAY_BYTES};
        let tag = self.tag_of(recv);
        let is_obj = self.tag_is(tag, TAG_OBJECT as u32);
        self.check(is_obj, probe);
        let obj = self.un(Operator::I32WrapI64, recv, Type::I32);
        let shape = self.load_i32(obj, SHAPE_OFFSET);
        let hit_b = self.body.add_block();
        let way = self.body.add_blockparam(hit_b, Type::I32);
        for w in 0..INLINE_IC_WAYS {
            let wb = if w == 0 {
                way0
            } else {
                let v = self.i32c(IC_WAY_ADDR_PLACEHOLDER);
                self.prop_ic_patches.push((v, way_off + w * INLINE_IC_WAY_BYTES));
                v
            };
            let wshape = self.load_i32(wb, IC_WAY_RECVSHAPE);
            let m = self.bin(Operator::I32Eq, shape, wshape, Type::I32);
            let next = if w + 1 < INLINE_IC_WAYS { self.body.add_block() } else { probe };
            self.cond_br(m, BlockTarget { block: hit_b, args: vec![wb] }, Self::to(next));
            self.cur = next;
        }
        self.cur = hit_b;
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

    /// The pristine `charCodeAt`/`charAt` on a linear string with an
    /// in-bounds int32 index, and `String.fromCharCode` of a code below 256
    /// (bbv's char arms): the char inline (`charAt` and `fromCharCode`
    /// only below 256, a static unit string), taking `ok_clean`; else
    /// branch to `other` (the call). The callee is compared against the
    /// startup-cached natives' bits: a monkeypatched one misses.
    fn char_arms(&mut self, inst: mir::Inst, ops: &[Value], other: Block) -> R<()> {
        let (callee, this, arg) = (ops[0], ops[1], ops[2]);
        let atag = self.tag_of(arg);
        let arg_int = self.tag_is(atag, TAG_INT32 as u32);
        let code = self.un(Operator::I32WrapI64, arg, Type::I32);
        let ccat_c = self.i32c(self.h.str_ccat_cell);
        let ccat = self.load_i64(ccat_c, 0);
        let cat_c = self.i32c(self.h.str_cat_cell);
        let cat = self.load_i64(cat_c, 0);
        let is_ccat = self.bin(Operator::I64Eq, callee, ccat, Type::I32);
        let is_cat = self.bin(Operator::I64Eq, callee, cat, Type::I32);
        let either = self.bin(Operator::I32Or, is_ccat, is_cat, Type::I32);
        let ttag = self.tag_of(this);
        let this_str = self.tag_is(ttag, TAG_STRING as u32);
        let m = self.bin(Operator::I32And, either, this_str, Type::I32);
        let m = self.bin(Operator::I32And, m, arg_int, Type::I32);
        let (chr, fcc) = (self.body.add_block(), self.body.add_block());
        self.cond_br(m, Self::to(chr), Self::to(fcc));
        // String.fromCharCode(code < 256): the static unit string.
        self.cur = fcc;
        let fcc_c = self.i32c(self.h.str_fcc_cell);
        let fcc_bits = self.load_i64(fcc_c, 0);
        let is_fcc = self.bin(Operator::I64Eq, callee, fcc_bits, Type::I32);
        let lim = self.i32c(256);
        let small = self.bin(Operator::I32LtU, code, lim, Type::I32);
        let f = self.bin(Operator::I32And, is_fcc, arg_int, Type::I32);
        let f = self.bin(Operator::I32And, f, small, Type::I32);
        self.check(f, other);
        let r = self.unit_string(code);
        let t = self.edge(inst, 0, &[r])?;
        self.terminate(Terminator::Br { target: t });
        // The char of a linear string.
        self.cur = chr;
        let sp = self.un(Operator::I32WrapI64, this, Type::I32);
        let flags = self.load_i32(sp, STRING_FLAGS_OFFSET);
        let lb = self.i32c(STRING_LINEAR_BIT);
        let lin = self.bin(Operator::I32And, flags, lb, Type::I32);
        self.check(lin, other);
        let len = self.load_i32(sp, STRING_LENGTH_OFFSET);
        let inb = self.bin(Operator::I32LtU, code, len, Type::I32);
        self.check(inb, other);
        let ib = self.i32c(STRING_INLINE_CHARS_BIT);
        let inl = self.bin(Operator::I32And, flags, ib, Type::I32);
        let outofline = self.load_i32(sp, STRING_CHARS_OFFSET);
        let inaddr = self.add_off(sp, STRING_CHARS_OFFSET);
        let chars = self.select(Type::I32, inaddr, outofline, inl);
        let latb = self.i32c(STRING_LATIN1_CHARS_BIT);
        let lat = self.bin(Operator::I32And, flags, latb, Type::I32);
        let (l8, l16, got) = (self.body.add_block(), self.body.add_block(), self.body.add_block());
        let c = self.body.add_blockparam(got, Type::I32);
        self.cond_br(lat, Self::to(l8), Self::to(l16));
        self.cur = l8;
        let a8 = self.bin(Operator::I32Add, chars, code, Type::I32);
        let m8 = self.mem(0, 0);
        let c8 = self.un(Operator::I32Load8U { memory: m8 }, a8, Type::I32);
        self.terminate(Terminator::Br {
            target: BlockTarget {
                block: got,
                args: vec![c8],
            },
        });
        self.cur = l16;
        let one = self.i32c(1);
        let off = self.bin(Operator::I32Shl, code, one, Type::I32);
        let a16 = self.bin(Operator::I32Add, chars, off, Type::I32);
        let m16 = self.mem(1, 0);
        let c16 = self.un(Operator::I32Load16U { memory: m16 }, a16, Type::I32);
        self.terminate(Terminator::Br {
            target: BlockTarget {
                block: got,
                args: vec![c16],
            },
        });
        self.cur = got;
        let (ccb, catb) = (self.body.add_block(), self.body.add_block());
        self.cond_br(is_ccat, Self::to(ccb), Self::to(catb));
        self.cur = ccb;
        let r = self.box_tagged(TAG_INT32, c);
        let t = self.edge(inst, 0, &[r])?;
        self.terminate(Terminator::Br { target: t });
        self.cur = catb;
        let lim = self.i32c(256);
        let small = self.bin(Operator::I32LtU, c, lim, Type::I32);
        self.check(small, other);
        let r = self.unit_string(c);
        let t = self.edge(inst, 0, &[r])?;
        self.terminate(Terminator::Br { target: t });
        Ok(())
    }

    /// The static unit string of code `c` (< 256), boxed.
    fn unit_string(&mut self, c: Value) -> Value {
        let slot = self.i32c(self.h.static_strings_slot);
        let tbl = self.load_i32(slot, 0);
        let two = self.i32c(2);
        let off = self.bin(Operator::I32Shl, c, two, Type::I32);
        let e = self.bin(Operator::I32Add, tbl, off, Type::I32);
        let atom = self.load_i32(e, 0);
        self.box_tagged(TAG_STRING, atom)
    }

    /// `x.length` for a string (its length word) or an array (its elements
    /// header's, when an int32), taking `ok_clean`; else branch to `other`.
    fn length_arms(&mut self, inst: mir::Inst, x: Value, other: Block) -> R<()> {
        let tag = self.tag_of(x);
        let (s_b, o_chk) = (self.body.add_block(), self.body.add_block());
        let is_str = self.tag_is(tag, TAG_STRING as u32);
        self.cond_br(is_str, Self::to(s_b), Self::to(o_chk));
        self.cur = s_b;
        let sp = self.un(Operator::I32WrapI64, x, Type::I32);
        let slen = self.load_i32(sp, STRING_LENGTH_OFFSET);
        let r = self.box_tagged(TAG_INT32, slen);
        let t = self.edge(inst, 0, &[r])?;
        self.terminate(Terminator::Br { target: t });
        self.cur = o_chk;
        let is_obj = self.tag_is(tag, TAG_OBJECT as u32);
        self.check(is_obj, other);
        let obj = self.un(Operator::I32WrapI64, x, Type::I32);
        let shape = self.load_i32(obj, SHAPE_OFFSET);
        let base = self.load_i32(shape, SHAPE_BASESHAPE_OFFSET);
        let clasp = self.load_i32(base, BASESHAPE_CLASP_OFFSET);
        let aslot = self.i32c(self.h.array_class_slot);
        let arr_class = self.load_i32(aslot, 0);
        let is_arr = self.bin(Operator::I32Eq, clasp, arr_class, Type::I32);
        let (arr_b, args_chk) = (self.body.add_block(), self.body.add_block());
        self.cond_br(is_arr, Self::to(arr_b), Self::to(args_chk));
        // An arguments object: its packed length (fixed slot 0, the count
        // above bit 5), unless the length was overwritten (bit 0).
        self.cur = args_chk;
        let acbase = self.i32c(self.h.args_class_base);
        let mapped = self.load_i32(acbase, 0);
        let unmapped = self.load_i32(acbase, 4);
        let m = self.bin(Operator::I32Eq, clasp, mapped, Type::I32);
        let u = self.bin(Operator::I32Eq, clasp, unmapped, Type::I32);
        let is_args = self.bin(Operator::I32Or, m, u, Type::I32);
        self.check(is_args, other);
        let packed = self.load_i32(obj, FIXED_SLOTS_BASE);
        let one = self.i32c(1);
        let over = self.bin(Operator::I32And, packed, one, Type::I32);
        let kept = self.un(Operator::I32Eqz, over, Type::I32);
        self.check(kept, other);
        let five = self.i32c(5);
        let argc = self.bin(Operator::I32ShrU, packed, five, Type::I32);
        let r = self.box_tagged(TAG_INT32, argc);
        let t = self.edge(inst, 0, &[r])?;
        self.terminate(Terminator::Br { target: t });
        self.cur = arr_b;
        let elements = self.load_i32(obj, OBJ_ELEMENTS_OFFSET);
        let back = self.i32c(ELEMENTS_LENGTH_BACK);
        let la = self.bin(Operator::I32Sub, elements, back, Type::I32);
        let alen = self.load_i32(la, 0);
        let z = self.i32c(0);
        let fits = self.bin(Operator::I32GeS, alen, z, Type::I32);
        self.check(fits, other);
        let r = self.box_tagged(TAG_INT32, alen);
        let t = self.edge(inst, 0, &[r])?;
        self.terminate(Terminator::Br { target: t });
        Ok(())
    }

    /// A layout constructor's first stamp of its completed `this`, inline
    /// (bbv's `emit_class_idx_stamp_impl`; `night_runtime_ctor_stamp`'s
    /// gates): an object still under construction whose early key is ours
    /// or none, with a slot span covering the row, gets the layout's idx
    /// plus the validity bits that survived construction.
    fn ctor_stamp_inline(&mut self, thisv: Value, layout: u32, nfields: u32, keep: u32) {
        let done = self.body.add_block();
        let tag = self.tag_of(thisv);
        let is_obj = self.tag_is(tag, TAG_OBJECT as u32);
        self.check(is_obj, done);
        let obj = self.un(Operator::I32WrapI64, thisv, Type::I32);
        let w0 = self.load_i32(obj, OBJ_CLASS_IDX_OFFSET);
        let sb = self.i32c(CLASS_WORD_SENTINEL);
        let sent = self.bin(Operator::I32And, w0, sb, Type::I32);
        self.check(sent, done);
        let km = self.i32c(EARLY_KEY_MAX << EARLY_KEY_SHIFT);
        let key = self.bin(Operator::I32And, w0, km, Type::I32);
        let z = self.i32c(0);
        let none = self.bin(Operator::I32Eq, key, z, Type::I32);
        let mine = self.i32c((layout + 1) << EARLY_KEY_SHIFT);
        let ours = self.bin(Operator::I32Eq, key, mine, Type::I32);
        let owned = self.bin(Operator::I32Or, none, ours, Type::I32);
        self.check(owned, done);
        let shape = self.load_i32(obj, SHAPE_OFFSET);
        let imm = self.load_i32(shape, SHAPE_IMMUTABLE_FLAGS_OFFSET);
        let sh = self.i32c(SHAPE_SMALL_SLOTSPAN_SHIFT);
        let span = self.bin(Operator::I32ShrU, imm, sh, Type::I32);
        let sm = self.i32c(SHAPE_SMALL_SLOTSPAN_MASK_BITS);
        let span = self.bin(Operator::I32And, span, sm, Type::I32);
        let n = self.i32c(nfields);
        let covers = self.bin(Operator::I32GeU, span, n, Type::I32);
        self.check(covers, done);
        let kb = self.i32c(keep);
        let bits = self.bin(Operator::I32And, w0, kb, Type::I32);
        let idx = self.i32c(layout + 1);
        let w = self.bin(Operator::I32Or, idx, bits, Type::I32);
        self.store_i32(obj, OBJ_CLASS_IDX_OFFSET, w);
        self.terminate(Terminator::Br { target: Self::to(done) });
        self.cur = done;
    }

    /// `x === k` for a `StrictConstantEq` operand `k` (the high byte its
    /// type: 2 boolean, 3 undefined, 4 null, else an int8), as a raw bool.
    fn constant_strict_eq(&mut self, x: Value, k: u16) -> Value {
        let (ty, lo) = ((k >> 8) & 0xFF, (k & 0xFF) as u8);
        let tag = self.tag_of(x);
        match ty {
            3 => self.tag_is(tag, TAG_UNDEFINED as u32),
            4 => self.tag_is(tag, TAG_NULL as u32),
            2 => {
                let want = self.i64c((TAG_BOOLEAN << 32) | u64::from(lo & 1));
                self.bin(Operator::I64Eq, x, want, Type::I32)
            }
            _ => {
                // An int32 of that value, or a double equal to it.
                let n = i32::from(lo as i8);
                let is_int = self.tag_is(tag, TAG_INT32 as u32);
                let low = self.un(Operator::I32WrapI64, x, Type::I32);
                let nv = self.i32c(n as u32);
                let low_eq = self.bin(Operator::I32Eq, low, nv, Type::I32);
                let int_eq = self.bin(Operator::I32And, is_int, low_eq, Type::I32);
                let it = self.i32c(TAG_INT32 as u32);
                let is_dbl = self.bin(Operator::I32LtU, tag, it, Type::I32);
                let d = self.un(Operator::F64ReinterpretI64, x, Type::F64);
                let dv = self.f64c(f64::from(n).to_bits());
                let dbl_eq = self.bin(Operator::F64Eq, d, dv, Type::I32);
                let dbl_eq = self.bin(Operator::I32And, is_dbl, dbl_eq, Type::I32);
                self.bin(Operator::I32Or, int_eq, dbl_eq, Type::I32)
            }
        }
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
    /// Element `idx` of native object `obj`: its address, branching to
    /// `fail` unless in bounds (and, with `load`, the value, unless a hole).
    fn elem_addr(&mut self, obj: Value, idx: Value, fail: Block, load: bool) -> (Value, Option<Value>) {
        let elements = self.load_i32(obj, OBJ_ELEMENTS_OFFSET);
        let back = self.i32c(ELEMENTS_INITLEN_BACK);
        let header = self.bin(Operator::I32Sub, elements, back, Type::I32);
        let initlen = self.load_i32(header, 0);
        let in_bounds = self.bin(Operator::I32LtU, idx, initlen, Type::I32);
        self.check(in_bounds, fail);
        let eight = self.i32c(8);
        let off = self.bin(Operator::I32Mul, idx, eight, Type::I32);
        let addr = self.bin(Operator::I32Add, elements, off, Type::I32);
        if !load {
            return (addr, None);
        }
        let v = self.load_i64(addr, 0);
        let vtag = self.tag_of(v);
        let hole = self.tag_is(vtag, TAG_MAGIC as u32);
        let not_hole = self.un(Operator::I32Eqz, hole, Type::I32);
        self.check(not_hole, fail);
        (addr, Some(v))
    }

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
        if ops.len() == 3 {
            let call = self.body.add_block();
            self.char_arms(inst, ops, call)?;
            self.cur = call;
            if self.names_atom("push") {
                let call = self.body.add_block();
                self.push_arm(inst, ops, call)?;
                self.cur = call;
            }
        }
        if ops.len() == 2 && self.names_atom("pop") {
            let call = self.body.add_block();
            self.pop_arm(inst, ops, call)?;
            self.cur = call;
        }
        // A leaf: nothing to root yet.
        let (funcidx, script, native) = self.classify_native(ops[0]);
        if ops.len() == 3 || ops.len() == 4 {
            let call = self.body.add_block();
            self.math_arms(inst, ops, native, call)?;
            self.cur = call;
        }
        let live = self.live_across(inst);
        self.root(&live)?;
        let frame = self.top_off(live.len());
        for (k, &v) in ops.iter().enumerate() {
            self.store_i64(self.vp, frame + 8 * u32::try_from(k).unwrap(), v);
        }
        let argc = u32::try_from(ops.len() - 2).unwrap();
        let top_off = frame + 8 * (argc + 2);
        let base = self.add_off(self.vp, frame);
        let top = self.add_off(self.vp, top_off);
        let z = self.i32c(0);
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
        self.after_gc(&live);
        let result = self.load_i64(self.vp, top_off);
        let t = self.edge(inst, 1, &[result])?;
        let e = self.edge(inst, 2, &[])?;
        self.cond_br(ok, t, e);
        Ok(())
    }

    /// An object or array literal (`array_len`) from the site's
    /// inline-alloc cell (bbv's `emit_alloc_inline`): with the cell filled
    /// and room in the nursery, bump and write the header the cell holds
    /// (an array's elements inline, empty), taking `ok_clean`. Returns the
    /// cell, for the helper that fills it, with `cur` on the miss.
    fn alloc_inline(&mut self, inst: mir::Inst, array_len: Option<u32>) -> R<Value> {
        let cell = self.i32c(ALLOC_CELL_ADDR_PLACEHOLDER);
        let idx = self.atoms.next_alloc_cell();
        self.alloc_cell_patches.push((cell, idx));
        let slow = self.body.add_block();
        let shape = self.load_i32(cell, 0);
        self.check(shape, slow);
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
        self.store_i32(obj, SHAPE_OFFSET, shape);
        let z = self.i32c(0);
        self.store_i32(obj, OBJ_CLASS_IDX_OFFSET, z);
        let slots = self.load_i32(cell, 8);
        self.store_i32(obj, NATIVE_SLOTS_OFFSET, slots);
        match array_len {
            None => {
                let elems = self.load_i32(cell, 12);
                self.store_i32(obj, OBJ_ELEMENTS_OFFSET, elems);
            }
            Some(_) => {
                let eoff = self.load_i32(cell, 12);
                let elems = self.bin(Operator::I32Add, obj, eoff, Type::I32);
                self.store_i32(obj, OBJ_ELEMENTS_OFFSET, elems);
                let ehdr = self.elem_header_addr(elems, ELEMENTS_HEADER_BYTES);
                let flags = self.load_i32(cell, 20);
                self.store_i32(ehdr, 0, flags);
                self.store_i32(ehdr, 4, z);
                let cap = self.load_i32(cell, 24);
                self.store_i32(ehdr, 8, cap);
                let len = self.load_i32(cell, 28);
                self.store_i32(ehdr, 12, len);
            }
        }
        let r = self.box_tagged(TAG_OBJECT, obj);
        let t = self.edge(inst, 0, &[r])?;
        self.terminate(Terminator::Br { target: t });
        self.cur = slow;
        Ok(cell)
    }

    /// `InitProp` on a literal under construction (bbv's `emit_init_prop`):
    /// replay the site's add transition from its IC row (the helper fills
    /// it) while the literal has the row's old shape: store the value in
    /// the fresh slot (no pre-barrier: nothing was there), swap in the new
    /// shape, taking `ok_clean`. Literals carry no class word, so no stamp
    /// bit needs keeping. Returns the site's cache index, with `cur` on
    /// the miss.
    fn init_prop_inline(&mut self, inst: mir::Inst, objv: Value, val: Value) -> R<u32> {
        let cache = self.atoms.next_prop_cache();
        let slow = self.body.add_block();
        let obj = self.un(Operator::I32WrapI64, objv, Type::I32);
        let shape = self.load_i32(obj, SHAPE_OFFSET);
        let row = self.i32c(IC_WAY_ADDR_PLACEHOLDER);
        self.prop_ic_patches.push((row, cache * INLINE_IC_STRIDE + IC_TRANS_ROW_OFF));
        let old = self.load_i32(row, IC_TRANS_OLDSHAPE);
        let same = self.bin(Operator::I32Eq, old, shape, Type::I32);
        self.check(same, slow);
        let off = self.load_i32(row, IC_TRANS_SLOTOFF);
        self.check(off, slow);
        let addr = self.bin(Operator::I32Add, obj, off, Type::I32);
        self.store_i64(addr, 0, val);
        let new_s = self.load_i32(row, IC_TRANS_NEWSHAPE);
        self.store_i32(obj, SHAPE_OFFSET, new_s);
        let abs = self.load_i32(row, IC_TRANS_ABSSLOT);
        self.post_barrier(self.h.post_write_barrier, obj, abs, val);
        let t = self.edge(inst, 0, &[])?;
        self.terminate(Terminator::Br { target: t });
        self.cur = slow;
        Ok(cache)
    }

    /// Native `Math` calls on numbers (bbv's arms), matched by the callee's
    /// `JSNative` against the pristine natives table, so a replaced or
    /// self-hosted clone is told apart without fuses: one-argument
    /// sqrt/abs/floor/ceil/trunc/fround inline, sin/cos by a leaf, clz32;
    /// two-argument min/max inline, pow by a leaf, imul. The result takes
    /// `ok_clean`; anything else goes to `other`.
    fn math_arms(&mut self, inst: mir::Inst, ops: &[Value], native: Value, other: Block) -> R<()> {
        use crate::wasm::translate::{
            MN_ABS, MN_CEIL, MN_CLZ32, MN_COS, MN_FLOOR, MN_FROUND, MN_IMUL, MN_MAX, MN_MIN, MN_POW,
            MN_SIN, MN_SQRT, MN_TRUNC,
        };
        self.check(native, other);
        let cp = self.un(Operator::I32WrapI64, ops[0], Type::I32);
        let nf = self.load_i32(cp, FUNC_ENV_SLOT_OFFSET);
        let is = |s: &mut Self, idx: u32| {
            let c = s.i32c(s.h.math_natives_base + 4 * idx);
            let slot = s.load_i32(c, 0);
            s.bin(Operator::I32Eq, nf, slot, Type::I32)
        };
        let is_num = |s: &mut Self, v: Value| {
            let t = s.tag_of(v);
            let k = s.i32c(TAG_INT32 as u32);
            s.bin(Operator::I32LeU, t, k, Type::I32)
        };
        let done = self.body.add_block();
        let res = self.body.add_blockparam(done, Type::F64);
        if ops.len() == 3 {
            let x = ops[2];
            let num = is_num(self, x);
            self.check(num, other);
            let f = self.to_f64(x);
            let (sqrt, abs, floor, ceil) = (is(self, MN_SQRT), is(self, MN_ABS), is(self, MN_FLOOR), is(self, MN_CEIL));
            let (trunc, fround, sin, cos) = (is(self, MN_TRUNC), is(self, MN_FROUND), is(self, MN_SIN), is(self, MN_COS));
            let clz = is(self, MN_CLZ32);
            // clz32: ToUint32 then i32.clz (|f| < 2^63 truncates exactly).
            let (clz_b, rest) = (self.body.add_block(), self.body.add_block());
            self.cond_br(clz, Self::to(clz_b), Self::to(rest));
            self.cur = clz_b;
            let af = self.un(Operator::F64Abs, f, Type::F64);
            let lim = self.f64c(9223372036854775808.0f64.to_bits());
            let ok = self.bin(Operator::F64Lt, af, lim, Type::I32);
            self.check(ok, other);
            let i = self.un(Operator::I64TruncSatF64S, f, Type::I64);
            let i = self.un(Operator::I32WrapI64, i, Type::I32);
            let c = self.un(Operator::I32Clz, i, Type::I32);
            let r = self.box_tagged(TAG_INT32, c);
            let t = self.edge(inst, 0, &[r])?;
            self.terminate(Terminator::Br { target: t });
            self.cur = rest;
            let trig = self.bin(Operator::I32Or, sin, cos, Type::I32);
            let (trig_b, opc) = (self.body.add_block(), self.body.add_block());
            self.cond_br(trig, Self::to(trig_b), Self::to(opc));
            self.cur = trig_b;
            let r = self.call1(self.h.math_unary, &[cos, f], Type::F64);
            self.terminate(Terminator::Br { target: BlockTarget { block: done, args: vec![r] } });
            self.cur = opc;
            let a = self.bin(Operator::I32Or, sqrt, abs, Type::I32);
            let b = self.bin(Operator::I32Or, floor, ceil, Type::I32);
            let c = self.bin(Operator::I32Or, trunc, fround, Type::I32);
            let any = self.bin(Operator::I32Or, a, b, Type::I32);
            let any = self.bin(Operator::I32Or, any, c, Type::I32);
            self.check(any, other);
            let r_sqrt = self.un(Operator::F64Sqrt, f, Type::F64);
            let r_abs = self.un(Operator::F64Abs, f, Type::F64);
            let r_floor = self.un(Operator::F64Floor, f, Type::F64);
            let r_ceil = self.un(Operator::F64Ceil, f, Type::F64);
            let r_trunc = self.un(Operator::F64Trunc, f, Type::F64);
            let f32v = self.un(Operator::F32DemoteF64, f, Type::F32);
            let r_fround = self.un(Operator::F64PromoteF32, f32v, Type::F64);
            let sel = self.select(Type::F64, r_trunc, r_fround, trunc);
            let sel = self.select(Type::F64, r_ceil, sel, ceil);
            let sel = self.select(Type::F64, r_floor, sel, floor);
            let sel = self.select(Type::F64, r_abs, sel, abs);
            let r = self.select(Type::F64, r_sqrt, sel, sqrt);
            self.terminate(Terminator::Br { target: BlockTarget { block: done, args: vec![r] } });
        } else {
            let (x, y) = (ops[2], ops[3]);
            let nx = is_num(self, x);
            let ny = is_num(self, y);
            let both = self.bin(Operator::I32And, nx, ny, Type::I32);
            self.check(both, other);
            let (fx, fy) = (self.to_f64(x), self.to_f64(y));
            let (min, max, pow, imul) = (is(self, MN_MIN), is(self, MN_MAX), is(self, MN_POW), is(self, MN_IMUL));
            let (imul_b, rest) = (self.body.add_block(), self.body.add_block());
            self.cond_br(imul, Self::to(imul_b), Self::to(rest));
            // imul: ToInt32 of each (|f| < 2^63 truncates exactly), i32.mul.
            self.cur = imul_b;
            let lim = self.f64c(9223372036854775808.0f64.to_bits());
            let ax = self.un(Operator::F64Abs, fx, Type::F64);
            let ay = self.un(Operator::F64Abs, fy, Type::F64);
            let sx = self.bin(Operator::F64Lt, ax, lim, Type::I32);
            let sy = self.bin(Operator::F64Lt, ay, lim, Type::I32);
            let safe = self.bin(Operator::I32And, sx, sy, Type::I32);
            self.check(safe, other);
            let ix = self.un(Operator::I64TruncSatF64S, fx, Type::I64);
            let ix = self.un(Operator::I32WrapI64, ix, Type::I32);
            let iy = self.un(Operator::I64TruncSatF64S, fy, Type::I64);
            let iy = self.un(Operator::I32WrapI64, iy, Type::I32);
            let m = self.bin(Operator::I32Mul, ix, iy, Type::I32);
            let r = self.box_tagged(TAG_INT32, m);
            let t = self.edge(inst, 0, &[r])?;
            self.terminate(Terminator::Br { target: t });
            self.cur = rest;
            let (pow_b, mm) = (self.body.add_block(), self.body.add_block());
            self.cond_br(pow, Self::to(pow_b), Self::to(mm));
            self.cur = pow_b;
            let r = self.call1(self.h.math_pow, &[fx, fy], Type::F64);
            self.terminate(Terminator::Br { target: BlockTarget { block: done, args: vec![r] } });
            self.cur = mm;
            let any = self.bin(Operator::I32Or, min, max, Type::I32);
            self.check(any, other);
            let r_min = self.bin(Operator::F64Min, fx, fy, Type::F64);
            let r_max = self.bin(Operator::F64Max, fx, fy, Type::F64);
            let r = self.select(Type::F64, r_min, r_max, min);
            self.terminate(Terminator::Br { target: BlockTarget { block: done, args: vec![r] } });
        }
        self.cur = done;
        let b = self.box_number(res);
        let t = self.edge(inst, 0, &[b])?;
        self.terminate(Terminator::Br { target: t });
        Ok(())
    }

    /// `InitElemArray index` filling an array literal (bbv's
    /// `emit_init_elem_array`): with a value that is neither a GC thing
    /// (no barrier) nor the hole, an unstamped array (no element claim to
    /// keep), dense elements with no flag but FIXED, and the initialized
    /// length at `index` with room, store and bump it, taking `ok_clean`;
    /// `cur` is left on the miss.
    fn init_elem_inline(&mut self, inst: mir::Inst, arr: Value, index: u32, val: Value) -> R<()> {
        use crate::wasm::bbv::abi::ELEMENTS_FLAG_FIXED;
        let slow = self.body.add_block();
        let vt = self.tag_of(val);
        let magic = self.i32c(TAG_MAGIC as u32);
        let v_ok = self.bin(Operator::I32LtU, vt, magic, Type::I32);
        let at = self.tag_of(arr);
        let a_obj = self.tag_is(at, TAG_OBJECT as u32);
        let ok = self.bin(Operator::I32And, v_ok, a_obj, Type::I32);
        self.check(ok, slow);
        let obj = self.un(Operator::I32WrapI64, arr, Type::I32);
        let word = self.load_i32(obj, OBJ_CLASS_IDX_OFFSET);
        let unstamped = self.un(Operator::I32Eqz, word, Type::I32);
        self.check(unstamped, slow);
        let elems = self.load_i32(obj, OBJ_ELEMENTS_OFFSET);
        let flags = self.elem_header(elems, ELEMENTS_FLAGS_BACK);
        let initlen = self.elem_header(elems, ELEMENTS_INITLEN_BACK);
        let cap = self.elem_header(elems, ELEMENTS_CAPACITY_BACK);
        let len = self.elem_header(elems, ELEMENTS_LENGTH_BACK);
        let nf = self.i32c(!ELEMENTS_FLAG_FIXED);
        let rest = self.bin(Operator::I32And, flags, nf, Type::I32);
        let f_ok = self.un(Operator::I32Eqz, rest, Type::I32);
        let iv = self.i32c(index);
        let i_ok = self.bin(Operator::I32Eq, initlen, iv, Type::I32);
        let c_ok = self.bin(Operator::I32GtU, cap, iv, Type::I32);
        let l_ok = self.bin(Operator::I32GtU, len, iv, Type::I32);
        let a = self.bin(Operator::I32And, f_ok, i_ok, Type::I32);
        let b = self.bin(Operator::I32And, c_ok, l_ok, Type::I32);
        let all = self.bin(Operator::I32And, a, b, Type::I32);
        self.check(all, slow);
        self.store_i64(elems, index * 8, val);
        let nl = self.i32c(index + 1);
        self.set_elem_header(elems, ELEMENTS_INITLEN_BACK, nl);
        let t = self.edge(inst, 0, &[])?;
        self.terminate(Terminator::Br { target: t });
        self.cur = slow;
        Ok(())
    }

    /// Whether the function names atom `s` (a builtin arm's gate, as bbv's
    /// `script_names_push`: an arm costs code where it never fires).
    fn names_atom(&self, s: &str) -> bool {
        self.mm.atoms.iter().any(|(_, a)| a.chars().iter().copied().eq(s.encode_utf16()))
    }

    /// Whether boxed `callee` is the pristine builtin of cell `idx`.
    fn builtin_is(&mut self, callee: Value, idx: u32) -> Value {
        let c = self.i32c(self.h.builtin_cells_base + 8 * idx);
        let bits = self.load_i64(c, 0);
        self.bin(Operator::I64Eq, callee, bits, Type::I32)
    }

    /// `Array.prototype.push(v)` on a dense array, call-free (bbv's push
    /// arm): with the elements packed, room left, and the receiver's shape
    /// in the append cache with its protos' shapes unchanged (no indexed
    /// property can appear on them), store at the end and bump the
    /// initialized length and `length`, taking `ok_clean` with the new
    /// length; else `other`.
    fn push_arm(&mut self, inst: mir::Inst, ops: &[Value], other: Block) -> R<()> {
        let (callee, this, arg) = (ops[0], ops[1], ops[2]);
        let is_push = self.builtin_is(callee, BC_ARR_PUSH);
        let ttag = self.tag_of(this);
        let this_obj = self.tag_is(ttag, TAG_OBJECT as u32);
        let m = self.bin(Operator::I32And, is_push, this_obj, Type::I32);
        self.check(m, other);
        let obj = self.un(Operator::I32WrapI64, this, Type::I32);
        let elements = self.load_i32(obj, OBJ_ELEMENTS_OFFSET);
        let flags = self.elem_header(elements, ELEMENTS_FLAGS_BACK);
        let initlen = self.elem_header(elements, ELEMENTS_INITLEN_BACK);
        let cap = self.elem_header(elements, ELEMENTS_CAPACITY_BACK);
        let len = self.elem_header(elements, ELEMENTS_LENGTH_BACK);
        let bm = self.i32c(ELEMENTS_PUSH_BAIL_MASK);
        let bail = self.bin(Operator::I32And, flags, bm, Type::I32);
        let flags_ok = self.un(Operator::I32Eqz, bail, Type::I32);
        let len_eq = self.bin(Operator::I32Eq, len, initlen, Type::I32);
        let has_cap = self.bin(Operator::I32LtU, initlen, cap, Type::I32);
        let imax = self.i32c(0x7FFF_FFFF);
        let fits = self.bin(Operator::I32LtU, len, imax, Type::I32);
        let a = self.bin(Operator::I32And, flags_ok, len_eq, Type::I32);
        let b = self.bin(Operator::I32And, has_cap, fits, Type::I32);
        let ok = self.bin(Operator::I32And, a, b, Type::I32);
        self.check(ok, other);
        let (row, hit) = self.append_row(obj);
        self.check(hit, other);
        let arr = self.load_i32(row, 20);
        self.check(arr, other);
        for k in 0..2 {
            let p = self.load_i32(row, 4 + 8 * k);
            let s = self.load_i32(row, 8 + 8 * k);
            // A null proto's row word is 0; its shape load reads the
            // (mapped) zero page's word, which the `or` discards.
            let live = self.load_i32(p, SHAPE_OFFSET);
            let empty = self.un(Operator::I32Eqz, p, Type::I32);
            let same = self.bin(Operator::I32Eq, live, s, Type::I32);
            let okp = self.bin(Operator::I32Or, empty, same, Type::I32);
            self.check(okp, other);
        }
        let three = self.i32c(3);
        let off = self.bin(Operator::I32Shl, initlen, three, Type::I32);
        let addr = self.bin(Operator::I32Add, elements, off, Type::I32);
        self.store_i64(addr, 0, arg);
        let one = self.i32c(1);
        let newlen = self.bin(Operator::I32Add, initlen, one, Type::I32);
        self.set_elem_header(elements, ELEMENTS_INITLEN_BACK, newlen);
        self.set_elem_header(elements, ELEMENTS_LENGTH_BACK, newlen);
        let f = self.h.post_write_barrier_elem;
        self.post_barrier(f, obj, initlen, arg);
        let r = self.box_tagged(TAG_INT32, newlen);
        let t = self.edge(inst, 0, &[r])?;
        self.terminate(Terminator::Br { target: t });
        Ok(())
    }

    /// The append-cache row for `obj`'s shape, and whether it is that
    /// shape's (the row's first word).
    fn append_row(&mut self, obj: Value) -> (Value, Value) {
        let shape = self.load_i32(obj, SHAPE_OFFSET);
        let three = self.i32c(3);
        let sh = self.bin(Operator::I32ShrU, shape, three, Type::I32);
        let k1 = self.i32c(2654435761);
        let h = self.bin(Operator::I32Mul, sh, k1, Type::I32);
        let mask = self.i32c(APPEND_CACHE_SIZE - 1);
        let ridx = self.bin(Operator::I32And, h, mask, Type::I32);
        let stride = self.i32c(APPEND_CACHE_ENTRY_BYTES);
        let roff = self.bin(Operator::I32Mul, ridx, stride, Type::I32);
        let base = self.i32c(self.h.append_cache_base);
        let row = self.bin(Operator::I32Add, base, roff, Type::I32);
        let rshape = self.load_i32(row, 0);
        let hit = self.bin(Operator::I32Eq, shape, rshape, Type::I32);
        (row, hit)
    }

    /// The address of the elements header word `back` bytes below
    /// `elements`.
    fn elem_header_addr(&mut self, elements: Value, back: u32) -> Value {
        let k = self.i32c(back);
        self.bin(Operator::I32Sub, elements, k, Type::I32)
    }

    fn elem_header(&mut self, elements: Value, back: u32) -> Value {
        let a = self.elem_header_addr(elements, back);
        self.load_i32(a, 0)
    }

    fn set_elem_header(&mut self, elements: Value, back: u32, v: Value) {
        let a = self.elem_header_addr(elements, back);
        self.store_i32(a, 0, v);
    }

    /// `Array.prototype.pop()` on a dense array (bbv's pop arm): with the
    /// elements packed and non-empty, no incremental marking (the dropped
    /// element would lose its barrier), and no hole at the end, shrink by
    /// one, taking `ok_clean` with the last element; else `other`.
    fn pop_arm(&mut self, inst: mir::Inst, ops: &[Value], other: Block) -> R<()> {
        let (callee, this) = (ops[0], ops[1]);
        let is_pop = self.builtin_is(callee, BC_ARR_POP);
        let ttag = self.tag_of(this);
        let this_obj = self.tag_is(ttag, TAG_OBJECT as u32);
        let m = self.bin(Operator::I32And, is_pop, this_obj, Type::I32);
        self.check(m, other);
        let obj = self.un(Operator::I32WrapI64, this, Type::I32);
        let shape = self.load_i32(obj, SHAPE_OFFSET);
        let base = self.load_i32(shape, SHAPE_BASESHAPE_OFFSET);
        let clasp = self.load_i32(base, BASESHAPE_CLASP_OFFSET);
        let aslot = self.i32c(self.h.array_class_slot);
        let arr_class = self.load_i32(aslot, 0);
        let is_arr = self.bin(Operator::I32Eq, clasp, arr_class, Type::I32);
        self.check(is_arr, other);
        let elements = self.load_i32(obj, OBJ_ELEMENTS_OFFSET);
        let flags = self.elem_header(elements, ELEMENTS_FLAGS_BACK);
        let initlen = self.elem_header(elements, ELEMENTS_INITLEN_BACK);
        let len = self.elem_header(elements, ELEMENTS_LENGTH_BACK);
        let bm = self.i32c(ELEMENTS_POP_BAIL_MASK);
        let bail = self.bin(Operator::I32And, flags, bm, Type::I32);
        let flags_ok = self.un(Operator::I32Eqz, bail, Type::I32);
        let len_eq = self.bin(Operator::I32Eq, len, initlen, Type::I32);
        let z = self.i32c(0);
        let nonempty = self.bin(Operator::I32Ne, len, z, Type::I32);
        let zone = self.load_i32(self.cx, JSCONTEXT_ZONE_OFFSET);
        let needs = self.load_i32(zone, ZONE_NEEDS_BARRIER_OFFSET);
        let no_barrier = self.un(Operator::I32Eqz, needs, Type::I32);
        let a = self.bin(Operator::I32And, flags_ok, len_eq, Type::I32);
        let b = self.bin(Operator::I32And, nonempty, no_barrier, Type::I32);
        let ok = self.bin(Operator::I32And, a, b, Type::I32);
        self.check(ok, other);
        let one = self.i32c(1);
        let newlen = self.bin(Operator::I32Sub, len, one, Type::I32);
        let three = self.i32c(3);
        let off = self.bin(Operator::I32Shl, newlen, three, Type::I32);
        let addr = self.bin(Operator::I32Add, elements, off, Type::I32);
        let elem = self.load_i64(addr, 0);
        let etag = self.tag_of(elem);
        let hole = self.tag_is(etag, TAG_MAGIC as u32);
        let not_hole = self.un(Operator::I32Eqz, hole, Type::I32);
        self.check(not_hole, other);
        self.set_elem_header(elements, ELEMENTS_INITLEN_BACK, newlen);
        self.set_elem_header(elements, ELEMENTS_LENGTH_BACK, newlen);
        let t = self.edge(inst, 0, &[elem])?;
        self.terminate(Terminator::Br { target: t });
        Ok(())
    }

    /// `night_call_classify` of boxed `callee`: its funcref-table index (0
    /// when not compiled or not a scripted function) and its `JSScript*`.
    fn classify(&mut self, callee: Value) -> (Value, Value) {
        let (f, s, _) = self.classify_native(callee);
        (f, s)
    }

    /// `classify`, and whether the callee is a native function (known
    /// only on a cell miss: the cell holds scripted callees).
    fn classify_native(&mut self, callee: Value) -> (Value, Value, Value) {
        // The site's value cell (bbv's `emit_inline_classify`): the steady
        // state is one callee repeating, and a hit is the whole classify.
        // The fill caches tenured functions only, and a major GC zeroes
        // the region; a zero row never false-hits (it is the double +0).
        let cell = self.i32c(CALL_CELL_ADDR_PLACEHOLDER);
        let idx = self.atoms.next_call_cell();
        self.call_cell_patches.push((cell, idx + 1));
        let trash = self.i32c(CALL_CELL_ADDR_PLACEHOLDER);
        self.call_cell_patches.push((trash, 0));
        let done = self.body.add_block();
        let fp = self.body.add_blockparam(done, Type::I32);
        let sp = self.body.add_blockparam(done, Type::I32);
        let np = self.body.add_blockparam(done, Type::I32);
        let cached = self.load_i64(cell, 0);
        let f = self.load_i32(cell, CALL_CELL_FUNCIDX);
        let sc = self.load_i32(cell, CALL_CELL_SCRIPT);
        let hit = self.bin(Operator::I64Eq, callee, cached, Type::I32);
        let miss = self.body.add_block();
        let z = self.i32c(0);
        self.cond_br(
            hit,
            BlockTarget {
                block: done,
                args: vec![f, sc, z],
            },
            Self::to(miss),
        );
        self.cur = miss;
        let args = self.body.arg_pool.from_iter([callee, cell, trash].into_iter());
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
        let native = self.push_val(ValueDef::PickOutput(cls, 2, Type::I32));
        self.terminate(Terminator::Br {
            target: BlockTarget {
                block: done,
                args: vec![funcidx, script, native],
            },
        });
        self.cur = done;
        (fp, sp, np)
    }

    /// `inline.enter` (§5.5): the inlined callee's frame, as its
    /// prologue would write it, from `callee, this, formals`. Every slot
    /// up to the frame's end is made a valid Value: helpers' GC scan limit
    /// inside the callee is that end.
    fn inline_enter(&mut self, d: &mir::func::InstData, a: &[Value]) -> R<()> {
        let fid = self.cur_frame as usize;
        self.framed.retain(|&(f, _), _| f as usize != fid);
        let (base, l) = (self.frame_off[fid], self.frame_layouts[fid]);
        let max_depth = self.f.inline_frames[fid - 1].max_depth;
        // A construct also passes its new.target.
        let construct = a.len() == 3 + l.nargs as usize;
        if a.len() != 2 + l.nargs as usize && !construct {
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
        let nt = if construct { boxed[boxed.len() - 1] } else { undef };
        self.store_i64(sp, base + l.new_target(), nt);
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
    /// body from `pc`. Write the operands (the frame holds only those
    /// written through, the formals of a mapped `arguments`), the resume
    /// word, then call the callee's entry with `ARGC_RESUME_BIT` on its
    /// frame. The caller continues on `ok` with the callee's result, or on
    /// `err`.
    #[allow(clippy::too_many_arguments)]
    /// Count this exit (`--mir-exit-census`), with its static record.
    fn census_exit(&mut self, script: ScriptId, pc: Pc, what: &str) {
        let Some(census) = self.exit_census else { return };
        static NEXT: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
        let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        crate::diag_line!("night: mir exit {id} sid#{script} pc {pc} {what}");
        let (k, i) = (
            self.i32c(crate::options::MIR_EXIT_CENSUS_KIND),
            self.i32c(id),
        );
        self.call1(census, &[k, i], Type::I32);
    }

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
        let fid = self.cur_frame;
        let callee = self.f.inline_frames[fid as usize - 1].script;
        let max_depth = self.f.inline_frames[fid as usize - 1].max_depth;
        let what = format!("inline{} in sid#{}", if throw { " throw" } else { "" }, self.f.script);
        self.census_exit(callee, pc, &what);
        // Rooted here, on the site's own state: the caller's managed values
        // live across the call (the same set at every exit of this frame,
        // which all continue at the call's join).
        let live = self.live_across(inst);
        self.root(&live)?;
        // The whole frame, boxed: a dead slot and the stack above this
        // pc's depth as undefined (baseline writes those before reading).
        let undef = self.i64c(UNDEF);
        let mut ops = vec![];
        for (&v, &mv) in a.iter().zip(&d.args) {
            let dead = matches!(
                self.f.values[mv].def,
                mir::func::ValueDef::Result(i, _)
                    if self.f.insts[i].op == Opcode::ConstVal(ConstVal::Dead)
            );
            ops.push(if dead {
                undef
            } else {
                let t = self.ty(mv);
                self.boxed(&t, v)?
            });
        }
        let full = (3 + nargs + nlocals + max_depth) as usize;
        if ops.len() > full {
            return Err("lowering: an exit.inline deeper than its frame".into());
        }
        ops.resize(full, undef);
        if !self.inline_hubs.contains_key(&fid) {
            let hub = self.inline_hub(fid, nargs, nlocals, max_depth)?;
            self.inline_hubs.insert(fid, hub);
        }
        let (hub, _, _, _, tails) = self.inline_hubs.get_mut(&fid).unwrap();
        let hub = *hub;
        let idx = u32::try_from(tails.len()).unwrap();
        let tail = self.body.add_block();
        let err = self.body.add_blockparam(tail, Type::I32);
        self.inline_hubs.get_mut(&fid).unwrap().4.push(tail);
        let mode = if throw {
            ResumeMode::Throw
        } else {
            ResumeMode::Continue
        };
        let w = ResumeWord { pc, mode };
        let mut args = vec![self.i32c(w.encode() as u32), self.i32c(idx)];
        args.extend(ops);
        self.terminate(Terminator::Br {
            target: BlockTarget { block: hub, args },
        });
        // The site's tail: back from the callee's baseline body, with the
        // site's own state after the call.
        self.cur = tail;
        self.after_gc(&live);
        let end = self.frame_end[fid as usize];
        let result = self.load_i64(self.vp, end);
        let ok = self.un(Operator::I32Eqz, err, Type::I32);
        let t = self.edge(inst, 0, &[result])?;
        let e = self.edge(inst, 1, &[])?;
        self.cond_br(ok, t, e);
        Ok(())
    }

    /// The `exit.inline` hub for inline frame `fid`: params the resume
    /// word, the site index, and the whole frame boxed (`this`, formals,
    /// locals, rval, the stack to its deepest); it writes the callee's
    /// frame, the resume word and the backoff, then runs the callee's
    /// baseline body on it. Its terminator, a dispatch to the sites'
    /// tails, is set once every site is lowered.
    fn inline_hub(
        &mut self,
        fid: u32,
        nargs: u32,
        nlocals: u32,
        max_depth: u32,
    ) -> R<(Block, Block, Value, Value, Vec<Block>)> {
        let saved = self.cur;
        let hub = self.body.add_block();
        let word = self.body.add_blockparam(hub, Type::I32);
        let site = self.body.add_blockparam(hub, Type::I32);
        let n = 3 + nargs + nlocals + max_depth;
        let ops: Vec<Option<Value>> = (0..n).map(|_| Some(self.body.add_blockparam(hub, Type::I64))).collect();
        self.cur = hub;
        let fp = frame_parts(&ops, nargs, nlocals).ok_or("lowering: malformed exit.inline")?;
        let f = fid as usize;
        let (base, end, l) = (self.frame_off[f], self.frame_end[f], self.frame_layouts[f]);
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
        let w64 = self.un(Operator::I64ExtendI32U, word, Type::I64);
        let tag = self.i64c(TAG_INT32 << 32);
        let wv = self.bin(Operator::I64Or, w64, tag, Type::I64);
        self.store_i64(sp, base + l.resume(), wv);
        let backoff = self.i64c((TAG_INT32 << 32) | u64::from(ONRAMP_BACKOFF));
        self.store_i64(sp, base + l.backoff(), backoff);
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
        // The dispatch goes where the body ends (classify branches).
        let last = self.cur;
        self.cur = saved;
        Ok((hub, last, site, err, vec![]))
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
        self.census_exit(self.f.script, w.pc, &format!("{:?}", w.mode));
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
        // Every stack slot: MIR's roots overlap them.
        for (k, v) in fp.stack.iter().enumerate() {
            let v = match *v {
                Some(v) => v,
                None => self.i64c(UNDEF),
            };
            self.store_i64(vp, l.operand(u32::try_from(k).unwrap()), v);
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
