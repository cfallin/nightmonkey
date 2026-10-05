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
    frame_parts, ArithOp, BindingCheck, BitOp, Cc, ConstVal, F64Op, JsBinop, JsCc, JsUnop, MathFn,
    NumRepr, Opcode, UnboxKind,
};
use crate::mir::types::{FactKind, Machine, ObjKind, TagSet, Type as MType};
use crate::region_shape::BINDING_FUSE_PREDICTED;
use crate::opsem::{
    Prims, PRIM_BIGINT, PRIM_BOOLEAN, PRIM_DOUBLE, PRIM_INT32, PRIM_NULL, PRIM_STRING, PRIM_SYMBOL,
    PRIM_UNDEFINED,
};
use crate::wasm::baseline::layout::{
    FrameLayout, ResumeMode, ResumeWord, ARGC_FLAGS, ARGC_ONRAMP_BIT, ARGC_RESUME_BIT, ERR_DEOPT,
    ONRAMP_BACKOFF,
};
use crate::wasm::mir::abi::{
    MAX_FIXED_SLOTS, CALLOBJ_CALLEE_OFFSET, CALLOBJ_ENCLOSING_OFFSET, ENV_CELL_ARMED, ENV_CELL_CLASS_WORD, ENV_CELL_GEN,
    LAMBDA_CELL_GEN, LAMBDA_CELL_TEMPLATE,
    BINOP_BITAND, BINOP_BITNOT, BINOP_BITOR, BINOP_BITXOR, BINOP_DEC, BINOP_DIV, BINOP_INC,
    BINOP_LSH, BINOP_MOD, BINOP_MUL, BINOP_RSH, BINOP_SUB, BINOP_URSH, CLASS_WORD_SHALLOW,
    CLASS_WORD_CLOSED, CLASS_WORD_RANGES, CLASS_WORD_SENTINEL, CLASS_WORD_SLOTS, SHAPE_SMALL_SLOTSPAN_MASK_BITS,
    SHAPE_PERMUTED_SLOTS_BIT, SHAPE_SMALL_SLOTSPAN_SHIFT, TA_DATA_PAYLOAD_OFFSET, TA_LENGTH_PAYLOAD_OFFSET, ELEMENTS_LENGTH_BACK,
    ELEMENTS_CAPACITY_BACK, ELEMENTS_PUSH_BAIL_MASK, ELEMENTS_HEADER_BYTES, ALLOC_CELL_ADDR_PLACEHOLDER,
    STRING_LENGTH_OFFSET, STRING_FLAGS_OFFSET, STRING_CHARS_OFFSET, STRING_LINEAR_BIT,
    STRING_INLINE_CHARS_BIT, STRING_LATIN1_CHARS_BIT, STRING_MAX_LENGTH, FAT_INLINE_MAX_LATIN1,
    FAT_INLINE_MAX_TWO_BYTE, JSCLASS_COPS_OFFSET, JSCLASS_EMULATES_UNDEFINED, JSCLASS_FLAGS_OFFSET,
    JSCLASS_IS_PROXY, JSCLASSOPS_CALL_OFFSET, ROPE_BYTES, ROPE_LEFT_OFFSET, ROPE_RIGHT_OFFSET, CALL_CELL_ADDR_PLACEHOLDER, CALL_CELL_FUNCIDX,
    CALL_CELL_SCRIPT, EARLY_KEY_MAX, EARLY_KEY_SHIFT, IC_SET_ABSSLOT,
    IC_SET_RECVSHAPE, IC_SET_SLOTENC, IC_TRANS_ABSSLOT, IC_TRANS_NEWSHAPE,
    IC_TRANS_OLDSHAPE, IC_TRANS_PROTO0, IC_TRANS_PROTO_HOPS, IC_TRANS_PROTO_ROW_BYTES,
    IC_TRANS_ROW_OFF, IC_TRANS_SLOTOFF, BASESHAPE_PROTO_OFFSET, IOF_CELL_ADDR_PLACEHOLDER,
    IOF_CELL_GEN, IOF_CELL_SLOTENC, CONSTRUCT_CELL_ADDR_PLACEHOLDER, CONSTRUCT_CELL_CTORSHAPE,
    CONSTRUCT_CELL_GEN, CONSTRUCT_CELL_PROTOPTR, CONSTRUCT_CELL_PROTOSLOTENC, NURSERY_HEADER_BYTES,
    CONSTRUCT_CELL_FINALSHAPE, CONSTRUCT_CELL_PROTOSHAPE, CONSTRUCT_CELL_PROTO2PTR, CONSTRUCT_CELL_PROTO2SHAPE,
    IC_WAY_HOLDERPTR, IC_WAY_MONO_OFF, IC_WAY_RECVSHAPE,
    IC_WAY_ADDR_PLACEHOLDER, IC_PATCH_RELATIVE, NATIVE_SLOTS_OFFSET, SHAPE_BASESHAPE_OFFSET, BASESHAPE_CLASP_OFFSET,
    BASESCRIPT_NIGHTFUNCINDEX_OFFSET, FUNC_FLAGS_SLOT_OFFSET, FUNCTION_FLAGS_CONSTRUCTOR, FUNC_ENV_SLOT_OFFSET, FUNC_SCRIPT_SLOT_OFFSET,
    SHAPE_FIXED_SLOTS_MASK_BITS, SHAPE_FIXED_SLOTS_SHIFT, JSCONTEXT_REALM_OFFSET,
    REALM_GLOBAL_OFFSET, CHUNK_STORE_BUFFER_OFFSET, CMP_EQ, CMP_GE, CMP_GT, CMP_LE, CMP_LT, CMP_NE, CMP_STRICTEQ, CMP_STRICTNE,
    ELEMENTS_FLAGS_BACK, ELEMENTS_FROZEN_FLAG, ELEMENTS_INITLEN_BACK, FIXED_SLOTS_BASE, FLAGS_ALL, OBJ_CLASS_IDX_OFFSET, OBJ_ELEMENTS_OFFSET,
    JSCONTEXT_ZONE_OFFSET, NOT_CHUNK_MASK, SHAPE_IMMUTABLE_FLAGS_OFFSET, SHAPE_IS_NATIVE_BIT,
    SHAPE_OFFSET, VAL_GCTHING_TAG_MIN, ZONE_NEEDS_BARRIER_OFFSET,
};
use crate::wasm::translate::{
    AtomTable, Helpers, APPEND_CACHE_ENTRY_BYTES, APPEND_CACHE_SIZE, BC_ARR_POP, BC_ARR_PUSH, BC_MAP_GET, BC_REGEXP_EXEC,
    BC_REGEXP_TEST,
    ELEMENTS_POP_BAIL_MASK, INLINE_IC_STRIDE, MAGIC_GENERATOR_CLOSING, MAGIC_IS_CONSTRUCTING, MAGIC_UNINITIALIZED_LEXICAL, TAG_BIGINT_HI, TAG_BOOLEAN, TAG_CLEAR,
    TAG_INT32, TAG_MAGIC, TAG_NULL, TAG_OBJECT, TAG_STRING, TAG_SYMBOL, TAG_UNDEFINED,
};

type R<T> = Result<T, String>;

/// Whether `new` of a compiled constructor calls it directly.
const DIRECT_CONSTRUCT: bool = true;

/// Whether global binding writes get their inline arm.
const INLINE_GNAME_SETS: bool = true;

/// A call whose callee's type proves its script calls that script's body
/// with no native arms and no classify (`js_call_proven`).
const PROVEN_CALLS: bool = true;
/// The most arguments past the first an inline `push` stores (each costs a
/// store and a post-barrier test).
const PUSH_ARM_MAX_EXTRA: usize = 7;

const UNDEF: u64 = TAG_UNDEFINED << 32;

/// The tags of values that are no GC thing (no barrier owes them anything).
const GC_FREE_TAGS: TagSet = TagSet::prims(crate::opsem::Prims::from_bits(
    crate::opsem::NUM.bits()
        | crate::opsem::PRIM_BOOLEAN.bits()
        | crate::opsem::PRIM_NULL.bits()
        | crate::opsem::PRIM_UNDEFINED.bits(),
));

/// `JS::GenericNaN()`'s bits.
const CANONICAL_NAN_BITS: u64 = 0x7FF8_0000_0000_0000;

/// How much of an inline frame's fixed slots (env, arguments object,
/// new.target, rval, resume word, backoff) its `inline.enter` writes.
/// Only an exit into the callee's baseline body reads the rest, so the
/// exit hub writes what the entry left out, and the frame's GC scan (`frame_top`) stops below it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Fixed {
    /// All six: the callee reads its arguments object or new.target from
    /// the frame, or it is a construct.
    All,
    /// The env slot only: the callee sets its environment (`EnvSet`,
    /// `EnvPop`).
    Env,
    /// None: the callee's environment is its function's, read from the
    /// callee where used.
    None,
}

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
    pub intrinsic_cell_patches: Vec<(Value, u32)>,
    /// Likely-callee direct calls: the expected-funcidx const, the stub
    /// `call`, and the callee's script id (`wasm/mod.rs` patches both).
    pub likely_patches: Vec<(Value, Value, u32)>,
    /// Per mnemonic: how many instructions, and the wasm values they
    /// lowered to (`--dump-opsize`).
    pub opsize: BTreeMap<String, (u32, u32)>,
    /// The body as text, each value marked with the MIR instruction that
    /// emitted it (`;;@i<n>`, n = the instruction's index): `--viz` only.
    pub viz_text: Option<String>,
}

/// `Lowered::viz_text`'s marks: from a value index on, which MIR
/// instruction (its index + 1; 0 for the entry, edges and hubs) emitted
/// the values.
struct VizMarks(Vec<(usize, u32)>);

impl waffle::PrintDecorator for VizMarks {
    fn after_inst(&self, value: Value, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let i = value.index();
        match self.0.partition_point(|&(s, _)| s <= i) {
            0 => Ok(()),
            k if self.0[k - 1].1 == 0 => Ok(()),
            k => write!(f, " ;;@i{}", self.0[k - 1].1 - 1),
        }
    }
}

/// A generic call of a native goes straight to it (`native_dispatch`).
const NATIVE_ROUTE: bool = true;

/// A for-in's start from its object's shape's cached iterator, inline
/// (`iter_from_shape`).
const ITER_FROM_SHAPE: bool = true;

/// An exec/test that does not match runs its AOT matcher in compiled code
/// (`regexp_no_match`).
const REGEXP_NO_MATCH_ARM: bool = true;

/// `obj[atom] = v` adding the property replays the element-add table's
/// transition (`elem_add_arm`).
const ELEM_ADD_ARM: bool = true;

/// A generic equality of two strings decides by pointer, length and
/// atomness before the helper.
const STRING_EQ_ARM: bool = true;

/// A generic element store tries the call-free append/hole arm first.
const APPEND_ARM: bool = true;

/// The `math_natives_base` slot of a Math native the builder names
/// (`Math.<fn>`).
pub(crate) fn native_math_index(name: &str) -> Option<u32> {
    use crate::wasm::translate::{
        MN_ABS, MN_CEIL, MN_COS, MN_FLOOR, MN_FROUND, MN_MAX, MN_MIN, MN_POW, MN_SIN, MN_SQRT, MN_TRUNC,
    };
    Some(match name {
        "Math.abs" => MN_ABS,
        "Math.floor" => MN_FLOOR,
        "Math.ceil" => MN_CEIL,
        "Math.trunc" => MN_TRUNC,
        "Math.sqrt" => MN_SQRT,
        "Math.fround" => MN_FROUND,
        "Math.min" => MN_MIN,
        "Math.max" => MN_MAX,
        "Math.pow" => MN_POW,
        "Math.sin" => MN_SIN,
        "Math.cos" => MN_COS,
        _ => return None,
    })
}


/// Property-IC sites address their ways from a base the function loads
/// from its context, not as patched absolute addresses (the per-context
/// regions prototype, KICKOFF-10 workstream 2 step 3). Off: against the
/// absolute form it cost react 5%, box2d 3.9%, deltablue 3.3%,
/// earley-boyer 3.1%, raytrace 2.2% (2026-10-04), so the owner decides.
const IC_BASE_FROM_CX: bool = false;

/// `guard.unbox.f64num` branches on the tag, the double first, rather
/// than converting both ways and selecting (`unbox_num_edges`).
const NUM_UNBOX_BRANCHY: bool = true;

/// An int32 add or sub of a constant checks overflow with one compare of
/// the other operand against a bound.
const CONST_OVF_COMPARE: bool = true;

/// `load_elem` tests the tag its `ok` block's unbox guard wants first
/// (`load_elem_unboxed`).
const FUSED_ELEM_UNBOX: bool = true;

/// A loop's managed values enter its header in registers unless one may
/// cross a GC on the loop's expected path (`gc_only_off_path`).
const HOT_CROSSINGS_ONLY: bool = true;

/// Whether `op`'s lowering reaches a may-GC call only off its expected
/// path: an inline arm handles the common case, and the helper behind it
/// (an IC miss, growth, a slow allocation, a generic numeric operand) or
/// the op itself (an exit, boxing a primitive `this`) is the exception. A
/// value live across a loop that GCs only there stays in a register on
/// the loop's back edges; the exceptional edge reloads it (`conform`).
/// Only a placement choice: a wrong answer costs reloads, never
/// correctness.
fn gc_only_off_path(op: &Opcode) -> bool {
    matches!(
        op,
        Opcode::StoreElem(..)
            | Opcode::InitField(_)
            | Opcode::GetElemData
            | Opcode::SetElemData(_)
            | Opcode::GetPropData(_)
            | Opcode::SetPropData(_)
            | Opcode::Prim(_)
            | Opcode::NewThis(..)
            | Opcode::NewThisInit { .. }
            | Opcode::ExitInline { .. }
            | Opcode::JsBoxThis
    )
}

/// A generator's resume dispatch over at most this many yields is a chain
/// of compares; past it, a `br_table`.
const RESUME_CHAIN_MAX: usize = 4;

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

/// The tags a value of MIR type `t` may have, boxed.
fn value_tags(t: &MType) -> TagSet {
    match t {
        MType::Val(v) => v.tags,
        MType::Obj(_) => TagSet::OBJECT,
        MType::Str(_) => TagSet::prims(PRIM_STRING),
        MType::Bool => TagSet::BOOLEAN,
        MType::I32(_) => TagSet::INT32,
        MType::F64(_) | MType::Int(_) => TagSet::NUMBER,
        _ => TagSet::ALL,
    }
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
    // By representation, not by `may_hold_gc_thing`: rooting a boxed
    // int32 too keeps overwriting home slots whose last GC thing is dead,
    // and without it a dead object stays pinned there across a GC
    // (gc/weak-marking-01.js).
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
    /// Home slots that may hold invalid bits: not written since entry
    /// (a dead frame's), or at or above the top of a may-GC call since
    /// (unscanned, so possibly stale, and possibly overwritten by the
    /// call's frame or out-slot). Those below the next may-GC call's top
    /// are cleared there, as its scan must see only valid Values. A slot
    /// written and scanned since stays valid (the GC updates it), so a
    /// value that dies is not cleared: it stays alive until its slot is
    /// reused, falls above a top, or the activation returns (§4.4).
    dirty: BTreeSet<u32>,
    /// The rooting slots a may-GC call scans, per strongly connected
    /// component of the CFG (by block): in a cycle, every frame-0 call
    /// scans the most any of its calls needs, so a loop's slots below
    /// that stay valid around it (`enter_block`). Absent: no cycle.
    scc_top: BTreeMap<mir::Block, u32>,
    /// Per inline frame inlined into the function's own frame (by frame
    /// id; 0 elsewhere): the rooting slots its region (it and the frames
    /// inlined into it) keeps -- one past the highest home of a value
    /// live anywhere in it. The frame sits right above them, over the
    /// rest, which nothing live in the region occupies.
    inline_k: Vec<u32>,
    /// The scan limit (offset from `sp`) of the last `root`: the top a
    /// may-GC call passes (`top_off`).
    gc_top: u32,
    /// Per (frame, slot): the value a `frame.store` put there, along the
    /// emission path; a store of the same value again is dropped.
    framed: BTreeMap<(u32, u32), mir::Value>,
    /// The builder's retaining frame stores before the next instruction:
    /// emitted where that instruction can GC (`root`), not before it.
    pending_retain: Vec<((u32, u32), mir::Value)>,
    /// `const.str`s whose only uses are `switch.str` cases: not emitted
    /// where they stand; the switch loads each atom where it compares it
    /// (a switch's cases would otherwise all load before its first).
    lazy_strs: BTreeMap<mir::Value, mir::entity::AtomId>,
    /// The MIR block being lowered.
    cur_mblock: mir::Block,
    /// Whether the stamp epoch was unchanged across the last `gc_call`.
    epoch_same: Option<Value>,
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
    /// may-GC call's scan limit is its frame's top: the end of frame 0,
    /// or an inline frame's fixed slots (its operand stack is baseline's,
    /// written only by the frame's exits, so nothing in MIR reads it or
    /// lets the GC see it). A nested inline frame starts at its parent's
    /// top; an exit's baseline body runs on the frame up to its end.
    inline: bool,
    frame_off: Vec<u32>,
    /// Per frame: where its variable region (locals, fixed slots,
    /// operands) starts, from `vp`: its `frame_off`, past the actuals
    /// beyond its formals for a callee reading its actuals (baseline's
    /// `vp` rebase).
    frame_voff: Vec<u32>,
    frame_end: Vec<u32>,
    frame_top: Vec<u32>,
    /// Per frame: how much of an inline frame's fixed slots its
    /// `inline.enter` writes (and its GC scan covers); the exit hub writes
    /// the rest (§5.5).
    fixed: Vec<Fixed>,
    frame_layouts: Vec<FrameLayout>,
    /// The frame of the instruction being lowered.
    cur_frame: u32,
    baseline_calls: Vec<Value>,
    /// The stress mode's period (`Options::mir_stress`); 0 = off.
    stress: u32,
    /// While a `guard.layout` is lowered: its word, identity and keys, for
    /// the guard census's miss reason.
    guard_word: Option<(Value, Value, mir::types::KeyRange)>,
    guard_obj: Option<Value>,
    /// A `guard.script` chain's function test, for the next guard on the
    /// same callee, keyed by the block that guard is in (the first's
    /// `fail`, its only way in).
    script_memo: BTreeMap<mir::Block, (mir::Value, Value)>,
    /// Whether the function makes an arguments object (`args.object`):
    /// then its element reads try the `arguments[i]` arm (`args_element`).
    makes_args: bool,
    /// A `check.binding`'s fact, with its value-fuse test (`load_gname`'s).
    binding_armed: BTreeMap<mir::Value, Value>,
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
    /// The property-IC region base, once a site needs it (`ic_base`).
    ic_base: Option<Value>,
    /// `instanceof` cell placeholders (`Outcome::Compiled::iof_cell_patches`).
    iof_cell_patches: Vec<(Value, u32)>,
    /// Construct cell placeholders (one cell per site).
    construct_cell_patches: Vec<(Value, u32)>,
    /// Call value cell placeholders (one cell per site; 0: the trash row).
    call_cell_patches: Vec<(Value, u32)>,
    likely_patches: Vec<(Value, Value, u32)>,
    alloc_cell_patches: Vec<(Value, u32)>,
    intrinsic_cell_patches: Vec<(Value, u32)>,
    opsize: BTreeMap<String, (u32, u32)>,
    /// The census helper, when exits are counted (`--mir-exit-census`).
    exit_census: Option<Func>,
    /// The census helper, when blocks are counted (`--block-census`).
    block_census: Option<Func>,
    /// The census helper, when rooting stores are counted (`--root-census`).
    root_census: Option<Func>,
    /// The census helper, when Wasm blocks are counted (`--value-census`),
    /// and the emitter of each Wasm value range: (first value, tag).
    value_census: Option<Func>,
    value_tags: Vec<(usize, String)>,
    /// `--viz`: `VizMarks`, as they are recorded.
    viz_marks: Option<Vec<(usize, u32)>>,
    /// The instruction being lowered, for the root census's labels.
    cur_inst: Option<mir::Inst>,
    /// Per frame (0 the function's own, then the inline frames): whether
    /// any instruction in it or in a frame inlined into it may GC
    /// (`may_gc`; an `exit.inline` does). Computed on first use.
    frame_gc: Option<Vec<bool>>,
    /// The inline frame the current block's `inline.enter` entered, if any:
    /// the retaining stores pending at its terminator are for that callee.
    block_enters: Option<u32>,
    /// Retaining stores handed to a block's sole predecessor's successor:
    /// still pending on entry, written at its first GC point (`root`).
    carried_retain: BTreeMap<mir::Block, Vec<((u32, u32), mir::Value)>>,
    /// One exit hub per frame shape (`exit_hub`).
    exit_hubs: BTreeMap<Vec<Option<BoxKind>>, Block>,
    /// One `exit.inline` hub per inline frame: its entry and last blocks,
    /// its site-index param and call status, and each site's tail
    /// (`exit_inline`).
    inline_hubs: BTreeMap<u32, (Block, Block, Value, Value, Value, Vec<Block>)>,
    strict: bool,
    plain_env: bool,
    own_env: bool,
    forward_resume: bool,
    is_gen: bool,
    mapped_formals: bool,
    inline_layouts: Vec<FrameLayout>,
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
#[derive(Clone, Default)]
pub struct LowerOpts {
    /// The stress mode's period (`Options::mir_stress`); 0 = off.
    pub stress: u32,
    /// Count every exit (`--mir-exit-census`).
    pub exit_census: bool,
    /// Count every MIR block's executions (`--block-census`).
    pub block_census: bool,
    /// Count every executed rooting site (`--root-census`).
    pub root_census: bool,
    /// Count every executed Wasm block, by the MIR ops in it
    /// (`--value-census`).
    pub value_census: bool,
    /// Keep the body's text, its values marked with their MIR
    /// instructions (`--viz`).
    pub viz: bool,
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
    /// A generator or async body: its entry also takes a generator's
    /// resume (`EnterNightResume`) to the yield's `Resume` root.
    pub is_gen: bool,
    /// The script's formals are a mapped `arguments`'s, which may write
    /// them behind MIR's back: their frame stores are never dropped.
    pub mapped_formals: bool,
    /// Each inline frame's callee layout (`FrameLayout::of`); empty for
    /// hand-written MIR, whose inline frames take the full layout.
    pub inline_layouts: Vec<FrameLayout>,
}

/// Lower `f` (a function of `mm`, whose baseline frame is `layout`) into a
/// new body of `m`.
/// The `const.str` results used only as `switch.str` cases (`Lower::lazy_strs`).
fn lazy_switch_strs(f: &mir::Func) -> BTreeMap<mir::Value, mir::entity::AtomId> {
    let mut strs: BTreeMap<mir::Value, mir::entity::AtomId> = BTreeMap::new();
    for &b in &f.layout {
        for &i in &f.blocks[b].insts {
            if let Opcode::ConstStr(a) = f.insts[i].op {
                strs.insert(f.insts[i].results[0], a);
            }
        }
    }
    for &b in &f.layout {
        for &i in &f.blocks[b].insts {
            let d = &f.insts[i];
            let case_uses = if matches!(d.op, Opcode::SwitchStr(_)) { 1 } else { usize::MAX };
            for (k, v) in d.args.iter().enumerate() {
                if k < case_uses {
                    strs.remove(v);
                }
            }
            for e in &d.succs {
                for a in &e.args {
                    if let EdgeArg::Value(v) = a {
                        strs.remove(v);
                    }
                }
            }
        }
    }
    for l in &f.loops {
        if let Some(e) = &l.entry {
            for v in &e.state {
                strs.remove(v);
            }
        }
    }
    strs
}

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
    let (cx, sp, argc, retval_out, new_target) = (p(0), p(1), p(2), p(3), p(5));
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
        new_target,
        blocks: BTreeMap::new(),
        live_in: BTreeMap::new(),
        vmap: BTreeMap::new(),
        root_base,
        home: BTreeMap::new(),
        nslots: 0,
        slotted: BTreeSet::new(),
        scc_top: BTreeMap::new(),
        inline_k: vec![],
        gc_top: root_base,
        dirty: BTreeSet::new(),
        framed: BTreeMap::new(),
        pending_retain: vec![],
        lazy_strs: lazy_switch_strs(f),
        cur_mblock: mir::Block::from_u32(0),
        cold: false,
        epoch_same: None,
        pending: BTreeMap::new(),
        plans: BTreeMap::new(),
        entry_dirty: BTreeMap::new(),
        rpo_index: BTreeMap::new(),
        preds: BTreeMap::new(),
        crossed_out: BTreeMap::new(),
        inline: !f.inline_frames.is_empty(),
        frame_off: vec![0],
        frame_voff: vec![0],
        frame_end: vec![root_base],
        frame_top: vec![root_base],
        fixed: vec![Fixed::All],
        frame_layouts: vec![layout],
        cur_frame: 0,
        baseline_calls: vec![],
        stress: o.stress,
        guard_word: None,
        script_memo: BTreeMap::new(),
        makes_args: f.insts.iter().any(|(_, d)| d.op == Opcode::ArgsObject),
        binding_armed: BTreeMap::new(),
        guard_obj: None,
        has_onramps: f.roots.iter().any(|r| r.kind != RootKind::Entry),
        onramp_flag: argc,
        mm,
        atoms,
        body_off_patches: vec![],
        prop_ic_patches: vec![],
        ic_base: None,
        iof_cell_patches: vec![],
        construct_cell_patches: vec![],
        call_cell_patches: vec![],
        likely_patches: vec![],
        alloc_cell_patches: vec![],
        intrinsic_cell_patches: vec![],
        opsize: BTreeMap::new(),
        exit_census: if o.exit_census { h.census } else { None },
        block_census: if o.block_census { h.census } else { None },
        root_census: if o.root_census { h.census } else { None },
        value_census: if o.value_census { h.census } else { None },
        value_tags: vec![],
        viz_marks: o.viz.then(Vec::new),
        cur_inst: None,
        frame_gc: None,
        block_enters: None,
        carried_retain: BTreeMap::new(),
        exit_hubs: BTreeMap::new(),
        inline_hubs: BTreeMap::new(),
        strict: o.strict,
        plain_env: o.plain_env,
        own_env: o.own_env,
        forward_resume: o.forward_resume,
        is_gen: o.is_gen,
        mapped_formals: o.mapped_formals,
        inline_layouts: o.inline_layouts.clone(),
        gname_bids,
        gname_fused,
        add_preds,
    };
    l.run()?;
    let viz_text = l.viz_marks.take().map(|marks| {
        let marks = VizMarks(marks);
        format!("{}", l.body.display_with_decorator("", None, Some(&marks)))
    });
    crate::wasm::pad_body(&mut l.body, u64::from(l.f.script.get()));
    Ok(Lowered {
        body: l.body,
        body_off_patches: l.body_off_patches,
        baseline_calls: l.baseline_calls,
        prop_ic_patches: l.prop_ic_patches,
        iof_cell_patches: l.iof_cell_patches,
        construct_cell_patches: l.construct_cell_patches,
        call_cell_patches: l.call_cell_patches,
        alloc_cell_patches: l.alloc_cell_patches,
        intrinsic_cell_patches: l.intrinsic_cell_patches,
        likely_patches: l.likely_patches,
        opsize: l.opsize,
        viz_text,
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

    /// Whether `headroom` bytes from `top` fit the value stack: the stack is
    /// a region aligned to its size (`VALUE_STACK_LOG2`), so they do iff
    /// their last byte has the frame base's high bits. No load: each
    /// context's stack is its own region, wherever it is.
    fn stack_fits(&mut self, top: Value, headroom: u32) -> Value {
        let last = self.add_off(top, headroom - 1);
        let x = self.bin(Operator::I32Xor, last, self.vp, Type::I32);
        let size = self.i32c(1 << crate::region_shape::VALUE_STACK_LOG2);
        self.bin(Operator::I32LtU, x, size, Type::I32)
    }

    /// The address `off` bytes into the property-IC region (a site's ways
    /// or add row). With `IC_BASE_FROM_CX`, the region base the function
    /// loads once from its context's tier state (`ic_base`) plus `off`;
    /// else the absolute address, patched in.
    fn ic_addr(&mut self, off: u32) -> Value {
        let c = self.i32c(IC_WAY_ADDR_PLACEHOLDER);
        if !IC_BASE_FROM_CX {
            self.prop_ic_patches.push((c, off));
            return c;
        }
        self.prop_ic_patches.push((c, off | IC_PATCH_RELATIVE));
        let base = self.ic_base();
        self.bin(Operator::I32Add, base, c, Type::I32)
    }

    /// The property-IC region's base: two loads (the context's tier state,
    /// then its `propIcBase`) at the head of the function's entry block,
    /// made at the first site that needs it.
    fn ic_base(&mut self) -> Value {
        if let Some(b) = self.ic_base {
            return b;
        }
        let m1 = self.mem(2, crate::wasm::mir::abi::CX_EXT_STATE_OFFSET);
        let args = self.body.arg_pool.from_iter([self.cx].into_iter());
        let ty = self.body.single_type_list(Type::I32);
        let st = self.body.add_value(ValueDef::Operator(Operator::I32Load { memory: m1 }, args, ty));
        let m2 = self.mem(2, crate::wasm::mir::abi::CTX_PROPIC_BASE_OFFSET);
        let args = self.body.arg_pool.from_iter([st].into_iter());
        let ty = self.body.single_type_list(Type::I32);
        let b = self.body.add_value(ValueDef::Operator(Operator::I32Load { memory: m2 }, args, ty));
        let entry = self.body.entry;
        self.body.blocks[entry].insts.insert(0, b);
        self.body.blocks[entry].insts.insert(0, st);
        self.ic_base = Some(b);
        b
    }

    /// `v`'s value where its type pins one int32 (as an i64: `-c` cannot
    /// overflow).
    fn const_i32(&self, v: mir::Value) -> Option<i64> {
        match self.ty(v) {
            MType::I32(r) if r.lo == r.hi => Some(r.lo),
            _ => None,
        }
    }

    /// Whether guard `inst`'s miss is a plain branch to its `fail` edge
    /// (no `--mir-stress` failures and no exit census call to emit).
    fn plain_guard(&self, inst: mir::Inst) -> bool {
        let fail_blk = self.f.insts[inst].succs[1].block;
        self.stress == 0 && (self.exit_census.is_none() || self.guard_exits(fail_blk).is_none())
    }

    /// `guard.unbox.f64num`'s edges from `v`'s `tag`, the double first: a
    /// double's bits are the f64 (one compare, no select), an int32
    /// converts, and anything else takes `fail`. `have` (what `v` may be)
    /// drops the arm a value cannot take.
    fn unbox_num_edges(&mut self, inst: mir::Inst, v: Value, tag: Value, have: TagSet) -> R<()> {
        let may_dbl = !have.intersect(TagSet::prims(PRIM_DOUBLE)).is_empty();
        let may_int = !have.intersect(TagSet::INT32).is_empty();
        let join = self.body.add_block();
        let x = self.body.add_blockparam(join, Type::F64);
        let fail = self.body.add_block();
        let not_dbl = if may_dbl {
            let (d_b, nd_b) = (self.body.add_block(), self.body.add_block());
            let k = self.i32c(TAG_INT32 as u32);
            let is_dbl = self.bin(Operator::I32LtU, tag, k, Type::I32);
            self.cond_br(is_dbl, Self::to(d_b), Self::to(nd_b));
            self.cur = d_b;
            let fd = self.un(Operator::F64ReinterpretI64, v, Type::F64);
            self.terminate(Terminator::Br {
                target: BlockTarget { block: join, args: vec![fd] },
            });
            nd_b
        } else {
            self.cur
        };
        self.cur = not_dbl;
        if may_int {
            let i_b = self.body.add_block();
            let is_int = self.tag_is(tag, TAG_INT32 as u32);
            self.cond_br(is_int, Self::to(i_b), Self::to(fail));
            self.cur = i_b;
            let low = self.un(Operator::I32WrapI64, v, Type::I32);
            let fi = self.un(Operator::F64ConvertI32S, low, Type::F64);
            self.terminate(Terminator::Br {
                target: BlockTarget { block: join, args: vec![fi] },
            });
        } else {
            self.terminate(Terminator::Br { target: Self::to(fail) });
        }
        self.cur = fail;
        let f = self.edge(inst, 1, &[])?;
        self.terminate(Terminator::Br { target: f });
        self.cur = join;
        let t = self.edge(inst, 0, &[x])?;
        self.terminate(Terminator::Br { target: t });
        Ok(())
    }

    /// The unbox guard a `load_elem` may test first: its `ok` edge's block
    /// has no other way in and begins with `guard.unbox` of the loaded
    /// value, in the same frame. Returns the guard, its kind, and the
    /// block param the value arrives in.
    fn fusable_unbox(&self, inst: mir::Inst) -> Option<(mir::Inst, UnboxKind, mir::Value)> {
        let f = self.f;
        let e = &f.insts[inst].succs[0];
        let k = e.args.iter().position(|a| *a == EdgeArg::Out(0))?;
        let p = *f.blocks[e.block].params.get(k)?;
        if self.preds.get(&e.block).map_or(0, |v| v.len()) != 1 || f.roots.iter().any(|r| r.block == e.block) {
            return None;
        }
        let &g = f.blocks[e.block].insts.first()?;
        let Opcode::GuardUnbox(kind) = f.insts[g].op else { return None };
        (f.insts[g].args[0] == p && f.inst_frame[g] == f.inst_frame[inst] && self.plain_guard(g)).then_some((g, kind, p))
    }

    /// `load_elem` whose `ok` block begins with `guard.unbox kind` of the
    /// value (`fusable_unbox`): the element's tag is tested for `kind`
    /// first, and a match takes the guard's `ok` edge with the payload
    /// directly (a hole's tag is never `kind`'s). Any other tag goes the
    /// unfused way: a hole to `fail`, the rest to the guard's block, whose
    /// guard then misses as it would have.
    fn load_elem_unboxed(&mut self, inst: mir::Inst, g: mir::Inst, kind: UnboxKind, p: mir::Value, obj: Value, idx: Value) -> R<()> {
        let fail = self.body.add_block();
        let (addr, _) = self.elem_addr(obj, idx, fail, false);
        let v = self.load_i64(addr, 0);
        let tag = self.tag_of(v);
        // The guard's edges see the loaded value as its block's param.
        self.vmap.insert(p, v);
        let other = self.body.add_block();
        if kind == UnboxKind::F64Num {
            let have = value_tags(&self.ty(p));
            // Its `fail` is `other` here: the hole test, then the guard.
            let join = self.body.add_block();
            let x = self.body.add_blockparam(join, Type::F64);
            let (d_b, nd_b, i_b) = (self.body.add_block(), self.body.add_block(), self.body.add_block());
            let k = self.i32c(TAG_INT32 as u32);
            let is_dbl = self.bin(Operator::I32LtU, tag, k, Type::I32);
            self.cond_br(is_dbl, Self::to(d_b), Self::to(nd_b));
            self.cur = d_b;
            let fd = self.un(Operator::F64ReinterpretI64, v, Type::F64);
            self.terminate(Terminator::Br {
                target: BlockTarget { block: join, args: vec![fd] },
            });
            self.cur = nd_b;
            let is_int = self.tag_is(tag, TAG_INT32 as u32);
            let may_int = !have.intersect(TagSet::INT32).is_empty();
            if may_int {
                self.cond_br(is_int, Self::to(i_b), Self::to(other));
            } else {
                self.terminate(Terminator::Br { target: Self::to(other) });
            }
            self.cur = i_b;
            let low = self.un(Operator::I32WrapI64, v, Type::I32);
            let fi = self.un(Operator::F64ConvertI32S, low, Type::F64);
            self.terminate(Terminator::Br {
                target: BlockTarget { block: join, args: vec![fi] },
            });
            self.cur = join;
            let t = self.edge(g, 0, &[x])?;
            self.terminate(Terminator::Br { target: t });
        } else {
            let want = match kind {
                UnboxKind::I32 => TAG_INT32,
                UnboxKind::Bool => TAG_BOOLEAN,
                UnboxKind::Obj => TAG_OBJECT,
                UnboxKind::Str => TAG_STRING,
                UnboxKind::F64Num => unreachable!(),
            };
            let hit = self.body.add_block();
            let is_k = self.tag_is(tag, want as u32);
            self.cond_br(is_k, Self::to(hit), Self::to(other));
            self.cur = hit;
            let payload = self.un(Operator::I32WrapI64, v, Type::I32);
            let t = self.edge(g, 0, &[payload])?;
            self.terminate(Terminator::Br { target: t });
        }
        self.cur = other;
        let hole = self.tag_is(tag, TAG_MAGIC as u32);
        let t = self.edge(inst, 0, &[v])?;
        let f_hole = self.body.add_block();
        self.cond_br(hole, Self::to(f_hole), t);
        self.cur = f_hole;
        self.terminate(Terminator::Br { target: Self::to(fail) });
        self.cur = fail;
        let f = self.edge(inst, 1, &[])?;
        self.terminate(Terminator::Br { target: f });
        Ok(())
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
            // A ghost (`Fact`) has no representation, and a lazy switch
            // case is loaded by the switch itself: a placeholder no
            // lowering reads.
            if machine(&self.ty(v)).is_none() || self.lazy_strs.contains_key(&v) {
                out.push(self.i32c(0));
                continue;
            }
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
        self.frame_top[0] = self.frame_end[0];
        self.inline_ks();
        self.scc_tops(&order);
        // A region in a cycle overlays only what the cycle's calls do not
        // scan: else each entry of it would dirty slots the cycle's other
        // calls then clear again, every iteration.
        for b in f.blocks.keys() {
            let Some(&top) = self.scc_top.get(&b) else { continue };
            for &i in &f.blocks[b].insts {
                let fr = f.inst_frame[i];
                if fr != 0 {
                    let o = self.outer_frame(fr) as usize;
                    self.inline_k[o] = self.inline_k[o].max(top);
                }
            }
        }
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
        self.value_tag("(entry)");
        self.entry()?;
        // In reverse postorder, so a block's dominators, which define the
        // unmanaged values it uses directly, are lowered before it.
        for b in order {
            self.cur_mblock = b;
            self.value_tag("(edges)");
            self.enter_block(b)?;
            if let Some(census) = self.block_census {
                self.value_tag("(census)");
                static NEXT: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
                let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let ops: Vec<String> = f.blocks[b].insts.iter().map(|&i| mir::print::mnemonic(&f.insts[i].op)).collect();
                crate::diag_line!("night: mir block {id} sid#{} {b} {}", self.f.script, ops.join(" "));
                let (k, i) = (self.i32c(crate::options::MIR_BLOCK_CENSUS_KIND), self.i32c(id));
                self.call1(census, &[k, i], Type::I32);
                self.value_tag("(edges)");
            }
            self.block_enters = None;
            for &inst in &f.blocks[b].insts {
                self.cold = false;
                self.cur_inst = Some(inst);
                if matches!(f.insts[inst].op, Opcode::InlineEnter) {
                    self.block_enters = Some(f.inst_frame[inst]);
                }
                // Retaining stores still pending at a terminator that
                // cannot GC (an inlined call's entry): the GC points are
                // past the block, so they are written here.
                if !self.pending_retain.is_empty()
                    && !self.f.insts[inst].succs.is_empty()
                    && !self.may_gc(inst)
                {
                    // An inlined callee that cannot GC needs none: the
                    // caller's next GC point retains its locals itself.
                    let callee_gc = self.block_enters.is_none_or(|fid| self.frame_may_gc(fid));
                    // Into a successor this block alone reaches, and before
                    // it is entered: still pending there, written only where
                    // a GC point actually runs (a slow path, a call).
                    let succs = &self.f.insts[inst].succs;
                    let sole = match succs.as_slice() {
                        [e] => Some(e.block),
                        _ => None,
                    }
                    .filter(|s| {
                        self.preds.get(s).is_some_and(|p| p.len() == 1) && !self.plans.contains_key(s)
                    });
                    if !callee_gc {
                        // An inlined callee that cannot GC needs none: the
                        // caller's next GC point retains its locals itself.
                    } else if let Some(s) = sole {
                        // What the successor has a value for (its live-ins);
                        // the rest is written here.
                        let live_in = &self.live_in[&s];
                        let (carry, write): (Vec<_>, Vec<_>) =
                            self.pending_retain.iter().copied().partition(|(_, v)| live_in.contains(v));
                        self.pending_retain = write;
                        let n = self.flush_retain(None)?;
                        self.root_tick("retain", n);
                        self.carried_retain.insert(s, carry);
                    } else {
                        let n = self.flush_retain(None)?;
                        self.root_tick("retain", n);
                    }
                    self.pending_retain.clear();
                }
                let before = self.body.values.len();
                if self.viz_marks.is_some() && self.value_census.is_none() {
                    self.value_tag("inst");
                }
                if self.value_census.is_some() {
                    let mut tag = mir::print::mnemonic(&f.insts[inst].op);
                    if let Some(site) = f.insts[inst].attach.and_then(|a| f.attachments[a].site) {
                        tag = format!("{tag}@{site}");
                    } else if let Some(pc) = self.exit_pc(inst) {
                        let fr = f.inst_frame[inst];
                        let script = if fr == 0 { f.script } else { f.inline_frames[fr as usize - 1].script };
                        tag = format!("{tag}@{script}:{pc}");
                    }
                    self.value_tag(&tag);
                }
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
        self.value_tag("(hubs)");
        // Each `exit.inline` hub continues at its site's tail.
        for (_, last, site, err, same, tails) in std::mem::take(&mut self.inline_hubs).into_values() {
            let targets: Vec<BlockTarget> = tails
                .iter()
                .map(|&t| BlockTarget {
                    block: t,
                    args: vec![err, same],
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
        self.instrument_values();
        Ok(())
    }

    /// The pc an instruction exits at on failure, where a successor is an
    /// exit block (the op's own bytecode pc): for `--value-census` tags.
    fn exit_pc(&self, inst: mir::Inst) -> Option<crate::ids::Pc> {
        self.f.insts[inst].succs.iter().find_map(|e| {
            let t = self.f.terminator(e.block)?;
            match self.f.insts[t].op {
                Opcode::Exit { pc, .. } | Opcode::ExitThrow { pc, .. } | Opcode::ExitInline { pc, .. } => Some(pc),
                _ => None,
            }
        })
    }

    /// `--value-census`: the Wasm values from here on are `tag`'s.
    fn value_tag(&mut self, tag: &str) {
        // `--viz`: an instruction's own tag marks it (the loop sets
        // `cur_inst` first); any other starts unattributed values.
        if let Some(marks) = self.viz_marks.as_mut() {
            let i = match (tag.starts_with('('), self.cur_inst) {
                (false, Some(inst)) => mir::entity::EntityRef::index(inst) as u32 + 1,
                _ => 0,
            };
            marks.push((self.body.values.len(), i));
        }
        if self.value_census.is_some() {
            self.value_tags.push((self.body.values.len(), tag.to_string()));
        }
    }

    /// `--value-census`: a census tick at the head of every Wasm block,
    /// and its static record of the values in it, by emitter.
    fn instrument_values(&mut self) {
        let Some(census) = self.value_census else { return };
        let tags = std::mem::take(&mut self.value_tags);
        let tag_of = |v: Value| -> &str {
            let i = v.index();
            match tags.partition_point(|&(s, _)| s <= i) {
                0 => "(other)",
                k => &tags[k - 1].1,
            }
        };
        static NEXT: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
        let blocks: Vec<Block> = self.body.blocks.iter().collect();
        for b in blocks {
            let mut n: BTreeMap<&str, u32> = BTreeMap::new();
            for &v in &self.body.blocks[b].insts {
                *n.entry(tag_of(v)).or_default() += 1;
            }
            if n.is_empty() {
                continue;
            }
            let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let rec: Vec<String> = n.iter().map(|(t, c)| format!("{t}:{c}")).collect();
            crate::diag_line!("night: mir vblock {id} sid#{} {}", self.f.script, rec.join(" "));
            let len = self.body.blocks[b].insts.len();
            let saved = self.cur;
            self.cur = b;
            let (k, i) = (self.i32c(crate::options::MIR_VALUE_CENSUS_KIND), self.i32c(id));
            self.call1(census, &[k, i], Type::I32);
            self.cur = saved;
            // The tick first, before the block's own instructions.
            self.body.blocks[b].insts.rotate_left(len);
        }
    }

    /// Whether an instruction in the loop through header `h` (back-edge
    /// sources `later`) may GC.
    fn loop_may_gc(&self, h: mir::Block, later: &[mir::Block]) -> bool {
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
        body.iter().any(|&b| f.blocks[b].insts.iter().any(|&i| self.may_gc(i)))
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

    /// Whether frame `fid`, or a frame inlined into it, has an instruction
    /// that may GC.
    fn frame_may_gc(&mut self, fid: u32) -> bool {
        if self.frame_gc.is_none() {
            let f = self.f;
            let mut gc = vec![false; f.inline_frames.len() + 1];
            for i in f.blocks.values().flat_map(|b| b.insts.iter().copied()) {
                if !self.may_gc(i) {
                    continue;
                }
                let mut fr = f.inst_frame[i];
                loop {
                    if gc[fr as usize] {
                        break;
                    }
                    gc[fr as usize] = true;
                    if fr == 0 {
                        break;
                    }
                    fr = f.inline_frames[fr as usize - 1].parent;
                }
            }
            self.frame_gc = Some(gc);
        }
        self.frame_gc.as_ref().unwrap()[fid as usize]
    }

    /// Whether `inst` may call something that GCs (a superset of where the
    /// lowering roots: any op with an `err` or `ok_dirty` edge).
    fn may_gc(&self, inst: mir::Inst) -> bool {
        use mir::ops::SuccRole;
        let op = &self.f.insts[inst].op;
        // `init_field` (ok, fail) calls the runtime's plain add on its
        // slow path.
        matches!(op, Opcode::InitField(_) | Opcode::StoreElem(_, true))
            || op.roles().iter().any(|r| matches!(r, SuccRole::Err | SuccRole::OkDirty))
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
                    let hot = HOT_CROSSINGS_ONLY && !gc_only_off_path(&d.op);
                    let g = crossed_gen.entry(b).or_default();
                    for &v in live.iter().filter(|&&v| managed(v)) {
                        cand.insert(v);
                        if hot || !HOT_CROSSINGS_ONLY {
                            g.insert(v);
                        }
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
        // What may hold a dead value on entry: as the hot edges have it (a
        // helper's slow path clears its own extra on its edge, `conform`,
        // so a hot GC point after the join need not).
        let hot_dirty = pend.iter().any(|p| !p.cold);
        let mut dirty: BTreeSet<u32> = pend
            .iter()
            .filter(|p| !hot_dirty || !p.cold)
            .flat_map(|p| p.dirty.iter().copied())
            .collect();
        // A loop that may GC starts clean: its entry edges clear what they
        // may leave dead (`conform`), so its GC points do not clear them
        // on every iteration.
        // (Only the slots its calls scan, `scc_top`: those above stay
        // unscanned inside the loop, and are dirty again past each call.)
        if !later.is_empty() && !dirty.is_empty() && self.loop_may_gc(b, &later) {
            let kept: BTreeSet<u32> = plan
                .iter()
                .filter(|&&(_, loc, es)| loc == Loc::Slot || es)
                .filter_map(|(v, _, _)| self.home.get(v).copied())
                .collect();
            let scanned = self.scc_top.get(&b).copied().unwrap_or(self.nslots).min(self.block_slots(b));
            dirty.retain(|&s| kept.contains(&s) || s >= scanned);
        }
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
        self.pending_retain = self.carried_retain.remove(&b).unwrap_or_default();
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
        let mut stores = 0u32;
        let mut stored: Vec<String> = vec![];
        for (v, loc, es) in self.plans[&b].clone() {
            let (reg, sl) = p.snap.get(&v).copied().unwrap_or((None, false));
            let lost = || format!("lowering: {v} is live into {b} but has no value on an edge");
            if (loc == Loc::Slot || es) && !sl {
                let r = reg.ok_or_else(lost)?;
                let t = self.ty(v);
                let boxed = self.boxed(&t, r)?;
                let off = self.home_off(v)?;
                self.store_i64(self.vp, off, boxed);
                stores += 1;
                if self.root_census.is_some() {
                    stored.push(format!("{v}:{loc:?}:{es}"));
                }
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
        // (Never one an inline frame overlays: `block_slots`.)
        let limit = self.block_slots(b);
        let extra: Vec<u32> = p
            .dirty
            .iter()
            .copied()
            .filter(|&s| s < limit && !self.entry_dirty[&b].contains(&s) && !kept.contains(&s))
            .collect();
        if !extra.is_empty() {
            let undef = self.i64c(UNDEF);
            for s in extra {
                self.store_i64(self.vp, self.root_base + 8 * s, undef);
                stores += 1;
            }
        }
        if self.root_census.is_some() {
            let cold = std::mem::replace(&mut self.cold, p.cold);
            self.root_tick(&format!("edge->{b}[{}]", stored.join(",")), stores);
            self.cold = cold;
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
                RootKind::Entry | RootKind::Resume { .. } => None,
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
        if self.is_gen {
            // A generator's resume stages the generator-closing magic as
            // `this`, which no call passes (`EnterNightResume`).
            let thisv = self.load_i64(self.sp, FrameLayout::THIS);
            let magic = self.i64c((TAG_MAGIC << 32) | MAGIC_GENERATOR_CLOSING);
            let is_resume = self.bin(Operator::I64Eq, thisv, magic, Type::I32);
            let (res, fresh) = (self.body.add_block(), self.body.add_block());
            self.cond_br(is_resume, Self::to(res), Self::to(fresh));
            self.cur = res;
            self.gen_resume_dispatch()?;
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
        if l.has_args_obj {
            self.store_i64(vp, l.args_obj(), undef);
        }
        self.store_i64(vp, l.rval(), undef);
        // The environment: the callee's own, or none (§5.1).
        let env = if self.plain_env {
            let callee = self.load_i64(self.sp, 0);
            let f = self.un(Operator::I32WrapI64, callee, Type::I32);
            self.load_i64(f, FUNC_ENV_SLOT_OFFSET)
        } else {
            undef
        };
        if l.has_env {
            self.store_i64(vp, l.env(), env);
        }
        if l.has_new_target {
            self.store_i64(vp, l.new_target(), self.new_target);
        }
        let zero = self.i64c(TAG_INT32 << 32);
        self.store_i64(vp, l.resume(), zero);
        self.store_i64(vp, l.backoff(), zero);
        if self.is_gen {
            self.init_root_area();
        } else {
            // Not written here: every slot may hold a dead frame's value,
            // which the first may-GC call on each path clears (`root`'s
            // stale slots), as a loop's entry edges do where the loop may
            // GC (`enter_block`).
            self.dirty = (0..self.nslots).collect();
        }
        if self.own_env {
            // The CallObject inline from the script's row, where it is
            // armed: no GC, so nothing is rooted and the frame's values
            // stand. Else the helper, which fills the row.
            let cell = self.i32c(CONSTRUCT_CELL_ADDR_PLACEHOLDER);
            let idx = self.atoms.next_construct_cell();
            self.construct_cell_patches.push((cell, idx + 1));
            let slow = self.body.add_block();
            let env = self.env_inline(cell, slow);
            self.store_i64(vp, l.env(), env);
            let dirty = self.dirty.clone();
            self.enter_entry_root(root, &vals)?;
            self.cur = slow;
            self.dirty = dirty;
            // The GC may run: nothing is live yet, so its scan stops at the
            // fixed frame, below every rooting slot. Failing, the throw has
            // no handler (baseline's prologue: pc 0, depth 0).
            self.gc_top = self.root_base;
            let top = self.add_off(self.vp, self.top_off(0));
            let script = self.script_ptr();
            let ok = self.call1(self.h.env_setup, &[self.cx, top, self.sp, script, cell], Type::I32);
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
        self.enter_entry_root(root, &vals)
    }

    /// The entry's last step: enter the entry root with callee, `this`
    /// and the formals, `vals`.
    fn enter_entry_root(&mut self, root: mir::Block, vals: &[Value]) -> R<()> {
        let params = self.f.blocks[root].params.clone();
        if params.len() != vals.len() {
            return Err("lowering: the entry root's params are not the frame".into());
        }
        let mut args = vec![];
        for (&p, &v) in params.iter().zip(vals) {
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
    /// A generator's resume (baseline's `finalize_gen_dispatch`): read
    /// the descriptor `EnterNightResume` staged over the locals, set the
    /// fixed slots a fresh prologue would, restore the locals, operands
    /// and environment from the generator, push the resume protocol's
    /// `[sent value, generator, resume kind]` at the landing's depth, and
    /// enter the `Resume` root for the saved resume index.
    fn gen_resume_dispatch(&mut self) -> R<()> {
        let l = self.layout;
        let vp = self.vp;
        let desc = self.add_off(vp, l.local_base());
        let ridx = self.load_i32(desc, 0);
        let roots: Vec<(u32, Pc, mir::Block)> = self
            .f
            .roots
            .iter()
            .filter_map(|r| match r.kind {
                RootKind::Resume { index, pc } => Some((index, pc, r.block)),
                _ => None,
            })
            .collect();
        // A yield this body has no root for (one in catch code, which is
        // baseline's, suspended there after an exit): baseline's own
        // resume dispatch, with the descriptor untouched.
        let other = self.body.add_block();
        let max_k = roots.iter().map(|&(k, _, _)| k).max().unwrap_or(0);
        let mut targets = vec![Self::to(other); (max_k + 1) as usize];
        let disp = self.cur;
        for (k, pc, root) in roots {
            let b = self.body.add_block();
            targets[k as usize] = Self::to(b);
            self.cur = b;
            let desc = self.add_off(vp, l.local_base());
            let rkind = self.load_i32(desc, 4);
            let rgen = self.load_i64(desc, 8);
            let rarg = self.load_i64(desc, 16);
            let undef = self.i64c(UNDEF);
            let mut fixed = l.optional_slots();
            fixed.push(l.rval());
            for off in fixed {
                self.store_i64(vp, off, undef);
            }
            let zero = self.i64c(TAG_INT32 << 32);
            self.store_i64(vp, l.resume(), zero);
            self.store_i64(vp, l.backoff(), zero);
            let lp = self.add_off(vp, l.local_base());
            let nl = self.i32c(l.nlocals);
            let ep = if self.plain_env || self.own_env {
                self.add_off(vp, l.env())
            } else {
                self.i32c(0)
            };
            let ops = self.add_off(vp, l.operand_base());
            self.call(self.h.gen_restore, &[self.cx, rgen, lp, nl, ep, ops], &[Type::I32]);
            let depth = *self.f.frame.depths.get(&pc).ok_or("lowering: no depth at a resume root")?;
            let saved = depth.checked_sub(3).ok_or("lowering: a resume landing below depth 3")?;
            self.store_i64(vp, l.operand(saved), rarg);
            self.store_i64(vp, l.operand(saved + 1), rgen);
            let kind = self.box_tagged(TAG_INT32, rkind);
            self.store_i64(vp, l.operand(saved + 2), kind);
            self.enter_onramp(pc, root)?;
        }
        self.cur = disp;
        let known: Vec<(u32, BlockTarget)> = targets
            .iter()
            .enumerate()
            .filter(|(_, t)| t.block != other)
            .map(|(k, t)| (u32::try_from(k).unwrap(), t.clone()))
            .collect();
        if known.len() <= RESUME_CHAIN_MAX {
            // A few yields (the usual generator, an async function's
            // awaits): compares, each a predicted branch, rather than a
            // `br_table`'s bounds check and indirect jump.
            for (k, t) in known {
                let kv = self.i32c(k);
                let hit = self.bin(Operator::I32Eq, ridx, kv, Type::I32);
                let next = self.body.add_block();
                self.cond_br(hit, t, Self::to(next));
                self.cur = next;
            }
            self.terminate(Terminator::Br { target: Self::to(other) });
        } else {
            self.terminate(Terminator::Select {
                value: ridx,
                targets,
                default: Self::to(other),
            });
        }
        self.cur = other;
        let argc = self.argc;
        self.tail_to_baseline(argc);
        Ok(())
    }

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
        let pre = self.epoch();
        let ok = self.call1(f, &full, Type::I32);
        let post = self.epoch();
        self.epoch_same = Some(self.bin(Operator::I32Eq, pre, post, Type::I32));
        self.after_gc(live);
        // A helper's slow path: its edges reload what their targets keep
        // in registers.
        self.cold = true;
        let result = self.load_i64(self.vp, top_off);
        Ok((ok, result))
    }

    /// The first free byte above everything a may-GC call's frame chain
    /// holds, as an offset from `sp`: where its helper's out-slot and GC
    /// scan limit, and a real call's frame, go -- as a native stack pointer
    /// would be. Set by the call's `root`: in the function's own frame,
    /// past the rooting slots its live values occupy (`root_top`); in an
    /// inline frame, past that frame, so past every rooting slot and every
    /// enclosing inline frame. (`live` no longer matters: kept for the
    /// callers' shape.)
    fn top_off(&self, _live: usize) -> u32 {
        self.gc_top
    }

    /// How many rooting slots a may-GC call with `live` live across it
    /// scans: in the function's own frame, past the highest home slot of
    /// `live`, and at least its cycle's (`scc_top`); in an inline frame,
    /// all of them (its frame is above them).
    fn root_top(&self, live: &[mir::Value]) -> u32 {
        if self.cur_frame != 0 {
            return self.inline_k[self.outer_frame(self.cur_frame) as usize];
        }
        let need = live.iter().filter_map(|v| self.home.get(v)).map(|&k| k + 1).max().unwrap_or(0);
        need.max(self.scc_top.get(&self.cur_mblock).copied().unwrap_or(0))
    }

    /// `scc_top`: the CFG's strongly connected components (Tarjan), and
    /// per component with a cycle, the most rooting slots any may-GC
    /// instruction in it needs (all of them for one in an inline frame).
    fn scc_tops(&mut self, order: &[mir::Block]) {
        let f = self.f;
        let blocks: Vec<mir::Block> = order.to_vec();
        let idx: BTreeMap<mir::Block, usize> = blocks.iter().enumerate().map(|(i, &b)| (b, i)).collect();
        let succs: Vec<Vec<usize>> = blocks
            .iter()
            .map(|&b| f.succs(b).into_iter().filter_map(|s| idx.get(&s).copied()).collect())
            .collect();
        let n = blocks.len();
        let (mut index, mut low, mut on) = (vec![usize::MAX; n], vec![0usize; n], vec![false; n]);
        let (mut stack, mut comps, mut next) = (vec![], vec![], 0usize);
        for root in 0..n {
            if index[root] != usize::MAX {
                continue;
            }
            // Iterative Tarjan: (node, next successor to visit).
            let mut work = vec![(root, 0usize)];
            index[root] = next;
            low[root] = next;
            next += 1;
            stack.push(root);
            on[root] = true;
            while let Some(&mut (v, ref mut k)) = work.last_mut() {
                if *k < succs[v].len() {
                    let w = succs[v][*k];
                    *k += 1;
                    if index[w] == usize::MAX {
                        index[w] = next;
                        low[w] = next;
                        next += 1;
                        stack.push(w);
                        on[w] = true;
                        work.push((w, 0));
                    } else if on[w] {
                        low[v] = low[v].min(index[w]);
                    }
                } else {
                    work.pop();
                    if let Some(&(u, _)) = work.last() {
                        low[u] = low[u].min(low[v]);
                    }
                    if low[v] == index[v] {
                        let mut comp = vec![];
                        loop {
                            let w = stack.pop().unwrap();
                            on[w] = false;
                            comp.push(w);
                            if w == v {
                                break;
                            }
                        }
                        comps.push(comp);
                    }
                }
            }
        }
        for comp in comps {
            let cyclic = comp.len() > 1 || succs[comp[0]].contains(&comp[0]);
            if !cyclic {
                continue;
            }
            let mut top = 0;
            for &c in &comp {
                for &i in &f.blocks[blocks[c]].insts {
                    if !self.may_gc(i) {
                        continue;
                    }
                    let need = if f.inst_frame[i] != 0 {
                        self.inline_k[self.outer_frame(f.inst_frame[i]) as usize]
                    } else {
                        self.live_across(i)
                            .iter()
                            .filter_map(|v| self.home.get(v))
                            .map(|&k| k + 1)
                            .max()
                            .unwrap_or(0)
                    };
                    top = top.max(need);
                }
            }
            for &c in &comp {
                self.scc_top.insert(blocks[c], top);
            }
        }
    }

    /// How many rooting slots a block's code may scan, so may clear: in an
    /// inline frame's region, those below the frame (`inline_k`), which
    /// overlays the rest; elsewhere all of them.
    fn block_slots(&self, b: mir::Block) -> u32 {
        match self.f.blocks[b].insts.first().map(|&i| self.f.inst_frame[i]) {
            Some(fr) if fr != 0 => self.inline_k[self.outer_frame(fr) as usize],
            _ => self.nslots,
        }
    }

    /// The inline frame inlined into the function's own frame that `fid`
    /// is in (itself, or an ancestor).
    fn outer_frame(&self, mut fid: u32) -> u32 {
        loop {
            let parent = self.f.inline_frames[fid as usize - 1].parent;
            if parent == 0 {
                return fid;
            }
            fid = parent;
        }
    }

    /// `inline_k`: per outermost inline frame, one past the highest home
    /// of a managed value live into a block of its region or across a
    /// may-GC instruction in it.
    fn inline_ks(&mut self) {
        let f = self.f;
        let mut k = vec![0u32; f.inline_frames.len() + 1];
        let homed = |l: &Lower, vs: &mut dyn Iterator<Item = mir::Value>| -> u32 {
            vs.filter_map(|v| l.home.get(&v)).map(|&h| h + 1).max().unwrap_or(0)
        };
        for b in f.blocks.keys() {
            let mut outers = BTreeSet::new();
            for &i in &f.blocks[b].insts {
                let fr = f.inst_frame[i];
                if fr == 0 {
                    continue;
                }
                let o = self.outer_frame(fr);
                outers.insert(o);
                let n = homed(self, &mut self.live_across(i).into_iter());
                k[o as usize] = k[o as usize].max(n);
            }
            if outers.is_empty() {
                continue;
            }
            let n = self.live_in.get(&b).map_or(0, |l| homed(self, &mut l.iter().copied()));
            for o in outers {
                k[o as usize] = k[o as usize].max(n);
            }
        }
        self.inline_k = k;
    }

    /// Lay out the inline frames (§5.5): one inlined into the function's
    /// own frame right above the rooting slots its region keeps
    /// (`inline_k`), one inlined into another at its parent's end.
    fn inline_layout(&mut self) {
        for (i, fr) in self.f.inline_frames.iter().enumerate() {
            // The callee's own layout (its baseline body resumes on the
            // frame), with the actuals placed by `voff` rather than a rebase.
            let lay = match self.inline_layouts.get(i) {
                Some(&l) => FrameLayout { rebase_vp: false, ..l },
                None => FrameLayout::full(fr.shape.formals, fr.shape.locals),
            };
            debug_assert!(lay.nargs == fr.shape.formals && lay.nlocals == fr.shape.locals);
            let off = if fr.parent == 0 {
                self.root_base + 8 * self.inline_k[i + 1]
            } else {
                self.frame_top[fr.parent as usize]
            };
            let voff = off + 8 * fr.argc.map_or(0, |n| n.saturating_sub(fr.shape.formals));
            let fid = u32::try_from(self.frame_off.len()).unwrap();
            let nact = fr.argc.map_or(lay.nargs, |n| n.max(lay.nargs)) as usize;
            let mut fixed = Fixed::None;
            for (i, d) in self.f.insts.iter() {
                if self.f.inst_frame[i] != fid {
                    continue;
                }
                match d.op {
                    Opcode::ArgsObject | Opcode::FrameNewTarget => fixed = Fixed::All,
                    Opcode::InlineEnter if d.args.len() != 2 + nact => fixed = Fixed::All,
                    Opcode::EnvSet | Opcode::EnvPop if fixed == Fixed::None => fixed = Fixed::Env,
                    _ => {}
                }
            }
            self.frame_off.push(off);
            self.frame_voff.push(voff);
            self.frame_end.push(voff + lay.top(fr.max_depth + 3));
            self.frame_top.push(match fixed {
                Fixed::All => voff + lay.operand_base(),
                Fixed::Env => voff + lay.env() + 8,
                Fixed::None => voff + lay.fixed_base(),
            });
            self.fixed.push(fixed);
            self.frame_layouts.push(lay);
        }
    }

    /// The stamp epoch (`gNightStampEpoch`, low word), which every
    /// demotion of a stamped object's class word bumps: unchanged across
    /// a call, no layout fact was invalidated.
    fn epoch(&mut self) -> Value {
        let slot = self.i32c(self.h.strlit_slot + crate::region_shape::STRLIT_STAMP_EPOCH_ADDR_OFF);
        let addr = self.load_i32(slot, 0);
        self.load_i32(addr, 0)
    }

    /// Bump the stamp epoch (a demotion in compiled code).
    fn bump_epoch(&mut self) {
        let slot = self.i32c(self.h.strlit_slot + crate::region_shape::STRLIT_STAMP_EPOCH_ADDR_OFF);
        let addr = self.load_i32(slot, 0);
        let v = self.load_i64(addr, 0);
        let one = self.i64c(1);
        let n = self.bin(Operator::I64Add, v, one, Type::I64);
        self.store_i64(addr, 0, n);
    }

    /// The success edges of a generic op after its helper `ok`: `ok_clean`
    /// when the stamp epoch did not move across it (`epoch_same`, from
    /// the last `gc_call` or a call's own sample), so its layout facts
    /// hold; `ok_dirty` otherwise; `err` on failure.
    fn clean_or_dirty(&mut self, inst: mir::Inst, ok: Value, same: Value, outs: &[Value]) -> R<()> {
        let e = self.edge(inst, 2, &[])?;
        let okb = self.body.add_block();
        self.cond_br(ok, Self::to(okb), e);
        self.cur = okb;
        let c = self.edge(inst, 0, outs)?;
        let d = self.edge(inst, 1, outs)?;
        self.cond_br(same, c, d);
        Ok(())
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
            let off = match k {
                0 => self.frame_off[f] + FrameLayout::THIS,
                k if k <= nargs => self.frame_off[f] + l.arg(k - 1),
                k if k <= nargs + nlocals => self.frame_voff[f] + l.local(k - 1 - nargs),
                _ => self.frame_voff[f] + l.rval(),
            };
            // A slot past the frame's GC scan (a lean inline frame's rval)
            // retains nothing, and a nested inline frame may occupy it.
            if f > 0 && off >= self.frame_top[f] {
                continue;
            }
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
        // The scan: the rooting slots below `top`, and the frame below
        // them. Slots there holding what is live now are valid; any other
        // dirty one may hold a dead frame's or stale bits, which the GC
        // must not see.
        let top = self.root_top(live);
        self.gc_top = if self.cur_frame != 0 {
            self.frame_top[self.cur_frame as usize]
        } else {
            self.root_base + 8 * top
        };
        let holding: BTreeSet<u32> = live.iter().filter_map(|v| self.home.get(v).copied()).collect();
        let stale: Vec<u32> = self.dirty.iter().copied().filter(|&s| s < top && !holding.contains(&s)).collect();
        if !stale.is_empty() {
            let undef = self.i64c(UNDEF);
            for s in &stale {
                self.store_i64(self.vp, self.root_base + 8 * s, undef);
            }
            stores += u32::try_from(stale.len()).unwrap();
        }
        // Every slot below `top` is valid now (a dead value may stay in
        // its slot); those above are unscanned, and the call's frame or
        // out-slot may overwrite them.
        self.dirty = (top..self.nslots).collect();
        self.slotted.retain(|v| live.contains(v));
        let e = self.opsize.entry("(root sites / stores)".into()).or_default();
        e.0 += 1;
        e.1 += stores;
        self.root_tick("root", stores);
        Ok(())
    }

    /// `--root-census`: count this rooting site's executions, where it
    /// stored anything, and print its static record.
    fn root_tick(&mut self, what: &str, stores: u32) {
        let Some(census) = self.root_census else { return };
        if stores == 0 {
            return;
        }
        static NEXT: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
        let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let op = self.cur_inst.map_or("-".to_string(), |i| mir::print::mnemonic(&self.f.insts[i].op));
        crate::diag_line!(
            "night: mir root {id} sid#{} {what}@{} {op} stores {stores} cold {}",
            self.f.script,
            self.cur_mblock,
            self.cold
        );
        let (k, i) = (self.i32c(crate::options::MIR_ROOT_CENSUS_KIND), self.i32c(id));
        self.call1(census, &[k, i], Type::I32);
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
        self.epoch_same = None;
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
                    ConstVal::Hole => (TAG_MAGIC << 32) | crate::wasm::translate::MAGIC_ELEMENTS_HOLE,
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
            Opcode::BoxDouble => {
                let bits = self.un(Operator::I64ReinterpretF64, a[0], Type::I64);
                let nan = self.bin(Operator::F64Ne, a[0], a[0], Type::I32);
                let canon = self.i64c(CANONICAL_NAN_BITS);
                let v = self.select(Type::I64, canon, bits, nan);
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
                    // Its type rules out a zero divisor.
                    ArithOp::Rem => Operator::I32RemS,
                };
                let v = self.bin(o, a[0], a[1], Type::I32);
                self.def(inst, v);
            }
            Opcode::IntArith(op) => {
                let o = match op {
                    ArithOp::Add => Operator::I64Add,
                    ArithOp::Sub => Operator::I64Sub,
                    ArithOp::Mul => Operator::I64Mul,
                    ArithOp::Rem => Operator::I64RemS,
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
                    // Wasm has no fmod: the leaf helper (`js::NumberMod`).
                    F64Op::Mod => {
                        let v = self.call1(self.h.fmod, &[a[0], a[1]], Type::F64);
                        self.def(inst, v);
                        return Ok(());
                    }
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
            Opcode::Math(m) => {
                let v = match m {
                    MathFn::Abs => self.un(Operator::F64Abs, a[0], Type::F64),
                    MathFn::Floor => self.un(Operator::F64Floor, a[0], Type::F64),
                    MathFn::Ceil => self.un(Operator::F64Ceil, a[0], Type::F64),
                    MathFn::Trunc => self.un(Operator::F64Trunc, a[0], Type::F64),
                    MathFn::Sqrt => self.un(Operator::F64Sqrt, a[0], Type::F64),
                    MathFn::Fround => {
                        let f = self.un(Operator::F32DemoteF64, a[0], Type::F32);
                        self.un(Operator::F64PromoteF32, f, Type::F64)
                    }
                    // wasm's min/max are JS's: NaN wins, -0 < +0.
                    MathFn::Min => self.bin(Operator::F64Min, a[0], a[1], Type::F64),
                    MathFn::Max => self.bin(Operator::F64Max, a[0], a[1], Type::F64),
                    MathFn::Pow => self.call1(self.h.math_pow, &[a[0], a[1]], Type::F64),
                    MathFn::Sin | MathFn::Cos => {
                        let k = self.i32c(u32::from(m == MathFn::Cos));
                        self.call1(self.h.math_unary, &[k, a[0]], Type::F64)
                    }
                    _ => return Err(format!("lowering: math {m:?}")),
                };
                self.def(inst, v);
            }
            Opcode::CheckNative(n) => {
                // The callee's JSNative is the pristine one (a function
                // object's native sits in its env slot's place, as
                // `math_arms` reads it).
                let idx = native_math_index(&self.mm.natives[n].name)
                    .ok_or_else(|| format!("lowering: native {}", self.mm.natives[n].name))?;
                let (_, _, native) = self.classify_native(a[0]);
                let fail = self.body.add_block();
                self.check(native, fail);
                let cp = self.un(Operator::I32WrapI64, a[0], Type::I32);
                let nf = self.load_i32(cp, FUNC_ENV_SLOT_OFFSET);
                let c = self.i32c(self.h.math_natives_base + 4 * idx);
                let slot = self.load_i32(c, 0);
                let same = self.bin(Operator::I32Eq, nf, slot, Type::I32);
                let (ok_b, cont) = (self.body.add_block(), self.body.add_block());
                self.cond_br(same, Self::to(ok_b), Self::to(fail));
                self.cur = fail;
                self.terminate(Terminator::Br { target: Self::to(cont) });
                self.cur = ok_b;
                let t = self.edge(inst, 0, &[])?;
                self.terminate(Terminator::Br { target: t });
                self.cur = cont;
                let e = self.edge(inst, 1, &[])?;
                self.terminate(Terminator::Br { target: e });
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
            Opcode::SwitchStr(n) => self.switch_str(inst, &a, n)?,
            Opcode::StampFresh(w) => {
                let obj = self.un(Operator::I32WrapI64, a[0], Type::I32);
                let wv = self.i32c(w);
                self.store_i32(obj, OBJ_CLASS_IDX_OFFSET, wv);
            }
            Opcode::Restamp(i) => self.restamp(a[0], self.mm.restamps[i as usize]),
            Opcode::Return => {
                self.store_i64(self.retval_out, 0, a[0]);
                let z = self.i32c(0);
                self.ret(z);
            }
            Opcode::Unreachable => self.terminate(Terminator::Unreachable),
            Opcode::GenSuspend { index, nargs, nlocals, initial, .. } => {
                self.gen_suspend(inst, &a, index, nargs, nlocals, initial)?;
            }
            Opcode::IsGenClosing => {
                let m = self.i64c((TAG_MAGIC << 32) | MAGIC_GENERATOR_CLOSING);
                let r = self.bin(Operator::I64Eq, a[0], m, Type::I32);
                self.def(inst, r);
            }
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
            Opcode::GuardUnbox(UnboxKind::F64Num) if NUM_UNBOX_BRANCHY && self.plain_guard(inst) => {
                let tag = self.tag_of(a[0]);
                let have = value_tags(&self.ty(d.args[0]));
                self.unbox_num_edges(inst, a[0], tag, have)?;
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
                // Of the tags the input may have, test the fewer: those
                // in `t`, or those outside it.
                let have = match self.ty(d.args[0]) {
                    MType::Val(s) => s.tags,
                    _ => TagSet::ALL,
                };
                let (inside, outside) = (have.intersect(t), have.minus(t));
                let c = if outside.count() < inside.count() {
                    let o = self.has_tags(a[0], outside);
                    self.un(Operator::I32Eqz, o, Type::I32)
                } else {
                    self.has_tags(a[0], inside)
                };
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
            Opcode::I32Ovf(op @ (ArithOp::Add | ArithOp::Sub))
                if CONST_OVF_COMPARE && self.const_i32(d.args[1]).or(if op == ArithOp::Add { self.const_i32(d.args[0]) } else { None }).is_some() =>
            {
                // `x + c` (either side) or `x - c`: overflow is `x` past
                // one bound, one compare rather than a widened sum.
                let (x, c) = match self.const_i32(d.args[1]) {
                    Some(c) => (a[0], c),
                    None => (a[1], self.const_i32(d.args[0]).unwrap()),
                };
                let c = if op == ArithOp::Sub { -c } else { c };
                let o = if op == ArithOp::Add { Operator::I32Add } else { Operator::I32Sub };
                let r = self.bin(o, a[0], a[1], Type::I32);
                let ok = if c >= 0 {
                    let bound = self.i32c((i64::from(i32::MAX) - c) as i32 as u32);
                    self.bin(Operator::I32LeS, x, bound, Type::I32)
                } else {
                    let bound = self.i32c((i64::from(i32::MIN) - c) as i32 as u32);
                    self.bin(Operator::I32GeS, x, bound, Type::I32)
                };
                self.guard(inst, ok, &[r])?;
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
                    ArithOp::Rem => {
                        // A zero divisor fails (NaN), and so does a zero
                        // remainder of a negative dividend (-0). `rem_s`
                        // traps on 0, so it divides by 1 there instead;
                        // INT_MIN % -1 is 0 in Wasm, and fails as -0.
                        let z = self.i32c(0);
                        let nz = self.bin(Operator::I32Ne, y, z, Type::I32);
                        let one = self.i32c(1);
                        let d = self.select(Type::I32, y, one, nz);
                        let r = self.bin(Operator::I32RemS, x, d, Type::I32);
                        let neg = self.bin(Operator::I32LtS, x, z, Type::I32);
                        let rz = self.un(Operator::I32Eqz, r, Type::I32);
                        let negz = self.bin(Operator::I32And, neg, rz, Type::I32);
                        let pos = self.un(Operator::I32Eqz, negz, Type::I32);
                        (r, self.bin(Operator::I32And, nz, pos, Type::I32))
                    }
                };
                self.guard(inst, ok, &[r])?;
            }
            Opcode::Prim(p) => self.prim_op(inst, p, &a)?,
            Opcode::JsAdd
            | Opcode::JsBinop(_)
            | Opcode::JsUnop(_)
            | Opcode::JsCompare(_)
            | Opcode::JsToNumeric => {
                self.numeric_fast_arms(inst, &d.op, &a)?;
                if d.op == Opcode::JsAdd {
                    self.concat_arm(inst, &d, &a)?;
                }
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
                let v = self.typeof_eq(a[0], k);
                self.def(inst, v);
            }
            Opcode::JsConstantStrictEq(k) => {
                // `ConstantStrictEqual` inline: the operand's type
                // byte, then its payload.
                let v = self.constant_strict_eq(a[0], k);
                self.def(inst, v);
            }
            // The activation's environment is fixed (§5.1): the frame's env
            // slot, which the fresh entry (or baseline, before an onramp)
            // set, and which is rooted with the frame.
            Opcode::GlobalObject => {
                let realm = self.load_i32(self.cx, JSCONTEXT_REALM_OFFSET);
                let global = self.load_i32(realm, REALM_GLOBAL_OFFSET);
                let g = self.box_tagged(TAG_OBJECT, global);
                self.def(inst, g);
            }
            Opcode::EnvCurrent => {
                let env = self.frame_env();
                let p = self.un(Operator::I32WrapI64, env, Type::I32);
                self.def(inst, p);
            }
            Opcode::EnvCallee(hops) => {
                let env = self.frame_env();
                let hv = self.i32c(hops);
                let r = self.call1(self.h.env_callee, &[self.cx, env, hv], Type::I64);
                self.def(inst, r);
            }
            Opcode::ObjectLit(index) => {
                let script = self.script_ptr();
                let iv = self.i32c(index);
                let r = self.call1(self.h.object, &[self.cx, script, iv], Type::I64);
                self.def(inst, r);
            }
            Opcode::EnvSet => {
                let off = self.frame_env_off();
                self.store_i64(self.vp, off, a[0]);
            }
            Opcode::EnvPop => {
                let env = self.frame_env();
                let p = self.un(Operator::I32WrapI64, env, Type::I32);
                let up = self.load_i64(p, FIXED_SLOTS_BASE);
                let off = self.frame_env_off();
                self.store_i64(self.vp, off, up);
            }
            // `EnvironmentObject::ENCLOSING_ENV_SLOT`, always fixed.
            Opcode::EnvParent => {
                let env = self.load_i64(a[0], FIXED_SLOTS_BASE);
                let p = self.un(Operator::I32WrapI64, env, Type::I32);
                self.def(inst, p);
            }
            Opcode::EnvLoad(slot) => {
                let (addr, off) = self.env_slot(a[0], slot.get());
                let v = self.load_i64(addr, off);
                self.def(inst, v);
            }
            Opcode::EnvStore(slot) => {
                // `setAliasedBinding` zero hops up, inline: the slot store
                // with its barriers.
                let (addr, off) = self.env_slot(a[0], slot.get());
                self.pre_barrier(addr, off);
                self.store_i64(addr, off, a[1]);
                let s = self.i32c(slot.get());
                self.post_barrier(self.h.post_write_barrier, a[0], s, a[1]);
            }
            Opcode::FrameStore(k) => {
                let fid = self.cur_frame as usize;
                let l = self.frame_layouts[fid];
                let (nargs, nlocals) = (l.nargs, l.nlocals);
                let off = match k {
                    0 => self.frame_off[fid] + FrameLayout::THIS,
                    k if k <= nargs => self.frame_off[fid] + l.arg(k - 1),
                    k if k <= nargs + nlocals => self.frame_voff[fid] + l.local(k - 1 - nargs),
                    _ => self.frame_voff[fid] + l.rval(),
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
            Opcode::LitNew(n) => {
                // As `js.rt.newobject`: the inline nursery allocation from
                // the site's cell, else the helper (which fills the cell).
                let cell = self.alloc_inline(inst, None)?;
                let nv = self.i32c(n);
                let live = self.live_across(inst);
                let (ok, r) = self.gc_call(self.h.new_object, &[cell, nv], &live)?;
                let t = self.edge(inst, 0, &[r])?;
                let e = self.edge(inst, 1, &[])?;
                self.cond_br(ok, t, e);
            }
            Opcode::LitInit(name, _) => {
                // As `js.rt.initprop`: the site's add transition replayed
                // inline, else the helper (which fills the row).
                let site = self.init_prop_inline(inst, a[0], a[1])?;
                let at = self.atom(name);
                let av = self.i32c(crate::wasm::mir::abi::INIT_ATTR_ENUMERATE);
                let sv = self.i32c(site);
                let live = self.live_across(inst);
                let (ok, _) = self.gc_call(self.h.init_prop, &[a[0], at, a[1], av, sv], &live)?;
                let t = self.edge(inst, 0, &[])?;
                let e = self.edge(inst, 1, &[])?;
                self.cond_br(ok, t, e);
            }
            Opcode::JsLambda(index) => {
                // Inline from the site's row: no GC, so the ok edge keeps
                // everything in registers. The helper (which fills the
                // row), and the rooting, only on the slow path.
                let env = self.box_tagged(TAG_OBJECT, a[0]);
                let cell = self.i32c(CONSTRUCT_CELL_ADDR_PLACEHOLDER);
                let idx = self.atoms.next_construct_cell();
                self.construct_cell_patches.push((cell, idx + 1));
                let slow = self.body.add_block();
                let r = self.lambda_inline(cell, env, slow);
                let t = self.edge(inst, 0, &[r])?;
                self.terminate(Terminator::Br { target: t });
                self.cur = slow;
                let script = self.script_ptr();
                let i = self.i32c(index);
                let live = self.live_across(inst);
                let (ok, r) = self.gc_call(self.h.lambda, &[env, script, i, cell], &live)?;
                let t = self.edge(inst, 0, &[r])?;
                let e = self.edge(inst, 1, &[])?;
                self.cond_br(ok, t, e);
            }
            Opcode::JsGetName(name) => {
                // A getter may run: clean only if no class word was
                // demoted meanwhile.
                if let Some(&bid) = self.gname_bids.get(&name) {
                    self.gname_fast_arms(inst, bid)?;
                }
                let at = self.atom(name);
                let z = self.i32c(0);
                self.js_call(inst, self.h.get_gname, &[at, z], false)?;
            }
            Opcode::JsGetProp(name) | Opcode::GetPropData(name) => {
                // The site's inline cache (a fact-free read): the
                // shared probe `night_ic_get` (own and holder ways, then
                // the megamorphic table) takes `ok_clean` on a hit; a miss
                // runs the generic get and fills the site's ways. For
                // `getprop.data` the same arms take `ok`, and a miss asks
                // the runtime's pure lookup, failing where it would run
                // code.
                let cache = self.atoms.next_prop_cache();
                let way_base = self.ic_addr(cache * INLINE_IC_STRIDE);
                let nm = String::from_utf16_lossy(self.mm.atoms[name].chars());
                if nm == "charCodeAt" || nm == "charAt" {
                    // A string's pristine char method, while String.prototype
                    // is untouched: the cached native.
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
                if let Opcode::GetPropData(_) = d.op {
                    self.get_ic_pure(inst, name, a[0], way_base, cache)?;
                } else {
                    self.get_ic(inst, name, a[0], way_base, cache)?;
                }
            }
            Opcode::JsSetProp(name, strict) => self.set_ic(inst, name, a[0], a[1], strict)?,
            Opcode::SetPropData(name) => self.set_ic_pure(inst, name, a[0], a[1])?,
            Opcode::JsGetElem | Opcode::GetElemData => {
                // An in-bounds, non-hole dense element of a native object
                // inline (as baseline does), taking `ok_clean` (`ok`);
                // everything else through the helper (for `getelem.data`,
                // its pure read, failing where the read would run code).
                let slow = self.body.add_block();
                let v = self.dense_element(a[0], a[1], slow);
                let t = self.edge(inst, 0, &[v])?;
                self.terminate(Terminator::Br { target: t });
                self.cur = slow;
                // The other pure arms, where the operands' types admit
                // them: a string's char, and a string key's megamorphic
                // probe (`obj[name]`).
                let (rt, kt) = (value_tags(&self.ty(d.args[0])), value_tags(&self.ty(d.args[1])));
                if !rt.intersect(TagSet::prims(PRIM_STRING)).is_empty() && !kt.intersect(TagSet::INT32).is_empty() {
                    let other = self.body.add_block();
                    let c = self.string_char(a[0], a[1], other);
                    let t = self.edge(inst, 0, &[c])?;
                    self.terminate(Terminator::Br { target: t });
                    self.cur = other;
                }
                if !rt.intersect(TagSet::OBJECT).is_empty() && !kt.intersect(TagSet::prims(PRIM_STRING)).is_empty() {
                    let other = self.body.add_block();
                    let tag = self.tag_of(a[0]);
                    let is_obj = self.tag_is(tag, TAG_OBJECT as u32);
                    let ktag = self.tag_of(a[1]);
                    let is_str = self.tag_is(ktag, TAG_STRING as u32);
                    let both = self.bin(Operator::I32And, is_obj, is_str, Type::I32);
                    self.check(both, other);
                    let obj = self.un(Operator::I32WrapI64, a[0], Type::I32);
                    let r = self.call1(self.h.elem_mega_get, &[obj, a[1]], Type::I64);
                    let rtag = self.tag_of(r);
                    let miss = self.tag_is(rtag, TAG_MAGIC as u32);
                    let hit = self.body.add_block();
                    self.cond_br(miss, Self::to(other), Self::to(hit));
                    self.cur = hit;
                    let t = self.edge(inst, 0, &[r])?;
                    self.terminate(Terminator::Br { target: t });
                    self.cur = other;
                }
                // An arguments object's element (`args_element`),
                // in a function that makes one.
                if self.makes_args && !rt.intersect(TagSet::OBJECT).is_empty() && !kt.intersect(TagSet::INT32).is_empty() {
                    let other = self.body.add_block();
                    let v = self.args_element(a[0], a[1], other);
                    let t = self.edge(inst, 0, &[v])?;
                    self.terminate(Terminator::Br { target: t });
                    self.cur = other;
                }
                if self.ta_poly(inst) {
                    // A typed array of any kind: the
                    // probe's value, or the magic tag on a miss.
                    let generic = self.body.add_block();
                    let (obj, idx) = self.obj_int(a[0], a[1], generic);
                    let r = self.call1(self.h.ta_get_poly, &[obj, idx], Type::I64);
                    let tag = self.tag_of(r);
                    let miss = self.tag_is(tag, TAG_MAGIC as u32);
                    let hit = self.body.add_block();
                    self.cond_br(miss, Self::to(generic), Self::to(hit));
                    self.cur = hit;
                    let t = self.edge(inst, 0, &[r])?;
                    self.terminate(Terminator::Br { target: t });
                    self.cur = generic;
                }
                if d.op == Opcode::GetElemData {
                    self.slow_census(inst);
                    let live = self.live_across(inst);
                    let (r, v) = self.gc_call(self.h.get_elem_pure, &[a[0], a[1]], &live)?;
                    self.epoch_same = None;
                    let one = self.i32c(1);
                    let ok = self.bin(Operator::I32Eq, r, one, Type::I32);
                    let t = self.edge(inst, 0, &[v])?;
                    let other = self.body.add_block();
                    self.cond_br(ok, t, Self::to(other));
                    self.cur = other;
                    let none = self.un(Operator::I32Eqz, r, Type::I32);
                    let f = self.edge(inst, 1, &[])?;
                    let e = self.edge(inst, 2, &[])?;
                    self.cond_br(none, f, e);
                } else {
                    self.js_call(inst, self.h.get_element, &[a[0], a[1]], false)?;
                }
            }
            Opcode::JsSetElem(_, duty) | Opcode::SetElemData(duty) => {
                // An in-bounds overwrite of a non-hole dense element inline,
                // taking `ok_clean`: an own writable data property unless
                // the elements are frozen. The store bypasses the engine,
                // so it owes the array stamp's RANGES claim its duty: a
                // clear for a value not proven inside the claim
                // (no MIR fact rests on it; the epoch bump tells callers').
                let num = matches!(self.ty(d.args[2]), MType::Val(s) if s.tags.subset_of(TagSet::NUMBER));
                let slow = self.body.add_block();
                let (obj, elements, idx, addr, _) = self.dense_slot(a[0], a[1], slow);
                let back = self.i32c(ELEMENTS_FLAGS_BACK);
                let header = self.bin(Operator::I32Sub, elements, back, Type::I32);
                let flags = self.load_i32(header, 0);
                let fz = self.i32c(ELEMENTS_FROZEN_FLAG);
                let frozen = self.bin(Operator::I32And, flags, fz, Type::I32);
                let good = self.un(Operator::I32Eqz, frozen, Type::I32);
                self.check(good, slow);
                if duty {
                    self.elem_duty(obj);
                }
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
                if APPEND_ARM {
                    let generic = self.body.add_block();
                    self.elem_append_arm(inst, a[0], a[1], a[2], duty, num, generic)?;
                    self.cur = generic;
                }
                if self.ta_poly(inst) {
                    // A typed array of any kind (the poly-TA store probe).
                    let generic = self.body.add_block();
                    let (obj, idx) = self.obj_int(a[0], a[1], generic);
                    let ok = self.call1(self.h.ta_set_poly, &[obj, idx, a[2]], Type::I32);
                    let hit = self.body.add_block();
                    self.cond_br(ok, Self::to(hit), Self::to(generic));
                    self.cur = hit;
                    let t = self.edge(inst, 0, &[])?;
                    self.terminate(Terminator::Br { target: t });
                    self.cur = generic;
                }
                // Only where the key may be a string: the arm at every
                // element store cost mandreel 5.6% of its code (-3.9%).
                let key_str = !value_tags(&self.ty(d.args[1])).intersect(TagSet::STRING).is_empty();
                if ELEM_ADD_ARM && key_str {
                    let generic = self.body.add_block();
                    self.elem_add_arm(inst, a[0], a[1], a[2], generic)?;
                    self.cur = generic;
                }
                if let Opcode::JsSetElem(strict, _) = d.op {
                    let sv = self.i32c(u32::from(strict));
                    self.js_call(inst, self.h.set_element, &[a[0], a[1], a[2], sv], false)?;
                } else {
                    // `setelem.data`: the runtime's set, as `set_ic_pure`'s.
                    self.slow_census(inst);
                    let live = self.live_across(inst);
                    let (r, _) = self.gc_call(self.h.set_elem_pure, &[a[0], a[1], a[2]], &live)?;
                    self.epoch_same = None;
                    self.store_codes(inst, r)?;
                }
            }
            Opcode::LengthArray => {
                // The elements header's length word, unsigned.
                let elements = self.load_i32(a[0], OBJ_ELEMENTS_OFFSET);
                let back = self.i32c(ELEMENTS_LENGTH_BACK);
                let la = self.bin(Operator::I32Sub, elements, back, Type::I32);
                let len = self.load_i32(la, 0);
                let r = self.un(Operator::I64ExtendI32U, len, Type::I64);
                self.def(inst, r);
            }
            Opcode::LengthString => {
                let len = self.load_i32(a[0], STRING_LENGTH_OFFSET);
                self.def(inst, len);
            }
            Opcode::GuardRange(r) => {
                // One unsigned compare: `x - lo <=u hi - lo`.
                let x = a[0];
                let lo = self.i32c(r.lo as i32 as u32);
                let d = self.bin(Operator::I32Sub, x, lo, Type::I32);
                let span = self.i32c((r.hi - r.lo) as u32);
                let ok = self.bin(Operator::I32LeU, d, span, Type::I32);
                self.guard(inst, ok, &[x])?;
            }
            Opcode::IntToI32 => {
                let x = a[0];
                let lo = self.i64c(i64::from(i32::MIN) as u64);
                let hi = self.i64c(i64::from(i32::MAX) as u64);
                let ge = self.bin(Operator::I64GeS, x, lo, Type::I32);
                let le = self.bin(Operator::I64LeS, x, hi, Type::I32);
                let ok = self.bin(Operator::I32And, ge, le, Type::I32);
                let i = self.un(Operator::I32WrapI64, x, Type::I32);
                self.guard(inst, ok, &[i])?;
            }
            Opcode::GuardKind(ObjKind::Array) => {
                let shape = self.load_i32(a[0], SHAPE_OFFSET);
                let base = self.load_i32(shape, SHAPE_BASESHAPE_OFFSET);
                let clasp = self.load_i32(base, BASESHAPE_CLASP_OFFSET);
                let aslot = self.i32c(self.h.array_class_slot);
                let arr_class = self.load_i32(aslot, 0);
                let is_arr = self.bin(Operator::I32Eq, clasp, arr_class, Type::I32);
                self.guard(inst, is_arr, &[a[0]])?;
            }
            Opcode::LengthTa => {
                // Its length slot's payload (a detached one reads 0).
                let len = self.load_i32(a[0], TA_LENGTH_PAYLOAD_OFFSET);
                self.def(inst, len);
            }
            Opcode::GuardKind(ObjKind::Plain) => {
                let shape = self.load_i32(a[0], SHAPE_OFFSET);
                let base = self.load_i32(shape, SHAPE_BASESHAPE_OFFSET);
                let clasp = self.load_i32(base, BASESHAPE_CLASP_OFFSET);
                let pslot = self.i32c(self.h.strlit_slot + crate::region_shape::STRLIT_PLAIN_CLASS_OFF);
                let plain_class = self.load_i32(pslot, 0);
                let is_plain = self.bin(Operator::I32Eq, clasp, plain_class, Type::I32);
                self.guard(inst, is_plain, &[a[0]])?;
            }
            Opcode::GuardKind(ObjKind::Native) => {
                let shape = self.load_i32(a[0], SHAPE_OFFSET);
                let flags = self.load_i32(shape, SHAPE_IMMUTABLE_FLAGS_OFFSET);
                let bit = self.i32c(SHAPE_IS_NATIVE_BIT);
                let native = self.bin(Operator::I32And, flags, bit, Type::I32);
                self.guard(inst, native, &[a[0]])?;
            }
            Opcode::GuardKind(ObjKind::TypedArray(k)) => {
                // The class is the kind's typed-array class.
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
            Opcode::LoadElem if FUSED_ELEM_UNBOX && self.fusable_unbox(inst).is_some() => {
                let (g, k, p) = self.fusable_unbox(inst).unwrap();
                self.load_elem_unboxed(inst, g, k, p, a[0], a[1])?;
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
            Opcode::StoreElem(duty, append) => {
                // An in-bounds overwrite of a non-hole dense element of
                // unfrozen elements (an own writable data property); else
                // `fail`. RANGES is dropped under the store's duty.
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
                if duty {
                    self.elem_duty(a[0]);
                }
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
                // Past the initialized length or into a hole: the append
                // arm, where the prototypes' proof allows (it writes the
                // lengths, and runs no JS); else `fail`.
                if APPEND_ARM && append {
                    let miss = self.body.add_block();
                    let recv = self.box_tagged(TAG_OBJECT, a[0]);
                    let key = self.box_tagged(TAG_INT32, a[1]);
                    self.elem_append_arm(inst, recv, key, a[2], duty, num, miss)?;
                    self.cur = miss;
                    // What the arm refused (growth, a row not yet cached):
                    // the runtime's append, which runs no JS.
                    if duty {
                        self.elem_duty(a[0]);
                    }
                    let live = self.live_across(inst);
                    let (ok, _) = self.gc_call(self.h.elem_grow, &[recv, a[1], a[2]], &live)?;
                    self.epoch_same = None;
                    let t = self.edge(inst, 0, &[])?;
                    let f = self.edge(inst, 1, &[])?;
                    self.cond_br(ok, t, f);
                    return Ok(());
                }
                let f = self.edge(inst, 1, &[])?;
                self.terminate(Terminator::Br { target: f });
            }
            Opcode::Call => self.js_call_op(inst, &a, false)?,
            Opcode::CallIter => self.js_call_op(inst, &a, true)?,
            Opcode::CallEval(pc) => self.js_eval_op(inst, &a, pc)?,
            Opcode::GuardScript(sid) => self.guard_script(inst, &d, &a, sid)?,
            Opcode::AccessorProbe(name, set) => {
                // The accessor arm: the (receiver shape, atom, kind)-hashed
                // row the IC miss helpers prime for a prototype getter or
                // setter, its holder's shape still the recorded one.
                use crate::wasm::translate::{
                    ACCESSOR_ATOM_KIND, ACCESSOR_CACHE_ENTRY_BYTES, ACCESSOR_CACHE_SIZE, ACCESSOR_CALLEE,
                    ACCESSOR_HOLDER_PTR, ACCESSOR_HOLDER_SHAPE, ACCESSOR_RECV_SHAPE,
                };
                let aid = self.atoms.intern_chars(self.mm.atoms[name].chars());
                let ak = (aid << 1) | u32::from(set);
                let fail_b = self.body.add_block();
                let tag = self.tag_of(a[0]);
                let is_obj = self.tag_is(tag, TAG_OBJECT as u32);
                self.check(is_obj, fail_b);
                let obj = self.un(Operator::I32WrapI64, a[0], Type::I32);
                let shape = self.load_i32(obj, SHAPE_OFFSET);
                let three = self.i32c(3);
                let sh = self.bin(Operator::I32ShrU, shape, three, Type::I32);
                let k1 = self.i32c(2654435761);
                let h1 = self.bin(Operator::I32Mul, sh, k1, Type::I32);
                let k2 = self.i32c(ak.wrapping_mul(0x9e37_79b9));
                let hh = self.bin(Operator::I32Xor, h1, k2, Type::I32);
                let mask = self.i32c(ACCESSOR_CACHE_SIZE - 1);
                let idx = self.bin(Operator::I32And, hh, mask, Type::I32);
                let stride = self.i32c(ACCESSOR_CACHE_ENTRY_BYTES);
                let off = self.bin(Operator::I32Mul, idx, stride, Type::I32);
                let base = self.i32c(self.h.accessor_cache_base);
                let entry = self.bin(Operator::I32Add, base, off, Type::I32);
                let es = self.load_i32(entry, ACCESSOR_RECV_SHAPE);
                let ea = self.load_i32(entry, ACCESSOR_ATOM_KIND);
                let m1 = self.bin(Operator::I32Eq, es, shape, Type::I32);
                let akv = self.i32c(ak);
                let m2 = self.bin(Operator::I32Eq, ea, akv, Type::I32);
                let m = self.bin(Operator::I32And, m1, m2, Type::I32);
                self.check(m, fail_b);
                // A matched row is primed: its holder is non-null.
                let hp = self.load_i32(entry, ACCESSOR_HOLDER_PTR);
                let hs = self.load_i32(entry, ACCESSOR_HOLDER_SHAPE);
                let live = self.load_i32(hp, SHAPE_OFFSET);
                let m3 = self.bin(Operator::I32Eq, live, hs, Type::I32);
                self.check(m3, fail_b);
                let callee = self.load_i64(entry, ACCESSOR_CALLEE);
                let t = self.edge(inst, 0, &[callee])?;
                self.terminate(Terminator::Br { target: t });
                self.cur = fail_b;
                let f = self.edge(inst, 1, &[])?;
                self.terminate(Terminator::Br { target: f });
            }
            Opcode::InlineEnter => self.inline_enter(&d, &a)?,
            Opcode::NewThis(nslots, word) => {
                // Runs no code. The inline nursery allocation cannot GC, so
                // it takes the ok edge with everything still in registers;
                // only the helper call on its slow path may GC, and only
                // there is what is live across it rooted.
                let live = self.live_across(inst);
                let callee = self.box_tagged(TAG_OBJECT, a[0]);
                let (this_v, slow, cell) = self.construct_this_inline(callee, Some(a[1]), word);
                let t = self.edge(inst, 0, &[this_v])?;
                self.terminate(Terminator::Br { target: t });
                self.cur = slow;
                self.root(&live)?;
                let top_off = self.top_off(live.len());
                let top = self.add_off(self.vp, top_off);
                let ok = self.construct_this_call(top, callee, callee, Some(a[1]), nslots, word, cell);
                self.after_gc(&live);
                self.cold = true;
                let r = self.load_i64(self.vp, top_off);
                let t = self.edge(inst, 0, &[r])?;
                let e = self.edge(inst, 1, &[])?;
                self.cond_br(ok, t, e);
            }
            Opcode::NewThisInit { nslots, word, types, n, .. } => {
                // As `new_this`, with the first `n` fields made with the
                // object: the row's final shape and one check of the
                // prototype chain, else the runtime's adds (which fill the
                // row), failing before anything observable where an add
                // would not be plain.
                let live = self.live_across(inst);
                let callee = self.box_tagged(TAG_OBJECT, a[0]);
                let xs: Vec<Value> = a[2..].to_vec();
                let (obj, slow, cell) = self.construct_this_final(a[1], word, &xs);
                let t = self.edge(inst, 0, &[obj])?;
                self.terminate(Terminator::Br { target: t });
                self.cur = slow;
                self.root(&live)?;
                let base = self.top_off(live.len());
                for (i, &x) in xs.iter().enumerate() {
                    self.store_i64(self.vp, base + 8 * u32::try_from(i).unwrap(), x);
                }
                let top_off = base + 8 * n;
                let top = self.add_off(self.vp, top_off);
                let vals = self.add_off(self.vp, base);
                let cache0 = self.atoms.next_prop_cache();
                for _ in 1..n {
                    self.atoms.next_prop_cache();
                }
                let bits = CLASS_WORD_SLOTS | if types { CLASS_WORD_SHALLOW } else { 0 };
                let args: Vec<Value> = [nslots, 0, word, 0, n, cache0, bits]
                    .iter()
                    .map(|&c| self.i32c(c))
                    .collect();
                let r = self.call1(
                    self.h.new_this_init,
                    &[self.cx, top, callee, a[1], args[0], cell, args[2], vals, args[4], args[5], args[6]],
                    Type::I32,
                );
                self.after_gc(&live);
                self.cold = true;
                let out = self.load_i64(self.vp, top_off);
                let o = self.un(Operator::I32WrapI64, out, Type::I32);
                let one = self.i32c(1);
                let made = self.bin(Operator::I32Eq, r, one, Type::I32);
                let (yes, no) = (self.body.add_block(), self.body.add_block());
                self.cond_br(made, Self::to(yes), Self::to(no));
                self.cur = yes;
                let t = self.edge(inst, 0, &[o])?;
                self.terminate(Terminator::Br { target: t });
                self.cur = no;
                let f = self.edge(inst, 1, &[])?;
                let e = self.edge(inst, 2, &[])?;
                self.cond_br(r, f, e);
            }
            Opcode::CreateThis(nslots, word) => {
                // May GC: root what is live across it.
                let live = self.live_across(inst);
                self.root(&live)?;
                let top_off = self.top_off(live.len());
                let top = self.add_off(self.vp, top_off);
                // `.prototype` may be a getter (a proxy's): clean only if
                // no class word was demoted meanwhile.
                let pre = self.epoch();
                let ok = self.construct_this(top, a[0], a[1], nslots, word);
                self.after_gc(&live);
                let post = self.epoch();
                let same = self.bin(Operator::I32Eq, pre, post, Type::I32);
                let r = self.load_i64(self.vp, top_off);
                self.clean_or_dirty(inst, ok, same, &[r])?;
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
            Opcode::CtorStamp(layout, nfields, keep) => self.ctor_stamp_inline(a[0], layout, nfields, keep, false),
            Opcode::CtorPublish(layout, nfields, keep) => self.ctor_stamp_inline(a[0], layout, nfields, keep, true),
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
                    RtOp::HasOwn => {
                        self.has_own_arm(inst, a[0], a[1])?;
                        (h.has_own, vec![a[0], a[1]])
                    }
                    RtOp::DelProp(name, strict) => {
                        let (at, sv) = (self.atom(name), self.i32c(u32::from(strict)));
                        (h.del_prop, vec![a[0], at, sv])
                    }
                    RtOp::DelElem(strict) => {
                        let sv = self.i32c(u32::from(strict));
                        (h.del_elem, vec![a[0], a[1], sv])
                    }
                    RtOp::NewObject(n) => {
                        let cell = self.alloc_inline(inst, None)?;
                        let nv = self.i32c(n);
                        (h.new_object, vec![cell, nv])
                    }
                    RtOp::NewArray(len) => {
                        let cell = self.alloc_inline(inst, Some(len))?;
                        let lv = self.i32c(len);
                        (h.new_array, vec![lv, cell])
                    }
                    RtOp::InitProp(name, attrs) => {
                        let site = if attrs == crate::wasm::mir::abi::INIT_ATTR_ENUMERATE {
                            self.init_prop_inline(inst, a[0], a[1])?
                        } else {
                            u32::MAX
                        };
                        let (at, av, sv) = (self.atom(name), self.i32c(attrs), self.i32c(site));
                        (h.init_prop, vec![a[0], at, a[1], av, sv])
                    }
                    RtOp::InitElem(attrs, duty) => {
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
                                if attrs == crate::wasm::mir::abi::INIT_ATTR_ENUMERATE
                                    && i < crate::constants::INLINE_INIT_ELEM_CAP =>
                            {
                                self.init_elem_inline(inst, a[0], i, a[2], duty)?
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
                    RtOp::ToString => {
                        // A string is its own; else the helper.
                        let tag = self.tag_of(a[0]);
                        let s = self.tag_is(tag, TAG_STRING as u32);
                        let (hit, miss) = (self.body.add_block(), self.body.add_block());
                        self.cond_br(s, Self::to(hit), Self::to(miss));
                        self.cur = hit;
                        let t = self.edge(inst, 0, &[a[0]])?;
                        self.terminate(Terminator::Br { target: t });
                        self.cur = miss;
                        (h.tostring, vec![a[0]])
                    }
                    RtOp::Symbol(code) => {
                        // A well-known symbol: permanent, from a leaf.
                        let cv = self.i32c(code);
                        let r = self.call1(h.symbol, &[self.cx, cv], Type::I64);
                        let t = self.edge(inst, 0, &[r])?;
                        self.terminate(Terminator::Br { target: t });
                        return Ok(());
                    }
                    RtOp::Intrinsic(_) | RtOp::BuiltinObject(_) => {
                        // A realm constant: the cell once armed; the helper
                        // resolves it and arms it.
                        let (id, row, helper) = match r {
                            RtOp::Intrinsic(name) => {
                                let id = self.atoms.intern_chars(self.mm.atoms[name].chars());
                                (id, self.atoms.intrinsic_cell(id), h.get_intrinsic_cell)
                            }
                            RtOp::BuiltinObject(kind) => (kind, self.atoms.builtin_object_cell(kind), h.builtin_object_cell),
                            _ => unreachable!(),
                        };
                        let cell = self.i32c(crate::wasm::mir::abi::INTRINSIC_CELL_ADDR_PLACEHOLDER);
                        self.intrinsic_cell_patches.push((cell, row));
                        let bits = self.load_i64(cell, 0);
                        let z = self.i64c(0);
                        let armed = self.bin(Operator::I64Ne, bits, z, Type::I32);
                        let (hit, miss) = (self.body.add_block(), self.body.add_block());
                        self.cond_br(armed, Self::to(hit), Self::to(miss));
                        self.cur = hit;
                        let t = self.edge(inst, 0, &[bits])?;
                        self.terminate(Terminator::Br { target: t });
                        self.cur = miss;
                        let iv = self.i32c(id);
                        (helper, vec![iv, cell])
                    }
                    RtOp::InitPropGetSet(name, kind) => {
                        let (at, kv) = (self.atom(name), self.i32c(kind));
                        (h.init_prop_getset, vec![a[0], at, a[1], kv])
                    }
                    RtOp::Iter => {
                        if ITER_FROM_SHAPE {
                            self.iter_from_shape(inst, a[0])?;
                        }
                        (h.iter_, vec![a[0]])
                    }
                    RtOp::Check(k) => {
                        let f = match k {
                            mir::ops::CHECK_OBJ_COERCIBLE => h.check_obj_coercible,
                            mir::ops::CHECK_CLASS_HERITAGE => h.check_class_heritage,
                            mir::ops::CHECK_THIS_REINIT => h.check_this_reinit,
                            _ => h.check_this,
                        };
                        (f, vec![a[0]])
                    }
                    RtOp::SetFunName(prefix) => {
                        let k = self.i32c(prefix);
                        (h.set_fun_name, vec![a[0], a[1], k])
                    }
                    RtOp::GlobalThis => (h.global_this, vec![]),
                    RtOp::BigInt(idx) => {
                        let script = self.script_ptr();
                        let iv = self.i32c(idx);
                        (h.bigint, vec![script, iv])
                    }
                    RtOp::MutateProto => (h.mutate_proto, vec![a[0], a[1]]),
                    RtOp::CheckIsObj(kind) => {
                        let k = self.i32c(kind);
                        (h.check_is_obj, vec![a[0], k])
                    }
                    RtOp::CloseIter(kind) => {
                        let k = self.i32c(kind);
                        (h.close_iter, vec![a[0], k])
                    }
                    RtOp::OptimizeSpreadCall => (h.optimize_spread_call, vec![a[0]]),
                    RtOp::PushEnv(kind, pc) => {
                        let f = match kind {
                            mir::ops::ENV_LEXICAL => h.push_lexical_env,
                            mir::ops::ENV_CLASS_BODY => h.push_class_body_env,
                            _ => h.push_var_env,
                        };
                        let env = self.frame_env();
                        let script = self.script_ptr();
                        let pcv = self.i32c(pc);
                        (f, vec![env, script, pcv])
                    }
                    RtOp::EnterWith(pc) => {
                        let env = self.frame_env();
                        let script = self.script_ptr();
                        let pcv = self.i32c(pc);
                        (h.enter_with, vec![env, a[0], script, pcv])
                    }
                    RtOp::FreshenEnv(recreate) => {
                        let f = if recreate != 0 { h.recreate_lexical_env } else { h.freshen_lexical_env };
                        (f, vec![self.frame_env()])
                    }
                    RtOp::GetName(name, for_typeof) => {
                        let env = self.frame_env();
                        let (at, tv) = (self.atom(name), self.i32c(for_typeof));
                        (h.get_name, vec![env, at, tv])
                    }
                    RtOp::BindName(name, unqualified) => {
                        let f = if unqualified != 0 { h.bind_unqualified_name } else { h.bind_name };
                        let env = self.frame_env();
                        (f, vec![env, self.atom(name)])
                    }
                    RtOp::DelName(name) => {
                        let env = self.frame_env();
                        (h.del_name, vec![env, self.atom(name)])
                    }
                    RtOp::BindVar => (h.bind_var, vec![self.frame_env()]),
                    RtOp::SuperBase => (h.super_base, vec![a[0]]),
                    RtOp::SuperFun => (h.super_fun, vec![a[0]]),
                    RtOp::GetPropSuper(name) => (h.get_prop_super, vec![a[0], a[1], self.atom(name)]),
                    RtOp::GetElemSuper => (h.get_elem_super, vec![a[0], a[1], a[2]]),
                    RtOp::SetPropSuper(name, strict) => {
                        let (at, sv) = (self.atom(name), self.i32c(u32::from(strict)));
                        (h.set_prop_super, vec![a[0], a[1], at, a[2], sv])
                    }
                    RtOp::SetElemSuper(strict) => {
                        let sv = self.i32c(u32::from(strict));
                        (h.set_elem_super, vec![a[0], a[1], a[2], a[3], sv])
                    }
                    RtOp::InitHomeObject => (h.init_home_object, vec![a[0], a[1]]),
                    RtOp::FunWithProto(index) => {
                        let env = self.frame_env();
                        let script = self.script_ptr();
                        let iv = self.i32c(index);
                        (h.fun_with_proto, vec![env, a[0], script, iv])
                    }
                    RtOp::CheckReturn => (h.check_return, vec![a[0], a[1]]),
                    RtOp::CreateGenerator => {
                        let callee = self.load_i64(self.sp, FrameLayout::CALLEE);
                        let env = if self.plain_env || self.own_env {
                            self.frame_env()
                        } else {
                            self.i64c(UNDEF)
                        };
                        (h.create_generator, vec![callee, env])
                    }
                    RtOp::GenFinal => (h.gen_final, vec![a[0]]),
                    RtOp::GenCheckResume => {
                        let k = self.un(Operator::I32WrapI64, a[2], Type::I32);
                        let rval = self.add_off(self.vp, self.frame_voff[self.cur_frame as usize] + self.layout.rval());
                        (h.gen_check_resume, vec![a[1], a[0], k, rval])
                    }
                    RtOp::AsyncAwait(resolve) => {
                        let f = if resolve != 0 { h.async_resolve } else { h.async_await };
                        (f, vec![a[1], a[0]])
                    }
                    RtOp::AsyncReject => (h.async_reject, vec![a[2], a[0], a[1]]),
                    RtOp::CanSkipAwait => (h.can_skip_await, vec![a[0]]),
                    RtOp::MaybeExtractAwait => {
                        let can = self.un(Operator::I32WrapI64, a[1], Type::I32);
                        (h.maybe_extract_await, vec![a[0], can])
                    }
                    RtOp::Resume => (h.resume, vec![a[0], a[1], a[2]]),
                    RtOp::AddDisposable(hint) => {
                        let env = self.frame_env();
                        let hv = self.i32c(hint);
                        (h.add_disposable, vec![env, a[0], a[1], a[2], hv])
                    }
                    RtOp::TakeDisposeCapability => (h.take_dispose_capability, vec![self.frame_env()]),
                    RtOp::CreateSuppressedError => (h.create_suppressed_error, vec![a[0], a[1]]),
                    RtOp::GetBoundName(name) => (h.get_bound_name, vec![a[0], self.atom(name)]),
                    RtOp::ObjWithProto => (h.obj_with_proto, vec![a[0]]),
                    RtOp::NewPrivateName(name) => (h.new_private_name, vec![self.atom(name)]),
                    RtOp::DynamicImport => {
                        let script = self.script_ptr();
                        (h.dynamic_import, vec![script, a[0], a[1]])
                    }
                    RtOp::SpreadEval(pc) => {
                        let env = self.frame_env();
                        let script = self.script_ptr();
                        let pcv = self.i32c(pc);
                        (h.spread_eval, vec![a[0], a[1], a[2], env, script, pcv])
                    }
                    RtOp::InitElemGetSet(kind) => {
                        let kv = self.i32c(kind);
                        (h.init_elem_getset, vec![a[0], a[1], a[2], kv])
                    }
                    RtOp::SetName(name, strict) => {
                        let (at, sv) = (self.atom(name), self.i32c(u32::from(strict)));
                        (h.set_name, vec![a[0], at, a[1], sv])
                    }
                    RtOp::SpreadCall(construct) => {
                        let c = self.i32c(construct);
                        (h.spread_call, vec![a[0], a[1], a[2], a[3], c])
                    }
                    RtOp::CheckPrivateField(cond, kind) => {
                        let (cv, kv) = (self.i32c(cond), self.i32c(kind));
                        (h.check_private_field, vec![a[0], a[1], cv, kv])
                    }
                    RtOp::GetNameTypeof(name) => {
                        // `get_gname`'s typeof form: unbound is undefined.
                        let (at, one) = (self.atom(name), self.i32c(1));
                        (h.get_gname, vec![at, one])
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
                let fid = self.cur_frame as usize;
                let l = self.frame_layouts[fid];
                let slot = self.frame_voff[fid] + l.args_obj();
                let (asp, argc) = self.actuals();
                let cached = self.load_i64(self.vp, slot);
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
                // (An inlined callee's object is unmapped: no env.)
                let (ok, r) = if fid == 0 && (self.plain_env || self.own_env) {
                    let env = self.load_i64(self.vp, l.env());
                    self.gc_call(self.h.arguments_env, &[asp, argc, env], &live)?
                } else {
                    self.gc_call(self.h.arguments_, &[asp, argc], &live)?
                };
                let (store, e) = (self.body.add_block(), self.edge(inst, 1, &[])?);
                self.cond_br(ok, Self::to(store), e);
                self.cur = store;
                self.store_i64(self.vp, slot, r);
                let t = self.edge(inst, 0, &[r])?;
                self.terminate(Terminator::Br { target: t });
            }
            Opcode::RestArray(n) => {
                let live = self.live_across(inst);
                let nv = self.i32c(n);
                let (asp, argc) = self.actuals();
                let (ok, r) = self.gc_call(self.h.rest, &[asp, argc, nv], &live)?;
                let t = self.edge(inst, 0, &[r])?;
                let e = self.edge(inst, 1, &[])?;
                self.cond_br(ok, t, e);
            }
            Opcode::ArgsLength => {
                let (_, argc) = self.actuals();
                self.def(inst, argc);
            }
            Opcode::IterMore => {
                let r = self.iter_more(a[0]);
                self.def(inst, r);
            }
            Opcode::IterEnd => self.iter_end(a[0]),
            Opcode::IterOptimizable => {
                let r = self.call1(self.h.optimize_get_iterator, &[self.cx, a[0]], Type::I32);
                self.def(inst, r);
            }
            Opcode::IterIsDone => {
                let m = self.i64c((TAG_MAGIC << 32) | crate::wasm::translate::MAGIC_NO_ITER_VALUE);
                let r = self.bin(Operator::I64Eq, a[0], m, Type::I32);
                self.def(inst, r);
            }
            Opcode::FrameCallee => {
                let fid = self.cur_frame as usize;
                let v = if fid == 0 {
                    self.load_i64(self.sp, FrameLayout::CALLEE)
                } else {
                    self.load_i64(self.vp, self.frame_off[fid] + FrameLayout::CALLEE)
                };
                self.def(inst, v);
            }
            Opcode::FrameNewTarget => {
                let fid = self.cur_frame as usize;
                let off = self.frame_voff[fid] + self.frame_layouts[fid].new_target();
                let v = self.load_i64(self.vp, off);
                self.def(inst, v);
            }
            Opcode::ActualArgOr(k) => {
                let (asp, argc) = self.actuals();
                let v = self.load_i64(asp, FrameLayout::ARGS + 8 * k);
                let kv = self.i32c(k);
                let have = self.bin(Operator::I32LtU, kv, argc, Type::I32);
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
                let (asp, argc) = self.actuals();
                self.js_call(inst, self.h.apply_fwd, &[a[0], a[1], a[2], asp, argc], false)?;
            }
            Opcode::ActualArg => {
                let eight = self.i32c(8);
                let off = self.bin(Operator::I32Mul, a[0], eight, Type::I32);
                let (asp, _) = self.actuals();
                let addr = self.bin(Operator::I32Add, asp, off, Type::I32);
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
                // `new Array()`: the pristine Array
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
                    let same = self.epoch_same.take().expect("gc_call sampled the epoch");
                    self.clean_or_dirty(inst, ok, same, &[r])?;
                    (self.vmap, self.slotted, self.dirty, self.framed) = saved;
                    self.cur = other;
                }
                // The frame `[callee, this, args…, new.target]` above the
                // rooting slots, then the runtime's construct (it creates
                // `this` sized and seeded for the site, and runs the
                // constructor). The result lands at the frame's top.
                let live = self.live_across(inst);
                self.root(&live)?;
                let construct_pre = self.epoch();
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
                // construct.
                const HEADROOM: u32 = 64 * 1024;
                let (funcidx, script) = self.classify(callee);
                let z = self.i32c(0);
                let compiled = self.bin(Operator::I32Ne, funcidx, z, Type::I32);
                let fits = self.stack_fits(top, HEADROOM);
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
                let post = self.epoch();
                let same = self.bin(Operator::I32Eq, construct_pre, post, Type::I32);
                self.clean_or_dirty(inst, ok_p, same, &[res_p])?;
            }
            Opcode::GuardLayout { keys, types, slots, closed } => {
                // The stamp word (`JSObject*+4`): identity is layout key + 1
                // in the low 16 bits; TYPES is the SHALLOW bit (§4.3). The
                // SLOTS bit too: a claim then holds
                // the fields at their slots, until a kill (only the engine
                // clears SLOTS, bumping the epoch), so the field ops under
                // it load and store with no test of their own.
                let w = self.load_i32(a[0], OBJ_CLASS_IDX_OFFSET);
                let m = self.i32c(0xFFFF);
                let id = self.bin(Operator::I32And, w, m, Type::I32);
                let want = if types { CLASS_WORD_SHALLOW } else { 0 }
                    | if slots { CLASS_WORD_SLOTS } else { 0 }
                    | if closed { CLASS_WORD_CLOSED } else { 0 };
                // One masked compare: identity and
                // the bits at once. Over a range, the masked word less the
                // lowest wanted word is at most the span only with every
                // bit there (a missing bit, at 1 << 16 or above, wraps it).
                // The sentinel too, which the expected word lacks: under
                // it the low half is a set of fields, not an identity.
                let mask = self.i32c(CLASS_WORD_SENTINEL | 0xFFFF | want);
                let wm = self.bin(Operator::I32And, w, mask, Type::I32);
                let exp = self.i32c((keys.lo.get() + 1) | want);
                let ok = if keys.lo == keys.hi {
                    self.bin(Operator::I32Eq, wm, exp, Type::I32)
                } else {
                    let rel = self.bin(Operator::I32Sub, wm, exp, Type::I32);
                    let span = self.i32c(keys.hi.get() - keys.lo.get());
                    self.bin(Operator::I32LeU, rel, span, Type::I32)
                };
                self.guard_word = Some((w, id, keys));
                self.guard_obj = Some(a[0]);
                self.guard(inst, ok, &[a[0]])?;
                self.guard_word = None;
                self.guard_obj = None;
            }
            Opcode::GuardCtor { key, n, types } => {
                // Under construction for `key` (§2.3): the sentinel with
                // its early key, SLOTS (and TYPES), the word's field set
                // `n`, and the span of `n` (every field is at its row's
                // slot, so a property past them would raise it): exactly
                // the fields `n`.
                let w = self.load_i32(a[0], OBJ_CLASS_IDX_OFFSET);
                let bits = CLASS_WORD_SLOTS | if types { CLASS_WORD_SHALLOW } else { 0 };
                let fm = (1 << mir::types::FieldSet::WORD_BITS) - 1;
                let m = self.i32c(CLASS_WORD_SENTINEL | (EARLY_KEY_MAX << EARLY_KEY_SHIFT) | bits | fm);
                let want = self.i32c(
                    CLASS_WORD_SENTINEL | ((key.get() + 1) << EARLY_KEY_SHIFT) | bits | n.word_bits(),
                );
                let wm = self.bin(Operator::I32And, w, m, Type::I32);
                let ok = self.bin(Operator::I32Eq, wm, want, Type::I32);
                let shape = self.load_i32(a[0], SHAPE_OFFSET);
                let imm = self.load_i32(shape, SHAPE_IMMUTABLE_FLAGS_OFFSET);
                let sm = self.i32c(SHAPE_SMALL_SLOTSPAN_MASK_BITS << SHAPE_SMALL_SLOTSPAN_SHIFT);
                let span = self.bin(Operator::I32And, imm, sm, Type::I32);
                let nv = self.i32c(n.span() << SHAPE_SMALL_SLOTSPAN_SHIFT);
                let s_ok = self.bin(Operator::I32Eq, span, nv, Type::I32);
                let ok = self.bin(Operator::I32And, ok, s_ok, Type::I32);
                self.guard(inst, ok, &[a[0]])?;
            }
            Opcode::InitField(name) => self.init_field(inst, name, a[0], a[1])?,
            Opcode::PublishLayout => {
                // The stamp of a completed `constructing(n)` object (its
                // type proves the sentinel, the key and every field): its
                // identity, keeping SLOTS and, where claimed, TYPES.
                let c = self
                    .ty(d.args[0])
                    .obj_info()
                    .and_then(|o| o.layout)
                    .ok_or("lowering: publish_layout without a layout claim")?;
                let w = self.load_i32(a[0], OBJ_CLASS_IDX_OFFSET);
                let keep = CLASS_WORD_SLOTS | if c.types { CLASS_WORD_SHALLOW } else { 0 };
                let kb = self.i32c(keep);
                let bits = self.bin(Operator::I32And, w, kb, Type::I32);
                // Exactly the row's fields: CLOSED, where the layout may be.
                let closed = if self.mm.layouts.get(&c.keys.lo).is_some_and(|l| l.closed) {
                    CLASS_WORD_CLOSED
                } else {
                    0
                };
                let idx = self.i32c((c.keys.lo.get() + 1) | closed);
                let nw = self.bin(Operator::I32Or, idx, bits, Type::I32);
                self.store_i32(a[0], OBJ_CLASS_IDX_OFFSET, nw);
                self.def(inst, a[0]);
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
            Opcode::MethodLoad { cell, atom, script } => {
                // The receiver's prototype is the one the cell is armed
                // for (an unarmed cell holds 0, an unarmable one 1): the
                // function there. Else, if unarmed, the runtime arms it
                // for this prototype (a leaf) and it is tested again.
                let sa = self
                    .mm
                    .script_addrs
                    .get(&script)
                    .copied()
                    .ok_or("lowering: method.load of a script with no address")?;
                let c = self.i32c(cell);
                let shape = self.load_i32(a[0], SHAPE_OFFSET);
                let base = self.load_i32(shape, SHAPE_BASESHAPE_OFFSET);
                let proto = self.load_i32(base, BASESHAPE_PROTO_OFFSET);
                let p = self.load_i32(c, 0);
                let hit = self.bin(Operator::I32Eq, proto, p, Type::I32);
                // CLOSED (the receiver is of a published layout: its word
                // is a stamp's).
                let w = self.load_i32(a[0], OBJ_CLASS_IDX_OFFSET);
                let cb = self.i32c(CLASS_WORD_CLOSED);
                let closed = self.bin(Operator::I32And, w, cb, Type::I32);
                let f = self.load_i32(c, crate::region_shape::METHOD_CELL_FN_OFF);
                let (miss, open) = (self.body.add_block(), self.body.add_block());
                let fail = self.edge(inst, 1, &[])?;
                self.cond_br(closed, Self::to(open), fail);
                self.cur = open;
                let t = self.edge(inst, 0, &[f])?;
                self.cond_br(hit, t, Self::to(miss));
                self.cur = miss;
                let (arm, done) = (self.body.add_block(), self.body.add_block());
                let ok = self.body.add_blockparam(done, Type::I32);
                let z = self.i32c(0);
                let unarmed = self.bin(Operator::I32Eq, p, z, Type::I32);
                self.cond_br(
                    unarmed,
                    Self::to(arm),
                    BlockTarget {
                        block: done,
                        args: vec![z],
                    },
                );
                self.cur = arm;
                let rb = self.box_tagged(TAG_OBJECT, a[0]);
                let av = self.atom(atom);
                let sv = self.i32c(sa);
                let r = self.call1(self.h.method_arm, &[rb, c, av, sv], Type::I32);
                self.terminate(Terminator::Br {
                    target: BlockTarget {
                        block: done,
                        args: vec![r],
                    },
                });
                self.cur = done;
                let f = self.load_i32(c, crate::region_shape::METHOD_CELL_FN_OFF);
                self.guard(inst, ok, &[f])?;
            }
            Opcode::CheckBinding(b, BindingCheck::Fn) => {
                // The value fuse in its predicted state: the binding holds
                // a compiled function of its predicted script. A cell a
                // major GC zeroed re-arms at the resolve, so a miss resolves
                // once before it exits.
                let slot = self.mm.bindings[b].slot;
                let vals = self.i32c(self.h.global_vals_base + 16 * slot);
                let fw = self.load_i32(vals, 8);
                let want = self.i32c(BINDING_FUSE_PREDICTED);
                let ok = self.bin(Operator::I32Eq, fw, want, Type::I32);
                let miss = self.body.add_block();
                let t = self.edge(inst, 0, &[])?;
                self.cond_br(ok, t, Self::to(miss));
                self.cur = miss;
                let bv = self.i32c(slot);
                self.call(self.h.resolve_global_slot_guarded, &[self.cx, bv], &[Type::I32]);
                let fw = self.load_i32(vals, 8);
                let ok = self.bin(Operator::I32Eq, fw, want, Type::I32);
                self.guard(inst, ok, &[])?;
            }
            Opcode::CheckBinding(b, k) => {
                let slot = self.mm.bindings[b].slot;
                let write = k == BindingCheck::Write;
                if !write {
                    // A read of a binding whose value fuse is armed
                    // (`gGlobalVals`) needs no slot: `load_gname` takes the
                    // value there. Straight to `ok`, the test kept for the
                    // loads its fact reaches (they dominate them).
                    let vals = self.i32c(self.h.global_vals_base + 16 * slot);
                    let fw = self.load_i32(vals, 8);
                    let armed = self.fuse_armed(fw);
                    if let Some(&EdgeArg::Out(0)) = d.succs[0].args.first() {
                        let fact = self.f.blocks[d.succs[0].block].params[0];
                        self.binding_armed.insert(fact, armed);
                    }
                    let chk = self.body.add_block();
                    let t = self.edge(inst, 0, &[])?;
                    self.cond_br(armed, t, Self::to(chk));
                    self.cur = chk;
                } else {
                    // An armed value fuse says the binding is still the
                    // global's own data property (a redefinition, delete or
                    // lexical shadow blows it), and a resolved row whether
                    // it is writable (bit 2; a major GC zeroes the row,
                    // which the full test below resolves again).
                    let vals = self.i32c(self.h.global_vals_base + 16 * slot);
                    let fw = self.load_i32(vals, 8);
                    let base = self.i32c(self.h.global_slots_base);
                    let entry = self.load_i32(base, 8 * slot);
                    let two = self.i32c(2);
                    let armed4 = self.bin(Operator::I32Shl, fw, two, Type::I32);
                    let both = self.bin(Operator::I32And, armed4, entry, Type::I32);
                    let four = self.i32c(4);
                    let fast = self.bin(Operator::I32And, both, four, Type::I32);
                    let chk = self.body.add_block();
                    let t = self.edge(inst, 0, &[])?;
                    self.cond_br(fast, t, Self::to(chk));
                    self.cur = chk;
                }
                let ok = self.binding_ok(slot, write);
                self.guard(inst, ok, &[])?;
            }
            Opcode::LoadGName(b) => {
                // The value fuse's copy while armed, else the slot. The
                // check that made the fact tested the fuse: its test, where
                // the fact is that check's (the fuse only disarms through
                // a write, which kills the fact).
                let slot = self.mm.bindings[b].slot;
                let vals = self.i32c(self.h.global_vals_base + 16 * slot);
                if self.ty(d.args[0]) == MType::Fact(FactKind::BindingFn(b)) {
                    // In the predicted state, which a write leaves only
                    // for another function of the script (and kills the
                    // fact meanwhile): the copy is the value.
                    let v = self.load_i64(vals, 0);
                    self.def(inst, v);
                    return Ok(());
                }
                // (A write to a global disarms its fuse but keeps the
                // fact: only a load in the check's `ok` block, before any
                // write there.)
                let fact = d.args[0];
                let fresh = matches!(self.f.values[fact].def, mir::func::ValueDef::Param(b, _) if b == self.cur_mblock)
                    && !self.f.blocks[self.cur_mblock]
                        .insts
                        .iter()
                        .take_while(|&&i| i != inst)
                        .any(|&i| matches!(self.f.insts[i].op, Opcode::StoreGName(_)));
                let armed = match self.binding_armed.get(&fact).filter(|_| fresh) {
                    Some(&a) => a,
                    None => {
                        let fw = self.load_i32(vals, 8);
                        self.fuse_armed(fw)
                    }
                };
                let (hit, miss, join) = (self.body.add_block(), self.body.add_block(), self.body.add_block());
                let r = self.body.add_blockparam(join, Type::I64);
                self.cond_br(armed, Self::to(hit), Self::to(miss));
                self.cur = hit;
                let v = self.load_i64(vals, 0);
                self.terminate(Terminator::Br {
                    target: BlockTarget { block: join, args: vec![v] },
                });
                self.cur = miss;
                let addr = self.binding_addr(slot);
                let v = self.load_i64(addr, 0);
                self.terminate(Terminator::Br {
                    target: BlockTarget { block: join, args: vec![v] },
                });
                self.cur = join;
                self.def(inst, r);
            }
            Opcode::StoreGName(b) => {
                let def = &self.mm.bindings[b];
                let (slot, name) = (def.slot, def.name);
                let fused = self.gname_fused.get(&name).copied();
                let gc_free = value_tags(&self.ty(d.args[1])).subset_of(GC_FREE_TAGS);
                self.binding_store(slot, a[1], gc_free, fused);
            }
            Opcode::LoadField(name) => self.field_op(inst, name, a[0], None)?,
            Opcode::LoadSlot(name) => {
                let t = self.ty(self.f.insts[inst].args[0]);
                let o = t.obj_info().ok_or("lowering: load_slot of a non-object")?;
                let slot = mir::ops::slot_of(o, name, self.mm).ok_or("lowering: load_slot without a proven slot")?;
                let v = self.load_i64(a[0], FIXED_SLOTS_BASE + 8 * slot);
                self.def(inst, v);
            }
            Opcode::StoreField(name) => self.field_op(inst, name, a[0], Some(a[1]))?,
            Opcode::StoreSlot(name) => {
                // `field_op`'s store with TYPES kept by type: RANGES dropped
                // (no MIR claim reads it), the barriers unless a number.
                let d = &self.f.insts[inst];
                let t = self.ty(d.args[0]);
                let num = matches!(self.ty(d.args[1]), MType::Val(s) if s.tags.subset_of(TagSet::NUMBER));
                let o = t.obj_info().ok_or("lowering: store_slot of a non-object")?;
                let slot = mir::ops::slot_of(o, name, self.mm).ok_or("lowering: store_slot without a proven slot")?;
                let off = FIXED_SLOTS_BASE + 8 * slot;
                let w = self.load_i32(a[0], OBJ_CLASS_IDX_OFFSET);
                self.clear_bits(a[0], w, CLASS_WORD_RANGES);
                if !num {
                    self.pre_barrier(a[0], off);
                }
                self.store_i64(a[0], off, a[1]);
                if !num {
                    let sv = self.i32c(slot);
                    self.post_barrier(self.h.post_write_barrier, a[0], sv, a[1]);
                }
            }
            Opcode::JsBoxThis => {
                // Allocates (a primitive's wrapper); runs no user code.
                let live = self.live_across(inst);
                let (ok, r) = self.gc_call(self.h.box_nonstrict_this, &[a[0]], &live)?;
                self.epoch_same = None;
                let t = self.edge(inst, 0, &[r])?;
                let e = self.edge(inst, 1, &[])?;
                self.cond_br(ok, t, e);
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
            Opcode::ConstStr(_) if self.lazy_strs.contains_key(&self.f.insts[inst].results[0]) => {}
            Opcode::ConstStr(name) => {
                // The atom itself, from the startup-filled atom table (a
                // pinned atom never moves):
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
        let Some(census) = self.exit_census.filter(|_| self.guard_exits(fail_blk).is_some()) else {
            self.cond_br(ok, t, f);
            return Ok(());
        };
        // `--mir-exit-census`: which guard failed (an exit's block is
        // shared by every guard at its pc).
        let counted = self.body.add_block();
        self.cond_br(ok, t, Self::to(counted));
        self.cur = counted;
        let id = self.census_guard(inst, fail_blk);
        let (k, i) = (self.i32c(crate::options::MIR_GUARD_CENSUS_KIND), self.i32c(id));
        self.call1(census, &[k, i], Type::I32);
        if let Some((w, idx, keys)) = self.guard_word {
            // A layout guard's miss, by the word: `id * 32 +` sentinel 16,
            // no identity 8, identity in range 4, TYPES 2, SLOTS 1.
            let bit = |l: &mut Self, v: Value, sh: u32| {
                let s = l.i32c(sh);
                l.bin(Operator::I32Shl, v, s, Type::I32)
            };
            let c31 = self.i32c(31);
            let sent = self.bin(Operator::I32ShrU, w, c31, Type::I32);
            let z = self.i32c(0);
            let none = self.bin(Operator::I32Eq, idx, z, Type::I32);
            let lo = self.i32c(keys.lo.get() + 1);
            let rel = self.bin(Operator::I32Sub, idx, lo, Type::I32);
            let span = self.i32c(keys.hi.get() - keys.lo.get());
            let inr = self.bin(Operator::I32LeU, rel, span, Type::I32);
            let tb = self.i32c(CLASS_WORD_SHALLOW);
            let ty = self.bin(Operator::I32And, w, tb, Type::I32);
            let ty = self.bin(Operator::I32Ne, ty, z, Type::I32);
            let sbit = self.i32c(CLASS_WORD_SLOTS);
            let sl = self.bin(Operator::I32And, w, sbit, Type::I32);
            let sl = self.bin(Operator::I32Ne, sl, z, Type::I32);
            let mut r = sl;
            for (v, sh) in [(ty, 1), (inr, 2), (none, 3), (sent, 4)] {
                let b = bit(self, v, sh);
                r = self.bin(Operator::I32Or, r, b, Type::I32);
            }
            let base = self.i32c(id * 32);
            let rid = self.bin(Operator::I32Add, base, r, Type::I32);
            let k = self.i32c(crate::options::MIR_GUARD_CENSUS_KIND + 1);
            self.call1(census, &[k, rid], Type::I32);
            // The object itself (the runtime's trace prints it).
            let obj = self.guard_obj.unwrap();
            let k = self.i32c(crate::options::MIR_GUARD_CENSUS_KIND + 4);
            self.call1(census, &[k, obj], Type::I32);
        }
        self.terminate(Terminator::Br { target: f });
        Ok(())
    }

    /// The pc of the exit (root or inline) guard failure block `b` ends in.
    fn guard_exits(&self, b: mir::Block) -> Option<Pc> {
        let t = self.f.terminator(b)?;
        match self.f.insts[t].op {
            Opcode::Exit { pc, .. } | Opcode::ExitThrow { pc, .. } | Opcode::ExitInline { pc, .. } => Some(pc),
            _ => None,
        }
    }

    /// The static record of a guard-failure census id: the guard, its
    /// operands' types, and the exit it takes.
    fn census_guard(&mut self, inst: mir::Inst, fail_blk: mir::Block) -> u32 {
        static NEXT: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
        let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let d = &self.f.insts[inst];
        let tys: Vec<String> = d.args.iter().map(|&a| format!("{:?}", self.ty(a))).collect();
        let pc = self.guard_exits(fail_blk).unwrap();
        let t = self.f.terminator(fail_blk).unwrap();
        let inl = matches!(self.f.insts[t].op, Opcode::ExitInline { .. });
        crate::diag_line!(
            "night: mir guard {id} sid#{} exit pc {pc}{} {} {:?} [{}]",
            self.f.script,
            if inl { " (inline)" } else { "" },
            mir::print::mnemonic(&d.op),
            d.op,
            tys.join(", ")
        );
        id
    }

    /// `a + b` of two strings, where both operands' types admit a string:
    /// `rope_concat`'s inline arms, then the quiet concat helper (it runs
    /// no user code and touches no stamp, so it takes `ok_clean`).
    fn concat_arm(&mut self, inst: mir::Inst, d: &mir::func::InstData, a: &[Value]) -> R<()> {
        let s = TagSet::prims(PRIM_STRING);
        if value_tags(&self.ty(d.args[0])).intersect(s).is_empty() || value_tags(&self.ty(d.args[1])).intersect(s).is_empty() {
            return Ok(());
        }
        let (x, y) = (a[0], a[1]);
        let tx = self.tag_of(x);
        let sx = self.tag_is(tx, TAG_STRING as u32);
        let ty = self.tag_of(y);
        let sy = self.tag_is(ty, TAG_STRING as u32);
        let both = self.bin(Operator::I32And, sx, sy, Type::I32);
        let (cat, other) = (self.body.add_block(), self.body.add_block());
        self.cond_br(both, Self::to(cat), Self::to(other));
        self.cur = cat;
        let helper = self.body.add_block();
        self.rope_concat(inst, x, y, helper)?;
        self.cur = helper;
        // The helper's reload rebinds the live values on its path only.
        let saved = (self.vmap.clone(), self.slotted.clone(), self.dirty.clone(), self.framed.clone(), self.cold);
        let live = self.live_across(inst);
        let (ok, r) = self.gc_call(self.h.concat, &[x, y], &live)?;
        let t = self.edge(inst, 0, &[r])?;
        let e = self.edge(inst, 2, &[])?;
        self.cond_br(ok, t, e);
        (self.vmap, self.slotted, self.dirty, self.framed, self.cold) = saved;
        self.epoch_same = None;
        self.cur = other;
        Ok(())
    }

    /// A for-in's start inline, taking edge 0, as the JIT's
    /// `ObjectToIterator` (`maybeLoadIteratorFromShape`, `registerIterator`):
    /// for an object whose shape caches an iterator that no for-in is using,
    /// with no dense elements on it or its prototypes, and whose prototypes'
    /// shapes are the ones the iterator recorded, that iterator, holding the
    /// object, marked active and joined to the compartment's list of active
    /// ones. The object is stored raw: a nursery one gets the whole-cell
    /// barrier on the (tenured) iterator object. Anything else falls through
    /// to the helper, which also fills the shape's cache.
    fn iter_from_shape(&mut self, inst: mir::Inst, v: Value) -> R<()> {
        use crate::wasm::mir::abi::{
            ITER_SLOT_OFFSET, NI_COUNT_OFFSET, NI_FIRST_PROPERTY_OFFSET, NI_FLAGS_OFFSET, NI_FLAG_ACTIVE,
            NI_FLAG_INDICES_ALLOCATED, NI_FLAG_INITIALIZED, NI_INDEX_BYTES, NI_NEXT_OFFSET, NI_OBJECT_OFFSET,
            NI_PREV_OFFSET, NI_PROTO_SHAPE_BYTES, SHAPE_CACHE_ITERATOR, SHAPE_CACHE_OFFSET, SHAPE_CACHE_TAG_MASK,
        };
        let miss = self.body.add_block();
        let tag = self.tag_of(v);
        let is_obj = self.tag_is(tag, TAG_OBJECT as u32);
        self.check(is_obj, miss);
        let obj = self.un(Operator::I32WrapI64, v, Type::I32);
        let shape = self.load_i32(obj, SHAPE_OFFSET);
        let cache = self.load_i32(shape, SHAPE_CACHE_OFFSET);
        let mask = self.i32c(SHAPE_CACHE_TAG_MASK);
        let kind = self.bin(Operator::I32And, cache, mask, Type::I32);
        let it = self.i32c(SHAPE_CACHE_ITERATOR);
        let is_iter = self.bin(Operator::I32Eq, kind, it, Type::I32);
        self.check(is_iter, miss);
        // No dense elements (the iterator lists only named properties).
        let no_elems = |l: &mut Self, o: Value| {
            let elements = l.load_i32(o, OBJ_ELEMENTS_OFFSET);
            let back = l.i32c(ELEMENTS_INITLEN_BACK);
            let header = l.bin(Operator::I32Sub, elements, back, Type::I32);
            let initlen = l.load_i32(header, 0);
            l.un(Operator::I32Eqz, initlen, Type::I32)
        };
        let ok = no_elems(self, obj);
        self.check(ok, miss);
        let notag = self.i32c(!SHAPE_CACHE_TAG_MASK);
        let iter = self.bin(Operator::I32And, cache, notag, Type::I32);
        let ni = self.load_i32(iter, ITER_SLOT_OFFSET);
        // Reusable: initialized and not active.
        let m8 = self.mem(0, NI_FLAGS_OFFSET);
        let flags = self.un(Operator::I32Load8U { memory: m8 }, ni, Type::I32);
        let ia = self.i32c(NI_FLAG_INITIALIZED | NI_FLAG_ACTIVE);
        let state = self.bin(Operator::I32And, flags, ia, Type::I32);
        let init = self.i32c(NI_FLAG_INITIALIZED);
        let reusable = self.bin(Operator::I32Eq, state, init, Type::I32);
        self.check(reusable, miss);
        // The recorded prototype shapes: after the properties, and their
        // indices if allocated.
        let count = self.load_i32(ni, NI_COUNT_OFFSET);
        let pb = self.i32c(4);
        let props = self.bin(Operator::I32Mul, count, pb, Type::I32);
        let ib = self.i32c(NI_INDEX_BYTES);
        let idx_bytes = self.bin(Operator::I32Mul, count, ib, Type::I32);
        let ab = self.i32c(NI_FLAG_INDICES_ALLOCATED);
        let has_idx = self.bin(Operator::I32And, flags, ab, Type::I32);
        let zero = self.i32c(0);
        let idx_bytes = self.select(Type::I32, idx_bytes, zero, has_idx);
        let skip = self.bin(Operator::I32Add, props, idx_bytes, Type::I32);
        let first = self.i32c(NI_FIRST_PROPERTY_OFFSET);
        let base = self.bin(Operator::I32Add, ni, first, Type::I32);
        let shapes = self.bin(Operator::I32Add, base, skip, Type::I32);
        // Each prototype: no dense elements and the recorded shape; a
        // matched shape fixes the next prototype, so the walk ends where
        // the recording does.
        let (walk, hit) = (self.body.add_block(), self.body.add_block());
        let cur_shape = self.body.add_blockparam(walk, Type::I32);
        let cur_rec = self.body.add_blockparam(walk, Type::I32);
        self.terminate(Terminator::Br { target: BlockTarget { block: walk, args: vec![shape, shapes] } });
        self.cur = walk;
        let bs = self.load_i32(cur_shape, SHAPE_BASESHAPE_OFFSET);
        let proto = self.load_i32(bs, BASESHAPE_PROTO_OFFSET);
        let more = self.body.add_block();
        self.cond_br(proto, Self::to(more), Self::to(hit));
        self.cur = more;
        let ok = no_elems(self, proto);
        self.check(ok, miss);
        let pshape = self.load_i32(proto, SHAPE_OFFSET);
        let want = self.load_i32(cur_rec, 0);
        let same = self.bin(Operator::I32Eq, pshape, want, Type::I32);
        self.check(same, miss);
        let step = self.i32c(NI_PROTO_SHAPE_BYTES);
        let next_rec = self.bin(Operator::I32Add, cur_rec, step, Type::I32);
        self.terminate(Terminator::Br { target: BlockTarget { block: walk, args: vec![pshape, next_rec] } });
        self.cur = hit;
        // Start it on this object.
        self.store_i32(ni, NI_OBJECT_OFFSET, obj);
        let act = self.i32c(NI_FLAG_ACTIVE);
        let nf = self.bin(Operator::I32Or, flags, act, Type::I32);
        let ms = self.mem(0, NI_FLAGS_OFFSET);
        self.op(Operator::I32Store8 { memory: ms }, &[ni, nf], None);
        let la = self.i32c(self.h.strlit_slot + crate::region_shape::STRLIT_ENUMERATORS_OFF);
        let list = self.load_i32(la, 0);
        self.store_i32(ni, NI_NEXT_OFFSET, list);
        let last = self.load_i32(list, NI_PREV_OFFSET);
        self.store_i32(ni, NI_PREV_OFFSET, last);
        self.store_i32(last, NI_NEXT_OFFSET, ni);
        self.store_i32(list, NI_PREV_OFFSET, ni);
        // The object in the nursery: the iterator object's whole-cell
        // barrier.
        let cmask = self.i32c(NOT_CHUNK_MASK);
        let chunk = self.bin(Operator::I32And, obj, cmask, Type::I32);
        let sb = self.load_i32(chunk, CHUNK_STORE_BUFFER_OFFSET);
        let (record, done) = (self.body.add_block(), self.body.add_block());
        self.cond_br(sb, Self::to(record), Self::to(done));
        self.cur = record;
        self.call(self.h.post_whole_cell, &[self.cx, iter], &[]);
        self.terminate(Terminator::Br { target: Self::to(done) });
        self.cur = done;
        let r = self.box_tagged(TAG_OBJECT, iter);
        let t = self.edge(inst, 0, &[r])?;
        self.terminate(Terminator::Br { target: t });
        self.cur = miss;
        Ok(())
    }

    /// A for-in iterator's next key, inline as the JIT's `iteratorMore`:
    /// the property at the cursor, advancing it past deleted ones, or the
    /// no-more magic.
    fn iter_more(&mut self, iter: Value) -> Value {
        use crate::wasm::mir::abi::{ITER_SLOT_OFFSET, NI_COUNT_OFFSET, NI_CURSOR_OFFSET, NI_DELETED_BIT, NI_FIRST_PROPERTY_OFFSET};
        let obj = self.un(Operator::I32WrapI64, iter, Type::I32);
        let ni = self.load_i32(obj, ITER_SLOT_OFFSET);
        let (lp, more, done) = (self.body.add_block(), self.body.add_block(), self.body.add_block());
        let r = self.body.add_blockparam(done, Type::I64);
        self.terminate(Terminator::Br { target: Self::to(lp) });
        self.cur = lp;
        let cur = self.load_i32(ni, NI_CURSOR_OFFSET);
        let cnt = self.load_i32(ni, NI_COUNT_OFFSET);
        let left = self.bin(Operator::I32LtU, cur, cnt, Type::I32);
        let none = self.i64c((TAG_MAGIC << 32) | crate::wasm::translate::MAGIC_NO_ITER_VALUE);
        self.cond_br(left, Self::to(more), BlockTarget { block: done, args: vec![none] });
        self.cur = more;
        let two = self.i32c(2);
        let off = self.bin(Operator::I32Shl, cur, two, Type::I32);
        let at = self.bin(Operator::I32Add, ni, off, Type::I32);
        let p = self.load_i32(at, NI_FIRST_PROPERTY_OFFSET);
        let one = self.i32c(1);
        let next = self.bin(Operator::I32Add, cur, one, Type::I32);
        self.store_i32(ni, NI_CURSOR_OFFSET, next);
        let db = self.i32c(NI_DELETED_BIT);
        let deleted = self.bin(Operator::I32And, p, db, Type::I32);
        let key = self.box_tagged(TAG_STRING, p);
        self.cond_br(deleted, Self::to(lp), BlockTarget { block: done, args: vec![key] });
        self.cur = done;
        r
    }

    /// A for-in iterator's close, inline as the JIT's `iteratorClose`:
    /// clear the iterated object, reset the cursor, clear the active bit
    /// and unlink it from the active list. The shared empty iterator is
    /// left alone. Incremental marking (the cleared object pointer owes a
    /// pre-barrier) and properties deleted unvisited (whose marks the
    /// close clears) take the helper.
    fn iter_end(&mut self, iter: Value) {
        use crate::wasm::mir::abi::{
            ITER_SLOT_OFFSET, NI_CURSOR_OFFSET, NI_FLAGS_OFFSET, NI_FLAG_ACTIVE, NI_FLAG_EMPTY_SINGLETON,
            NI_FLAG_UNVISITED_DELETION, NI_NEXT_OFFSET, NI_OBJECT_OFFSET, NI_PREV_OFFSET,
        };
        let obj = self.un(Operator::I32WrapI64, iter, Type::I32);
        let ni = self.load_i32(obj, ITER_SLOT_OFFSET);
        let m8 = self.mem(0, NI_FLAGS_OFFSET);
        let flags = self.un(Operator::I32Load8U { memory: m8 }, ni, Type::I32);
        let (helper, inline, done) = (self.body.add_block(), self.body.add_block(), self.body.add_block());
        let es = self.i32c(NI_FLAG_EMPTY_SINGLETON);
        let empty = self.bin(Operator::I32And, flags, es, Type::I32);
        let go = self.body.add_block();
        self.cond_br(empty, Self::to(done), Self::to(go));
        self.cur = go;
        let ud = self.i32c(NI_FLAG_UNVISITED_DELETION);
        let deletions = self.bin(Operator::I32And, flags, ud, Type::I32);
        let zone = self.load_i32(self.cx, JSCONTEXT_ZONE_OFFSET);
        let marking = self.load_i32(zone, ZONE_NEEDS_BARRIER_OFFSET);
        let slow = self.bin(Operator::I32Or, deletions, marking, Type::I32);
        self.cond_br(slow, Self::to(helper), Self::to(inline));
        self.cur = helper;
        let boxed = self.box_tagged(TAG_OBJECT, obj);
        self.call(self.h.end_iter, &[self.cx, boxed], &[]);
        self.terminate(Terminator::Br { target: Self::to(done) });
        self.cur = inline;
        let z = self.i32c(0);
        self.store_i32(ni, NI_OBJECT_OFFSET, z);
        self.store_i32(ni, NI_CURSOR_OFFSET, z);
        let keep = self.i32c(!NI_FLAG_ACTIVE & 0xFF);
        let nf = self.bin(Operator::I32And, flags, keep, Type::I32);
        let ms = self.mem(0, NI_FLAGS_OFFSET);
        self.op(Operator::I32Store8 { memory: ms }, &[ni, nf], None);
        let next = self.load_i32(ni, NI_NEXT_OFFSET);
        let prev = self.load_i32(ni, NI_PREV_OFFSET);
        self.store_i32(next, NI_PREV_OFFSET, prev);
        self.store_i32(prev, NI_NEXT_OFFSET, next);
        self.terminate(Terminator::Br { target: Self::to(done) });
        self.cur = done;
    }

    /// `Object.hasOwn(obj, key)` for an object and a string key inline,
    /// taking edge 0: the runtime's has-own row for (the object's shape,
    /// the key's atom), whose slotEnc is the answer (`HasOwnRow`). A key
    /// that is not an atom matches no row; a miss takes the helper, which
    /// fills the row.
    fn has_own_arm(&mut self, inst: mir::Inst, key: Value, obj: Value) -> R<()> {
        use crate::wasm::translate::{MEGA_GET_ENTRY_BYTES, MEGA_GET_SIZE};
        let (kt, ot) = (self.tag_of(key), self.tag_of(obj));
        let ks = self.tag_is(kt, TAG_STRING as u32);
        let oo = self.tag_is(ot, TAG_OBJECT as u32);
        let both = self.bin(Operator::I32And, ks, oo, Type::I32);
        let (probe, miss) = (self.body.add_block(), self.body.add_block());
        self.cond_br(both, Self::to(probe), Self::to(miss));
        self.cur = probe;
        let kp = self.un(Operator::I32WrapI64, key, Type::I32);
        let two = self.i32c(2);
        let ekey = self.bin(Operator::I32Or, kp, two, Type::I32);
        let op = self.un(Operator::I32WrapI64, obj, Type::I32);
        let shape = self.load_i32(op, SHAPE_OFFSET);
        // NightRuntime.cpp's CacheHash.
        let three = self.i32c(3);
        let sh = self.bin(Operator::I32ShrU, shape, three, Type::I32);
        let k1 = self.i32c(2654435761);
        let h1 = self.bin(Operator::I32Mul, sh, k1, Type::I32);
        let k2c = self.i32c(0x9e37_79b9);
        let k2 = self.bin(Operator::I32Mul, ekey, k2c, Type::I32);
        let hh = self.bin(Operator::I32Xor, h1, k2, Type::I32);
        let mask = self.i32c(MEGA_GET_SIZE - 1);
        let idx = self.bin(Operator::I32And, hh, mask, Type::I32);
        let stride = self.i32c(MEGA_GET_ENTRY_BYTES);
        let off = self.bin(Operator::I32Mul, idx, stride, Type::I32);
        let base = self.i32c(self.h.mega_get_base);
        let row = self.bin(Operator::I32Add, base, off, Type::I32);
        let rshape = self.load_i32(row, 0);
        let rkey = self.load_i32(row, 4);
        let ms = self.bin(Operator::I32Eq, rshape, shape, Type::I32);
        let mk = self.bin(Operator::I32Eq, rkey, ekey, Type::I32);
        let hit = self.bin(Operator::I32And, ms, mk, Type::I32);
        let hit_b = self.body.add_block();
        self.cond_br(hit, Self::to(hit_b), Self::to(miss));
        self.cur = hit_b;
        let own = self.load_i32(row, 16);
        let own = self.un(Operator::I64ExtendI32U, own, Type::I64);
        let tag = self.i64c(TAG_BOOLEAN << 32);
        let r = self.bin(Operator::I64Or, own, tag, Type::I64);
        let t = self.edge(inst, 0, &[r])?;
        self.terminate(Terminator::Br { target: t });
        self.cur = miss;
        Ok(())
    }

    /// `typeof x == T` (`!=` with bit 7 of `k`) inline. The tag decides
    /// every type but an object's, and a primitive type is decided by it
    /// alone. An object's class decides the rest: the function classes are
    /// "function"; a class without a call hook that is neither a proxy nor
    /// emulates undefined is "object". Any other object asks the helper (a
    /// leaf: no GC, no JS).
    fn typeof_eq(&mut self, x: Value, k: u8) -> Value {
        const JSTYPE_UNDEFINED: u8 = 0;
        const JSTYPE_OBJECT: u8 = 1;
        const JSTYPE_FUNCTION: u8 = 2;
        let (ty, neg) = (k & 0x7f, k & 0x80 != 0);
        let prims = match ty {
            JSTYPE_UNDEFINED => PRIM_UNDEFINED,
            JSTYPE_OBJECT => PRIM_NULL,
            JSTYPE_FUNCTION => Prims::EMPTY,
            3 => PRIM_STRING,
            4 => PRIM_INT32 | PRIM_DOUBLE,
            5 => PRIM_BOOLEAN,
            6 => PRIM_SYMBOL,
            _ => PRIM_BIGINT,
        };
        let negate = |l: &mut Self, v: Value| if neg { l.un(Operator::I32Eqz, v, Type::I32) } else { v };
        let prim = self.has_tags(x, TagSet::prims(prims));
        if !matches!(ty, JSTYPE_UNDEFINED | JSTYPE_OBJECT | JSTYPE_FUNCTION) {
            return negate(self, prim);
        }
        let join = self.body.add_block();
        let r = self.body.add_blockparam(join, Type::I32);
        let (obj_b, prim_b) = (self.body.add_block(), self.body.add_block());
        let tag = self.tag_of(x);
        let is_obj = self.tag_is(tag, TAG_OBJECT as u32);
        self.cond_br(is_obj, Self::to(obj_b), Self::to(prim_b));
        self.cur = prim_b;
        let pv = negate(self, prim);
        self.terminate(Terminator::Br { target: BlockTarget { block: join, args: vec![pv] } });
        self.cur = obj_b;
        let obj = self.un(Operator::I32WrapI64, x, Type::I32);
        let shape = self.load_i32(obj, SHAPE_OFFSET);
        let base = self.load_i32(shape, SHAPE_BASESHAPE_OFFSET);
        let clasp = self.load_i32(base, BASESHAPE_CLASP_OFFSET);
        let slot = self.i32c(self.h.fn_class_slot);
        let fn_class = self.load_i32(slot, 0);
        let ext_class = self.load_i32(slot, 4);
        let is_fn = self.bin(Operator::I32Eq, clasp, fn_class, Type::I32);
        let is_ext = self.bin(Operator::I32Eq, clasp, ext_class, Type::I32);
        let is_fn = self.bin(Operator::I32Or, is_fn, is_ext, Type::I32);
        let (fun_b, other_b, helper_b) = (self.body.add_block(), self.body.add_block(), self.body.add_block());
        self.cond_br(is_fn, Self::to(fun_b), Self::to(other_b));
        self.cur = fun_b;
        let fv = self.i32c(u32::from((ty == JSTYPE_FUNCTION) != neg));
        self.terminate(Terminator::Br { target: BlockTarget { block: join, args: vec![fv] } });
        self.cur = other_b;
        let flags = self.load_i32(clasp, JSCLASS_FLAGS_OFFSET);
        let odd = self.i32c(JSCLASS_IS_PROXY | JSCLASS_EMULATES_UNDEFINED);
        let odd = self.bin(Operator::I32And, flags, odd, Type::I32);
        let plain = self.un(Operator::I32Eqz, odd, Type::I32);
        self.check(plain, helper_b);
        let cops = self.load_i32(clasp, JSCLASS_COPS_OFFSET);
        let (ops_b, obj_t) = (self.body.add_block(), self.body.add_block());
        self.cond_br(cops, Self::to(ops_b), Self::to(obj_t));
        self.cur = ops_b;
        let call = self.load_i32(cops, JSCLASSOPS_CALL_OFFSET);
        let uncallable = self.un(Operator::I32Eqz, call, Type::I32);
        self.cond_br(uncallable, Self::to(obj_t), Self::to(helper_b));
        self.cur = obj_t;
        let ov = self.i32c(u32::from((ty == JSTYPE_OBJECT) != neg));
        self.terminate(Terminator::Br { target: BlockTarget { block: join, args: vec![ov] } });
        self.cur = helper_b;
        let kv = self.i32c(u32::from(k));
        let hv = self.call1(self.h.typeof_eq, &[self.cx, x, kv], Type::I32);
        self.terminate(Terminator::Br { target: BlockTarget { block: join, args: vec![hv] } });
        self.cur = join;
        r
    }

    /// The concat of strings `x` and `y` inline, as the JIT's concat stub
    /// does, taking edge 0: either half when the other is empty, else a
    /// nursery rope over the two. A result short enough to be an inline
    /// string (which the engine flattens rather than ropes), one past the
    /// maximum length, a zone that does not allocate strings in the nursery
    /// (the runtime's header word is 0) and a full nursery take `helper`.
    /// No GC, no user code: nothing live needs rooting.
    fn rope_concat(&mut self, inst: mir::Inst, x: Value, y: Value, helper: Block) -> R<()> {
        let (xp, yp) = (self.un(Operator::I32WrapI64, x, Type::I32), self.un(Operator::I32WrapI64, y, Type::I32));
        let z = self.i32c(0);
        let lx = self.load_i32(xp, STRING_LENGTH_OFFSET);
        let ly = self.load_i32(yp, STRING_LENGTH_OFFSET);
        for (len, other) in [(lx, y), (ly, x)] {
            let empty = self.bin(Operator::I32Eq, len, z, Type::I32);
            let (take, next) = (self.body.add_block(), self.body.add_block());
            self.cond_br(empty, Self::to(take), Self::to(next));
            self.cur = take;
            let t = self.edge(inst, 0, &[other])?;
            self.terminate(Terminator::Br { target: t });
            self.cur = next;
        }
        let total = self.bin(Operator::I32Add, lx, ly, Type::I32);
        let fx = self.load_i32(xp, STRING_FLAGS_OFFSET);
        let fy = self.load_i32(yp, STRING_FLAGS_OFFSET);
        let both = self.bin(Operator::I32And, fx, fy, Type::I32);
        let l1 = self.i32c(STRING_LATIN1_CHARS_BIT);
        let flags = self.bin(Operator::I32And, both, l1, Type::I32);
        let (fl, ft) = (self.i32c(FAT_INLINE_MAX_LATIN1), self.i32c(FAT_INLINE_MAX_TWO_BYTE));
        let inline_max = self.select(Type::I32, fl, ft, flags);
        let roped = self.bin(Operator::I32GtU, total, inline_max, Type::I32);
        self.check(roped, helper);
        let max = self.i32c(STRING_MAX_LENGTH);
        let fits = self.bin(Operator::I32LeU, total, max, Type::I32);
        self.check(fits, helper);
        let hslot = self.i32c(self.h.strlit_slot + crate::region_shape::STRLIT_STR_HEADER_OFF);
        let hdr = self.load_i32(hslot, 0);
        let armed = self.bin(Operator::I32Ne, hdr, z, Type::I32);
        self.check(armed, helper);
        let size = self.i32c(NURSERY_HEADER_BYTES + ROPE_BYTES);
        let pos = self.nursery_bump(size, helper);
        self.store_i32(pos, 0, hdr);
        // The catch-all site's count, as the engine's allocation bumps it.
        let cslot = self.i32c(self.h.strlit_slot + crate::region_shape::STRLIT_STR_COUNT_ADDR_OFF);
        let caddr = self.load_i32(cslot, 0);
        let n = self.load_i32(caddr, 0);
        let one = self.i32c(1);
        let n1 = self.bin(Operator::I32Add, n, one, Type::I32);
        self.store_i32(caddr, 0, n1);
        let hb = self.i32c(NURSERY_HEADER_BYTES);
        let s = self.bin(Operator::I32Add, pos, hb, Type::I32);
        self.store_i32(s, STRING_FLAGS_OFFSET, flags);
        self.store_i32(s, STRING_LENGTH_OFFSET, total);
        self.store_i32(s, ROPE_LEFT_OFFSET, xp);
        self.store_i32(s, ROPE_RIGHT_OFFSET, yp);
        let payload = self.un(Operator::I64ExtendI32U, s, Type::I64);
        let tag = self.i64c(TAG_STRING << 32);
        let r = self.bin(Operator::I64Or, payload, tag, Type::I64);
        let t = self.edge(inst, 0, &[r])?;
        self.terminate(Terminator::Br { target: t });
        Ok(())
    }

    /// A generic JS op through its helper (`ok_clean`, `ok_dirty`, `err`).
    /// With no dynamic effect report yet, success takes `ok_dirty`, which
    /// is always sound.
    fn js_op(&mut self, inst: mir::Inst, op: &Opcode, a: &[Value]) -> R<()> {
        if let Opcode::JsCompare(cc) = *op {
            self.equality_arms(inst, cc, a)?;
        }
        let (f, args, bool_out) = self.op_helper(op, a);
        self.js_call(inst, f, &args, bool_out)
    }

    /// An equality's inline arms (against a string literal, then the
    /// tag ladder), taking edge 0.
    fn equality_arms(&mut self, inst: mir::Inst, cc: JsCc, a: &[Value]) -> R<()> {
        if matches!(cc, JsCc::Eq | JsCc::Ne | JsCc::StrictEq | JsCc::StrictNe) {
            // Against a string literal (an atom): `literal_eq`'s ladder.
            let args = self.f.insts[inst].args.clone();
            if self.is_str_literal(args[1]) {
                self.literal_eq(inst, cc, a[0], a[1])?;
            } else if self.is_str_literal(args[0]) {
                self.literal_eq(inst, cc, a[1], a[0])?;
            }
            self.equality_fast_arm(inst, cc, a[0], a[1])?;
        }
        Ok(())
    }

    /// The runtime helper of a generic numeric op or compare, its
    /// arguments, and whether its result is a bool.
    fn op_helper(&mut self, op: &Opcode, a: &[Value]) -> (Func, Vec<Value>, bool) {
        let h = self.h;
        match *op {
            Opcode::JsAdd => (h.add, vec![a[0], a[1]], false),
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
                    JsBinop::Pow => return (h.pow, vec![a[0], a[1]], false),
                };
                let k = self.i32c(kind);
                (h.binop, vec![k, a[0], a[1]], false)
            }
            Opcode::JsUnop(u) => match u {
                JsUnop::Neg => (h.neg, vec![a[0]], false),
                JsUnop::Pos => (h.pos, vec![a[0]], false),
                JsUnop::BitNot | JsUnop::Inc | JsUnop::Dec => {
                    let kind = match u {
                        JsUnop::BitNot => BINOP_BITNOT,
                        JsUnop::Inc => BINOP_INC,
                        _ => BINOP_DEC,
                    };
                    let k = self.i32c(kind);
                    (h.binop, vec![k, a[0], a[0]], false)
                }
            },
            Opcode::JsCompare(cc) => {
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
                (h.compare, vec![k, a[0], a[1]], true)
            }
            Opcode::JsToNumeric => (h.tonumeric, vec![a[0]], false),
            _ => unreachable!(),
        }
    }

    /// `prim.*` (`Opcode::Prim`): the generic op's inline arms taking
    /// `ok`; then `fail` where an operand's conversion would call user
    /// code (an object whose ToPrimitive is not Object.prototype's own,
    /// unless an equality compares it with an object, null or undefined;
    /// never in a strict one); then its helper, which runs no user code on
    /// such operands: `ok` with the result, or `err` for the op's own
    /// TypeError or RangeError.
    fn prim_op(&mut self, inst: mir::Inst, p: crate::mir::ops::PrimOp, a: &[Value]) -> R<()> {
        use crate::mir::ops::PrimOp;
        let g = p.generic();
        self.numeric_fast_arms(inst, &g, a)?;
        if p == PrimOp::Add {
            let d = self.f.insts[inst].clone();
            self.concat_arm(inst, &d, a)?;
        }
        if let PrimOp::Compare(cc) = p {
            self.equality_arms(inst, cc, a)?;
        }
        let is_obj = |l: &mut Self, v: Value| {
            let t = l.tag_of(v);
            l.tag_is(t, TAG_OBJECT as u32)
        };
        let user = match p {
            PrimOp::Compare(JsCc::StrictEq | JsCc::StrictNe) => None,
            PrimOp::Compare(JsCc::Eq | JsCc::Ne) => {
                // Converted only against a primitive other than null or
                // undefined.
                let (oa, ob) = (is_obj(self, a[0]), is_obj(self, a[1]));
                let one = self.bin(Operator::I32Xor, oa, ob, Type::I32);
                let nullish = |l: &mut Self, v: Value| {
                    let t = l.tag_of(v);
                    let u = l.tag_is(t, TAG_UNDEFINED as u32);
                    let n = l.tag_is(t, TAG_NULL as u32);
                    l.bin(Operator::I32Or, u, n, Type::I32)
                };
                let (na, nb) = (nullish(self, a[0]), nullish(self, a[1]));
                let either = self.bin(Operator::I32Or, na, nb, Type::I32);
                let neither = self.un(Operator::I32Eqz, either, Type::I32);
                let conv = self.bin(Operator::I32And, one, neither, Type::I32);
                let (ua, ub) = (self.converts_user(a[0]), self.converts_user(a[1]));
                let u = self.bin(Operator::I32Or, ua, ub, Type::I32);
                Some(self.bin(Operator::I32And, conv, u, Type::I32))
            }
            PrimOp::Unop(_) | PrimOp::ToNumeric => Some(self.converts_user(a[0])),
            _ => {
                let (ua, ub) = (self.converts_user(a[0]), self.converts_user(a[1]));
                Some(self.bin(Operator::I32Or, ua, ub, Type::I32))
            }
        };
        if let Some(user) = user {
            let fail = self.edge(inst, 1, &[])?;
            let go = self.body.add_block();
            self.cond_br(user, fail, Self::to(go));
            self.cur = go;
        }
        let (f, args, bool_out) = self.op_helper(&g, a);
        self.slow_census(inst);
        let live = self.live_across(inst);
        let (ok, result) = self.gc_call(f, &args, &live)?;
        self.epoch_same = None;
        let out = if bool_out {
            self.un(Operator::I32WrapI64, result, Type::I32)
        } else {
            result
        };
        let t = self.edge(inst, 0, &[out])?;
        let e = self.edge(inst, 2, &[])?;
        self.cond_br(ok, t, e);
        Ok(())
    }

    /// The inline arms of a read of syntactic global binding `bid`, each
    /// taking the op's `ok` edge:
    /// the binding's value-fuse cell while armed; else its cached slot row
    /// while the global's shape is the one the row was resolved against;
    /// else the resolve leaf (no GC) and the slot. Falls through to the
    /// generic helper when the binding is not cacheable (lexicals, TDZ).
    /// `check.binding` (§3): binding row `slot` resolved against the
    /// global object's live shape (writable too, for `write`), re-resolved
    /// by the leaf when it is not. The row then says where the slot is.
    fn binding_ok(&mut self, slot: u32, write: bool) -> Value {
        let base = self.i32c(self.h.global_slots_base);
        let entry0 = self.load_i32(base, 8 * slot);
        let shape0 = self.load_i32(base, 8 * slot + 4);
        // Resolved (bit 0), and for a write writable (bit 2).
        let usable = |l: &mut Self, e: Value| {
            let m = l.i32c(if write { 5 } else { 1 });
            let r = l.bin(Operator::I32And, e, m, Type::I32);
            if !write {
                return r;
            }
            l.bin(Operator::I32Eq, r, m, Type::I32)
        };
        let u0 = usable(self, entry0);
        let realm = self.load_i32(self.cx, JSCONTEXT_REALM_OFFSET);
        let global = self.load_i32(realm, REALM_GLOBAL_OFFSET);
        let live = self.load_i32(global, SHAPE_OFFSET);
        let same = self.bin(Operator::I32Eq, shape0, live, Type::I32);
        let hit = self.bin(Operator::I32And, u0, same, Type::I32);
        let join = self.body.add_block();
        let ok = self.body.add_blockparam(join, Type::I32);
        let resolve_b = self.body.add_block();
        self.cond_br(hit, BlockTarget { block: join, args: vec![hit] }, Self::to(resolve_b));
        self.cur = resolve_b;
        let b = self.i32c(slot);
        let entry1 = self.call1(self.h.resolve_global_slot_guarded, &[self.cx, b], Type::I32);
        let u1 = usable(self, entry1);
        self.terminate(Terminator::Br {
            target: BlockTarget { block: join, args: vec![u1] },
        });
        self.cur = join;
        ok
    }

    /// The address of binding row `slot`'s global slot, the row resolved
    /// (bit 1 of the entry selects the dynamic slots; `entry & !7` is the
    /// byte offset from that base, past the fixed-slot header when fixed).
    fn binding_addr(&mut self, slot: u32) -> Value {
        self.binding_slot(slot).0
    }

    /// Binding row `slot`'s global slot, the binding checked: its address,
    /// the global object, the row's entry and whether the slot is dynamic
    /// (`binding_addr`). A major GC since the check zeroes the row (its
    /// shape word may dangle): resolved again first, to the same slot (the
    /// check's binding is a data property that cannot move).
    fn binding_slot(&mut self, slot: u32) -> (Value, Value, Value, Value) {
        let base = self.i32c(self.h.global_slots_base);
        let entry0 = self.load_i32(base, 8 * slot);
        let one = self.i32c(1);
        let resolved = self.bin(Operator::I32And, entry0, one, Type::I32);
        let (resolve_b, join) = (self.body.add_block(), self.body.add_block());
        let entry = self.body.add_blockparam(join, Type::I32);
        self.cond_br(resolved, BlockTarget { block: join, args: vec![entry0] }, Self::to(resolve_b));
        self.cur = resolve_b;
        let bv = self.i32c(slot);
        let entry1 = self.call1(self.h.resolve_global_slot_guarded, &[self.cx, bv], Type::I32);
        self.terminate(Terminator::Br {
            target: BlockTarget { block: join, args: vec![entry1] },
        });
        self.cur = join;
        let realm = self.load_i32(self.cx, JSCONTEXT_REALM_OFFSET);
        let global = self.load_i32(realm, REALM_GLOBAL_OFFSET);
        let one = self.i32c(1);
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
        (addr, global, entry, dynamic)
    }

    /// `store_gname` (§3): the resolved, writable slot of binding row
    /// `slot` takes `val`, with the barriers and the binding's value fuse
    /// as the syntactic global store keeps them, and a
    /// fused literal's fuse (`gname_set_arms`' tail). `gc_free`: the value
    /// is no GC thing, by its type.
    fn binding_store(&mut self, slot: u32, val: Value, gc_free: bool, fused: Option<crate::wasm::translate::FusedGname>) {
        let (addr, global, entry, dynamic) = self.binding_slot(slot);
        self.pre_barrier(addr, 0);
        self.store_i64(addr, 0, val);
        if !gc_free {
            // The generational post-barrier: the global object is tenured,
            // so a nursery GC thing is recorded, by the slot's index (its
            // shape's fixed slots first), which only that path computes.
            let cont = self.body.add_block();
            let tag = self.tag_of(val);
            let min = self.i32c(VAL_GCTHING_TAG_MIN);
            let is_gc = self.bin(Operator::I32GeU, tag, min, Type::I32);
            let gc = self.body.add_block();
            self.cond_br(is_gc, Self::to(gc), Self::to(cont));
            self.cur = gc;
            let mask = self.i32c(NOT_CHUNK_MASK);
            let cell = self.un(Operator::I32WrapI64, val, Type::I32);
            let chunk = self.bin(Operator::I32And, cell, mask, Type::I32);
            let sb = self.load_i32(chunk, CHUNK_STORE_BUFFER_OFFSET);
            let record = self.body.add_block();
            self.cond_br(sb, Self::to(record), Self::to(cont));
            self.cur = record;
            let three = self.i32c(3);
            let idx = self.bin(Operator::I32ShrU, entry, three, Type::I32);
            let live = self.load_i32(global, SHAPE_OFFSET);
            let flags = self.load_i32(live, SHAPE_IMMUTABLE_FLAGS_OFFSET);
            let fs = self.i32c(SHAPE_FIXED_SLOTS_SHIFT);
            let nf = self.bin(Operator::I32ShrU, flags, fs, Type::I32);
            let fm = self.i32c(SHAPE_FIXED_SLOTS_MASK_BITS);
            let nfixed = self.bin(Operator::I32And, nf, fm, Type::I32);
            let idx_plus = self.bin(Operator::I32Add, idx, nfixed, Type::I32);
            let abs = self.select(Type::I32, idx_plus, idx, dynamic);
            let owner = self.box_tagged(TAG_OBJECT, global);
            self.call(self.h.post_write_barrier, &[owner, abs, val], &[]);
            self.terminate(Terminator::Br { target: Self::to(cont) });
            self.cur = cont;
        }
        self.binding_fuses(slot, val, gc_free, fused);
    }

    /// A syntactic global store's bookkeeping, after the slot store: the
    /// binding's value fuse (`gGlobalVals[bid]`) and a fused literal's
    /// fuse.
    fn binding_fuses(&mut self, bid: u32, val: Value, gc_free: bool, fused: Option<crate::wasm::translate::FusedGname>) {
        let one = self.i32c(1);
        let two = self.i32c(2);
        // The binding's value fuse (`gGlobalVals[bid]`): an armed cell whose
        // value changes mirrors a non-GC value in place, and otherwise is
        // unarmed with the re-arm left to the runtime.
        let vals = self.i32c(self.h.global_vals_base + 16 * bid);
        let fw = self.load_i32(vals, 8);
        let armed = self.fuse_armed(fw);
        let old = self.load_i64(vals, 0);
        let changed = self.bin(Operator::I64Ne, old, val, Type::I32);
        let blow = self.bin(Operator::I32And, armed, changed, Type::I32);
        let (blow_b, cont) = (self.body.add_block(), self.body.add_block());
        self.cond_br(blow, Self::to(blow_b), Self::to(cont));
        self.cur = blow_b;
        let (gc_b, plain_b) = (self.body.add_block(), self.body.add_block());
        if gc_free {
            self.terminate(Terminator::Br { target: Self::to(plain_b) });
        } else {
            let tag = self.tag_of(val);
            let st = self.i32c(TAG_STRING as u32);
            let is_gc = self.bin(Operator::I32GeU, tag, st, Type::I32);
            self.cond_br(is_gc, Self::to(gc_b), Self::to(plain_b));
        }
        self.cur = plain_b;
        // Armed with the new value; no function, so not predicted.
        self.store_i64(vals, 0, val);
        self.store_i32(vals, 8, one);
        self.terminate(Terminator::Br { target: Self::to(cont) });
        self.cur = gc_b;
        let z = self.i32c(0);
        self.store_i32(vals, 8, z);
        let b = self.i32c(bid);
        self.call(self.h.binding_written, &[b], &[]);
        self.terminate(Terminator::Br { target: Self::to(cont) });
        self.cur = cont;
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
    }

    /// Whether a binding's value-fuse word `fw` is armed: 1, or 3 (armed
    /// with its predicted function).
    fn fuse_armed(&mut self, fw: Value) -> Value {
        let one = self.i32c(1);
        self.bin(Operator::I32And, fw, one, Type::I32)
    }

    fn gname_fast_arms(&mut self, inst: mir::Inst, bid: u32) -> R<()> {
        let vals = self.i32c(self.h.global_vals_base + 16 * bid);
        let fw = self.load_i32(vals, 8);
        let one = self.i32c(1);
        let armed = self.fuse_armed(fw);
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

    /// The inline arm of binding syntactic global name `bid`:
    /// with the binding's slot row resolved
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

    /// The inline arm of a write to syntactic global binding `bid`,
    /// taking `ok_clean`: with the
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
        self.binding_fuses(bid, val, false, fused);
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

    /// Whether `v` is a string literal (an atom): a `const.str`, boxed
    /// and weakened.
    fn is_str_literal(&self, mut v: mir::Value) -> bool {
        loop {
            let mir::func::ValueDef::Result(i, _) = self.f.values[v].def else { return false };
            match self.f.insts[i].op {
                Opcode::ConstStr(_) => return true,
                Opcode::Box | Opcode::Weaken => v = self.f.insts[i].args[0],
                _ => return false,
            }
        }
    }

    /// `x ==/=== lit` for a string literal `lit` (an atom), a
    /// literal-RHS ladder, each deciding arm taking `ok_clean`: a
    /// non-string is unequal (strictly; loosely it coerces: the helper's);
    /// the same pointer is equal; an atom that is not it is unequal (one
    /// flag load, the common miss of a `switch` on an atomized key); a
    /// different length is unequal; two linear strings compare their
    /// characters (a pure leaf). A rope falls through to the generic arms.
    fn literal_eq(&mut self, inst: mir::Inst, cc: JsCc, x: Value, lit: Value) -> R<()> {
        use crate::wasm::mir::abi::{STRING_ATOM_BIT, STRING_FLAGS_OFFSET};
        let negate = matches!(cc, JsCc::Ne | JsCc::StrictNe);
        let strict = matches!(cc, JsCc::StrictEq | JsCc::StrictNe);
        let generic = self.body.add_block();
        let (eq_b, ne_b) = (self.body.add_block(), self.body.add_block());
        let tx = self.tag_of(x);
        let is_s = self.tag_is(tx, TAG_STRING as u32);
        let str_b = self.body.add_block();
        self.cond_br(is_s, Self::to(str_b), Self::to(if strict { ne_b } else { generic }));
        self.cur = str_b;
        let same = self.bin(Operator::I64Eq, x, lit, Type::I32);
        let other = self.body.add_block();
        self.cond_br(same, Self::to(eq_b), Self::to(other));
        self.cur = other;
        let (xp, lp) = (self.un(Operator::I32WrapI64, x, Type::I32), self.un(Operator::I32WrapI64, lit, Type::I32));
        let xf = self.load_i32(xp, STRING_FLAGS_OFFSET);
        let ab = self.i32c(STRING_ATOM_BIT);
        let atom = self.bin(Operator::I32And, xf, ab, Type::I32);
        let len_b = self.body.add_block();
        self.cond_br(atom, Self::to(ne_b), Self::to(len_b));
        self.cur = len_b;
        let xl = self.load_i32(xp, STRING_LENGTH_OFFSET);
        let ll = self.load_i32(lp, STRING_LENGTH_OFFSET);
        let len_eq = self.bin(Operator::I32Eq, xl, ll, Type::I32);
        let lin_b = self.body.add_block();
        self.cond_br(len_eq, Self::to(lin_b), Self::to(ne_b));
        self.cur = lin_b;
        let lb = self.i32c(STRING_LINEAR_BIT);
        let lin = self.bin(Operator::I32And, xf, lb, Type::I32);
        let chars_b = self.body.add_block();
        self.cond_br(lin, Self::to(chars_b), Self::to(generic));
        self.cur = chars_b;
        let r = self.call1(self.h.str_chars_eq, &[xp, lp], Type::I32);
        let r = if negate { self.un(Operator::I32Eqz, r, Type::I32) } else { r };
        let t = self.edge(inst, 0, &[r])?;
        self.terminate(Terminator::Br { target: t });
        for (blk, equal) in [(eq_b, true), (ne_b, false)] {
            self.cur = blk;
            let v = self.i32c(u32::from(equal != negate));
            let t = self.edge(inst, 0, &[v])?;
            self.terminate(Terminator::Br { target: t });
        }
        self.cur = generic;
        Ok(())
    }

    /// `switch.str`: `x` against atoms `cases`. A non-string takes the
    /// default. An atom equals a case exactly when it is that atom, so its
    /// tag, flags and pointer are tested once and each case is one compare
    /// of pointers (where a chain of `===`s retests the tag and the flags
    /// and reloads the atom table at every case). Another linear string
    /// compares lengths, then characters (a pure leaf); a rope takes
    /// `fail`.
    fn switch_str(&mut self, inst: mir::Inst, a: &[Value], n: u32) -> R<()> {
        use crate::wasm::mir::abi::{STRING_ATOM_BIT, STRING_FLAGS_OFFSET};
        let x = a[0];
        let n = n as usize;
        // The cases' atoms, each loaded where it is compared (or, for a
        // case whose atom has other uses, the value already there).
        let margs = self.f.insts[inst].args.clone();
        let tslot = self.i32c(self.h.atom_table_slot);
        let tbl = self.load_i32(tslot, 0);
        let case = |l: &mut Self, k: usize| -> Value {
            match l.lazy_strs.get(&margs[1 + k]).copied() {
                Some(name) => {
                    let id = l.atoms.intern_chars(l.mm.atoms[name].chars());
                    l.load_i32(tbl, 4 * id)
                }
                None => a[1 + k],
            }
        };
        let default = self.edge(inst, n, &[])?;
        let tag = self.tag_of(x);
        let is_s = self.tag_is(tag, TAG_STRING as u32);
        let str_b = self.body.add_block();
        self.cond_br(is_s, Self::to(str_b), default.clone());
        self.cur = str_b;
        let p = self.un(Operator::I32WrapI64, x, Type::I32);
        let flags = self.load_i32(p, STRING_FLAGS_OFFSET);
        let ab = self.i32c(STRING_ATOM_BIT);
        let atom = self.bin(Operator::I32And, flags, ab, Type::I32);
        let (atom_b, other_b) = (self.body.add_block(), self.body.add_block());
        self.cond_br(atom, Self::to(atom_b), Self::to(other_b));
        self.cur = atom_b;
        for k in 0..n {
            let c = case(self, k);
            let same = self.bin(Operator::I32Eq, p, c, Type::I32);
            let next = self.body.add_block();
            let t = self.edge(inst, k, &[])?;
            self.cond_br(same, t, Self::to(next));
            self.cur = next;
        }
        self.terminate(Terminator::Br { target: default.clone() });
        // Not an atom: linear, then by length and characters.
        self.cur = other_b;
        let lb = self.i32c(STRING_LINEAR_BIT);
        let lin = self.bin(Operator::I32And, flags, lb, Type::I32);
        let lin_b = self.body.add_block();
        let fail = self.edge(inst, n + 1, &[])?;
        self.cond_br(lin, Self::to(lin_b), fail);
        self.cur = lin_b;
        let len = self.load_i32(p, STRING_LENGTH_OFFSET);
        for k in 0..n {
            let c = case(self, k);
            let cl = self.load_i32(c, STRING_LENGTH_OFFSET);
            let eq_len = self.bin(Operator::I32Eq, len, cl, Type::I32);
            let (chars_b, next) = (self.body.add_block(), self.body.add_block());
            self.cond_br(eq_len, Self::to(chars_b), Self::to(next));
            self.cur = chars_b;
            let eq = self.call1(self.h.str_chars_eq, &[p, c], Type::I32);
            let t = self.edge(inst, k, &[])?;
            self.cond_br(eq, t, Self::to(next));
            self.cur = next;
        }
        self.terminate(Terminator::Br { target: default });
        Ok(())
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
        if STRING_EQ_ARM {
            // Two strings: one pointer is
            // equal; different lengths (a rope carries its length, so no
            // flatten) or two atoms (deduplicated) are unequal. Else the
            // helper compares the characters.
            use crate::wasm::mir::abi::{STRING_ATOM_BIT, STRING_FLAGS_OFFSET};
            let generic = self.body.add_block();
            let sa = self.tag_is(ta, TAG_STRING as u32);
            let sb = self.tag_is(tb, TAG_STRING as u32);
            let both = self.bin(Operator::I32And, sa, sb, Type::I32);
            self.check(both, generic);
            let negate = matches!(cc, JsCc::Ne | JsCc::StrictNe);
            let (eq_b, ne_b, len_b) = (self.body.add_block(), self.body.add_block(), self.body.add_block());
            self.cond_br(bits_eq, Self::to(eq_b), Self::to(len_b));
            self.cur = len_b;
            let (ap, bp) = (self.un(Operator::I32WrapI64, a, Type::I32), self.un(Operator::I32WrapI64, b, Type::I32));
            let al = self.load_i32(ap, STRING_LENGTH_OFFSET);
            let bl = self.load_i32(bp, STRING_LENGTH_OFFSET);
            let len_eq = self.bin(Operator::I32Eq, al, bl, Type::I32);
            let atom_b = self.body.add_block();
            self.cond_br(len_eq, Self::to(atom_b), Self::to(ne_b));
            self.cur = atom_b;
            let af = self.load_i32(ap, STRING_FLAGS_OFFSET);
            let bf = self.load_i32(bp, STRING_FLAGS_OFFSET);
            let flags = self.bin(Operator::I32And, af, bf, Type::I32);
            let atom = self.i32c(STRING_ATOM_BIT);
            let both_atom = self.bin(Operator::I32And, flags, atom, Type::I32);
            self.cond_br(both_atom, Self::to(ne_b), Self::to(generic));
            for (blk, equal) in [(eq_b, true), (ne_b, false)] {
                self.cur = blk;
                let v = self.i32c(u32::from(equal != negate));
                let t = self.edge(inst, 0, &[v])?;
                self.terminate(Terminator::Br { target: t });
            }
            self.cur = generic;
        }
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
        let same = self.epoch_same.take().expect("gc_call sampled the epoch");
        self.clean_or_dirty(inst, ok, same, &[out])
    }

    /// A property read's inline cache past its special arms (a
    /// fact-free read): the ways, then the shared probe `night_ic_get`
    /// (own and holder ways, the megamorphic table), taking `ok_clean` on
    /// a hit; a miss runs the generic get and fills the site's ways.
    fn get_ic(&mut self, inst: mir::Inst, name: mir::entity::AtomId, recv: Value, way_base: Value, cache: u32) -> R<()> {
        let at = self.atom(name);
        let probe = self.body.add_block();
        self.get_ic_ways(inst, recv, way_base, cache * INLINE_IC_STRIDE, probe)?;
        self.cur = probe;
        let r = self.call(self.h.ic_get_poly, &[recv, at, way_base], &[Type::I64]);
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
        self.js_call(inst, self.h.get_prop_ic_miss, &[recv, at, c], false)
    }

    /// `getprop.data`'s inline cache: `get_ic`'s ways and probe taking
    /// `ok`, then the runtime's pure lookup (a leaf: no rooting), which
    /// fills the ways as the IC miss does; its magic result (the lookup
    /// would run code or throw) takes `fail`.
    fn get_ic_pure(&mut self, inst: mir::Inst, name: mir::entity::AtomId, recv: Value, way_base: Value, cache: u32) -> R<()> {
        let at = self.atom(name);
        let probe = self.body.add_block();
        self.get_ic_ways(inst, recv, way_base, cache * INLINE_IC_STRIDE, probe)?;
        self.cur = probe;
        let r = self.call(self.h.ic_get_poly, &[recv, at, way_base], &[Type::I64]);
        let tag = self.tag_of(r);
        let miss = self.tag_is(tag, TAG_MAGIC as u32);
        let slow = self.body.add_block();
        let t = self.edge(inst, 0, &[r])?;
        self.cond_br(miss, Self::to(slow), t);
        self.cur = slow;
        self.slow_census(inst);
        let c = self.i32c(cache);
        let r = self.call(self.h.get_prop_pure, &[self.cx, recv, at, c], &[Type::I64]);
        let tag = self.tag_of(r);
        let fail = self.tag_is(tag, TAG_MAGIC as u32);
        let t = self.edge(inst, 0, &[r])?;
        let f = self.edge(inst, 1, &[])?;
        self.cond_br(fail, f, t);
        Ok(())
    }

    /// A property store's inline cache: way 0 (an overwrite of the own slot
    /// the way describes) and the add-transition replay, taking `ok_clean`;
    /// a miss runs the generic set (vouched where the value keeps the
    /// object's TYPES) and fills the way.
    fn set_ic(&mut self, inst: mir::Inst, name: mir::entity::AtomId, recv: Value, val: Value, strict: bool) -> R<()> {
        let at = self.atom(name);
        let cache = self.atoms.next_prop_cache();
        let way = self.ic_addr(cache * INLINE_IC_STRIDE);
        let (trans, slow) = (self.body.add_block(), self.body.add_block());
        self.set_ic_ways(inst, at, recv, val, way, trans, slow)?;
        self.cur = trans;
        let row = self.add_off(way, IC_TRANS_ROW_OFF);
        let preds = self.add_preds.get(&name).cloned().unwrap_or_default();
        let num = matches!(self.ty(self.f.insts[inst].args[1]), MType::Val(s) if s.tags.subset_of(TagSet::NUMBER));
        self.set_ic_trans(inst, &preds, recv, val, num, row, slow)?;
        self.cur = slow;
        if let Some(census) = self.exit_census {
            static NEXT: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
            let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let site = self.f.insts[inst].attach.and_then(|a| self.f.attachments[a].site);
            crate::diag_line!(
                "night: mir setmiss {id} sid#{} frame {} {:?} {}",
                self.f.script,
                self.cur_frame,
                site,
                std::string::String::from_utf16_lossy(self.mm.atoms[name].chars())
            );
            let (k, i) = (self.i32c(crate::options::MIR_GUARD_CENSUS_KIND + 3), self.i32c(id));
            self.call1(census, &[k, i], Type::I32);
        }
        let vouch = self.vouch_types(inst, recv, val);
        let (c, sv) = (self.i32c(cache), self.i32c(u32::from(strict)));
        let sv = self.bin(Operator::I32Or, sv, vouch, Type::I32);
        self.js_call(inst, self.h.set_prop_ic_miss, &[recv, at, val, c, sv], false)
    }

    /// `--mir-exit-census`: count a split op's call of its runtime helper
    /// (kind `MIR_SLOW_CENSUS_KIND`), with its static record.
    fn slow_census(&mut self, inst: mir::Inst) {
        let Some(census) = self.exit_census else { return };
        static NEXT: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
        let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let name = match self.f.insts[inst].op {
            Opcode::GetPropData(n) | Opcode::SetPropData(n) => {
                format!(" {}", String::from_utf16_lossy(self.mm.atoms[n].chars()))
            }
            _ => String::new(),
        };
        crate::diag_line!(
            "night: mir slowcall {id} sid#{} {}{name}",
            self.f.script,
            mir::print::mnemonic(&self.f.insts[inst].op)
        );
        let (k, i) = (self.i32c(crate::options::MIR_SLOW_CENSUS_KIND), self.i32c(id));
        self.call1(census, &[k, i], Type::I32);
    }

    /// 1 iff boxed `v` is an object whose ToPrimitive would run user code
    /// (anything but Object.prototype's own conversion: the runtime's pure
    /// check, a leaf).
    fn converts_user(&mut self, v: Value) -> Value {
        let t = self.tag_of(v);
        let obj = self.tag_is(t, TAG_OBJECT as u32);
        let (chk, join) = (self.body.add_block(), self.body.add_block());
        let r = self.body.add_blockparam(join, Type::I32);
        let z = self.i32c(0);
        self.cond_br(obj, Self::to(chk), BlockTarget { block: join, args: vec![z] });
        self.cur = chk;
        let ok = self.call1(self.h.to_primitive_pure, &[self.cx, v], Type::I32);
        let bad = self.un(Operator::I32Eqz, ok, Type::I32);
        self.terminate(Terminator::Br {
            target: BlockTarget { block: join, args: vec![bad] },
        });
        self.cur = join;
        r
    }

    /// `setprop.data`'s inline cache: `set_ic`'s way and add-transition
    /// replay taking `ok_clean` (they demote no claim MIR reads), then the
    /// runtime's set, which fails where it would run code, and reports a
    /// demotion (`ok_dirty`).
    fn set_ic_pure(&mut self, inst: mir::Inst, name: mir::entity::AtomId, recv: Value, val: Value) -> R<()> {
        let at = self.atom(name);
        let cache = self.atoms.next_prop_cache();
        let way = self.ic_addr(cache * INLINE_IC_STRIDE);
        let (trans, slow) = (self.body.add_block(), self.body.add_block());
        self.set_ic_ways(inst, at, recv, val, way, trans, slow)?;
        self.cur = trans;
        let row = self.add_off(way, IC_TRANS_ROW_OFF);
        let preds = self.add_preds.get(&name).cloned().unwrap_or_default();
        let num = matches!(self.ty(self.f.insts[inst].args[1]), MType::Val(s) if s.tags.subset_of(TagSet::NUMBER));
        self.set_ic_trans(inst, &preds, recv, val, num, row, slow)?;
        self.cur = slow;
        self.slow_census(inst);
        let vouch = self.vouch_types(inst, recv, val);
        let c = self.i32c(cache);
        let live = self.live_across(inst);
        let (r, _) = self.gc_call(self.h.set_prop_pure, &[recv, at, val, c, vouch], &live)?;
        self.epoch_same = None;
        self.store_codes(inst, r)
    }

    /// A data store's helper result `r` (1 clean, 2 dirty, 0 fail, 3 err)
    /// to the edge of that role (`setprop.data`, `setelem.data`).
    fn store_codes(&mut self, inst: mir::Inst, r: Value) -> R<()> {
        for (code, idx) in [(1, 0), (2, 1), (0, 2)] {
            let c = self.i32c(code);
            let is = self.bin(Operator::I32Eq, r, c, Type::I32);
            let t = self.edge(inst, idx, &[])?;
            let other = self.body.add_block();
            self.cond_br(is, t, Self::to(other));
            self.cur = other;
        }
        let e = self.edge(inst, 3, &[])?;
        self.terminate(Terminator::Br { target: e });
        Ok(())
    }

    /// `load_field`/`store_field` (§4.3). Under a SLOTS claim (a guard
    /// proved it, or the object is under construction), a field with a
    /// slot prediction is at its slot, read or written directly. Any other
    /// access (a field with no slot prediction, or a claim of TYPES
    /// alone) finds the slot through the site's inline cache: the field,
    /// by name, is still of its claim's type. A store keeps TYPES only with
    /// a value of the field's predicted type (`store_types`); at a known
    /// slot another demotes the word inline (the store choke: the bits
    /// cleared, the epoch bumped) and takes `ok_dirty`. GC barriers unless
    /// the value is a number.
    fn field_op(
        &mut self,
        inst: mir::Inst,
        name: mir::entity::AtomId,
        obj: Value,
        val: Option<Value>,
    ) -> R<()> {
        let recv_ty = self.ty(self.f.insts[inst].args[0]);
        let claim = recv_ty
            .obj_info()
            .and_then(|o| o.layout)
            .ok_or("lowering: a field op without a layout claim")?;
        let slot = self
            .mm
            .layouts
            .get(&claim.keys.lo)
            .and_then(|l| l.field(name))
            .map(|(s, _)| u32::try_from(s).unwrap());
        let Some(slot) = slot.filter(|_| claim.slots) else {
            let boxed = self.box_tagged(TAG_OBJECT, obj);
            return match val {
                None => {
                    let cache = self.atoms.next_prop_cache();
                    let way_base = self.ic_addr(cache * INLINE_IC_STRIDE);
                    self.get_ic(inst, name, boxed, way_base, cache)
                }
                Some(v) => self.set_ic(inst, name, boxed, v, self.strict),
            };
        };
        let off = FIXED_SLOTS_BASE + 8 * slot;
        let Some(v) = val else {
            let r = self.load_i64(obj, off);
            let t = self.edge(inst, 0, &[r])?;
            self.terminate(Terminator::Br { target: t });
            return Ok(());
        };
        let num = matches!(self.ty(self.f.insts[inst].args[1]), MType::Val(s) if s.tags.subset_of(TagSet::NUMBER));
        let w = self.load_i32(obj, OBJ_CLASS_IDX_OFFSET);
        let demote = self.body.add_block();
        self.store_types(inst, obj, w, v, demote);
        for dirty in [false, true] {
            if dirty {
                self.cur = demote;
                self.clear_bits(obj, w, CLASS_WORD_RANGES | CLASS_WORD_SHALLOW);
            }
            if !num {
                self.pre_barrier(obj, off);
            }
            self.store_i64(obj, off, v);
            if !num {
                let s = self.i32c(slot);
                self.post_barrier(self.h.post_write_barrier, obj, s, v);
            }
            let t = self.edge(inst, usize::from(dirty), &[])?;
            self.terminate(Terminator::Br { target: t });
        }
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

    /// A get IC's inline ways: with
    /// `recv` an object whose shape one of the site's ways names (way 0 at
    /// `way0`, the rest `INLINE_IC_WAY_BYTES` apart from its row offset
    /// `way_off`), the value from its own fixed slot, or through the way's
    /// holder (a prototype method) while the holder keeps its shape,
    /// taking `ok_clean`; else `probe`.
    /// A property IC's receiver test: an object, or `miss`. Skipped when
    /// the receiver's type (`args[0]`) already says object.
    fn check_recv_object(&mut self, inst: mir::Inst, recv: Value, miss: Block) {
        let tags = value_tags(&self.ty(self.f.insts[inst].args[0]));
        if tags.is_nonempty_subset_of(TagSet::OBJECT) {
            return;
        }
        let tag = self.tag_of(recv);
        let is_obj = self.tag_is(tag, TAG_OBJECT as u32);
        self.check(is_obj, miss);
    }

    fn get_ic_ways(&mut self, inst: mir::Inst, recv: Value, way0: Value, way_off: u32, probe: Block) -> R<()> {
        use crate::region_shape::{INLINE_IC_WAYS, INLINE_IC_WAY_BYTES};
        self.check_recv_object(inst, recv, probe);
        let obj = self.un(Operator::I32WrapI64, recv, Type::I32);
        let shape = self.load_i32(obj, SHAPE_OFFSET);
        let hit_b = self.body.add_block();
        let way = self.body.add_blockparam(hit_b, Type::I32);
        for w in 0..INLINE_IC_WAYS {
            let wb = if w == 0 {
                way0
            } else {
                let v = self.ic_addr(way_off + w * INLINE_IC_WAY_BYTES);
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
        // A proven absence.
        let absent = self.i32c(crate::region_shape::IC_SLOT_ENC_ABSENT);
        let is_absent = self.bin(Operator::I32Eq, enc, absent, Type::I32);
        let (abs_b, ld_b) = (self.body.add_block(), self.body.add_block());
        self.cond_br(is_absent, Self::to(abs_b), Self::to(ld_b));
        self.cur = abs_b;
        let undef = self.i64c(TAG_UNDEFINED << 32);
        let t = self.edge(inst, 0, &[undef])?;
        self.terminate(Terminator::Br { target: t });
        self.cur = ld_b;
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

    /// A set IC's way 0 (not its
    /// transition and megamorphic arms): with `recv` an object of the
    /// way's shape, store `val` to the slot the way names and take
    /// `ok_clean`; else branch to `slow`. The store bypasses the engine's
    /// choke, so it also requires the object's word to carry no bit it
    /// could falsify: RANGES never, TYPES unless `val` is a number.
    /// A set IC's overwrite arms: way 0 (the site's one shape), or past
    /// one shape (way 0 sentineled) the (shape, atom) row the module's
    /// `night_ic_set_cold` finds in the mega-set table. Both
    /// name the slot for one shared store; a mono miss takes `trans`, no
    /// mega row or a non-object `slow`.
    #[allow(clippy::too_many_arguments)]
    fn set_ic_ways(
        &mut self,
        inst: mir::Inst,
        atom: Value,
        recv: Value,
        val: Value,
        way: Value,
        trans: Block,
        slow: Block,
    ) -> R<()> {
        use crate::region_shape::{MEGA_SET_ABS_SLOT_OFF, MEGA_SET_SLOT_ENC_OFF};
        let num = matches!(self.ty(self.f.insts[inst].args[1]), MType::Val(s) if s.tags.subset_of(TagSet::NUMBER));
        self.check_recv_object(inst, recv, slow);
        let obj = self.un(Operator::I32WrapI64, recv, Type::I32);
        let shape = self.load_i32(obj, SHAPE_OFFSET);
        let store = self.body.add_block();
        let enc = self.body.add_blockparam(store, Type::I32);
        let abs = self.body.add_blockparam(store, Type::I32);
        let to_store = |s: &mut Self, src: Value, enc_off: u32, abs_off: u32| {
            let e = s.load_i32(src, enc_off);
            let a = if num { e } else { s.load_i32(src, abs_off) };
            s.terminate(Terminator::Br {
                target: BlockTarget {
                    block: store,
                    args: vec![e, a],
                },
            });
        };
        let cached = self.load_i32(way, IC_SET_RECVSHAPE);
        let hit = self.bin(Operator::I32Eq, shape, cached, Type::I32);
        let (w0, poly) = (self.body.add_block(), self.body.add_block());
        self.cond_br(hit, Self::to(w0), Self::to(poly));
        self.cur = w0;
        to_store(self, way, IC_SET_SLOTENC, IC_SET_ABSSLOT);
        self.cur = poly;
        let sentinel = self.i32c(crate::wasm::mir::abi::IC_POLY_SENTINEL);
        let is_poly = self.bin(Operator::I32Eq, cached, sentinel, Type::I32);
        let mega = self.body.add_block();
        self.cond_br(is_poly, Self::to(mega), Self::to(trans));
        self.cur = mega;
        let cold = self.call1(self.h.ic_set_cold, &[shape, way, atom], Type::I64);
        let found = self.un(Operator::I64Eqz, cold, Type::I32);
        let mhit = self.un(Operator::I32Eqz, found, Type::I32);
        if let Some(census) = self.exit_census {
            static NEXT: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
            let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let site = self.f.insts[inst].attach.and_then(|a| self.f.attachments[a].site);
            crate::diag_line!("night: mir megaset {id} sid#{} {:?}", self.f.script, site);
            let k = self.i32c(crate::options::MIR_GUARD_CENSUS_KIND + 4);
            let base = self.i32c(id * 2);
            let i = self.bin(Operator::I32Add, base, mhit, Type::I32);
            self.call1(census, &[k, i], Type::I32);
        }
        self.check(mhit, slow);
        let entry = self.un(Operator::I32WrapI64, cold, Type::I32);
        to_store(self, entry, MEGA_SET_SLOT_ENC_OFF, MEGA_SET_ABS_SLOT_OFF);
        // The store: the slot `enc & 1` selects the dynamic slots over the
        // object, `enc & !1` is the byte offset from that base.
        self.cur = store;
        let w = self.load_i32(obj, OBJ_CLASS_IDX_OFFSET);
        self.check_store_bits(inst, obj, w, val, num, slow);
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
            self.post_barrier(self.h.post_write_barrier, obj, abs, val);
        }
        let t = self.edge(inst, 0, &[])?;
        self.terminate(Terminator::Br { target: t });
        Ok(())
    }

    /// Where environment object `obj`'s slot `slot` is, as a base and an
    /// offset: decided statically, as Ion's `GetAliasedVar` is
    /// (`MAX_FIXED_SLOTS`).
    fn env_slot(&mut self, obj: Value, slot: u32) -> (Value, u32) {
        if slot < MAX_FIXED_SLOTS {
            (obj, FIXED_SLOTS_BASE + 8 * slot)
        } else {
            let slots = self.load_i32(obj, NATIVE_SLOTS_OFFSET);
            (slots, 8 * (slot - MAX_FIXED_SLOTS))
        }
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

    /// A set IC's add-transition row replayed inline (in a
    /// sound subset): `recv` an object of the row's pre-add shape, the
    /// row's prototype hops unchanged (all four, live), and the add unable to falsify the object's class-word bits.
    /// That holds when it has no SLOTS, or lands where one of the name's
    /// predicted (layout key, offset) pairs says; with no RANGES; and no
    /// TYPES unless the value is a number. Then store the fresh slot, swap
    /// the shape word and take `ok_clean`; else branch to `slow` (the
    /// helper keeps the bits itself).
    fn set_ic_trans(
        &mut self,
        inst: mir::Inst,
        preds: &[(u32, u32)],
        recv: Value,
        val: Value,
        num: bool,
        row: Value,
        slow: Block,
    ) -> R<()> {
        self.check_recv_object(inst, recv, slow);
        let obj = self.un(Operator::I32WrapI64, recv, Type::I32);
        let shape = self.load_i32(obj, SHAPE_OFFSET);
        let old = self.load_i32(row, IC_TRANS_OLDSHAPE);
        let m_old = self.bin(Operator::I32Eq, old, shape, Type::I32);
        self.check(m_old, slow);
        let slot_off = self.load_i32(row, IC_TRANS_SLOTOFF);
        self.check(slot_off, slow);
        // Every recorded hop, live: a class hierarchy built with
        // prototype objects (`inheritsFrom`) puts three or four protos
        // under its instances, and a constructor's adds that fell to the
        // helper would each clear TYPES there.
        for n in 0..IC_TRANS_PROTO_HOPS {
            let p = self.load_i32(row, IC_TRANS_PROTO0 + IC_TRANS_PROTO_ROW_BYTES * n);
            let empty = self.un(Operator::I32Eqz, p, Type::I32);
            let want = self.load_i32(row, IC_TRANS_PROTO0 + IC_TRANS_PROTO_ROW_BYTES * n + 4);
            // An empty hop's load reads the null page's first word: only
            // its `empty` matters.
            let live = self.load_i32(p, SHAPE_OFFSET);
            let same = self.bin(Operator::I32Eq, live, want, Type::I32);
            let ok = self.bin(Operator::I32Or, empty, same, Type::I32);
            self.check(ok, slow);
        }
        // The class word.
        let w = self.load_i32(obj, OBJ_CLASS_IDX_OFFSET);
        self.check_store_bits(inst, obj, w, val, num, slow);
        let sb = self.i32c(CLASS_WORD_SLOTS);
        let slots = self.bin(Operator::I32And, w, sb, Type::I32);
        let (keyed, go) = (self.body.add_block(), self.body.add_block());
        self.cond_br(slots, Self::to(keyed), Self::to(go));
        self.cur = keyed;
        // The live layout key: the early key under the CONSTRUCTING
        // sentinel, else the stamped identity (they are disjoint).
        let ksh = self.i32c(EARLY_KEY_SHIFT);
        let kraw = self.bin(Operator::I32ShrU, w, ksh, Type::I32);
        let km = self.i32c(EARLY_KEY_MAX);
        let k_sent = self.bin(Operator::I32And, kraw, km, Type::I32);
        let m16 = self.i32c(0xFFFF);
        let k_idx = self.bin(Operator::I32And, w, m16, Type::I32);
        let sb = self.i32c(CLASS_WORD_SENTINEL);
        let sent = self.bin(Operator::I32And, w, sb, Type::I32);
        let k = self.select(Type::I32, k_sent, k_idx, sent);
        // An add past the layout's extent (its bound in the this-cells
        // table; 0 = unknown) leaves every predicted slot where it was:
        // SLOTS holds.
        let three = self.i32c(3);
        let koff = self.bin(Operator::I32Shl, k, three, Type::I32);
        let tbase = self.i32c(self.h.this_cells_base.wrapping_sub(8));
        let taddr = self.bin(Operator::I32Add, tbase, koff, Type::I32);
        let bound = self.load_i32(taddr, 0);
        let z = self.i32c(0);
        let known = self.bin(Operator::I32Ne, bound, z, Type::I32);
        let keyed_k = self.bin(Operator::I32Ne, k, z, Type::I32);
        let past = self.bin(Operator::I32GeU, slot_off, bound, Type::I32);
        let past = self.bin(Operator::I32And, past, known, Type::I32);
        let past = self.bin(Operator::I32And, past, keyed_k, Type::I32);
        let mut hit = past;
        for &(key, off) in preds {
            let kv = self.i32c(key);
            let ke = self.bin(Operator::I32Eq, k, kv, Type::I32);
            let ov = self.i32c(off);
            let oe = self.bin(Operator::I32Eq, slot_off, ov, Type::I32);
            let both = self.bin(Operator::I32And, ke, oe, Type::I32);
            hit = self.bin(Operator::I32Or, hit, both, Type::I32);
        }
        // An add to a CLOSED object (which holds SLOTS, so is keyed) is
        // outside its row: the helper, whose engine add clears the bit.
        let cm = self.i32c(CLASS_WORD_SENTINEL | CLASS_WORD_CLOSED);
        let cbits = self.bin(Operator::I32And, w, cm, Type::I32);
        let cv = self.i32c(CLASS_WORD_CLOSED);
        let open = self.bin(Operator::I32Ne, cbits, cv, Type::I32);
        let hit = self.bin(Operator::I32And, hit, open, Type::I32);
        self.cond_br(hit, Self::to(go), Self::to(slow));
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

    /// `obj[key] = val` adding `key`, an atom (`props[name] = config[name]`
    /// over a for-in's keys): the transition the runtime's set learned for
    /// (the object's shape, the atom), from the element-add table, replayed
    /// as a named add site replays its own row (`set_ic_trans`, with no
    /// slot predictions for an unknown name). A key that is no atom, or
    /// an index, never has a row. Else `other`.
    fn elem_add_arm(&mut self, inst: mir::Inst, recv: Value, key: Value, val: Value, other: Block) -> R<()> {
        use crate::region_shape::{ELEM_ADD_KEY_OFF, ELEM_ADD_ROWS, ELEM_ADD_ROW_BYTES, STRLIT_ELEM_ADD_OFF};
        let kt = self.tag_of(key);
        let ks = self.tag_is(kt, TAG_STRING as u32);
        let rt = self.tag_of(recv);
        let ro = self.tag_is(rt, TAG_OBJECT as u32);
        let both = self.bin(Operator::I32And, ks, ro, Type::I32);
        self.check(both, other);
        let kp = self.un(Operator::I32WrapI64, key, Type::I32);
        let one = self.i32c(1);
        let ekey = self.bin(Operator::I32Or, kp, one, Type::I32);
        let op = self.un(Operator::I32WrapI64, recv, Type::I32);
        let shape = self.load_i32(op, SHAPE_OFFSET);
        // NightRuntime.cpp's CacheHash.
        let three = self.i32c(3);
        let sh = self.bin(Operator::I32ShrU, shape, three, Type::I32);
        let k1 = self.i32c(2654435761);
        let h1 = self.bin(Operator::I32Mul, sh, k1, Type::I32);
        let k2c = self.i32c(0x9e37_79b9);
        let k2 = self.bin(Operator::I32Mul, ekey, k2c, Type::I32);
        let hh = self.bin(Operator::I32Xor, h1, k2, Type::I32);
        let mask = self.i32c(ELEM_ADD_ROWS - 1);
        let idx = self.bin(Operator::I32And, hh, mask, Type::I32);
        let stride = self.i32c(ELEM_ADD_ROW_BYTES);
        let off = self.bin(Operator::I32Mul, idx, stride, Type::I32);
        let ta = self.i32c(self.h.strlit_slot + STRLIT_ELEM_ADD_OFF);
        let tbl = self.load_i32(ta, 0);
        let row = self.bin(Operator::I32Add, tbl, off, Type::I32);
        let rkey = self.load_i32(row, ELEM_ADD_KEY_OFF);
        let same = self.bin(Operator::I32Eq, rkey, ekey, Type::I32);
        self.check(same, other);
        let num = matches!(self.ty(self.f.insts[inst].args[2]), MType::Val(s) if s.tags.subset_of(TagSet::NUMBER));
        self.set_ic_trans(inst, &[], recv, val, num, row, other)
    }

    /// The pristine `charCodeAt`/`charAt` on a linear string with an
    /// in-bounds int32 index, and `String.fromCharCode` of a code below 256
    /// (the char arms): the char inline (`charAt` and `fromCharCode`
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
    /// (`night_runtime_ctor_stamp`'s gates): an object still under construction whose early key is ours
    /// or none, with a slot span covering the row, gets the layout's idx
    /// plus the validity bits that survived construction.
    fn ctor_stamp_inline(&mut self, thisv: Value, layout: u32, nfields: u32, keep: u32, exact: bool) {
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
        let mine = self.i32c((layout + 1) << EARLY_KEY_SHIFT);
        let ours = self.bin(Operator::I32Eq, key, mine, Type::I32);
        let owned = if exact {
            ours
        } else {
            let z = self.i32c(0);
            let none = self.bin(Operator::I32Eq, key, z, Type::I32);
            self.bin(Operator::I32Or, none, ours, Type::I32)
        };
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
        // A permuted shape's span may cover holes: count its properties.
        let pb = self.i32c(SHAPE_PERMUTED_SLOTS_BIT);
        let perm = self.bin(Operator::I32And, imm, pb, Type::I32);
        let (holes, covered) = (self.body.add_block(), self.body.add_block());
        self.cond_br(perm, Self::to(holes), Self::to(covered));
        self.cur = holes;
        let r = self.call1(self.h.slots_covered, &[obj, n], Type::I32);
        self.cond_br(r, Self::to(covered), Self::to(done));
        self.cur = covered;
        if let Some(census) = self.exit_census.filter(|_| keep & CLASS_WORD_SHALLOW != 0) {
            // `--mir-exit-census`: a stamp publishing without the TYPES
            // its layout claims (lost during construction), by layout.
            let tb = self.i32c(CLASS_WORD_SHALLOW);
            let t = self.bin(Operator::I32And, w0, tb, Type::I32);
            let (count, go) = (self.body.add_block(), self.body.add_block());
            self.cond_br(t, Self::to(go), Self::to(count));
            self.cur = count;
            let (k, i) = (self.i32c(crate::options::MIR_GUARD_CENSUS_KIND + 3), self.i32c(layout));
            self.call1(census, &[k, i], Type::I32);
            self.terminate(Terminator::Br { target: Self::to(go) });
            self.cur = go;
        }
        // CLOSED in `keep` says the layout may be (the bit itself is an
        // early-key bit in `w0`).
        let kb = self.i32c(keep & !CLASS_WORD_CLOSED);
        let bits = self.bin(Operator::I32And, w0, kb, Type::I32);
        let idx = self.i32c(layout + 1);
        let w = self.bin(Operator::I32Or, idx, bits, Type::I32);
        // Every field there and a span of the row's length: nothing else
        // (CLOSED).
        let w = if keep & CLASS_WORD_CLOSED != 0 {
            self.or_closed_if_span(w, span, nfields)
        } else {
            w
        };
        self.store_i32(obj, OBJ_CLASS_IDX_OFFSET, w);
        self.terminate(Terminator::Br { target: Self::to(done) });
        self.cur = done;
    }

    /// Stamp word `w` with CLOSED where its object holds its row's `n`
    /// fields and nothing else: `span`, its slot span with every slot
    /// below `n` holding a property, is `n`, and `w` keeps SLOTS (every
    /// add landed where the row puts its name, so those properties are the
    /// row's).
    fn or_closed_if_span(&mut self, w: Value, span: Value, n: u32) -> Value {
        let nv = self.i32c(n);
        let eq = self.bin(Operator::I32Eq, span, nv, Type::I32);
        let ssh = self.i32c(CLASS_WORD_SLOTS.trailing_zeros());
        let sl = self.bin(Operator::I32ShrU, w, ssh, Type::I32);
        let ok = self.bin(Operator::I32And, eq, sl, Type::I32);
        let one = self.i32c(1);
        let ok = self.bin(Operator::I32And, ok, one, Type::I32);
        let sh = self.i32c(CLASS_WORD_CLOSED.trailing_zeros());
        let c = self.bin(Operator::I32Shl, ok, sh, Type::I32);
        self.bin(Operator::I32Or, w, c, Type::I32)
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
    fn check_store_bits(&mut self, inst: mir::Inst, obj: Value, w: Value, val: Value, _num: bool, slow: Block) {
        self.store_types(inst, obj, w, val, slow);
    }

    /// A store's duty to the object's word `w` (§4.6): TYPES survives
    /// only a value of the stored field's predicted type for the object's
    /// own class (`field_types`: the classes the site expects, as an IC
    /// validating the object's class before it stores); any other store
    /// drops it (`drop_types`). RANGES, which no MIR claim reads, is
    /// dropped either way.
    fn store_types(&mut self, inst: mir::Inst, obj: Value, w: Value, val: Value, slow: Block) {
        let Some(a) = self.f.insts[inst].attach.filter(|&a| {
            let at = &self.f.attachments[a];
            at.field_types_complete || !at.field_types.is_empty()
        }) else {
            self.drop_types(inst, obj, w, slow);
            return;
        };
        let at = &self.f.attachments[a];
        let mut classes: Vec<(u32, TagSet)> =
            at.field_types.iter().map(|&(k, m)| (k, mir::func::decode_tags(m))).collect();
        let complete = at.field_types_complete;
        // A receiver proven of some layouts is of no other class.
        let proven = self
            .ty(self.f.insts[inst].args[0])
            .obj_info()
            .and_then(|o| o.layout)
            .filter(|c| c.state == mir::types::LayoutState::Published)
            .map(|c| (c.keys.lo.get() + 1, c.keys.hi.get() + 1));
        if let Some((lo, hi)) = proven {
            if complete {
                classes.retain(|&(k, _)| k >= lo && k <= hi);
                let n = (hi - lo + 1) as usize;
                let first = classes.first().map(|c| c.1);
                if classes.is_empty() {
                    self.clear_bits(obj, w, CLASS_WORD_RANGES);
                    return;
                }
                if classes.len() == n && classes.iter().all(|c| Some(c.1) == first) {
                    self.keep_types_known(inst, obj, w, val, first.unwrap(), slow);
                    return;
                }
            }
        }
        // By the object's class: its stamp's identity, or while it is
        // constructed its early key (none: no class, no claim to check).
        let m16 = self.i32c(0xFFFF);
        let idx = self.bin(Operator::I32And, w, m16, Type::I32);
        let ksh = self.i32c(EARLY_KEY_SHIFT);
        let kraw = self.bin(Operator::I32ShrU, w, ksh, Type::I32);
        let km = self.i32c(EARLY_KEY_MAX);
        let early = self.bin(Operator::I32And, kraw, km, Type::I32);
        let sb = self.i32c(CLASS_WORD_SENTINEL);
        let sent = self.bin(Operator::I32And, w, sb, Type::I32);
        let id = self.select(Type::I32, early, idx, sent);
        let join = self.body.add_block();
        for (k, t) in classes {
            let kv = self.i32c(k);
            let is = self.bin(Operator::I32Eq, id, kv, Type::I32);
            let (this_b, next) = (self.body.add_block(), self.body.add_block());
            self.cond_br(is, Self::to(this_b), Self::to(next));
            self.cur = this_b;
            self.keep_types_known(inst, obj, w, val, t, slow);
            self.terminate(Terminator::Br { target: Self::to(join) });
            self.cur = next;
        }
        // Another class: with the list complete its layout types no such
        // field (the store touches no claim), unless it has no class.
        if complete {
            let z = self.i32c(0);
            let none = self.bin(Operator::I32Eq, id, z, Type::I32);
            let (drop_b, keep_b) = (self.body.add_block(), self.body.add_block());
            self.cond_br(none, Self::to(drop_b), Self::to(keep_b));
            self.cur = keep_b;
            self.clear_bits(obj, w, CLASS_WORD_RANGES);
            self.terminate(Terminator::Br { target: Self::to(join) });
            self.cur = drop_b;
        }
        self.drop_types(inst, obj, w, slow);
        self.terminate(Terminator::Br { target: Self::to(join) });
        self.cur = join;
    }

    /// The set helper's vouch bit (`night_runtime_set_prop_ic_miss`'s
    /// flag 2) for a store of `val` through `recv`: 2 when `recv` is an
    /// object whose class types the field and `val` is of that type, or,
    /// the site's list complete, a class typing no such field; else 0.
    /// The helper's own stores (replays, the mega-set probe) then keep
    /// TYPES, as the inline arms do: a polymorphic site's other classes
    /// miss its one inline way, and must not be demoted for it.
    fn vouch_types(&mut self, inst: mir::Inst, recv: Value, val: Value) -> Value {
        let Some(a) = self.f.insts[inst].attach.filter(|&a| {
            let at = &self.f.attachments[a];
            at.field_types_complete || !at.field_types.is_empty()
        }) else {
            return self.i32c(0);
        };
        let at = &self.f.attachments[a];
        let classes: Vec<(u32, TagSet)> =
            at.field_types.iter().map(|&(k, m)| (k, mir::func::decode_tags(m))).collect();
        let complete = at.field_types_complete;
        let vt = match self.ty(self.f.insts[inst].args[1]) {
            MType::Val(s) => s.tags,
            _ => TagSet::ALL,
        };
        // A non-object's word is read off the null page, then ignored.
        let tag = self.tag_of(recv);
        let is_obj = self.tag_is(tag, TAG_OBJECT as u32);
        let o = self.un(Operator::I32WrapI64, recv, Type::I32);
        let z = self.i32c(0);
        let obj = self.select(Type::I32, o, z, is_obj);
        let w = self.load_i32(obj, OBJ_CLASS_IDX_OFFSET);
        // Its class: the stamp's identity, or while it is constructed its
        // early key.
        let m16 = self.i32c(0xFFFF);
        let idx = self.bin(Operator::I32And, w, m16, Type::I32);
        let ksh = self.i32c(EARLY_KEY_SHIFT);
        let kraw = self.bin(Operator::I32ShrU, w, ksh, Type::I32);
        let km = self.i32c(EARLY_KEY_MAX);
        let early = self.bin(Operator::I32And, kraw, km, Type::I32);
        let sb = self.i32c(CLASS_WORD_SENTINEL);
        let sent = self.bin(Operator::I32And, w, sb, Type::I32);
        let id = self.select(Type::I32, early, idx, sent);
        let mut ok = self.i32c(0);
        let mut listed = self.i32c(0);
        for (k, t) in classes {
            let kv = self.i32c(k);
            let is = self.bin(Operator::I32Eq, id, kv, Type::I32);
            listed = self.bin(Operator::I32Or, listed, is, Type::I32);
            let conf = if vt.is_nonempty_subset_of(t) {
                self.i32c(1)
            } else if vt.intersect(t).is_empty() {
                self.i32c(0)
            } else {
                self.has_tags(val, t)
            };
            let hit = self.bin(Operator::I32And, is, conf, Type::I32);
            ok = self.bin(Operator::I32Or, ok, hit, Type::I32);
        }
        if complete {
            let unlisted = self.un(Operator::I32Eqz, listed, Type::I32);
            let keyed = self.bin(Operator::I32Ne, id, z, Type::I32);
            let other = self.bin(Operator::I32And, unlisted, keyed, Type::I32);
            ok = self.bin(Operator::I32Or, ok, other, Type::I32);
        }
        let ok = self.bin(Operator::I32And, ok, is_obj, Type::I32);
        let one = self.i32c(1);
        self.bin(Operator::I32Shl, ok, one, Type::I32)
    }

    /// A store that falsifies TYPES: on an object under construction (no
    /// fact covers its word) the bit is cleared here; on a published one
    /// the store goes to `slow`, the engine's, which clears it and bumps
    /// the epoch (so the op reports dirt, and facts leave with it).
    fn drop_types(&mut self, inst: mir::Inst, obj: Value, w: Value, slow: Block) {
        let m = self.i32c(CLASS_WORD_SHALLOW | CLASS_WORD_SENTINEL);
        let bits = self.bin(Operator::I32And, w, m, Type::I32);
        let pub_shallow = self.i32c(CLASS_WORD_SHALLOW);
        let bad = self.bin(Operator::I32Eq, bits, pub_shallow, Type::I32);
        let ok = self.un(Operator::I32Eqz, bad, Type::I32);
        self.check(ok, slow);
        if let Some(census) = self.exit_census {
            // `--mir-exit-census`: which stores drop TYPES from an object
            // under construction (no epoch bump, so no other trace).
            static NEXT: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
            let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let d = &self.f.insts[inst];
            let site = d.attach.and_then(|a| self.f.attachments[a].site);
            crate::diag_line!(
                "night: mir typesdrop {id} sid#{} {:?} {} [{:?}]",
                self.f.script,
                site,
                mir::print::mnemonic(&d.op),
                d.args.get(1).map(|&v| self.ty(v))
            );
            let all = self.i32c(CLASS_WORD_SHALLOW | CLASS_WORD_SENTINEL);
            let hit = self.bin(Operator::I32Eq, bits, all, Type::I32);
            let (count, go) = (self.body.add_block(), self.body.add_block());
            self.cond_br(hit, Self::to(count), Self::to(go));
            self.cur = count;
            let (k, i) = (self.i32c(crate::options::MIR_GUARD_CENSUS_KIND + 2), self.i32c(id));
            self.call1(census, &[k, i], Type::I32);
            self.terminate(Terminator::Br { target: Self::to(go) });
            self.cur = go;
        }
        self.clear_bits(obj, w, CLASS_WORD_RANGES | CLASS_WORD_SHALLOW);
    }

    /// A store of `val` to an object whose class types the field `mask`:
    /// TYPES survives iff the value is of it.
    fn keep_types_known(&mut self, inst: mir::Inst, obj: Value, w: Value, val: Value, mask: TagSet, slow: Block) {
        let vt = match self.ty(self.f.insts[inst].args[1]) {
            MType::Val(s) => s.tags,
            _ => TagSet::ALL,
        };
        if vt.is_nonempty_subset_of(mask) {
            self.clear_bits(obj, w, CLASS_WORD_RANGES);
        } else if vt.intersect(mask).is_empty() {
            self.drop_types(inst, obj, w, slow);
        } else {
            let conf = self.has_tags(val, mask);
            let (keep, drop, join) = (self.body.add_block(), self.body.add_block(), self.body.add_block());
            self.cond_br(conf, Self::to(keep), Self::to(drop));
            self.cur = keep;
            self.clear_bits(obj, w, CLASS_WORD_RANGES);
            self.terminate(Terminator::Br { target: Self::to(join) });
            self.cur = drop;
            self.drop_types(inst, obj, w, slow);
            self.terminate(Terminator::Br { target: Self::to(join) });
            self.cur = join;
        }
    }

    /// `init_field` (§2.3): add field `n` of the receiver's
    /// `constructing(n)` layout, of a value of its type. The site's
    /// add-transition row replayed inline where it adds exactly that
    /// field at its fixed slot (every recorded prototype hop live, as
    /// `set_ic_trans`); else the runtime's plain add, which also fills the
    /// row, continuing iff the object is then `constructing(n + 1)`, and
    /// leaving the rest of the constructor to baseline (`fail`) if not.
    /// TYPES holds by the value's type; RANGES, which no MIR claim reads,
    /// is dropped.
    fn init_field(&mut self, inst: mir::Inst, name: mir::entity::AtomId, obj: Value, val: Value) -> R<()> {
        let d = &self.f.insts[inst];
        let c = self
            .ty(d.args[0])
            .obj_info()
            .and_then(|o| o.layout)
            .ok_or("lowering: init_field without a layout claim")?;
        let mir::types::LayoutState::Constructing(n) = c.state else {
            return Err("lowering: init_field on a published object".into());
        };
        let i = self
            .mm
            .layouts
            .get(&c.keys.lo)
            .and_then(|l| l.field(name))
            .map(|(i, _)| u32::try_from(i).unwrap())
            .ok_or("lowering: init_field of a field its layout lacks")?;
        let num = matches!(self.ty(d.args[1]), MType::Val(s) if s.tags.subset_of(TagSet::NUMBER));
        let at = self.atom(name);
        let cache = self.atoms.next_prop_cache();
        let way = self.ic_addr(cache * INLINE_IC_STRIDE);
        let slow = self.body.add_block();
        let row = self.add_off(way, IC_TRANS_ROW_OFF);
        let shape = self.load_i32(obj, SHAPE_OFFSET);
        let old = self.load_i32(row, IC_TRANS_OLDSHAPE);
        let m_old = self.bin(Operator::I32Eq, old, shape, Type::I32);
        self.check(m_old, slow);
        let off = FIXED_SLOTS_BASE + 8 * i;
        let slot_off = self.load_i32(row, IC_TRANS_SLOTOFF);
        let want = self.i32c(off);
        let at_slot = self.bin(Operator::I32Eq, slot_off, want, Type::I32);
        self.check(at_slot, slow);
        for h in 0..IC_TRANS_PROTO_HOPS {
            let p = self.load_i32(row, IC_TRANS_PROTO0 + IC_TRANS_PROTO_ROW_BYTES * h);
            let empty = self.un(Operator::I32Eqz, p, Type::I32);
            let wv = self.load_i32(row, IC_TRANS_PROTO0 + IC_TRANS_PROTO_ROW_BYTES * h + 4);
            let live = self.load_i32(p, SHAPE_OFFSET);
            let same = self.bin(Operator::I32Eq, live, wv, Type::I32);
            let ok = self.bin(Operator::I32Or, empty, same, Type::I32);
            self.check(ok, slow);
        }
        // An add past the span (a field ahead of others in the row): the
        // slots it skips, which the new shape covers, hold undefined until
        // their fields come.
        for j in n.span()..i {
            let u = self.i64c(UNDEF);
            self.store_i64(obj, FIXED_SLOTS_BASE + 8 * j, u);
        }
        self.store_i64(obj, off, val);
        let new_s = self.load_i32(row, IC_TRANS_NEWSHAPE);
        self.store_i32(obj, SHAPE_OFFSET, new_s);
        if !num {
            let abs = self.load_i32(row, IC_TRANS_ABSSLOT);
            self.post_barrier(self.h.post_write_barrier, obj, abs, val);
        }
        // The word: the field in its set; RANGES dropped (no MIR claim
        // reads it). The word is the sentinel's, which no fact covers.
        let w = self.load_i32(obj, OBJ_CLASS_IDX_OFFSET);
        let keep = self.i32c(!CLASS_WORD_RANGES);
        let w = self.bin(Operator::I32And, w, keep, Type::I32);
        let w = if i < mir::types::FieldSet::WORD_BITS {
            let b = self.i32c(1 << i);
            self.bin(Operator::I32Or, w, b, Type::I32)
        } else {
            w
        };
        self.store_i32(obj, OBJ_CLASS_IDX_OFFSET, w);
        let t = self.edge(inst, 0, &[obj])?;
        self.terminate(Terminator::Br { target: t });
        self.cur = slow;
        let live = self.live_across(inst);
        let recv = self.box_tagged(TAG_OBJECT, obj);
        let bits = CLASS_WORD_SLOTS | if c.types { CLASS_WORD_SHALLOW } else { 0 };
        let (cv, sv, bv) = (self.i32c(cache), self.i32c(n.with(i).0), self.i32c(bits));
        let (ok, out) = self.gc_call(self.h.init_field, &[recv, at, val, cv, sv, bv], &live)?;
        self.epoch_same = None;
        let o2 = self.un(Operator::I32WrapI64, out, Type::I32);
        let t = self.edge(inst, 0, &[o2])?;
        let f = self.edge(inst, 1, &[])?;
        self.cond_br(ok, t, f);
        Ok(())
    }

    /// An element store's duty to the array stamp's claims on `obj`'s
    /// word (`ranges_duty` says it owes one): RANGES cleared, and TYPES
    /// where the word is an array's stamp, whose TYPES claims its
    /// elements. On any other object (BigInteger's digits are elements of
    /// a plain object) TYPES is its fields' claim, which an element store
    /// cannot touch.
    fn elem_duty(&mut self, obj: Value) {
        let w = self.load_i32(obj, OBJ_CLASS_IDX_OFFSET);
        let Some(min) = self.mm.array_key_min else {
            self.clear_bits(obj, w, CLASS_WORD_RANGES);
            return;
        };
        // A stamped word's identity (under the sentinel the low half is a
        // set of fields).
        let m16 = self.i32c(CLASS_WORD_SENTINEL | 0xFFFF);
        let idx = self.bin(Operator::I32And, w, m16, Type::I32);
        let lo = self.i32c(min);
        let hi = self.i32c(0xFFFF);
        let arr_lo = self.bin(Operator::I32GeU, idx, lo, Type::I32);
        let arr_hi = self.bin(Operator::I32LeU, idx, hi, Type::I32);
        let arr = self.bin(Operator::I32And, arr_lo, arr_hi, Type::I32);
        let (a, o, join) = (self.body.add_block(), self.body.add_block(), self.body.add_block());
        self.cond_br(arr, Self::to(a), Self::to(o));
        self.cur = a;
        self.clear_bits(obj, w, CLASS_WORD_RANGES | CLASS_WORD_SHALLOW);
        self.terminate(Terminator::Br { target: Self::to(join) });
        self.cur = o;
        self.clear_bits(obj, w, CLASS_WORD_RANGES);
        self.terminate(Terminator::Br { target: Self::to(join) });
        self.cur = join;
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
        // A demotion of a stamped word invalidates facts: bump the epoch
        // (not for a mid-construction sentinel word, which no fact
        // covers), as the runtime's `NightNoteDemotion`.
        let sent = self.i32c(CLASS_WORD_SENTINEL);
        let s = self.bin(Operator::I32And, w, sent, Type::I32);
        let (bump, after) = (self.body.add_block(), self.body.add_block());
        self.cond_br(s, Self::to(after), Self::to(bump));
        self.cur = bump;
        self.bump_epoch();
        self.terminate(Terminator::Br { target: Self::to(after) });
        self.cur = after;
        self.terminate(Terminator::Br { target: Self::to(done) });
        self.cur = done;
    }

    /// The construct `this` for a direct construct:
    /// with the site's cell describing the callee
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
        self.construct_this_with(top, callee, new_target, None, nslots, word)
    }

    /// `construct_this`, or with `proto` (`new_this`: the callee is its own
    /// new.target and its `prototype` is read) the cell's arm comparing it
    /// with the cell's prototype, and the `new_this` helper.
    fn construct_this_with(
        &mut self,
        top: Value,
        callee: Value,
        new_target: Value,
        proto: Option<Value>,
        nslots: u32,
        word: u32,
    ) -> Value {
        let done = self.body.add_block();
        let ok_p = self.body.add_blockparam(done, Type::I32);
        let (this_v, slow, cell) = self.construct_this_inline(callee, proto, word);
        self.store_i64(top, 0, this_v);
        let one = self.i32c(1);
        self.terminate(Terminator::Br {
            target: BlockTarget {
                block: done,
                args: vec![one],
            },
        });
        self.cur = slow;
        let made = self.construct_this_call(top, callee, new_target, proto, nslots, word, cell);
        self.terminate(Terminator::Br {
            target: BlockTarget {
                block: done,
                args: vec![made],
            },
        });
        self.cur = done;
        ok_p
    }

    /// `construct_this_with`'s helper call, in its slow block: the
    /// object from the runtime (which also fills the site's cell), at
    /// `top`; the status.
    fn construct_this_call(
        &mut self,
        top: Value,
        callee: Value,
        new_target: Value,
        proto: Option<Value>,
        nslots: u32,
        word: u32,
        cell: Value,
    ) -> Value {
        let (nv, wv) = (self.i32c(nslots), self.i32c(word));
        match proto {
            Some(p) => self.call1(self.h.new_this, &[self.cx, top, callee, p, nv, cell, wv], Type::I32),
            None => self.call1(
                self.h.create_this,
                &[self.cx, top, callee, new_target, nv, cell, wv],
                Type::I32,
            ),
        }
    }

    /// Bump `total` bytes off the nursery, or branch to `slow` where it has
    /// no room; returns the new cell's start (where its nursery header
    /// goes).
    fn nursery_bump(&mut self, total: Value, slow: Block) -> Value {
        let posp_slot = self.i32c(self.h.nursery_pos_slot);
        let posp = self.load_i32(posp_slot, 0);
        let pos = self.load_i32(posp, 0);
        let newpos = self.bin(Operator::I32Add, pos, total, Type::I32);
        let endp_slot = self.i32c(self.h.nursery_end_slot);
        let endp = self.load_i32(endp_slot, 0);
        let end = self.load_i32(endp, 0);
        let fits = self.bin(Operator::I32LeU, newpos, end, Type::I32);
        self.check(fits, slow);
        self.store_i32(posp, 0, newpos);
        pos
    }

    /// Whether row `cell` is armed (its word at `armed_off` nonzero) under
    /// the live property-IC generation (at `gen_off`); else `slow`.
    fn check_row(&mut self, cell: Value, armed_off: u32, gen_off: u32, slow: Block) -> Value {
        let armed = self.load_i32(cell, armed_off);
        let z = self.i32c(0);
        let filled = self.bin(Operator::I32Ne, armed, z, Type::I32);
        let cgen = self.load_i32(cell, gen_off);
        let gen_addr = self.i32c(self.h.prop_ic_gen_base);
        let live_gen = self.load_i32(gen_addr, 0);
        let g_ok = self.bin(Operator::I32Eq, cgen, live_gen, Type::I32);
        let hit = self.bin(Operator::I32And, filled, g_ok, Type::I32);
        self.check(hit, slow);
        armed
    }

    /// Copy `nbytes` (a multiple of 8, at least 8) from `src` to `dst`.
    fn copy_words(&mut self, dst: Value, src: Value, nbytes: Value) {
        let (lp, body, done) = (self.body.add_block(), self.body.add_block(), self.body.add_block());
        let off = self.body.add_blockparam(lp, Type::I32);
        let z = self.i32c(0);
        self.terminate(Terminator::Br { target: BlockTarget { block: lp, args: vec![z] } });
        self.cur = lp;
        let more = self.bin(Operator::I32LtU, off, nbytes, Type::I32);
        self.cond_br(more, Self::to(body), Self::to(done));
        self.cur = body;
        let s = self.bin(Operator::I32Add, src, off, Type::I32);
        let w = self.load_i64(s, 0);
        let d = self.bin(Operator::I32Add, dst, off, Type::I32);
        self.store_i64(d, 0, w);
        let eight = self.i32c(8);
        let next = self.bin(Operator::I32Add, off, eight, Type::I32);
        self.terminate(Terminator::Br { target: BlockTarget { block: lp, args: vec![next] } });
        self.cur = done;
    }

    /// `Lambda` inline from the site's row (`NightLambdaCell`): a nursery
    /// copy of the canonical function with environment `env` (boxed).
    /// Returns the boxed closure; `slow` where the row is not armed under
    /// the live generation or the nursery has no room.
    fn lambda_inline(&mut self, cell: Value, env: Value, slow: Block) -> Value {
        let tmpl = self.check_row(cell, LAMBDA_CELL_TEMPLATE, LAMBDA_CELL_GEN, slow);
        let total = self.load_i32(cell, 4);
        let pos = self.nursery_bump(total, slow);
        let hdr = self.load_i32(cell, 16);
        self.store_i32(pos, 0, hdr);
        let hb = self.i32c(NURSERY_HEADER_BYTES);
        let obj = self.bin(Operator::I32Add, pos, hb, Type::I32);
        let nbytes = self.bin(Operator::I32Sub, total, hb, Type::I32);
        self.copy_words(obj, tmpl, nbytes);
        self.store_i64(obj, FUNC_ENV_SLOT_OFFSET, env);
        let payload = self.un(Operator::I64ExtendI32U, obj, Type::I64);
        let tag = self.i64c(TAG_OBJECT << 32);
        self.bin(Operator::I64Or, payload, tag, Type::I64)
    }

    /// The prologue's CallObject inline from the script's row
    /// (`NightEnvCell`): enclosing environment the callee's, callee, then
    /// the bindings undefined. Returns it boxed; `slow` where the row is
    /// not armed under the live generation or the nursery has no room.
    fn env_inline(&mut self, cell: Value, slow: Block) -> Value {
        let span = self.check_row(cell, ENV_CELL_ARMED, ENV_CELL_GEN, slow);
        let total = self.load_i32(cell, 4);
        let pos = self.nursery_bump(total, slow);
        let hdr = self.load_i32(cell, 16);
        self.store_i32(pos, 0, hdr);
        let hb = self.i32c(NURSERY_HEADER_BYTES);
        let obj = self.bin(Operator::I32Add, pos, hb, Type::I32);
        let shape = self.load_i32(cell, 0);
        self.store_i32(obj, SHAPE_OFFSET, shape);
        let word = self.load_i32(cell, ENV_CELL_CLASS_WORD);
        self.store_i32(obj, OBJ_CLASS_IDX_OFFSET, word);
        let slotsw = self.load_i32(cell, 8);
        self.store_i32(obj, NATIVE_SLOTS_OFFSET, slotsw);
        let elemsw = self.load_i32(cell, 12);
        self.store_i32(obj, OBJ_ELEMENTS_OFFSET, elemsw);
        let callee = self.load_i64(self.sp, FrameLayout::CALLEE);
        let f = self.un(Operator::I32WrapI64, callee, Type::I32);
        let enclosing = self.load_i64(f, FUNC_ENV_SLOT_OFFSET);
        self.store_i64(obj, CALLOBJ_ENCLOSING_OFFSET, enclosing);
        self.store_i64(obj, CALLOBJ_CALLEE_OFFSET, callee);
        // The bindings, slots 2 up to the span: undefined.
        let (lp, body, done) = (self.body.add_block(), self.body.add_block(), self.body.add_block());
        let k = self.body.add_blockparam(lp, Type::I32);
        let two = self.i32c(2);
        self.terminate(Terminator::Br { target: BlockTarget { block: lp, args: vec![two] } });
        self.cur = lp;
        let more = self.bin(Operator::I32LtU, k, span, Type::I32);
        self.cond_br(more, Self::to(body), Self::to(done));
        self.cur = body;
        let three = self.i32c(3);
        let off = self.bin(Operator::I32Shl, k, three, Type::I32);
        let a = self.bin(Operator::I32Add, obj, off, Type::I32);
        let undef = self.i64c(UNDEF);
        self.store_i64(a, FIXED_SLOTS_BASE, undef);
        let one = self.i32c(1);
        let next = self.bin(Operator::I32Add, k, one, Type::I32);
        self.terminate(Terminator::Br { target: BlockTarget { block: lp, args: vec![next] } });
        self.cur = done;
        let payload = self.un(Operator::I64ExtendI32U, obj, Type::I64);
        let tag = self.i64c(TAG_OBJECT << 32);
        self.bin(Operator::I64Or, payload, tag, Type::I64)
    }

    /// `construct_this_with`'s inline half: with the site's cell
    /// describing the callee (and its `.prototype`), bump-allocate the
    /// object in the nursery and fill its header. Leaves the current
    /// block at the success point with the boxed object; returns it, the
    /// (empty) slow block every miss branches to, and the cell. Runs no
    /// code and cannot GC: the slow block's helper call can.
    fn construct_this_inline(&mut self, callee: Value, proto: Option<Value>, word: u32) -> (Value, Block, Value) {
        let cell = self.i32c(CONSTRUCT_CELL_ADDR_PLACEHOLDER);
        let idx = self.atoms.next_construct_cell();
        self.construct_cell_patches.push((cell, idx + 1));
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
        // With the prototype given, the cell's shape is the object's for
        // it, whoever the callee's shape is.
        let hit = if proto.is_some() { filled } else { self.bin(Operator::I32And, filled, s_ok, Type::I32) };
        let hit = self.bin(Operator::I32And, hit, g_ok, Type::I32);
        self.check(hit, slow);
        let pval = match proto {
            Some(p) => p,
            None => {
                // A reassigned `.prototype` keeps the callee's shape.
                let enc = self.load_i32(cell, CONSTRUCT_CELL_PROTOSLOTENC);
                let one = self.i32c(1);
                let dynamic = self.bin(Operator::I32And, enc, one, Type::I32);
                let not1 = self.i32c(!1);
                let off = self.bin(Operator::I32And, enc, not1, Type::I32);
                let slots = self.load_i32(cptr, NATIVE_SLOTS_OFFSET);
                let sb = self.select(Type::I32, slots, cptr, dynamic);
                let addr = self.bin(Operator::I32Add, sb, off, Type::I32);
                self.load_i64(addr, 0)
            }
        };
        let pt = self.tag_of(pval);
        let p_obj = self.tag_is(pt, TAG_OBJECT as u32);
        let pptr = self.un(Operator::I32WrapI64, pval, Type::I32);
        let cproto = self.load_i32(cell, CONSTRUCT_CELL_PROTOPTR);
        let p_eq = self.bin(Operator::I32Eq, pptr, cproto, Type::I32);
        let p_ok = self.bin(Operator::I32And, p_obj, p_eq, Type::I32);
        self.check(p_ok, slow);
        // Room in the nursery, then bump and fill the header.
        let total = self.load_i32(cell, 4);
        let pos = self.nursery_bump(total, slow);
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
        (this_v, slow, cell)
    }

    /// `new_this.init`'s inline arm: with the site's construct cell's final
    /// part armed under the live IC generation, `proto` its prototype, and
    /// the prototype chain's shapes as recorded (no setter or read-only
    /// property of the fields' names added since), a nursery bump with the
    /// final shape, the class word (RANGES cleared, as the adds leave it),
    /// and the fields `xs` in their fixed slots (no barriers: the object is
    /// in the nursery, and new). Returns the object, the miss block and the
    /// cell.
    fn construct_this_final(&mut self, proto: Value, word: u32, xs: &[Value]) -> (Value, Block, Value) {
        let cell = self.i32c(CONSTRUCT_CELL_ADDR_PLACEHOLDER);
        let idx = self.atoms.next_construct_cell();
        self.construct_cell_patches.push((cell, idx + 1));
        let slow = self.body.add_block();
        let fshape = self.load_i32(cell, CONSTRUCT_CELL_FINALSHAPE);
        let cgen = self.load_i32(cell, CONSTRUCT_CELL_GEN);
        let gen_addr = self.i32c(self.h.prop_ic_gen_base);
        let live_gen = self.load_i32(gen_addr, 0);
        let z = self.i32c(0);
        let filled = self.bin(Operator::I32Ne, fshape, z, Type::I32);
        let g_ok = self.bin(Operator::I32Eq, cgen, live_gen, Type::I32);
        let hit = self.bin(Operator::I32And, filled, g_ok, Type::I32);
        self.check(hit, slow);
        let pt = self.tag_of(proto);
        let p_obj = self.tag_is(pt, TAG_OBJECT as u32);
        let pptr = self.un(Operator::I32WrapI64, proto, Type::I32);
        let cproto = self.load_i32(cell, CONSTRUCT_CELL_PROTOPTR);
        let p_eq = self.bin(Operator::I32Eq, pptr, cproto, Type::I32);
        let p_ok = self.bin(Operator::I32And, p_obj, p_eq, Type::I32);
        self.check(p_ok, slow);
        let ps = self.load_i32(pptr, SHAPE_OFFSET);
        let cps = self.load_i32(cell, CONSTRUCT_CELL_PROTOSHAPE);
        let ps_ok = self.bin(Operator::I32Eq, ps, cps, Type::I32);
        self.check(ps_ok, slow);
        let p2 = self.load_i32(cell, CONSTRUCT_CELL_PROTO2PTR);
        let (has2, done2) = (self.body.add_block(), self.body.add_block());
        self.cond_br(p2, Self::to(has2), Self::to(done2));
        self.cur = has2;
        let p2s = self.load_i32(p2, SHAPE_OFFSET);
        let cp2s = self.load_i32(cell, CONSTRUCT_CELL_PROTO2SHAPE);
        let p2_ok = self.bin(Operator::I32Eq, p2s, cp2s, Type::I32);
        self.check(p2_ok, slow);
        self.terminate(Terminator::Br { target: Self::to(done2) });
        self.cur = done2;
        let total = self.load_i32(cell, 4);
        let pos = self.nursery_bump(total, slow);
        let hdr = self.load_i32(cell, 16);
        self.store_i32(pos, 0, hdr);
        let hb = self.i32c(NURSERY_HEADER_BYTES);
        let obj = self.bin(Operator::I32Add, pos, hb, Type::I32);
        self.store_i32(obj, SHAPE_OFFSET, fshape);
        // The fields' set with them.
        let set = mir::types::FieldSet::prefix(u32::try_from(xs.len()).unwrap());
        let wv = self.i32c((word & !CLASS_WORD_RANGES) | set.word_bits());
        self.store_i32(obj, OBJ_CLASS_IDX_OFFSET, wv);
        let slotsw = self.load_i32(cell, 8);
        self.store_i32(obj, NATIVE_SLOTS_OFFSET, slotsw);
        let elemsw = self.load_i32(cell, 12);
        self.store_i32(obj, OBJ_ELEMENTS_OFFSET, elemsw);
        for (i, &x) in xs.iter().enumerate() {
            self.store_i64(obj, FIXED_SLOTS_BASE + 8 * u32::try_from(i).unwrap(), x);
        }
        (obj, slow, cell)
    }

    /// `lhs instanceof rhs` inline, taking
    /// `ok_clean`: with the site's cell describing `rhs` (its shape, under
    /// the live IC generation), read its `.prototype` from the cached slot
    /// and walk `lhs`'s prototype chain (bounded) for it. Anything else
    /// falls through to the helper, which also fills the cell.
    fn instanceof_arms(&mut self, inst: mir::Inst, lhs: Value, rhs: Value, cell: Value) -> R<()> {
        let slow = self.body.add_block();
        // (An object by its type: a predicted global's function, say.)
        if !value_tags(&self.ty(self.f.insts[inst].args[1])).is_nonempty_subset_of(TagSet::OBJECT) {
            let rt = self.tag_of(rhs);
            let r_obj = self.tag_is(rt, TAG_OBJECT as u32);
            self.check(r_obj, slow);
        }
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
    /// Element `key` (a boxed int32) of `recv` (boxed), an arguments
    /// object whose element is neither overridden nor forwarded to a call
    /// object (as `ArgumentsObject::element`): its data's slot;
    /// anything else branches to `fail`.
    fn args_element(&mut self, recv: Value, key: Value, fail: Block) -> Value {
        let tag = self.tag_of(recv);
        let is_obj = self.tag_is(tag, TAG_OBJECT as u32);
        let ktag = self.tag_of(key);
        let is_int = self.tag_is(ktag, TAG_INT32 as u32);
        let both = self.bin(Operator::I32And, is_obj, is_int, Type::I32);
        self.check(both, fail);
        let obj = self.un(Operator::I32WrapI64, recv, Type::I32);
        let shape = self.load_i32(obj, SHAPE_OFFSET);
        let base = self.load_i32(shape, SHAPE_BASESHAPE_OFFSET);
        let clasp = self.load_i32(base, BASESHAPE_CLASP_OFFSET);
        let acbase = self.i32c(self.h.args_class_base);
        let mapped = self.load_i32(acbase, 0);
        let unmapped = self.load_i32(acbase, 4);
        let m = self.bin(Operator::I32Eq, clasp, mapped, Type::I32);
        let u = self.bin(Operator::I32Eq, clasp, unmapped, Type::I32);
        let is_args = self.bin(Operator::I32Or, m, u, Type::I32);
        self.check(is_args, fail);
        // Packed in fixed slot 0: the length above bit 5; bit 2, an
        // element overridden.
        let packed = self.load_i32(obj, FIXED_SLOTS_BASE);
        let four = self.i32c(4);
        let over = self.bin(Operator::I32And, packed, four, Type::I32);
        let kept = self.un(Operator::I32Eqz, over, Type::I32);
        let five = self.i32c(5);
        let len = self.bin(Operator::I32ShrU, packed, five, Type::I32);
        let idx = self.un(Operator::I32WrapI64, key, Type::I32);
        let inb = self.bin(Operator::I32LtU, idx, len, Type::I32);
        let ok = self.bin(Operator::I32And, kept, inb, Type::I32);
        self.check(ok, fail);
        // The data (fixed slot 1's private pointer), its args at the
        // engine's offset.
        let data = self.load_i32(obj, FIXED_SLOTS_BASE + 8);
        let eoff = self.load_i32(acbase, 8);
        let elems = self.bin(Operator::I32Add, data, eoff, Type::I32);
        let eight = self.i32c(8);
        let off = self.bin(Operator::I32Mul, idx, eight, Type::I32);
        let addr = self.bin(Operator::I32Add, elems, off, Type::I32);
        let v = self.load_i64(addr, 0);
        // A forwarded (mapped, aliased) element is magic.
        let vt = self.tag_of(v);
        let magic = self.tag_is(vt, TAG_MAGIC as u32);
        let plain = self.un(Operator::I32Eqz, magic, Type::I32);
        self.check(plain, fail);
        v
    }

    /// `s[i]` of a linear latin1 string (boxed) and an in-bounds int32
    /// index (boxed): the unit string from the static strings table;
    /// anything else branches to `fail`.
    fn string_char(&mut self, recv: Value, key: Value, fail: Block) -> Value {
        let tag = self.tag_of(recv);
        let is_str = self.tag_is(tag, TAG_STRING as u32);
        let ktag = self.tag_of(key);
        let is_int = self.tag_is(ktag, TAG_INT32 as u32);
        let both = self.bin(Operator::I32And, is_str, is_int, Type::I32);
        self.check(both, fail);
        let s = self.un(Operator::I32WrapI64, recv, Type::I32);
        let flags = self.load_i32(s, STRING_FLAGS_OFFSET);
        let want = self.i32c(STRING_LINEAR_BIT | STRING_LATIN1_CHARS_BIT);
        let masked = self.bin(Operator::I32And, flags, want, Type::I32);
        let lin = self.bin(Operator::I32Eq, masked, want, Type::I32);
        let len = self.load_i32(s, STRING_LENGTH_OFFSET);
        let idx = self.un(Operator::I32WrapI64, key, Type::I32);
        let inb = self.bin(Operator::I32LtU, idx, len, Type::I32);
        let ok = self.bin(Operator::I32And, lin, inb, Type::I32);
        self.check(ok, fail);
        let ib = self.i32c(STRING_INLINE_CHARS_BIT);
        let inline = self.bin(Operator::I32And, flags, ib, Type::I32);
        let heap = self.load_i32(s, STRING_CHARS_OFFSET);
        let here = self.add_off(s, STRING_CHARS_OFFSET);
        let chars = self.select(Type::I32, here, heap, inline);
        let at = self.bin(Operator::I32Add, chars, idx, Type::I32);
        let m = self.mem(0, 0);
        let c = self.un(Operator::I32Load8U { memory: m }, at, Type::I32);
        let tslot = self.i32c(self.h.static_strings_slot);
        let tbl = self.load_i32(tslot, 0);
        let two = self.i32c(2);
        let off = self.bin(Operator::I32Shl, c, two, Type::I32);
        let ea = self.bin(Operator::I32Add, tbl, off, Type::I32);
        let atom = self.load_i32(ea, 0);
        self.box_tagged(TAG_STRING, atom)
    }

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

    /// A dense append, or a store into a hole, call-free: with
    /// `night_elem_append_check` proving it
    /// legal (the receiver's shape in the append cache, its prototypes
    /// holding no indexed property, room left) and returning the element's
    /// address, store it and, for an append, bump the initialized length,
    /// and an Array's length when the index passes it; taking `ok_clean`.
    /// Else `miss`.
    fn elem_append_arm(&mut self, inst: mir::Inst, recv: Value, key: Value, val: Value, duty: bool, num: bool, miss: Block) -> R<()> {
        let tag = self.tag_of(recv);
        let is_obj = self.tag_is(tag, TAG_OBJECT as u32);
        let ktag = self.tag_of(key);
        let is_int = self.tag_is(ktag, TAG_INT32 as u32);
        let both = self.bin(Operator::I32And, is_obj, is_int, Type::I32);
        self.check(both, miss);
        let obj = self.un(Operator::I32WrapI64, recv, Type::I32);
        let elements = self.load_i32(obj, OBJ_ELEMENTS_OFFSET);
        let initlen = self.elem_header(elements, ELEMENTS_INITLEN_BACK);
        let idx = self.un(Operator::I32WrapI64, key, Type::I32);
        let packed = self.call1(self.h.elem_append_check, &[obj, elements, initlen, idx], Type::I64);
        let z = self.i64c(0);
        let ok = self.bin(Operator::I64Ne, packed, z, Type::I32);
        self.check(ok, miss);
        let addr = self.un(Operator::I32WrapI64, packed, Type::I32);
        let sh = self.i64c(32);
        let row = self.bin(Operator::I64ShrU, packed, sh, Type::I64);
        let row = self.un(Operator::I32WrapI64, row, Type::I32);
        if duty {
            self.elem_duty(obj);
        }
        // A hole or the space past the initialized length holds no GC
        // thing: no pre-barrier.
        self.store_i64(addr, 0, val);
        let is_app = self.bin(Operator::I32Eq, idx, initlen, Type::I32);
        let (bump, done) = (self.body.add_block(), self.body.add_block());
        self.cond_br(is_app, Self::to(bump), Self::to(done));
        self.cur = bump;
        let one = self.i32c(1);
        let n = self.bin(Operator::I32Add, idx, one, Type::I32);
        self.set_elem_header(elements, ELEMENTS_INITLEN_BACK, n);
        let len = self.elem_header(elements, ELEMENTS_LENGTH_BACK);
        let passes = self.bin(Operator::I32GeU, idx, len, Type::I32);
        // The length word is an Array's (the row's isArray, from its prime).
        let is_arr = self.load_i32(row, 20);
        let both = self.bin(Operator::I32And, passes, is_arr, Type::I32);
        let lb = self.body.add_block();
        self.cond_br(both, Self::to(lb), Self::to(done));
        self.cur = lb;
        self.set_elem_header(elements, ELEMENTS_LENGTH_BACK, n);
        self.terminate(Terminator::Br { target: Self::to(done) });
        self.cur = done;
        if !num {
            let f = self.h.post_write_barrier_elem;
            self.post_barrier(f, obj, idx, val);
        }
        let t = self.edge(inst, 0, &[])?;
        self.terminate(Terminator::Br { target: t });
        Ok(())
    }

    /// Whether `inst` is at a polymorphic typed-array site.
    fn ta_poly(&self, inst: mir::Inst) -> bool {
        self.f.insts[inst].attach.is_some_and(|a| self.f.attachments[a].ta_poly)
    }

    /// Boxed `recv` as an object pointer and `key` as an int32, else
    /// `miss`.
    fn obj_int(&mut self, recv: Value, key: Value, miss: Block) -> (Value, Value) {
        let tag = self.tag_of(recv);
        let is_obj = self.tag_is(tag, TAG_OBJECT as u32);
        let ktag = self.tag_of(key);
        let is_int = self.tag_is(ktag, TAG_INT32 as u32);
        let both = self.bin(Operator::I32And, is_obj, is_int, Type::I32);
        self.check(both, miss);
        let obj = self.un(Operator::I32WrapI64, recv, Type::I32);
        let idx = self.un(Operator::I32WrapI64, key, Type::I32);
        (obj, idx)
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
    /// The op's frame's actuals: where its callee, `this` and actuals
    /// start, and its actual count. An inlined callee's are its inline
    /// frame's, its count the call's (`InlineFrame::argc`).
    fn actuals(&mut self) -> (Value, Value) {
        let fid = self.cur_frame as usize;
        if fid == 0 {
            return (self.sp, self.argc);
        }
        let fr = &self.f.inline_frames[fid - 1];
        let n = fr.argc.unwrap_or(fr.shape.formals);
        let base = self.add_off(self.vp, self.frame_off[fid]);
        (base, self.i32c(n))
    }

    /// The op's frame's env slot offset from `vp`.
    fn frame_env_off(&self) -> u32 {
        let fid = self.cur_frame as usize;
        self.frame_voff[fid] + self.frame_layouts[fid].env()
    }

    /// The op's frame's current environment (boxed), from its env slot.
    fn frame_env(&mut self) -> Value {
        let fid = self.cur_frame as usize;
        if self.fixed[fid] == Fixed::None {
            // Not in the frame: the callee's own (an inlined callee has no
            // activation environment of its own).
            let callee = self.load_i64(self.vp, self.frame_off[fid] + FrameLayout::CALLEE);
            let fun = self.un(Operator::I32WrapI64, callee, Type::I32);
            return self.load_i64(fun, FUNC_ENV_SLOT_OFFSET);
        }
        let off = self.frame_env_off();
        self.load_i64(self.vp, off)
    }

    /// A direct `eval` (baseline's `Eval`): the call's frame
    /// `[callee, this, args]` above the live values, and the helper, which
    /// evaluates in the frame's environment (or calls a callee that is not
    /// `eval`).
    fn js_eval_op(&mut self, inst: mir::Inst, ops: &[Value], pc: u32) -> R<()> {
        let live = self.live_across(inst);
        self.root(&live)?;
        let call_pre = self.epoch();
        let frame = self.top_off(live.len());
        for (k, &v) in ops.iter().enumerate() {
            self.store_i64(self.vp, frame + 8 * u32::try_from(k).unwrap(), v);
        }
        let argc = u32::try_from(ops.len() - 2).unwrap();
        let top_off = frame + 8 * (argc + 2);
        let base = self.add_off(self.vp, frame);
        let top = self.add_off(self.vp, top_off);
        let av = self.i32c(argc);
        let env = self.frame_env();
        let script = self.script_ptr();
        let pcv = self.i32c(pc);
        let ok = self.call1(self.h.eval, &[self.cx, top, base, av, env, script, pcv], Type::I32);
        self.after_gc(&live);
        let result = self.load_i64(self.vp, top_off);
        let post = self.epoch();
        let same = self.bin(Operator::I32Eq, call_pre, post, Type::I32);
        self.clean_or_dirty(inst, ok, same, &[result])
    }

    fn js_call_op(&mut self, inst: mir::Inst, ops: &[Value], iter: bool) -> R<()> {
        /// Headroom a compiled body may use past its actuals (the runtime
        /// entries' `kNightStackHeadroomSlots`).
        const HEADROOM: u32 = 64 * 1024;
        // A callee whose type proves its script (a predicted global's
        // read, a guarded closure): a compiled body (what proved it tested
        // that), no native, its table index in its script.
        let proven = match self.ty(self.f.insts[inst].args[0]) {
            MType::Val(v) if v.tags.is_nonempty_subset_of(TagSet::OBJECT) => match v.obj.kind {
                ObjKind::Function(Some(k)) => self.mm.script_addrs.get(&k).copied(),
                _ => None,
            },
            _ => None,
        };
        if let Some(addr) = proven.filter(|_| PROVEN_CALLS) {
            return self.js_call_proven(inst, ops, iter, addr, HEADROOM);
        }
        if ops.len() == 3 && !iter {
            let call = self.body.add_block();
            self.char_arms(inst, ops, call)?;
            self.cur = call;
        }
        if (3..=3 + PUSH_ARM_MAX_EXTRA).contains(&ops.len()) && !iter && self.names_atom("push") {
            let call = self.body.add_block();
            self.push_arm(inst, ops, call)?;
            self.cur = call;
        }
        if ops.len() == 3 && !iter && self.names_atom("get") {
            let call = self.body.add_block();
            self.map_get_arm(inst, ops, call)?;
            self.cur = call;
        }
        if ops.len() == 3 && !iter && (self.names_atom("exec") || self.names_atom("test")) {
            let call = self.body.add_block();
            self.regexp_arm(inst, ops, call)?;
            self.cur = call;
        }
        if ops.len() == 2 && !iter && self.names_atom("pop") {
            let call = self.body.add_block();
            self.pop_arm(inst, ops, call)?;
            self.cur = call;
        }
        // A leaf: nothing to root yet.
        let (funcidx, script, native) = self.classify_native(ops[0]);
        if (ops.len() == 3 || ops.len() == 4) && !iter {
            let call = self.body.add_block();
            self.math_arms(inst, ops, native, call)?;
            self.cur = call;
        }
        let live = self.live_across(inst);
        self.root(&live)?;
        let call_pre = self.epoch();
        let frame = self.top_off(live.len());
        for (k, &v) in ops.iter().enumerate() {
            self.store_i64(self.vp, frame + 8 * u32::try_from(k).unwrap(), v);
        }
        let argc = u32::try_from(ops.len() - 2).unwrap();
        let top_off = frame + 8 * (argc + 2);
        let base = self.add_off(self.vp, frame);
        let top = self.add_off(self.vp, top_off);
        let z = self.i32c(0);
        let fits = self.stack_fits(top, HEADROOM);
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
        // The site's likely callees (one, or a guard
        // chain for a small polymorphic set): each one's table index (a
        // patched const; `u32::MAX` while uncompiled, so the arm is dead)
        // against the classified funcidx, and on a match a static `call`
        // of its body, which wasmtime may inline.
        let likely: Vec<u32> = self.f.insts[inst]
            .attach
            .map(|a| self.f.attachments[a].targets.iter().map(|k| k.get()).collect())
            .unwrap_or_default();
        for sid in likely {
            let expected = self.i32c(u32::MAX);
            let is_likely = self.bin(Operator::I32Eq, funcidx, expected, Type::I32);
            let (likely_b, indirect_b) = (self.body.add_block(), self.body.add_block());
            self.cond_br(is_likely, Self::to(likely_b), Self::to(indirect_b));
            self.cur = likely_b;
            let args = self
                .body
                .arg_pool
                .from_iter([self.cx, base, argc_v, top, script, undef].into_iter());
            let tys = self.body.type_pool.from_iter([Type::I32, Type::I32].into_iter());
            let call = self.push_val(ValueDef::Operator(
                Operator::Call {
                    function_index: self.h.direct_call_stub2,
                },
                args,
                tys,
            ));
            self.likely_patches.push((expected, call, sid));
            let err = self.push_val(ValueDef::PickOutput(call, 0, Type::I32));
            let ok_likely = self.un(Operator::I32Eqz, err, Type::I32);
            self.terminate(Terminator::Br {
                target: BlockTarget {
                    block: join,
                    args: vec![ok_likely],
                },
            });
            self.cur = indirect_b;
        }
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
        if NATIVE_ROUTE {
            // A native callee (the classify proved a function with no
            // script) goes straight to its JSNative;
            // `native_dispatch` punts the natives that need the generic
            // call's handling back to it.
            let (nat_b, gen_b) = (self.body.add_block(), self.body.add_block());
            self.cond_br(native, Self::to(nat_b), Self::to(gen_b));
            self.cur = nat_b;
            let ok_nat = self.call1(self.h.native_dispatch, &[self.cx, top, base, argc_v], Type::I32);
            self.terminate(Terminator::Br {
                target: BlockTarget {
                    block: join,
                    args: vec![ok_nat],
                },
            });
            self.cur = gen_b;
        }
        // An iterator method's call reports an uncallable callee as the
        // iterator protocol does.
        let generic_f = if iter { self.h.call_iter } else { self.h.call };
        let ok_generic = self.call1(generic_f, &[self.cx, top, base, argc_v], Type::I32);
        self.terminate(Terminator::Br {
            target: BlockTarget {
                block: join,
                args: vec![ok_generic],
            },
        });

        self.cur = join;
        self.after_gc(&live);
        let result = self.load_i64(self.vp, top_off);
        let post = self.epoch();
        let same = self.bin(Operator::I32Eq, call_pre, post, Type::I32);
        self.clean_or_dirty(inst, ok, same, &[result])
    }

    /// `js_call_op` for a callee of a known compiled script at `addr`: no
    /// native arms and no classify; the script's table index, and the
    /// site's static call of that body where it is the one the site
    /// predicts. (Such a callee is never a class constructor, whose call
    /// throws: no binding predicts one.)
    fn js_call_proven(&mut self, inst: mir::Inst, ops: &[Value], iter: bool, addr: u32, headroom: u32) -> R<()> {
        let live = self.live_across(inst);
        self.root(&live)?;
        let call_pre = self.epoch();
        let frame = self.top_off(live.len());
        for (k, &v) in ops.iter().enumerate() {
            self.store_i64(self.vp, frame + 8 * u32::try_from(k).unwrap(), v);
        }
        let argc = u32::try_from(ops.len() - 2).unwrap();
        let top_off = frame + 8 * (argc + 2);
        let base = self.add_off(self.vp, frame);
        let top = self.add_off(self.vp, top_off);
        let fits = self.stack_fits(top, headroom);
        let (direct_b, generic_b, join) = (self.body.add_block(), self.body.add_block(), self.body.add_block());
        let ok = self.body.add_blockparam(join, Type::I32);
        self.cond_br(fits, Self::to(direct_b), Self::to(generic_b));

        self.cur = direct_b;
        let script = self.i32c(addr);
        let funcidx = self.load_i32(script, BASESCRIPT_NIGHTFUNCINDEX_OFFSET);
        let argc_v = self.i32c(argc);
        let undef = self.i64c(UNDEF);
        let likely: Vec<u32> = self.f.insts[inst]
            .attach
            .map(|a| self.f.attachments[a].targets.iter().map(|k| k.get()).collect())
            .unwrap_or_default();
        if let Some(&sid) = likely.first().filter(|_| likely.len() == 1) {
            let expected = self.i32c(u32::MAX);
            let is_likely = self.bin(Operator::I32Eq, funcidx, expected, Type::I32);
            let (likely_b, indirect_b) = (self.body.add_block(), self.body.add_block());
            self.cond_br(is_likely, Self::to(likely_b), Self::to(indirect_b));
            self.cur = likely_b;
            let args = self.body.arg_pool.from_iter([self.cx, base, argc_v, top, script, undef].into_iter());
            let tys = self.body.type_pool.from_iter([Type::I32, Type::I32].into_iter());
            let call = self.push_val(ValueDef::Operator(
                Operator::Call {
                    function_index: self.h.direct_call_stub2,
                },
                args,
                tys,
            ));
            self.likely_patches.push((expected, call, sid));
            let err = self.push_val(ValueDef::PickOutput(call, 0, Type::I32));
            let ok_likely = self.un(Operator::I32Eqz, err, Type::I32);
            self.terminate(Terminator::Br {
                target: BlockTarget {
                    block: join,
                    args: vec![ok_likely],
                },
            });
            self.cur = indirect_b;
        }
        let off = self.i32c(u32::MAX);
        self.body_off_patches.push(off);
        let body_idx = self.bin(Operator::I32Sub, funcidx, off, Type::I32);
        let args = self.body.arg_pool.from_iter([self.cx, base, argc_v, top, script, undef, body_idx].into_iter());
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
        let ok_direct = self.un(Operator::I32Eqz, err, Type::I32);
        self.terminate(Terminator::Br {
            target: BlockTarget {
                block: join,
                args: vec![ok_direct],
            },
        });

        // Out of stack: the generic call, which reports the overflow.
        self.cur = generic_b;
        let argc_v = self.i32c(argc);
        let generic_f = if iter { self.h.call_iter } else { self.h.call };
        let ok_generic = self.call1(generic_f, &[self.cx, top, base, argc_v], Type::I32);
        self.terminate(Terminator::Br {
            target: BlockTarget {
                block: join,
                args: vec![ok_generic],
            },
        });

        self.cur = join;
        self.after_gc(&live);
        let result = self.load_i64(self.vp, top_off);
        let post = self.epoch();
        let same = self.bin(Operator::I32Eq, call_pre, post, Type::I32);
        self.clean_or_dirty(inst, ok, same, &[result])
    }

    /// An object or array literal (`array_len`) from the site's
    /// inline-alloc cell: with the cell filled
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

    /// `InitProp` on a literal under construction:
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
        let row = self.ic_addr(cache * INLINE_IC_STRIDE + IC_TRANS_ROW_OFF);
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

    /// Native `Math` calls on numbers, matched by the callee's
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

    /// `InitElemArray index` filling an array literal:
    /// with a value that is not the hole, dense elements with no flag but
    /// FIXED, and the initialized length at `index` with room, store (with
    /// the post-barrier a tenured literal owes a nursery value) and bump it
    /// (clearing RANGES under the store's `duty`), taking `ok_clean`;
    /// `cur` is left on the miss.
    fn init_elem_inline(&mut self, inst: mir::Inst, arr: Value, index: u32, val: Value, duty: bool) -> R<()> {
        use crate::wasm::mir::abi::ELEMENTS_FLAG_FIXED;
        let slow = self.body.add_block();
        let vt = self.tag_of(val);
        let magic = self.i32c(TAG_MAGIC as u32);
        let v_ok = self.bin(Operator::I32Ne, vt, magic, Type::I32);
        let at = self.tag_of(arr);
        let a_obj = self.tag_is(at, TAG_OBJECT as u32);
        let ok = self.bin(Operator::I32And, v_ok, a_obj, Type::I32);
        self.check(ok, slow);
        let obj = self.un(Operator::I32WrapI64, arr, Type::I32);
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
        if duty {
            self.elem_duty(obj);
        }
        self.store_i64(elems, index * 8, val);
        let nl = self.i32c(index + 1);
        self.set_elem_header(elems, ELEMENTS_INITLEN_BACK, nl);
        if !value_tags(&self.ty(self.f.insts[inst].args[2])).subset_of(GC_FREE_TAGS) {
            let f = self.h.post_write_barrier_elem;
            self.post_barrier(f, obj, iv, val);
        }
        let t = self.edge(inst, 0, &[])?;
        self.terminate(Terminator::Br { target: t });
        self.cur = slow;
        Ok(())
    }

    /// Whether the function names atom `s` (a builtin arm's gate: an arm
    /// costs code where it never fires).
    fn names_atom(&self, s: &str) -> bool {
        self.mm.atoms.iter().any(|(_, a)| a.chars().iter().copied().eq(s.encode_utf16()))
    }

    /// Whether boxed `callee` is the pristine builtin of cell `idx`.
    fn builtin_is(&mut self, callee: Value, idx: u32) -> Value {
        let c = self.i32c(self.h.builtin_cells_base + 8 * idx);
        let bits = self.load_i64(c, 0);
        self.bin(Operator::I64Eq, callee, bits, Type::I32)
    }

    /// `Array.prototype.push(v, ...)` on a dense array, call-free: with
    /// the elements packed, room left for every argument, and the
    /// receiver's shape in the append cache with its protos' shapes
    /// unchanged (no indexed property can appear on them), store them at
    /// the end and bump the initialized length and `length`, taking
    /// `ok_clean` with the new length; else `other`.
    fn push_arm(&mut self, inst: mir::Inst, ops: &[Value], other: Block) -> R<()> {
        let (callee, this, args) = (ops[0], ops[1], &ops[2..]);
        let n = u32::try_from(args.len()).unwrap();
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
        // `cap - initlen >= n` (initlen <= cap always).
        let room = self.bin(Operator::I32Sub, cap, initlen, Type::I32);
        let nv = self.i32c(n);
        let has_cap = self.bin(Operator::I32GeU, room, nv, Type::I32);
        let imax = self.i32c(0x7FFF_FFFF - n);
        let fits = self.bin(Operator::I32LeU, len, imax, Type::I32);
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
        // A stamped array's element claims (RANGES, TYPES) hold for a value
        // no site proves here: dropped (the array stamp's store duty).
        self.elem_duty(obj);
        for (k, &arg) in args.iter().enumerate() {
            self.store_i64(addr, 8 * u32::try_from(k).unwrap(), arg);
        }
        let newlen = self.bin(Operator::I32Add, initlen, nv, Type::I32);
        self.set_elem_header(elements, ELEMENTS_INITLEN_BACK, newlen);
        self.set_elem_header(elements, ELEMENTS_LENGTH_BACK, newlen);
        let f = self.h.post_write_barrier_elem;
        for (k, &arg) in args.iter().enumerate() {
            let kv = self.i32c(u32::try_from(k).unwrap());
            let idx = self.bin(Operator::I32Add, initlen, kv, Type::I32);
            self.post_barrier(f, obj, idx, arg);
        }
        let r = self.box_tagged(TAG_INT32, newlen);
        let t = self.edge(inst, 0, &[r])?;
        self.terminate(Terminator::Br { target: t });
        Ok(())
    }

    /// The pristine `RegExp.prototype.exec(s)` / `.test(s)` decided by the
    /// runtime's leaf (a non-global, non-sticky regexp with an AOT matcher:
    /// no frame, no GC, the heap untouched), taking `ok_clean` with the
    /// result; else `other` (which also builds a successful exec's result).
    fn regexp_arm(&mut self, inst: mir::Inst, ops: &[Value], other: Block) -> R<()> {
        let (callee, this, s) = (ops[0], ops[1], ops[2]);
        let is_exec = self.builtin_is(callee, BC_REGEXP_EXEC);
        let is_test = self.builtin_is(callee, BC_REGEXP_TEST);
        let either = self.bin(Operator::I32Or, is_exec, is_test, Type::I32);
        self.check(either, other);
        let leaf = self.body.add_block();
        if REGEXP_NO_MATCH_ARM {
            self.regexp_no_match(inst, this, s, is_test, leaf)?;
        } else {
            self.terminate(Terminator::Br { target: Self::to(leaf) });
        }
        self.cur = leaf;
        let r = self.call1(self.h.regexp_leaf, &[self.cx, this, s, is_test], Type::I64);
        let tag = self.tag_of(r);
        let miss = self.tag_is(tag, TAG_MAGIC as u32);
        let t = self.edge(inst, 0, &[r])?;
        self.cond_br(miss, Self::to(other), t);
        Ok(())
    }

    /// The no-match half of `re.exec(s)` / `re.test(s)` (the builtins),
    /// taking edge 0 with `null` / `false`: where `re` has the optimizable
    /// regexp shape the leaf armed (a plain RegExpObject of this realm's
    /// prototype, no own properties but `lastIndex`) and the prototype's
    /// fuse is intact, its `lastIndex` is a number (reading it runs
    /// nothing), its shared has a row (armed only for one neither global nor
    /// sticky, with AOT matchers), and `s` is a linear string, the matcher
    /// runs here, as the JIT's RegExp stubs call theirs. A failed match
    /// changes nothing (no statics, no `lastIndex`), so that answer is
    /// final; a match or a retry goes to `leaf`, which runs it again and
    /// builds what a match needs.
    fn regexp_no_match(&mut self, inst: mir::Inst, re: Value, s: Value, is_test: Value, leaf: Block) -> R<()> {
        use crate::region_shape::{
            REGEX_LEAF_BT_ELEMS_OFF, REGEX_LEAF_BT_STACK_OFF, REGEX_LEAF_PAIRS_OFF, REGEX_LEAF_ROWS,
            REGEX_LEAF_ROWS_OFF, REGEX_LEAF_ROW_BYTES, STRLIT_REG_EXP_FUSE_ADDR_OFF, STRLIT_REG_EXP_SHAPE_OFF,
            STRLIT_REGEX_LEAF_OFF,
        };
        use crate::wasm::mir::abi::{REGEXP_LAST_INDEX_OFFSET, REGEXP_SHARED_OFFSET};
        let rt = self.tag_of(re);
        let st = self.tag_of(s);
        let ro = self.tag_is(rt, TAG_OBJECT as u32);
        let ss = self.tag_is(st, TAG_STRING as u32);
        let both = self.bin(Operator::I32And, ro, ss, Type::I32);
        self.check(both, leaf);
        let obj = self.un(Operator::I32WrapI64, re, Type::I32);
        let shape = self.load_i32(obj, SHAPE_OFFSET);
        let wsh = self.i32c(self.h.strlit_slot + STRLIT_REG_EXP_SHAPE_OFF);
        let armed = self.load_i32(wsh, 0);
        let same = self.bin(Operator::I32Eq, shape, armed, Type::I32);
        self.check(same, leaf);
        let wfuse = self.i32c(self.h.strlit_slot + STRLIT_REG_EXP_FUSE_ADDR_OFF);
        let fuse_at = self.load_i32(wfuse, 0);
        let fuse = self.load_i32(fuse_at, 0);
        let intact = self.un(Operator::I32Eqz, fuse, Type::I32);
        self.check(intact, leaf);
        let li = self.load_i64(obj, REGEXP_LAST_INDEX_OFFSET);
        let lt = self.tag_of(li);
        let k = self.i32c(TAG_INT32 as u32);
        let num = self.bin(Operator::I32LeU, lt, k, Type::I32);
        self.check(num, leaf);
        let shared = self.load_i32(obj, REGEXP_SHARED_OFFSET);
        let wblk = self.i32c(self.h.strlit_slot + STRLIT_REGEX_LEAF_OFF);
        let blk = self.load_i32(wblk, 0);
        let four = self.i32c(4);
        let h = self.bin(Operator::I32ShrU, shared, four, Type::I32);
        let mask = self.i32c(REGEX_LEAF_ROWS - 1);
        let h = self.bin(Operator::I32And, h, mask, Type::I32);
        let rb = self.i32c(REGEX_LEAF_ROW_BYTES);
        let off = self.bin(Operator::I32Mul, h, rb, Type::I32);
        let rows = self.add_off(blk, REGEX_LEAF_ROWS_OFF);
        let row = self.bin(Operator::I32Add, rows, off, Type::I32);
        let rshared = self.load_i32(row, 0);
        let hit = self.bin(Operator::I32Eq, rshared, shared, Type::I32);
        let z = self.i32c(0);
        let nz = self.bin(Operator::I32Ne, shared, z, Type::I32);
        let hit = self.bin(Operator::I32And, hit, nz, Type::I32);
        self.check(hit, leaf);
        // The subject: linear; its encoding picks the matcher.
        let p = self.un(Operator::I32WrapI64, s, Type::I32);
        let flags = self.load_i32(p, STRING_FLAGS_OFFSET);
        let lb = self.i32c(STRING_LINEAR_BIT);
        let lin = self.bin(Operator::I32And, flags, lb, Type::I32);
        self.check(lin, leaf);
        let l1b = self.i32c(STRING_LATIN1_CHARS_BIT);
        let latin1 = self.bin(Operator::I32And, flags, l1b, Type::I32);
        let l1 = self.load_i32(row, 4);
        let tb = self.load_i32(row, 8);
        let fidx = self.select(Type::I32, l1, tb, latin1);
        self.check(fidx, leaf);
        let len = self.load_i32(p, STRING_LENGTH_OFFSET);
        let ib = self.i32c(STRING_INLINE_CHARS_BIT);
        let inline = self.bin(Operator::I32And, flags, ib, Type::I32);
        let heap = self.load_i32(p, STRING_CHARS_OFFSET);
        let here = self.add_off(p, STRING_CHARS_OFFSET);
        let chars = self.select(Type::I32, here, heap, inline);
        let start = self.i32c(0);
        let pairs = self.add_off(blk, REGEX_LEAF_PAIRS_OFF);
        let bt = self.load_i32(blk, REGEX_LEAF_BT_STACK_OFF);
        let bte = self.load_i32(blk, REGEX_LEAF_BT_ELEMS_OFF);
        let args = self.body.arg_pool.from_iter([chars, len, start, pairs, bt, bte, fidx].into_iter());
        let tys = self.body.type_pool.from_iter([Type::I32].into_iter());
        let status = self.push_val(ValueDef::Operator(
            Operator::CallIndirect {
                sig_index: self.h.regex_matcher_sig,
                table_index: self.h.indirect_table,
            },
            args,
            tys,
        ));
        // kRegexMatcherFailure (0): no match.
        let none = self.un(Operator::I32Eqz, status, Type::I32);
        let done = self.body.add_block();
        self.cond_br(none, Self::to(done), Self::to(leaf));
        self.cur = done;
        let f = self.i64c((TAG_BOOLEAN << 32) | 0);
        let n = self.i64c(TAG_NULL << 32);
        let r = self.select(Type::I64, f, n, is_test);
        let t = self.edge(inst, 0, &[r])?;
        self.terminate(Terminator::Br { target: t });
        Ok(())
    }

    /// The pristine `Map.prototype.get(k)` on a Map, inline as the JIT's
    /// `mapObjectGet` does, taking `ok_clean` with the value or `undefined`:
    /// an atom key hashed by its stored hash, an int32 key by its bits
    /// (`OrderedHashTableImpl::prepareHash`, the hash scrambled), the
    /// bucket by the table's hash shift, then the chain compared by key
    /// bits (keys are stored normalized: strings atomized, integral
    /// doubles as int32). Any other key or receiver takes `other`.
    fn map_get_arm(&mut self, inst: mir::Inst, ops: &[Value], other: Block) -> R<()> {
        use crate::wasm::mir::abi::{
            ATOM_HASH_OFFSET, FAT_ATOM_HASH_OFFSET, GOLDEN_RATIO_U32, MAP_ENTRY_CHAIN_OFFSET, MAP_ENTRY_KEY_OFFSET,
            MAP_ENTRY_VALUE_OFFSET, MAP_HASH_SHIFT_OFFSET, MAP_HASH_TABLE_OFFSET, MAP_LIVE_COUNT_OFFSET,
            STRING_ATOM_BIT, STRING_FAT_INLINE_MASK,
        };
        let (callee, this, key) = (ops[0], ops[1], ops[2]);
        let is_get = self.builtin_is(callee, BC_MAP_GET);
        let ttag = self.tag_of(this);
        let this_obj = self.tag_is(ttag, TAG_OBJECT as u32);
        let m = self.bin(Operator::I32And, is_get, this_obj, Type::I32);
        self.check(m, other);
        let obj = self.un(Operator::I32WrapI64, this, Type::I32);
        let shape = self.load_i32(obj, SHAPE_OFFSET);
        let base = self.load_i32(shape, SHAPE_BASESHAPE_OFFSET);
        let clasp = self.load_i32(base, BASESHAPE_CLASP_OFFSET);
        let cslot = self.i32c(self.h.strlit_slot + crate::region_shape::STRLIT_MAP_CLASS_OFF);
        let map_class = self.load_i32(cslot, 0);
        let is_map = self.bin(Operator::I32Eq, clasp, map_class, Type::I32);
        self.check(is_map, other);
        // The key's hash.
        let hashed = self.body.add_block();
        let h = self.body.add_blockparam(hashed, Type::I32);
        let (str_b, not_str, int_b) = (self.body.add_block(), self.body.add_block(), self.body.add_block());
        let ktag = self.tag_of(key);
        let is_str = self.tag_is(ktag, TAG_STRING as u32);
        self.cond_br(is_str, Self::to(str_b), Self::to(not_str));
        self.cur = not_str;
        let is_int = self.tag_is(ktag, TAG_INT32 as u32);
        self.cond_br(is_int, Self::to(int_b), Self::to(other));
        self.cur = str_b;
        let golden = self.i32c(GOLDEN_RATIO_U32);
        let kp = self.un(Operator::I32WrapI64, key, Type::I32);
        let flags = self.load_i32(kp, STRING_FLAGS_OFFSET);
        let ab = self.i32c(STRING_ATOM_BIT);
        let atom = self.bin(Operator::I32And, flags, ab, Type::I32);
        self.check(atom, other);
        let fm = self.i32c(STRING_FAT_INLINE_MASK);
        let fbits = self.bin(Operator::I32And, flags, fm, Type::I32);
        let fat = self.bin(Operator::I32Eq, fbits, fm, Type::I32);
        let (fo, no) = (self.i32c(FAT_ATOM_HASH_OFFSET), self.i32c(ATOM_HASH_OFFSET));
        let hoff = self.select(Type::I32, fo, no, fat);
        let haddr = self.bin(Operator::I32Add, kp, hoff, Type::I32);
        let ah = self.load_i32(haddr, 0);
        let sh = self.bin(Operator::I32Mul, ah, golden, Type::I32);
        self.terminate(Terminator::Br { target: BlockTarget { block: hashed, args: vec![sh] } });
        self.cur = int_b;
        // mozilla::HashGeneric over the value's two words, then the scramble:
        // G * (rotl5(G * lo) ^ hi) * G.
        let golden = self.i32c(GOLDEN_RATIO_U32);
        let lo = self.un(Operator::I32WrapI64, key, Type::I32);
        let r = self.bin(Operator::I32Mul, lo, golden, Type::I32);
        let five = self.i32c(5);
        let r = self.bin(Operator::I32Rotl, r, five, Type::I32);
        let r = self.bin(Operator::I32Xor, r, ktag, Type::I32);
        let gg = self.i32c(GOLDEN_RATIO_U32.wrapping_mul(GOLDEN_RATIO_U32));
        let ih = self.bin(Operator::I32Mul, r, gg, Type::I32);
        self.terminate(Terminator::Br { target: BlockTarget { block: hashed, args: vec![ih] } });
        // The lookup.
        self.cur = hashed;
        let undef_b = self.body.add_block();
        let live = self.load_i32(obj, MAP_LIVE_COUNT_OFFSET);
        let (has, walk) = (self.body.add_block(), self.body.add_block());
        let e = self.body.add_blockparam(walk, Type::I32);
        self.cond_br(live, Self::to(has), Self::to(undef_b));
        self.cur = has;
        let shift = self.load_i32(obj, MAP_HASH_SHIFT_OFFSET);
        let bucket = self.bin(Operator::I32ShrU, h, shift, Type::I32);
        let table = self.load_i32(obj, MAP_HASH_TABLE_OFFSET);
        let two = self.i32c(2);
        let boff = self.bin(Operator::I32Shl, bucket, two, Type::I32);
        let baddr = self.bin(Operator::I32Add, table, boff, Type::I32);
        let first = self.load_i32(baddr, 0);
        self.terminate(Terminator::Br { target: BlockTarget { block: walk, args: vec![first] } });
        self.cur = walk;
        let (probe, found, next) = (self.body.add_block(), self.body.add_block(), self.body.add_block());
        self.cond_br(e, Self::to(probe), Self::to(undef_b));
        self.cur = probe;
        let k = self.load_i64(e, MAP_ENTRY_KEY_OFFSET);
        let same = self.bin(Operator::I64Eq, k, key, Type::I32);
        self.cond_br(same, Self::to(found), Self::to(next));
        self.cur = next;
        let chain = self.load_i32(e, MAP_ENTRY_CHAIN_OFFSET);
        self.terminate(Terminator::Br { target: BlockTarget { block: walk, args: vec![chain] } });
        self.cur = found;
        let v = self.load_i64(e, MAP_ENTRY_VALUE_OFFSET);
        let t = self.edge(inst, 0, &[v])?;
        self.terminate(Terminator::Br { target: t });
        self.cur = undef_b;
        let u = self.i64c(TAG_UNDEFINED << 32);
        let t = self.edge(inst, 0, &[u])?;
        self.terminate(Terminator::Br { target: t });
        self.cur = other;
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

    /// `Array.prototype.pop()` on a dense array: with the
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

    /// `restamp`: the
    /// runtime's two-phase gates (`night_runtime_ctor_restamp`), with its
    /// two common outcomes inline: a word already of the layout stays,
    /// and a native object under construction for it (its early key none,
    /// the layout's or a prefix's) with every field's slot is stamped.
    /// Anything else (a prefix-stamped word advancing, a short or capped
    /// slot span, not an object) is the helper's.
    fn restamp(&mut self, this: Value, r: [u32; 7]) {
        let [layout, nfields, keep, prefixes @ ..] = r;
        let done = self.body.add_block();
        let (obj_b, slow) = (self.body.add_block(), self.body.add_block());
        let tag = self.tag_of(this);
        let is_obj = self.tag_is(tag, TAG_OBJECT as u32);
        self.cond_br(is_obj, Self::to(obj_b), Self::to(done));
        self.cur = obj_b;
        let obj = self.un(Operator::I32WrapI64, this, Type::I32);
        let w0 = self.load_i32(obj, OBJ_CLASS_IDX_OFFSET);
        // A stamped word's identity (under the sentinel the low half is a
        // set of fields).
        let m16 = self.i32c(CLASS_WORD_SENTINEL | 0xFFFF);
        let idx = self.bin(Operator::I32And, w0, m16, Type::I32);
        let want = self.i32c(layout + 1);
        let already = self.bin(Operator::I32Eq, idx, want, Type::I32);
        let work = self.body.add_block();
        self.cond_br(already, Self::to(done), Self::to(work));
        self.cur = work;
        // The sentinel with an early key it owns.
        let sentb = self.i32c(CLASS_WORD_SENTINEL);
        let sent = self.bin(Operator::I32And, w0, sentb, Type::I32);
        let z = self.i32c(0);
        let s_nz = self.bin(Operator::I32Ne, sent, z, Type::I32);
        let km = self.i32c(EARLY_KEY_MAX << EARLY_KEY_SHIFT);
        let key = self.bin(Operator::I32And, w0, km, Type::I32);
        let mut k_ok = self.bin(Operator::I32Eq, key, z, Type::I32);
        for k in std::iter::once(layout + 1).chain(prefixes.iter().copied().filter(|&p| p != 0)) {
            let kv = self.i32c(k << EARLY_KEY_SHIFT);
            let e = self.bin(Operator::I32Eq, key, kv, Type::I32);
            k_ok = self.bin(Operator::I32Or, k_ok, e, Type::I32);
        }
        let ok = self.bin(Operator::I32And, s_nz, k_ok, Type::I32);
        // A native object with every field's slot.
        let shape = self.load_i32(obj, SHAPE_OFFSET);
        let imm = self.load_i32(shape, SHAPE_IMMUTABLE_FLAGS_OFFSET);
        let nb = self.i32c(SHAPE_IS_NATIVE_BIT);
        let native = self.bin(Operator::I32And, imm, nb, Type::I32);
        let native = self.bin(Operator::I32Ne, native, z, Type::I32);
        let sh = self.i32c(SHAPE_SMALL_SLOTSPAN_SHIFT);
        let span = self.bin(Operator::I32ShrU, imm, sh, Type::I32);
        let sm = self.i32c(SHAPE_SMALL_SLOTSPAN_MASK_BITS);
        let span = self.bin(Operator::I32And, span, sm, Type::I32);
        let n = self.i32c(nfields);
        let full = self.bin(Operator::I32GeU, span, n, Type::I32);
        let ok = self.bin(Operator::I32And, ok, native, Type::I32);
        let ok = self.bin(Operator::I32And, ok, full, Type::I32);
        // A permuted shape's span may cover holes: the helper counts.
        let pb = self.i32c(SHAPE_PERMUTED_SLOTS_BIT);
        let perm = self.bin(Operator::I32And, imm, pb, Type::I32);
        let seq = self.bin(Operator::I32Eq, perm, z, Type::I32);
        let ok = self.bin(Operator::I32And, ok, seq, Type::I32);
        let stamp = self.body.add_block();
        self.cond_br(ok, Self::to(stamp), Self::to(slow));
        self.cur = stamp;
        let kb = self.i32c(keep & !CLASS_WORD_CLOSED);
        let bits = self.bin(Operator::I32And, w0, kb, Type::I32);
        let nw = self.bin(Operator::I32Or, want, bits, Type::I32);
        let nw = if keep & CLASS_WORD_CLOSED != 0 {
            self.or_closed_if_span(nw, span, nfields)
        } else {
            nw
        };
        self.store_i32(obj, OBJ_CLASS_IDX_OFFSET, nw);
        self.terminate(Terminator::Br { target: Self::to(done) });
        self.cur = slow;
        let mut args = vec![this];
        for x in r {
            args.push(self.i32c(x));
        }
        self.call(self.h.ctor_restamp, &args, &[]);
        self.terminate(Terminator::Br { target: Self::to(done) });
        self.cur = done;
    }

    /// `guard.script`: the callee is a function of `sid`'s script, which
    /// is compiled (§5.5): its class is a function class, its script slot
    /// is that script (a native's slot never is), and the script has a
    /// table index. A lone guard (one likely callee) first probes a value
    /// cell of its own: a hit is one compare of the
    /// callee against the row, with no load through it. The full test fills
    /// the row as `night_call_classify` does (tenured callees only; a
    /// second callee poisons it). In a chain over several targets the
    /// function test is made once, by the first guard.
    fn guard_script(&mut self, inst: mir::Inst, d: &mir::func::InstData, a: &[Value], sid: crate::ids::ScriptId) -> R<()> {
        let addr = *self
            .mm
            .script_addrs
            .get(&sid)
            .ok_or("lowering: guard.script without the script's address")?;
        let callee = d.args[0];
        let fail_m = d.succs[1].block;
        let chains = self.f.terminator(fail_m).is_some_and(|t| {
            matches!(self.f.insts[t].op, Opcode::GuardScript(_)) && self.f.insts[t].args[0] == callee
        });
        let memo = self
            .script_memo
            .get(&self.cur_mblock)
            .filter(|(v, _)| *v == callee)
            .map(|&(_, f)| f);
        let cell = (memo.is_none() && !chains).then(|| {
            // This guard's own row: it learns only a callee that passed
            // the whole test below (a function of the script, which is
            // compiled, as it stays), else holds 0 (empty, or a GC's
            // zeroing) or the poison 1. So a hit is the whole test: the
            // row's low word, a learned callee's pointer, is the callee.
            let cell = self.i32c(CALL_CELL_ADDR_PLACEHOLDER);
            let idx = self.atoms.next_call_cell();
            self.call_cell_patches.push((cell, idx + 1));
            let cached = self.load_i32(cell, 0);
            let ok = self.bin(Operator::I32Eq, a[0], cached, Type::I32);
            let slow = self.body.add_block();
            let t = self.edge(inst, 0, &[a[0]])?;
            self.cond_br(ok, t, Self::to(slow));
            self.cur = slow;
            let boxed = self.box_tagged(TAG_OBJECT, a[0]);
            Ok::<_, String>((cell, boxed))
        });
        let cell = cell.transpose()?;
        let is_function = match memo {
            Some(f) => f,
            None => {
                let shape = self.load_i32(a[0], SHAPE_OFFSET);
                let base = self.load_i32(shape, SHAPE_BASESHAPE_OFFSET);
                let clasp = self.load_i32(base, BASESHAPE_CLASP_OFFSET);
                let slot = self.i32c(self.h.fn_class_slot);
                let fn_class = self.load_i32(slot, 0);
                let ext_class = self.load_i32(slot, 4);
                let is_fn = self.bin(Operator::I32Eq, clasp, fn_class, Type::I32);
                let is_ext = self.bin(Operator::I32Eq, clasp, ext_class, Type::I32);
                self.bin(Operator::I32Or, is_fn, is_ext, Type::I32)
            }
        };
        if chains && self.preds.get(&fail_m).is_some_and(|p| p.len() == 1) {
            self.script_memo.insert(fail_m, (callee, is_function));
        }
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
        let e = self.edge(inst, 1, &[])?;
        match cell {
            None => {
                let t = self.edge(inst, 0, &[a[0]])?;
                self.cond_br(ok, t, e);
            }
            Some((cell, boxed)) => {
                // The row's fill (`night_call_classify`'s): an empty row
                // learns this callee (a nursery one's store goes to the
                // trash row), a populated one is poisoned.
                let fill = self.body.add_block();
                self.cond_br(ok, Self::to(fill), e);
                self.cur = fill;
                let trash = self.i32c(CALL_CELL_ADDR_PLACEHOLDER);
                self.call_cell_patches.push((trash, 0));
                let cached = self.load_i64(cell, 0);
                let z64 = self.i64c(0);
                let empty = self.bin(Operator::I64Eq, cached, z64, Type::I32);
                let mask = self.i32c(NOT_CHUNK_MASK);
                let chunk = self.bin(Operator::I32And, a[0], mask, Type::I32);
                let sb = self.load_i32(chunk, CHUNK_STORE_BUFFER_OFFSET);
                let dst = self.select(Type::I32, trash, cell, sb);
                let (learn, poison) = (self.body.add_block(), self.body.add_block());
                self.cond_br(empty, Self::to(learn), Self::to(poison));
                self.cur = learn;
                self.store_i64(dst, 0, boxed);
                let t = self.edge(inst, 0, &[a[0]])?;
                self.terminate(Terminator::Br { target: t });
                self.cur = poison;
                let one = self.i64c(1);
                self.store_i64(cell, 0, one);
                let t = self.edge(inst, 0, &[a[0]])?;
                self.terminate(Terminator::Br { target: t });
            }
        }
        self.cur = fail_b;
        let e = self.edge(inst, 1, &[])?;
        self.terminate(Terminator::Br { target: e });
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
        // The site's value cell: the steady
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
    /// prologue would write it, from `callee, this, formals`. Every fixed
    /// slot is made a valid Value: helpers' GC scan limit inside the callee
    /// is the frame's top (`frame_top`), past them.
    fn inline_enter(&mut self, d: &mir::func::InstData, a: &[Value]) -> R<()> {
        let fid = self.cur_frame as usize;
        self.framed.retain(|&(f, _), _| f as usize != fid);
        if self.f.inline_frames[fid - 1].parent == 0 {
            // The frame overlays the rooting slots from `inline_k` up,
            // which no value live in its region has: what they hold is
            // gone, and they are dirty again from here.
            let k = self.inline_k[fid];
            let home = &self.home;
            self.slotted.retain(|v| home.get(v).is_some_and(|&h| h < k));
            self.dirty.extend(k..self.nslots);
        }
        let (base, vbase, l) = (self.frame_off[fid], self.frame_voff[fid], self.frame_layouts[fid]);
        // Every actual for a callee reading them, else every formal.
        let nact = self.f.inline_frames[fid - 1].argc.map_or(l.nargs, |n| n.max(l.nargs));
        // A construct also passes its new.target.
        let construct = a.len() == 3 + nact as usize;
        if a.len() != 2 + nact as usize && !construct {
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
        for i in 0..nact {
            self.store_i64(sp, base + l.arg(i), boxed[2 + i as usize]);
        }
        let undef = self.i64c(UNDEF);
        for j in 0..l.nlocals {
            self.store_i64(sp, vbase + l.local(j), undef);
        }
        if self.fixed[fid] == Fixed::None {
            return Ok(());
        }
        // The callee's own environment: what its prologue loads, for a
        // script whose activation has none of its own (the only kind
        // inlined).
        let fun = self.un(Operator::I32WrapI64, boxed[0], Type::I32);
        let env = self.load_i64(fun, FUNC_ENV_SLOT_OFFSET);
        if l.has_env {
            self.store_i64(sp, vbase + l.env(), env);
        }
        if self.fixed[fid] == Fixed::Env {
            return Ok(());
        }
        if l.has_args_obj {
            self.store_i64(sp, vbase + l.args_obj(), undef);
        }
        if l.has_new_target {
            let nt = if construct { boxed[boxed.len() - 1] } else { undef };
            self.store_i64(sp, vbase + l.new_target(), nt);
        }
        self.store_i64(sp, vbase + l.rval(), undef);
        let zero = self.i64c(TAG_INT32 << 32);
        self.store_i64(sp, vbase + l.resume(), zero);
        self.store_i64(sp, vbase + l.backoff(), zero);
        // The operand stack is past the frame's GC scan limit
        // (`frame_top`): its exits write it, as they write the fixed slots
        // a leaner frame leaves out (`Fixed`).
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
        let (hub, _, _, _, _, tails) = self.inline_hubs.get_mut(&fid).unwrap();
        let hub = *hub;
        let idx = u32::try_from(tails.len()).unwrap();
        let tail = self.body.add_block();
        let err = self.body.add_blockparam(tail, Type::I32);
        let same = self.body.add_blockparam(tail, Type::I32);
        self.inline_hubs.get_mut(&fid).unwrap().5.push(tail);
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
        self.clean_or_dirty(inst, ok, same, &[result])
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
    ) -> R<(Block, Block, Value, Value, Value, Vec<Block>)> {
        let saved = self.cur;
        let hub = self.body.add_block();
        let word = self.body.add_blockparam(hub, Type::I32);
        let site = self.body.add_blockparam(hub, Type::I32);
        let n = 3 + nargs + nlocals + max_depth;
        let ops: Vec<Option<Value>> = (0..n).map(|_| Some(self.body.add_blockparam(hub, Type::I64))).collect();
        self.cur = hub;
        let fp = frame_parts(&ops, nargs, nlocals).ok_or("lowering: malformed exit.inline")?;
        let f = fid as usize;
        let (base, vbase, end, l) = (self.frame_off[f], self.frame_voff[f], self.frame_end[f], self.frame_layouts[f]);
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
                self.store_i64(sp, vbase + l.local(u32::try_from(j).unwrap()), v);
            }
        }
        if let Some(v) = *fp.rval {
            self.store_i64(sp, vbase + l.rval(), v);
        }
        for (k, v) in fp.stack.iter().enumerate() {
            if let Some(v) = *v {
                self.store_i64(sp, vbase + l.operand(u32::try_from(k).unwrap()), v);
            }
        }
        let w64 = self.un(Operator::I64ExtendI32U, word, Type::I64);
        let tag = self.i64c(TAG_INT32 << 32);
        let wv = self.bin(Operator::I64Or, w64, tag, Type::I64);
        self.store_i64(sp, vbase + l.resume(), wv);
        let backoff = self.i64c((TAG_INT32 << 32) | u64::from(ONRAMP_BACKOFF));
        self.store_i64(sp, vbase + l.backoff(), backoff);
        // The fixed slots the frame's entry left out (`Fixed`).
        if self.fixed[f] == Fixed::None && l.has_env {
            let callee = self.load_i64(sp, base + FrameLayout::CALLEE);
            let fun = self.un(Operator::I32WrapI64, callee, Type::I32);
            let env = self.load_i64(fun, FUNC_ENV_SLOT_OFFSET);
            self.store_i64(sp, vbase + l.env(), env);
        }
        if self.fixed[f] != Fixed::All {
            let undef = self.i64c(UNDEF);
            if l.has_args_obj {
                self.store_i64(sp, vbase + l.args_obj(), undef);
            }
            if l.has_new_target {
                self.store_i64(sp, vbase + l.new_target(), undef);
            }
        }
        let callee = self.load_i64(sp, base + FrameLayout::CALLEE);
        let (funcidx, script) = self.classify(callee);
        let off = self.i32c(u32::MAX);
        self.body_off_patches.push(off);
        let body_idx = self.bin(Operator::I32Sub, funcidx, off, Type::I32);
        let frame = self.add_off(sp, base);
        let top = self.add_off(sp, end);
        // The call's actual count, for a callee reading its actuals: its
        // `vp` rebase is the frame's.
        let n = self.f.inline_frames[f - 1].argc.unwrap_or(nargs);
        let argc = self.i32c(n | ARGC_RESUME_BIT);
        let undef = self.i64c(UNDEF);
        let args = self
            .body
            .arg_pool
            .from_iter([self.cx, frame, argc, top, script, undef, body_idx].into_iter());
        let tys = self.body.type_pool.from_iter([Type::I32, Type::I32].into_iter());
        // Whether the callee's baseline rest demoted a class word: the
        // sites continue on their clean edge only if not.
        let pre = self.epoch();
        let call = self.push_val(ValueDef::Operator(
            Operator::CallIndirect {
                sig_index: self.h.night_abi_sig2,
                table_index: self.h.indirect_table,
            },
            args,
            tys,
        ));
        let err = self.push_val(ValueDef::PickOutput(call, 0, Type::I32));
        let post = self.epoch();
        let same = self.bin(Operator::I32Eq, pre, post, Type::I32);
        // The dispatch goes where the body ends (classify branches).
        let last = self.cur;
        self.cur = saved;
        Ok((hub, last, site, err, same, vec![]))
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
        self.write_frame(&boxed, nargs, nlocals)?;
        let vp = self.vp;
        let l = self.layout;
        // The fixed slots MIR does not keep current. The env slot is
        // written through (scopes), and the arguments-object slot holds the
        // one `args.object` made, if any (the fresh entry cleared it).
        if l.has_new_target {
            self.store_i64(vp, l.new_target(), self.new_target);
        }
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

    /// Write frame state `boxed` (this, formals, locals, rval, stack; a
    /// dead operand's slot keeps the frame's valid value) to the baseline
    /// frame.
    fn write_frame(&mut self, boxed: &[Option<Value>], nargs: u32, nlocals: u32) -> R<()> {
        let fp = frame_parts(boxed, nargs, nlocals).ok_or("lowering: malformed exit")?;
        let (sp, vp) = (self.sp, self.vp);
        let l = self.layout;
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
        Ok(())
    }

    /// `gen.suspend` (baseline's `suspend`): write the frame, save its
    /// locals, the operands below the yielded ones and the environment
    /// into the generator under resume index `index`, and return the
    /// yielded value (the generator, for `InitialYield`).
    fn gen_suspend(&mut self, inst: mir::Inst, a: &[Value], index: u32, nargs: u32, nlocals: u32, initial: bool) -> R<()> {
        let d = self.f.insts[inst].clone();
        let mut boxed = vec![];
        for (&v, &mv) in a.iter().zip(&d.args) {
            let dead = matches!(
                self.f.values[mv].def,
                mir::func::ValueDef::Result(i, _) if self.f.insts[i].op == Opcode::ConstVal(ConstVal::Dead)
            );
            boxed.push(if dead { None } else { Some(self.boxed(&self.ty(mv), v)?) });
        }
        let depth = frame_parts(&boxed, nargs, nlocals).ok_or("lowering: malformed gen.suspend")?.stack.len();
        let popped = if initial { 1 } else { 2 };
        let saved = u32::try_from(depth.checked_sub(popped).ok_or("lowering: gen.suspend stack too shallow")?).unwrap();
        let g = boxed[boxed.len() - 1].ok_or("lowering: gen.suspend without its generator")?;
        let rv = if initial {
            g
        } else {
            boxed[boxed.len() - 2].ok_or("lowering: gen.suspend without its value")?
        };
        // A dead local goes into the generator as undefined, not as the
        // frame's stale copy: a binding out of scope must not keep its
        // last value alive while the generator is suspended.
        let undef = self.i64c(UNDEF);
        let nlead = 1 + nargs as usize;
        for (i, b) in boxed.iter_mut().enumerate() {
            if b.is_none() && i >= nlead && i <= nlead + nlocals as usize {
                *b = Some(undef);
            }
        }
        self.write_frame(&boxed, nargs, nlocals)?;
        let l = self.layout;
        let env = if self.plain_env || self.own_env {
            self.frame_env()
        } else {
            self.i64c(0)
        };
        let lp = self.add_off(self.vp, l.local_base());
        let nl = self.i32c(l.nlocals);
        let ops = self.add_off(self.vp, l.operand_base());
        let (kv, dv) = (self.i32c(index), self.i32c(saved));
        self.call(self.h.gen_suspend, &[self.cx, g, kv, lp, nl, ops, dv, env], &[Type::I32]);
        self.store_i64(self.retval_out, 0, rv);
        let z = self.i32c(0);
        self.ret(z);
        Ok(())
    }

    /// Run this script's baseline body on the frame at `sp` with `argc`
    /// (resume and onramp bits included), and return its result.
    fn tail_to_baseline(&mut self, argc: Value) {
        // The script from the frame's callee, not the `script` param: a
        // param used anywhere is copied at entry, and that i32 stack
        // argument read as a 64-bit slot defeats store forwarding from the
        // caller's store on every call.
        let callee = self.load_i64(self.sp, FrameLayout::CALLEE);
        let fp = self.un(Operator::I32WrapI64, callee, Type::I32);
        let script = self.load_i32(fp, FUNC_SCRIPT_SLOT_OFFSET);
        let call = self.call(
            Func::invalid(),
            &[
                self.cx,
                self.sp,
                argc,
                self.retval_out,
                script,
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
