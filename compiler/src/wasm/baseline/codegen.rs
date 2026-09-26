//! Baseline code generation: one pass over the bytecode, each op lowered to
//! a direct call to one runtime helper (trivial ops inline), with every JS
//! value in the NightStack frame (`layout`).
//!
//! No JS value lives in SSA between ops. An op loads its inputs from their
//! operand slots, calls its helper with `top` just above the operand
//! stack at the op's entry depth (so its inputs stay rooted), and stores its
//! result back to a slot. After a may-GC call nothing loaded before it is
//! reused: a moving GC updates the rooted slots, not SSA copies, so every
//! post-call use reloads from memory.
//!
//! Control flow follows the bytecode: one waffle block per basic block
//! (`layout::leaders`), no block params. Exceptions branch from the
//! throwing op to its statically known handler, running the unwinding the
//! interpreter's `ProcessTryNotes` does (iterator closes, env pops) on the
//! way.

use std::collections::{BTreeMap, BTreeSet};

use waffle::entity::EntityRef;
use waffle::{
    Block, BlockTarget, Func, FunctionBody, MemoryArg, Operator, Terminator, Type, Value, ValueDef,
};

use super::layout::{
    self, FrameLayout, ResumeMode, ResumeWord, StackDepths, ARGC_FLAGS, ARGC_ONRAMP_BIT,
    ARGC_RESUME_BIT, ERR_DEOPT,
};
use crate::bytecode::{BytecodeParser, JSOp, Script, TryNoteKind};
use crate::ids::Pc;
use crate::source::{ScopeData, SourceObject};
use crate::wasm::bbv::abi::{
    BINOP_BITAND, BINOP_BITNOT, BINOP_BITOR, BINOP_BITXOR, BINOP_DEC, BINOP_DIV, BINOP_INC,
    BINOP_LSH, BINOP_MOD, BINOP_MUL, BINOP_RSH, BINOP_SUB, BINOP_URSH, CMP_EQ, CMP_GE, CMP_GT,
    CMP_LE, CMP_LT, CMP_NE, CMP_STRICTEQ, CMP_STRICTNE, ELEMENTS_INITLEN_BACK, FIXED_SLOTS_BASE,
    FLAGS_ALL, FUNC_ENV_SLOT_OFFSET, FUNC_SCRIPT_SLOT_OFFSET, INIT_ATTR_ENUMERATE,
    INIT_ATTR_HIDDEN, INIT_ATTR_LOCKED, NO_NSLOTS, OBJ_ELEMENTS_OFFSET,
    SHAPE_IMMUTABLE_FLAGS_OFFSET, SHAPE_IS_NATIVE_BIT, SHAPE_OFFSET,
};
use crate::wasm::translate::{
    AtomTable, Helpers, TranslateCtx, MAGIC_ELEMENTS_HOLE, MAGIC_GENERATOR_CLOSING,
    MAGIC_IS_CONSTRUCTING, MAGIC_NO_ITER_VALUE, MAGIC_UNINITIALIZED_LEXICAL, TAG_BOOLEAN,
    TAG_CLEAR, TAG_INT32, TAG_MAGIC, TAG_NULL, TAG_OBJECT, TAG_UNDEFINED,
};

/// The most frame a baseline body may use above `sp`, in bytes. Runtime
/// entries guarantee 64 KiB of NightStack headroom beyond the callee's
/// actuals (`kNightStackHeadroomSlots`), and nothing checks a body's own
/// frame against it, so a larger frame is declined rather than risked.
const MAX_FRAME_BYTES: u32 = 48 * 1024;

const UNDEF: u64 = TAG_UNDEFINED << 32;

/// The resume word's "not resuming" payload: no encoded pc is `u32::MAX`
/// (`ResumeWord::MAX_PC` leaves the top bit clear).
const RESUME_NONE: u32 = u32::MAX;

/// One try-note-driven unwinding step on the way to a handler.
#[derive(Clone, Copy)]
enum Close {
    /// A for-in iterator at operand depth `d - 1`.
    ForIn(u32),
    /// A destructuring iterator at `d - 2`, its done flag at `d - 1`.
    Destructuring(u32),
}

pub(super) struct Gen<'a> {
    ctx: &'a TranslateCtx<'a>,
    atoms: &'a mut AtomTable,
    script: &'a Script,
    is_global: bool,
    h: Helpers,
    pub(super) body: FunctionBody,
    layout: FrameLayout,
    depths: StackDepths,
    needs_env: bool,
    env_scopes: Vec<u32>,
    cur: Block,
    /// Whether `cur` is open (reachable and not yet terminated).
    live: bool,
    cx: Value,
    sp: Value,
    vp: Value,
    argc: Value,
    retval_out: Value,
    new_target: Value,
    blocks: BTreeMap<Pc, Block>,
    error_blk: Option<Block>,
    finally_landing: BTreeMap<Pc, Block>,
    exc_targets: BTreeMap<(Pc, u32), BlockTarget>,
    /// Generator or async body: suspend/resume through the generator
    /// object (`EnterNightResume` protocol).
    is_gen: bool,
    /// Resume labels: (resume index, landing pc, saved operand depth).
    gen_resume: Vec<(u32, Pc, u32)>,
    /// Loop intervals `[header, end)`, from the bytecode's back edges.
    loops: Vec<(Pc, Pc)>,
    /// Every pc a resume may land on (`docs/BASELINE.md` §4).
    resume_targets: BTreeSet<Pc>,
    /// Every resume word a resume may carry: the generator landings and
    /// the MIR body's exit and throw pcs (`resumes`).
    resume_words: BTreeSet<ResumeWord>,
    /// Resume words the caller asked for (a MIR body's exits), entered
    /// through the `ARGC_RESUME_BIT` fork.
    ext_resumes: Vec<ResumeWord>,
    /// `argc` as passed, flags included.
    argc_raw: Value,
    /// The ABI's script parameter, passed through to onramp calls.
    script_param: Value,
    /// Loop headers with a MIR onramp root (`docs/BASELINE.md` §7), with
    /// the resume words that root reaches.
    onramps: BTreeMap<Pc, Vec<ResumeWord>>,
    /// Direct-call placeholders for the script's MIR body.
    pub(super) main_calls: Vec<Value>,
    /// The resume dispatch (`ARGC_RESUME_BIT` entry).
    resume_disp: Option<Block>,
    /// Loop headers that dispatch resumes: header pc -> (dispatch block,
    /// the header's own code block). Every branch to the header goes to the
    /// dispatch block, which is therefore the loop's header node.
    dispatch: BTreeMap<Pc, (Block, Block)>,
    /// The resume entry, if the body has one (generators).
    gen_dispatch_blk: Option<Block>,
    /// Adapter-offset placeholders of direct calls (`Outcome::Compiled`'s
    /// `body_off_patches`).
    pub(super) body_off_patches: Vec<Value>,
    /// The op being lowered and its entry depth.
    pc: Pc,
    d: u32,
}

type R<T> = Result<T, String>;

/// An inline int32 operation: the raw i32 result of two raw i32 operands,
/// or a branch to the slow block (the op's helper call) when the result is
/// not an int32.
type Int32Op<'a> = fn(&mut Gen<'a>, Value, Value, Block) -> Value;

/// `number_arms`' int32 arm: raw i32 operands to a boxed result, or a
/// branch to the block given (the next arm).
type IntArm<'s, 'a> = dyn Fn(&mut Gen<'a>, &[Value], Block) -> Value + 's;

/// `number_arms`' number arm: f64 operands to a boxed result.
type NumArm<'s, 'a> = dyn Fn(&mut Gen<'a>, &[Value]) -> Value + 's;

/// `JS::GenericNaN()`'s bits.
const CANONICAL_NAN_BITS: u64 = 0x7FF8_0000_0000_0000;

/// The `night_runtime_binop` kind of an arithmetic op.
fn binop_kind(op: JSOp) -> u32 {
    match op {
        JSOp::Sub => BINOP_SUB,
        JSOp::Mul => BINOP_MUL,
        JSOp::Div => BINOP_DIV,
        JSOp::Mod => BINOP_MOD,
        JSOp::BitAnd => BINOP_BITAND,
        JSOp::BitOr => BINOP_BITOR,
        JSOp::BitXor => BINOP_BITXOR,
        JSOp::Lsh => BINOP_LSH,
        JSOp::Rsh => BINOP_RSH,
        JSOp::Ursh => BINOP_URSH,
        JSOp::Inc => BINOP_INC,
        JSOp::Dec => BINOP_DEC,
        JSOp::BitNot => BINOP_BITNOT,
        _ => unreachable!("{op:?} is not a binop kind"),
    }
}

impl<'a> Gen<'a> {
    pub(super) fn new(
        ctx: &'a TranslateCtx<'a>,
        atoms: &'a mut AtomTable,
        script: &'a Script,
        is_global: bool,
        body: FunctionBody,
        depths: StackDepths,
        resumes: &[ResumeWord],
        onramps: &[(Pc, Vec<ResumeWord>)],
    ) -> R<Gen<'a>> {
        let layout = FrameLayout::of(script);
        let needs_env = needs_env(script);
        let frame_top = layout.top(depths.max + 3);
        if frame_top > MAX_FRAME_BYTES {
            return Err(format!("frame too large ({frame_top} bytes)"));
        }
        let entry = body.entry;
        let p = |i: usize| body.blocks[entry].params[i].1;
        let (cx, sp, argc, retval_out, script_param, new_target) =
            (p(0), p(1), p(2), p(3), p(4), p(5));
        Ok(Gen {
            ctx,
            atoms,
            script,
            is_global,
            h: ctx.helpers,
            body,
            layout,
            depths,
            needs_env,
            env_scopes: env_scopes_of(script),
            cur: entry,
            live: true,
            cx,
            sp,
            vp: sp,
            argc,
            retval_out,
            new_target,
            blocks: BTreeMap::new(),
            error_blk: None,
            finally_landing: BTreeMap::new(),
            exc_targets: BTreeMap::new(),
            is_gen: script.is_generator_or_async,
            gen_resume: vec![],
            loops: vec![],
            resume_targets: BTreeSet::new(),
            resume_words: BTreeSet::new(),
            ext_resumes: resumes.to_vec(),
            argc_raw: argc,
            script_param,
            onramps: onramps.iter().cloned().collect(),
            main_calls: vec![],
            resume_disp: None,
            dispatch: BTreeMap::new(),
            gen_dispatch_blk: None,
            body_off_patches: vec![],
            pc: Pc::new(0),
            d: 0,
        })
    }

    // --- waffle primitives ------------------------------------------------

    fn push_val(&mut self, def: ValueDef) -> Value {
        let v = self.body.add_value(def);
        self.body.append_to_block(self.cur, v);
        v
    }

    fn i32c(&mut self, value: u32) -> Value {
        let ty = self.body.single_type_list(Type::I32);
        self.push_val(ValueDef::Operator(
            Operator::I32Const { value },
            Default::default(),
            ty,
        ))
    }

    fn i64c(&mut self, value: u64) -> Value {
        let ty = self.body.single_type_list(Type::I64);
        self.push_val(ValueDef::Operator(
            Operator::I64Const { value },
            Default::default(),
            ty,
        ))
    }

    fn unop(&mut self, op: Operator, a: Value, t: Type) -> Value {
        let args = self.body.arg_pool.single(a);
        let ty = self.body.single_type_list(t);
        self.push_val(ValueDef::Operator(op, args, ty))
    }

    fn binop(&mut self, op: Operator, a: Value, b: Value, t: Type) -> Value {
        let args = self.body.arg_pool.double(a, b);
        let ty = self.body.single_type_list(t);
        self.push_val(ValueDef::Operator(op, args, ty))
    }

    fn select(&mut self, t: Type, a: Value, b: Value, cond: Value) -> Value {
        let args = self.body.arg_pool.from_iter([a, b, cond].into_iter());
        let ty = self.body.single_type_list(t);
        self.push_val(ValueDef::Operator(
            Operator::TypedSelect { ty: t },
            args,
            ty,
        ))
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
        self.unop(Operator::I64Load { memory: m }, addr, Type::I64)
    }

    fn load_i32(&mut self, addr: Value, offset: u32) -> Value {
        let m = self.mem(2, offset);
        self.unop(Operator::I32Load { memory: m }, addr, Type::I32)
    }

    fn store_i64(&mut self, addr: Value, offset: u32, value: Value) {
        let m = self.mem(3, offset);
        let args = self.body.arg_pool.double(addr, value);
        self.push_val(ValueDef::Operator(
            Operator::I64Store { memory: m },
            args,
            Default::default(),
        ));
    }

    fn add_off(&mut self, addr: Value, off: u32) -> Value {
        if off == 0 {
            return addr;
        }
        let k = self.i32c(off);
        self.binop(Operator::I32Add, addr, k, Type::I32)
    }

    fn call(&mut self, f: Func, args: &[Value], ret: Option<Type>) -> Option<Value> {
        let args = self.body.arg_pool.from_iter(args.iter().copied());
        let ty = match ret {
            Some(t) => self.body.single_type_list(t),
            None => Default::default(),
        };
        let v = self.push_val(ValueDef::Operator(
            Operator::Call { function_index: f },
            args,
            ty,
        ));
        ret.map(|_| v)
    }

    fn terminate(&mut self, t: Terminator) {
        self.body.set_terminator(self.cur, t);
        self.live = false;
    }

    fn br(&mut self, target: BlockTarget) {
        self.terminate(Terminator::Br { target });
    }

    fn cond_br(&mut self, cond: Value, if_true: BlockTarget, if_false: BlockTarget) {
        self.terminate(Terminator::CondBr {
            cond,
            if_true,
            if_false,
        });
    }

    fn goto(block: Block) -> BlockTarget {
        BlockTarget {
            block,
            args: vec![],
        }
    }

    /// Start emitting into a fresh block.
    fn fresh(&mut self) -> Block {
        let b = self.body.add_block();
        self.cur = b;
        self.live = true;
        b
    }

    // --- frame access -------------------------------------------------------

    /// Operand slot `k`.
    fn slot(&mut self, k: u32) -> Value {
        self.load_i64(self.vp, self.layout.operand(k))
    }

    fn set_slot(&mut self, k: u32, v: Value) {
        self.store_i64(self.vp, self.layout.operand(k), v)
    }

    fn top_addr(&mut self, depth: u32) -> Value {
        self.add_off(self.vp, self.layout.top(depth))
    }

    fn env(&mut self) -> Value {
        self.load_i64(self.vp, self.layout.env())
    }

    fn set_env(&mut self, v: Value) {
        self.store_i64(self.vp, self.layout.env(), v)
    }

    fn boxed_bool(&mut self, b: Value) -> Value {
        let b64 = self.unop(Operator::I64ExtendI32U, b, Type::I64);
        let tag = self.i64c(TAG_BOOLEAN << 32);
        self.binop(Operator::I64Or, tag, b64, Type::I64)
    }

    fn boxed_int32(&mut self, i: Value) -> Value {
        let i64v = self.unop(Operator::I64ExtendI32U, i, Type::I64);
        let tag = self.i64c(TAG_INT32 << 32);
        self.binop(Operator::I64Or, tag, i64v, Type::I64)
    }

    /// The value's tag (high word).
    fn tag_of(&mut self, v: Value) -> Value {
        let sh = self.i64c(32);
        let hi = self.binop(Operator::I64ShrU, v, sh, Type::I64);
        self.unop(Operator::I32WrapI64, hi, Type::I32)
    }

    fn tag_eq(&mut self, v: Value, tag: u64) -> Value {
        let t = self.tag_of(v);
        let k = self.i32c(tag as u32);
        self.binop(Operator::I32Eq, t, k, Type::I32)
    }

    /// This frame's `JSScript*`, re-derived from the rooted callee slot
    /// (the ABI's script parameter does not survive a compacting GC).
    fn script_ptr(&mut self) -> Value {
        let slot0 = self.load_i64(self.sp, 0);
        let low = self.unop(Operator::I32WrapI64, slot0, Type::I32);
        if self.is_global {
            return low;
        }
        self.load_i32(low, FUNC_SCRIPT_SLOT_OFFSET)
    }

    fn atom(&mut self, name_index: u32) -> R<u32> {
        let gc = *self
            .script
            .gcthings
            .get(usize::try_from(name_index).unwrap())
            .ok_or_else(|| format!("name index {name_index} out of range"))?;
        match self.ctx.source.object(gc) {
            SourceObject::String(s) => {
                let name = self.atoms.names.intern(s);
                Ok(self.atoms.intern(name))
            }
            _ => Err(format!("name index {name_index} is not a string")),
        }
    }

    // --- helper calls and exceptions ------------------------------------------

    /// A may-GC, may-throw helper: `helper(cx, top, args...)` with `top`
    /// above the operand stack at the op's entry depth. Branches to the
    /// op's exception landing on failure; returns the boxed result the
    /// helper wrote to `*top` (meaningless for helpers without one).
    fn rt(&mut self, f: Func, args: &[Value]) -> Value {
        let top = self.top_addr(self.d);
        let mut full = vec![self.cx, top];
        full.extend_from_slice(args);
        let ok = self.call(f, &full, Some(Type::I32)).unwrap();
        self.branch_on_err(ok);
        let top = self.top_addr(self.d);
        self.load_i64(top, 0)
    }

    /// A may-GC helper that always throws.
    fn rt_throw(&mut self, f: Func, args: &[Value]) {
        let top = self.top_addr(self.d);
        let mut full = vec![self.cx, top];
        full.extend_from_slice(args);
        self.call(f, &full, None);
        let t = self.exc_target(self.pc, self.d);
        self.br(t);
    }

    fn branch_on_err(&mut self, ok: Value) {
        let t = self.exc_target(self.pc, self.d);
        let cont = self.body.add_block();
        self.cond_br(ok, Self::goto(cont), t);
        self.cur = cont;
        self.live = true;
    }

    /// Where an exception with no handler goes. Outside a generator, each
    /// throwing pc gets its own two-instruction return block rather than a
    /// shared one: a shared block would have one predecessor per helper
    /// call in the body, and on a huge body that fan-in makes dominator
    /// computation (here, and in waffle's backend) quadratic.
    fn error_return(&mut self) -> Block {
        if self.is_gen {
            return self.error_block();
        }
        let saved = (self.cur, self.live);
        let b = self.fresh();
        let one = self.i32c(1);
        let flags = self.i32c(FLAGS_ALL);
        self.terminate(Terminator::Return {
            values: vec![one, flags],
        });
        (self.cur, self.live) = saved;
        b
    }

    fn error_block(&mut self) -> Block {
        if let Some(b) = self.error_blk {
            return b;
        }
        let saved = (self.cur, self.live);
        let b = self.fresh();
        if self.is_gen {
            // A pending generator-closing magic is a forced `.return()`
            // that finished unwinding its finallys: return rval normally
            // (the interpreter's `HandleError` for generator frames).
            let gc = self.h.gen_closing;
            let closing = self.call(gc, &[self.cx], Some(Type::I32)).unwrap();
            let ret_blk = self.body.add_block();
            let err_blk = self.body.add_block();
            self.cond_br(closing, Self::goto(ret_blk), Self::goto(err_blk));
            self.cur = ret_blk;
            self.live = true;
            let v = self.load_i64(self.vp, self.layout.rval());
            self.ret(v);
            self.cur = err_blk;
            self.live = true;
        }
        let one = self.i32c(1);
        let flags = self.i32c(FLAGS_ALL);
        self.terminate(Terminator::Return {
            values: vec![one, flags],
        });
        (self.cur, self.live) = saved;
        self.error_blk = Some(b);
        b
    }

    /// The try-note walk of the interpreter's `ProcessTryNotes` for an
    /// exception at `pc` with operand depth `depth`: the closes on the way
    /// and the handler (pc, depth, is-finally), if any.
    fn walk_try_notes(&self, pc: Pc, depth: u32) -> (Vec<Close>, Option<(Pc, u32, bool)>) {
        self.walk_try_notes_impl(pc, depth, false)
    }

    fn walk_try_notes_impl(
        &self,
        pc: Pc,
        depth: u32,
        skip_catches: bool,
    ) -> (Vec<Close>, Option<(Pc, u32, bool)>) {
        let notes = &self.script.try_notes;
        let n = notes.len();
        let in_range = |t: &crate::bytecode::TryNote| pc >= t.start && pc < t.start + t.length;
        let mut closes = Vec::new();
        let mut i = 0;
        while i < n {
            let t = &notes[i];
            if !in_range(t) {
                i += 1;
                continue;
            }
            if matches!(t.kind, TryNoteKind::ForOfIterClose) {
                // Skip to the matching ForOf: the iterator is being closed
                // already.
                let mut nest = 1u32;
                i += 1;
                while nest > 0 && i < n {
                    let u = &notes[i];
                    if in_range(u) {
                        match u.kind {
                            TryNoteKind::ForOfIterClose => nest += 1,
                            TryNoteKind::ForOf => nest -= 1,
                            _ => {}
                        }
                    }
                    i += 1;
                }
                continue;
            }
            if t.stack_depth > depth {
                i += 1;
                continue;
            }
            match t.kind {
                TryNoteKind::Catch if skip_catches => {}
                TryNoteKind::Catch => {
                    return (closes, Some((t.start + t.length, t.stack_depth, false)))
                }
                TryNoteKind::Finally => {
                    return (closes, Some((t.start + t.length, t.stack_depth, true)))
                }
                TryNoteKind::ForIn => closes.push(Close::ForIn(t.stack_depth)),
                TryNoteKind::Destructuring => closes.push(Close::Destructuring(t.stack_depth)),
                TryNoteKind::ForOf | TryNoteKind::Loop | TryNoteKind::ForOfIterClose => {}
            }
            i += 1;
        }
        (closes, None)
    }

    /// Where an exception raised at `pc` (operand depth `depth`) goes:
    /// through its closes and env unwinding, to the catch handler, the
    /// finally landing, or the error return.
    fn exc_target(&mut self, pc: Pc, depth: u32) -> BlockTarget {
        if let Some(t) = self.exc_targets.get(&(pc, depth)) {
            return t.clone();
        }
        let (closes, handler) = self.walk_try_notes(pc, depth);
        if self.is_gen && matches!(handler, Some((_, _, false))) {
            let t = self.gen_catch_target(pc, depth, closes, handler);
            self.exc_targets.insert((pc, depth), t.clone());
            return t;
        }
        let target = if closes.is_empty() {
            self.handler_dest(pc, handler)
        } else {
            let saved = (self.cur, self.live);
            let t = self.fresh();
            self.run_closes(&closes, depth);
            let dest = self.handler_dest(pc, handler);
            self.br(dest);
            (self.cur, self.live) = saved;
            Self::goto(t)
        };
        self.exc_targets.insert((pc, depth), target.clone());
        target
    }

    /// A catch handler in a generator body: a forced `.return()` unwind (a
    /// pending generator-closing magic) passes catches over and runs only
    /// finallys, so the edge tests for it at runtime (the peek helper, so
    /// the magic stays pending) and takes the catch-skipping walk's
    /// target when set -- `ProcessTryNotes`' `isClosingGenerator` rule.
    fn gen_catch_target(
        &mut self,
        pc: Pc,
        depth: u32,
        closes: Vec<Close>,
        handler: Option<(Pc, u32, bool)>,
    ) -> BlockTarget {
        let (all_closes, closing_handler) = self.walk_try_notes_impl(pc, depth, true);
        let saved = (self.cur, self.live);
        let t = self.fresh();
        self.run_closes(&closes, depth);
        let closing_blk = self.body.add_block();
        let catch_blk = self.body.add_block();
        let gic = self.h.gen_is_closing;
        let closing = self.call(gic, &[self.cx], Some(Type::I32)).unwrap();
        self.cond_br(closing, Self::goto(closing_blk), Self::goto(catch_blk));
        self.cur = catch_blk;
        self.live = true;
        let dest = self.handler_dest(pc, handler);
        self.br(dest);
        self.cur = closing_blk;
        self.live = true;
        self.run_closes(&all_closes[closes.len()..], depth);
        let dest = self.handler_dest(pc, closing_handler);
        self.br(dest);
        (self.cur, self.live) = saved;
        Self::goto(t)
    }

    /// The handler block for an exception at `pc`, after popping the block
    /// environments the handler does not see.
    fn handler_dest(&mut self, pc: Pc, handler: Option<(Pc, u32, bool)>) -> BlockTarget {
        let dest = match handler {
            None => return Self::goto(self.error_return()),
            Some((hpc, _, false)) => self.block(hpc),
            Some((hpc, hd, true)) => self.finally_landing(hpc, hd),
        };
        let pops = match handler {
            Some((hpc, _, _)) if self.needs_env => self.env_pops(pc, hpc),
            _ => 0,
        };
        if pops == 0 {
            return Self::goto(dest);
        }
        let saved = (self.cur, self.live);
        let t = self.fresh();
        self.pop_envs(pops);
        self.br(Self::goto(dest));
        (self.cur, self.live) = saved;
        Self::goto(t)
    }

    fn pop_envs(&mut self, pops: u32) {
        let mut env = self.env();
        for _ in 0..pops {
            let p = self.unop(Operator::I32WrapI64, env, Type::I32);
            env = self.load_i64(p, FIXED_SLOTS_BASE);
        }
        self.set_env(env);
    }

    fn run_closes(&mut self, closes: &[Close], depth: u32) {
        for c in closes {
            match *c {
                Close::ForIn(sd) => {
                    let it = self.slot(sd - 1);
                    let ei = self.h.end_iter;
                    self.call(ei, &[self.cx, it], None);
                }
                Close::Destructuring(sd) => {
                    let done = self.slot(sd - 1);
                    let it = self.slot(sd - 2);
                    let top = self.top_addr(depth);
                    let f = self.h.close_iter_for_exception;
                    self.call(f, &[self.cx, top, done, it], None);
                }
            }
        }
    }

    /// How many block environments the frame's env chain holds at `pc`
    /// beyond those in effect at the `Try` of the handler at `handler_pc`:
    /// what the interpreter's `UnwindEnvironmentToTryPc` pops.
    fn env_pops(&self, pc: Pc, handler_pc: Pc) -> u32 {
        let Some(try_start) = self
            .script
            .try_notes
            .iter()
            .find(|t| {
                matches!(t.kind, TryNoteKind::Catch | TryNoteKind::Finally)
                    && t.start + t.length == handler_pc
            })
            .map(|t| t.start)
        else {
            return 0;
        };
        let try_pc = Pc::new(try_start.get() - 1);
        self.env_depth_at(pc)
            .saturating_sub(self.env_depth_at(try_pc))
    }

    fn env_depth_at(&self, pc: Pc) -> u32 {
        let n = self
            .script
            .scope_notes
            .iter()
            .filter(|n| pc >= n.start && pc < n.start + n.length)
            .filter(|n| self.env_scopes.contains(&n.gcthing_index))
            .count();
        u32::try_from(n).unwrap()
    }

    /// The exceptional entry to a finally block: push the pending
    /// exception, its stack and `true` (throwing) at the note's depth.
    fn finally_landing(&mut self, handler_pc: Pc, sd: u32) -> Block {
        if let Some(&b) = self.finally_landing.get(&handler_pc) {
            return b;
        }
        let saved = (self.cur, self.live, self.pc, self.d);
        let lp = self.fresh();
        self.finally_landing.insert(handler_pc, lp);
        let exc = self.top_addr(sd);
        let stk = self.top_addr(sd + 1);
        let gef = self.h.get_exception_for_finally;
        let ok = self
            .call(gef, &[self.cx, exc, stk], Some(Type::I32))
            .unwrap();
        (self.pc, self.d) = (handler_pc, sd);
        self.branch_on_err(ok);
        let t = self.i64c((TAG_BOOLEAN << 32) | 1);
        self.set_slot(sd + 2, t);
        let target = Self::goto(self.block(handler_pc));
        self.br(target);
        (self.cur, self.live, self.pc, self.d) = saved;
        lp
    }

    /// The block that starts at `pc`.
    fn block(&mut self, pc: Pc) -> Block {
        if let Some(&b) = self.blocks.get(&pc) {
            return b;
        }
        let b = self.body.add_block();
        self.blocks.insert(pc, b);
        if self.needs_dispatch(pc) {
            let code = self.body.add_block();
            self.dispatch.insert(pc, (b, code));
        }
        b
    }

    /// Whether the loop headed at `pc` contains a resume target (other than
    /// itself), so resumes must be dispatched through it.
    fn needs_dispatch(&self, pc: Pc) -> bool {
        self.loops
            .iter()
            .any(|&(h, e)| h == pc && self.resume_targets.iter().any(|&t| t > h && t < e))
    }

    /// The dispatching loop headers enclosing `t`, outermost first.
    fn dispatch_chain(&self, t: Pc) -> Vec<Pc> {
        let mut hs: Vec<(Pc, Pc)> = self
            .loops
            .iter()
            .copied()
            .filter(|&(h, e)| h < t && t < e)
            .collect();
        // Outermost first: earlier header, then the longer interval.
        hs.sort_by_key(|&(h, e)| (h, std::cmp::Reverse(e)));
        hs.into_iter().map(|(h, _)| h).collect()
    }

    // --- prologue -------------------------------------------------------------

    fn env_is_plain(&self) -> bool {
        let Some(bs) = self.script.body_scope else {
            return false;
        };
        let SourceObject::Scope(ScopeData {
            kind: 0,
            has_environment: false,
            enclosing,
            ..
        }) = self.ctx.source.object(bs)
        else {
            return false;
        };
        // A named lambda's own-name environment is built by the setup.
        !enclosing.is_some_and(|e| {
            matches!(
                self.ctx.source.object(e),
                SourceObject::Scope(ScopeData {
                    is_named_lambda: true,
                    has_environment: true,
                    ..
                })
            )
        })
    }

    /// `argc` without its flag bits, and `vp`. Emitted in the entry block,
    /// ahead of any fork, so every path (fresh call or resume) sees them. A
    /// generator resume passes `argc = 0`, so its `vp` is `sp`.
    fn frame_regs(&mut self) {
        let nargs = u32::from(self.script.nargs);
        let flags = self.i32c(!ARGC_FLAGS);
        self.argc = self.binop(Operator::I32And, self.argc, flags, Type::I32);
        if self.layout.rebase_vp {
            let n = self.i32c(nargs);
            let extra = self.binop(Operator::I32Sub, self.argc, n, Type::I32);
            let more = self.binop(Operator::I32GtU, self.argc, n, Type::I32);
            let zero = self.i32c(0);
            let extra = self.select(Type::I32, extra, zero, more);
            let eight = self.i32c(8);
            let bytes = self.binop(Operator::I32Mul, extra, eight, Type::I32);
            self.vp = self.binop(Operator::I32Add, self.sp, bytes, Type::I32);
        }
    }

    fn prologue(&mut self) {
        let nargs = u32::from(self.script.nargs);
        // Formals the caller did not pass read as undefined.
        let undef = self.i64c(UNDEF);
        for i in 0..nargs {
            let off = self.layout.arg(i);
            let cur = self.load_i64(self.sp, off);
            let iv = self.i32c(i);
            let keep = self.binop(Operator::I32LtU, iv, self.argc, Type::I32);
            let v = self.select(Type::I64, cur, undef, keep);
            self.store_i64(self.sp, off, v);
        }
        // Every slot is a valid Value before the first helper call.
        for j in 0..self.layout.nlocals {
            self.store_i64(self.vp, self.layout.local(j), undef);
        }
        self.store_i64(self.vp, self.layout.env(), undef);
        self.store_i64(self.vp, self.layout.args_obj(), undef);
        self.store_i64(self.vp, self.layout.new_target(), self.new_target);
        self.store_i64(self.vp, self.layout.rval(), undef);
        let resume = self.i64c(TAG_INT32 << 32);
        self.store_i64(self.vp, self.layout.resume(), resume);
        self.store_i64(self.vp, self.layout.backoff(), resume);
        // Exceptions from the prologue have no handler: pc 0, depth 0.
        (self.pc, self.d) = (Pc::new(0), 0);
        if self.needs_env {
            if self.env_is_plain() {
                let callee = self.load_i64(self.sp, 0);
                let p = self.unop(Operator::I32WrapI64, callee, Type::I32);
                let env = self.load_i64(p, FUNC_ENV_SLOT_OFFSET);
                self.set_env(env);
            } else {
                let script = self.script_ptr();
                let es = self.h.env_setup;
                let env = self.rt(es, &[self.sp, script]);
                self.set_env(env);
            }
        }
        if self.script.has_mapped_args {
            let args = if self.needs_env {
                let env = self.env();
                let f = self.h.arguments_env;
                self.rt(f, &[self.sp, self.argc, env])
            } else {
                let f = self.h.arguments_;
                self.rt(f, &[self.sp, self.argc])
            };
            self.store_i64(self.vp, self.layout.args_obj(), args);
        }
    }

    // --- the walk ---------------------------------------------------------------

    pub(super) fn run(&mut self) -> R<()> {
        self.loops = crate::wasm::translate::scan_loop_intervals(self.script)
            .into_iter()
            .map(|(h, e)| (Pc::new(h), Pc::new(e)))
            .collect();
        self.loops.sort();
        self.frame_regs();
        for w in self.ext_resumes.clone() {
            if self.depths.at(w.pc).is_none() {
                return Err(format!("resume at pc {} with no stack depth", w.pc));
            }
            self.resume_targets.insert(w.pc);
            self.resume_words.insert(w);
        }
        if self.is_gen {
            self.scan_resumes()?;
            // Fresh call or resume: a resume stages the generator-closing
            // magic as `this`, which no call can pass.
            let thisv = self.load_i64(self.sp, FrameLayout::THIS);
            let magic = self.i64c((TAG_MAGIC << 32) | MAGIC_GENERATOR_CLOSING);
            let is_resume = self.binop(Operator::I64Eq, thisv, magic, Type::I32);
            let disp = self.body.add_block();
            let fresh = self.body.add_block();
            self.gen_dispatch_blk = Some(disp);
            self.cond_br(is_resume, Self::goto(disp), Self::goto(fresh));
            self.cur = fresh;
            self.live = true;
        }
        let resume_blk = if self.ext_resumes.is_empty() {
            None
        } else {
            // A resume (from a MIR exit) finds the frame already written:
            // it skips the prologue and routes by the resume word.
            let bit = self.i32c(ARGC_RESUME_BIT);
            let is_resume = self.binop(Operator::I32And, self.argc_raw, bit, Type::I32);
            let disp = self.body.add_block();
            let fresh = self.body.add_block();
            self.cond_br(is_resume, Self::goto(disp), Self::goto(fresh));
            self.cur = fresh;
            self.live = true;
            Some(disp)
        };
        self.resume_disp = resume_blk;
        if !self.onramps.is_empty() && resume_blk.is_none() {
            return Err("BUG: onramps without resume words".into());
        }
        self.prologue();
        let mut leaders = layout::leaders(self.script);
        // A suspend returns, so the code after it is entered only by a
        // resume: each landing starts a block.
        leaders.extend(self.resume_targets.iter().copied());
        let len = self.script.bytecode.len();
        let mut p = self.script.parser();
        loop {
            let pc = Pc::new(u32::try_from(len - p.remaining()).unwrap());
            let Some(op) = p.next_op() else { break };
            let depth = self.depths.at(pc);
            if leaders.contains(&pc) && depth.is_some() {
                let b = self.block(pc);
                if self.live {
                    self.br(Self::goto(b));
                }
                self.cur = match self.dispatch.get(&pc) {
                    Some(&(_, code)) => code,
                    None => b,
                };
                self.live = true;
                if depth.is_some() && self.onramps.contains_key(&pc) {
                    self.onramp(pc);
                }
            }
            let (Some(d), true) = (depth, self.live) else {
                // Unreachable: skip the op.
                skip(&mut p, op);
                continue;
            };
            (self.pc, self.d) = (pc, d);
            let before = p.remaining();
            self.op(&mut p, op)?;
            let consumed = before - p.remaining() + 1;
            if consumed != op.len() as usize {
                return Err(format!(
                    "BUG: {op:?} at {pc} consumed {consumed} bytes, expected {}",
                    op.len()
                ));
            }
            // A falling-through op whose successor starts a block is joined
            // at the top of the loop; a non-falling-through one has already
            // terminated.
        }
        if self.live {
            self.terminate(Terminator::Unreachable);
        }
        self.finalize_dispatch();
        self.finalize_gen_dispatch();
        if let Some(disp) = resume_blk {
            self.finalize_resume_dispatch(disp);
        }
        // Every block must end somewhere: an unterminated one would be
        // emitted as a trap. Declining is always safe; trapping is not.
        for (b, data) in self.body.blocks.entries() {
            if matches!(data.terminator, Terminator::None) {
                let pc = self.blocks.iter().find(|&(_, &x)| x == b).map(|(p, _)| *p);
                return Err(format!("BUG: unterminated block {b} (pc {pc:?})"));
            }
        }
        Ok(())
    }

    /// Find every yield's resume label and landing.
    fn scan_resumes(&mut self) -> R<()> {
        let len = self.script.bytecode.len();
        let mut p = self.script.parser();
        loop {
            let pc = Pc::new(u32::try_from(len - p.remaining()).unwrap());
            let Some(op) = p.next_op() else { break };
            if matches!(op, JSOp::InitialYield | JSOp::Yield | JSOp::Await) {
                let k = p.next_uint24().ok_or("yield: missing resume index")?;
                let popped = if op == JSOp::InitialYield { 1 } else { 2 };
                if let Some(d) = self.depths.at(pc) {
                    let landing = pc + op.len();
                    self.gen_resume.push((k, landing, d - popped));
                    self.resume_targets.insert(landing);
                    self.resume_words.insert(ResumeWord {
                        pc: landing,
                        mode: ResumeMode::Continue,
                    });
                }
            } else {
                skip(&mut p, op);
            }
        }
        Ok(())
    }

    fn resume_word(&mut self) -> Value {
        self.load_i32(self.vp, self.layout.resume())
    }

    fn set_resume_word(&mut self, payload: u32) {
        let v = self.i64c((TAG_INT32 << 32) | u64::from(payload));
        self.store_i64(self.vp, self.layout.resume(), v);
    }

    /// A MIR onramp at loop header `h`, before the header's code: count the
    /// frame's backoff down, or, when it is zero, call the MIR body at its
    /// onramp root for `h` with this frame. The MIR body returns normally
    /// (baseline returns its result), or DEOPT with the frame rewritten
    /// and a resume word set (baseline resumes through its dispatch). MIR
    /// exits set the backoff, so baseline runs some iterations before it
    /// tries again.
    fn onramp(&mut self, h: Pc) {
        let backoff = self.load_i32(self.vp, self.layout.backoff());
        let z = self.i32c(0);
        let ready = self.binop(Operator::I32Eq, backoff, z, Type::I32);
        let (try_blk, wait_blk, cont) = (
            self.body.add_block(),
            self.body.add_block(),
            self.body.add_block(),
        );
        self.cond_br(ready, Self::goto(try_blk), Self::goto(wait_blk));
        self.cur = wait_blk;
        self.live = true;
        let one = self.i32c(1);
        let left = self.binop(Operator::I32Sub, backoff, one, Type::I32);
        let boxed = self.boxed_int32(left);
        self.store_i64(self.vp, self.layout.backoff(), boxed);
        self.br(Self::goto(cont));
        self.cur = try_blk;
        self.live = true;
        let w = ResumeWord {
            pc: h,
            mode: ResumeMode::Continue,
        };
        self.set_resume_word(w.encode() as u32);
        let bit = self.i32c(ARGC_ONRAMP_BIT);
        let argc = self.binop(Operator::I32Or, self.argc, bit, Type::I32);
        let args = [
            self.cx,
            self.sp,
            argc,
            self.retval_out,
            self.script_param,
            self.new_target,
        ];
        let args = self.body.arg_pool.from_iter(args.into_iter());
        let tys = self
            .body
            .type_pool
            .from_iter([Type::I32, Type::I32].into_iter());
        let call = self.push_val(ValueDef::Operator(
            Operator::Call {
                function_index: Func::invalid(),
            },
            args,
            tys,
        ));
        self.main_calls.push(call);
        let err = self.push_val(ValueDef::PickOutput(call, 0, Type::I32));
        let eff = self.push_val(ValueDef::PickOutput(call, 1, Type::I32));
        let (done, other, deopt) = (
            self.body.add_block(),
            self.body.add_block(),
            self.body.add_block(),
        );
        let z = self.i32c(0);
        let is_done = self.binop(Operator::I32Eq, err, z, Type::I32);
        self.cond_br(is_done, Self::goto(done), Self::goto(other));
        self.cur = done;
        self.live = true;
        self.terminate(Terminator::Return {
            values: vec![err, eff],
        });
        self.cur = other;
        self.live = true;
        let d = self.i32c(ERR_DEOPT);
        let is_deopt = self.binop(Operator::I32Eq, err, d, Type::I32);
        let error = self.error_return();
        self.cond_br(is_deopt, Self::goto(deopt), Self::goto(error));
        // DEOPT: route by the resume word the MIR exit wrote, among those
        // this onramp's root reaches -- only pcs inside the loops around
        // it or after it, which route reducibly (`deopt_route`). Not
        // through the entry's resume dispatch: that block is also entered
        // from the function entry, so a loop reaching it would have two
        // entries.
        let words = self.onramps[&h].clone();
        let hops: Vec<(ResumeWord, Block)> =
            words.iter().map(|&w| (w, self.deopt_route(h, w))).collect();
        self.cur = deopt;
        self.live = true;
        let word = self.resume_word();
        let bad = self.body.add_block();
        self.dispatch_on(word, hops, Self::goto(bad));
        self.cur = bad;
        self.live = true;
        self.terminate(Terminator::Unreachable);
        self.cur = cont;
        self.live = true;
    }

    /// Where an onramp at header `h` sends a DEOPT for resume word `w`,
    /// keeping the CFG reducible: to the dispatch block of the innermost
    /// loop around the onramp that contains `w.pc` (a back edge to that
    /// loop's header, which routes inward), or, when none does, along
    /// `w`'s route from outside every loop (a loop exit, then entries only
    /// through headers).
    fn deopt_route(&mut self, h: Pc, w: ResumeWord) -> Block {
        let mut around: Vec<(Pc, Pc)> = self
            .loops
            .iter()
            .copied()
            .filter(|&(hh, e)| hh <= h && h < e)
            .collect();
        // Innermost first.
        around.sort_by_key(|&(hh, e)| (std::cmp::Reverse(hh), e));
        match around.iter().find(|&&(hh, e)| hh < w.pc && w.pc < e) {
            Some(&(hh, _)) => self.block(hh),
            None => self.resume_route(w),
        }
    }

    /// The first hop toward resume word `w` from outside every loop: the
    /// outermost dispatching header enclosing its pc, or its landing.
    fn resume_route(&mut self, w: ResumeWord) -> Block {
        match self.dispatch_chain(w.pc).first() {
            Some(&h) => self.block(h),
            None => self.resume_landing(w),
        }
    }

    /// The last hop for resume word `w`: clear the resume word, then
    /// - `Continue`: enter `w.pc`, through its own dispatch block if it is
    ///   a dispatching header, so no loop is entered anywhere but its
    ///   header node;
    /// - `Throw` (a MIR throw exit, the exception pending): take `w.pc`'s
    ///   exception landing, as the op there would have on failure.
    fn resume_landing(&mut self, w: ResumeWord) -> Block {
        let saved = (self.cur, self.live, self.pc, self.d);
        let l = self.fresh();
        self.set_resume_word(RESUME_NONE);
        let target = match w.mode {
            ResumeMode::Continue => Self::goto(self.block(w.pc)),
            ResumeMode::Throw => {
                let d = self.depths.at(w.pc).expect("resume pcs have a depth");
                (self.pc, self.d) = (w.pc, d);
                self.exc_target(w.pc, d)
            }
        };
        self.br(target);
        (self.cur, self.live, self.pc, self.d) = saved;
        l
    }

    /// Emit each dispatching header's dispatch block: not resuming, run the
    /// header; resuming to a target inside, take the next hop toward it.
    fn finalize_dispatch(&mut self) {
        let headers: Vec<(Pc, Block, Block)> = self
            .dispatch
            .iter()
            .map(|(&h, &(d, c))| (h, d, c))
            .collect();
        let targets: Vec<ResumeWord> = self.resume_words.iter().copied().collect();
        for (h, disp, code) in headers {
            let mut hops = vec![];
            for &t in &targets {
                let chain = self.dispatch_chain(t.pc);
                if let Some(i) = chain.iter().position(|&x| x == h) {
                    let next = match chain.get(i + 1) {
                        Some(&inner) => self.block(inner),
                        None => self.resume_landing(t),
                    };
                    hops.push((t, next));
                }
            }
            self.cur = disp;
            self.live = true;
            let w = self.resume_word();
            self.dispatch_on(w, hops, Self::goto(code));
        }
    }

    /// Branch on the resume word `w` to each hop's block; anything else
    /// goes to `default`.
    fn dispatch_on(&mut self, w: Value, hops: Vec<(ResumeWord, Block)>, default: BlockTarget) {
        for (t, next) in hops {
            let k = self.i32c(t.encode() as u32);
            let hit = self.binop(Operator::I32Eq, w, k, Type::I32);
            let no = self.body.add_block();
            self.cond_br(hit, Self::goto(next), Self::goto(no));
            self.cur = no;
            self.live = true;
        }
        self.br(default);
    }

    /// The `ARGC_RESUME_BIT` entry (a MIR exit): route by the resume word
    /// to one of `ext_resumes`. The MIR body wrote the whole frame, so the
    /// prologue does not run. A word outside the set is a compiler bug.
    fn finalize_resume_dispatch(&mut self, disp: Block) {
        self.cur = disp;
        self.live = true;
        let bad = self.body.add_block();
        let words = self.ext_resumes.clone();
        let hops: Vec<(ResumeWord, Block)> =
            words.iter().map(|&w| (w, self.resume_route(w))).collect();
        self.cur = disp;
        self.live = true;
        let w = self.resume_word();
        self.dispatch_on(w, hops, Self::goto(bad));
        self.cur = bad;
        self.live = true;
        self.terminate(Terminator::Unreachable);
    }

    /// The generator resume entry: read the descriptor `EnterNightResume`
    /// staged, restore the frame from the generator object, push the
    /// resume protocol's `[sent value, generator, resume kind]` at the
    /// label's depth, and route to its landing.
    fn finalize_gen_dispatch(&mut self) {
        let Some(disp) = self.gen_dispatch_blk else {
            return;
        };
        self.cur = disp;
        self.live = true;
        // The descriptor [index i32, kind i32, gen, arg] overlaps the
        // locals: read it all before writing the frame.
        let desc = self.add_off(self.vp, self.layout.local_base());
        let ridx = self.load_i32(desc, 0);
        let rkind = self.load_i32(desc, 4);
        let m = self.mem(3, 8);
        let rgen = self.unop(Operator::I64Load { memory: m }, desc, Type::I64);
        let m = self.mem(3, 16);
        let rarg = self.unop(Operator::I64Load { memory: m }, desc, Type::I64);
        // The fixed slots the skipped prologue would have set.
        let undef = self.i64c(UNDEF);
        for off in [
            self.layout.env(),
            self.layout.args_obj(),
            self.layout.new_target(),
            self.layout.rval(),
        ] {
            self.store_i64(self.vp, off, undef);
        }
        let zero = self.i64c(TAG_INT32 << 32);
        self.store_i64(self.vp, self.layout.backoff(), zero);
        self.set_resume_word(RESUME_NONE);
        let lp = self.add_off(self.vp, self.layout.local_base());
        let nl = self.i32c(self.layout.nlocals);
        let ep = if self.needs_env {
            self.add_off(self.vp, self.layout.env())
        } else {
            self.i32c(0)
        };
        let ops = self.add_off(self.vp, self.layout.operand_base());
        let gr = self.h.gen_restore;
        self.call(gr, &[self.cx, rgen, lp, nl, ep, ops], Some(Type::I32));
        let bad = self.body.add_block();
        let labels = std::mem::take(&mut self.gen_resume);
        let max_k = labels.iter().map(|&(k, _, _)| k).max().unwrap_or(0);
        let mut targets = vec![Self::goto(bad); (max_k + 1) as usize];
        for &(k, landing, depth) in &labels {
            let pre = self.fresh();
            self.set_slot(depth, rarg);
            self.set_slot(depth + 1, rgen);
            let kb = self.boxed_int32(rkind);
            self.set_slot(depth + 2, kb);
            let enc = layout::ResumeWord {
                pc: landing,
                mode: layout::ResumeMode::Continue,
            }
            .encode() as u32;
            self.set_resume_word(enc);
            let first = self.resume_route(ResumeWord {
                pc: landing,
                mode: ResumeMode::Continue,
            });
            self.br(Self::goto(first));
            targets[k as usize] = Self::goto(pre);
        }
        self.cur = disp;
        self.live = true;
        self.terminate(Terminator::Select {
            value: ridx,
            targets,
            default: Self::goto(bad),
        });
        // A resume index with no label: report an error.
        self.cur = bad;
        self.live = true;
        let one = self.i32c(1);
        let flags = self.i32c(FLAGS_ALL);
        self.terminate(Terminator::Return {
            values: vec![one, flags],
        });
    }

    fn ret(&mut self, v: Value) {
        self.store_i64(self.retval_out, 0, v);
        let zero = self.i32c(0);
        let flags = self.i32c(FLAGS_ALL);
        self.terminate(Terminator::Return {
            values: vec![zero, flags],
        });
    }

    /// `v` to a raw i32 truth value.
    fn truthy(&mut self, v: Value) -> Value {
        let tb = self.h.to_boolean;
        self.call(tb, &[self.cx, v], Some(Type::I32)).unwrap()
    }

    fn branch_to(&mut self, off: i32) -> BlockTarget {
        let t = self.pc.branch(off);
        Self::goto(self.block(t))
    }

    fn next_pc(&self, op: JSOp) -> Pc {
        self.pc + op.len()
    }

    /// Lower one op. Immediates are read from `p`.
    fn op(&mut self, p: &mut BytecodeParser, op: JSOp) -> R<()> {
        use JSOp::*;
        let d = self.d;
        let h = self.h;
        match op {
            Nop | Lineno | JumpTarget | LoopHead | Debugger | NopDestructuring | NopIsAssignOp
            | TryDestructuring | DebugLeaveLexicalEnv | Finally | Try | DebugCheckSelfHosted => {
                skip(p, op);
            }

            // --- constants ---
            Undefined => self.push_const(d, UNDEF),
            Null => self.push_const(d, TAG_NULL << 32),
            False => self.push_const(d, TAG_BOOLEAN << 32),
            True => self.push_const(d, (TAG_BOOLEAN << 32) | 1),
            Zero => self.push_const(d, TAG_INT32 << 32),
            One => self.push_const(d, (TAG_INT32 << 32) | 1),
            Int8 => {
                let i = p.next_int8().unwrap();
                self.push_const(d, (TAG_INT32 << 32) | u64::from(i32::from(i) as u32));
            }
            Uint16 => {
                let i = p.next_uint16().unwrap();
                self.push_const(d, (TAG_INT32 << 32) | u64::from(i));
            }
            Uint24 => {
                let i = p.next_uint24().unwrap();
                self.push_const(d, (TAG_INT32 << 32) | u64::from(i));
            }
            Int32 => {
                let i = p.next_int32().unwrap();
                self.push_const(d, (TAG_INT32 << 32) | u64::from(i as u32));
            }
            Double => {
                let bits = p.next_uint64().unwrap();
                self.push_const(d, bits);
            }
            Hole => self.push_const(d, (TAG_MAGIC << 32) | MAGIC_ELEMENTS_HOLE),
            Uninitialized => self.push_const(d, (TAG_MAGIC << 32) | MAGIC_UNINITIALIZED_LEXICAL),
            IsConstructing => self.push_const(d, (TAG_MAGIC << 32) | MAGIC_IS_CONSTRUCTING),
            Void => self.push_const(d - 1, UNDEF),
            String => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let av = self.i32c(a);
                let r = self.rt(h.string, &[av]);
                self.set_slot(d, r);
            }
            GetIntrinsic => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let av = self.i32c(a);
                let r = self.rt(h.get_intrinsic, &[av]);
                self.set_slot(d, r);
            }
            Object | CallSiteObj => {
                let idx = p.next_uint32().unwrap();
                let iv = self.i32c(idx);
                let script = self.script_ptr();
                let r = self
                    .call(h.object, &[self.cx, script, iv], Some(Type::I64))
                    .unwrap();
                self.set_slot(d, r);
            }
            Symbol => {
                let code = p.next_uint8().unwrap();
                let c = self.i32c(u32::from(code));
                let r = self.call(h.symbol, &[self.cx, c], Some(Type::I64)).unwrap();
                self.set_slot(d, r);
            }
            RegExp => {
                let idx = p.next_uint32().unwrap();
                let iv = self.i32c(idx);
                let script = self.script_ptr();
                let r = self.rt(h.regexp, &[script, iv]);
                self.set_slot(d, r);
            }
            BuiltinObject => {
                let kind = p.next_uint8().unwrap();
                let k = self.i32c(u32::from(kind));
                let r = self.rt(h.builtin_object, &[k]);
                self.set_slot(d, r);
            }

            // --- checks and coercions ---
            IsNullOrUndefined => {
                let v = self.slot(d - 1);
                let u = self.tag_eq(v, TAG_UNDEFINED);
                let n = self.tag_eq(v, TAG_NULL);
                let b = self.binop(Operator::I32Or, u, n, Type::I32);
                let r = self.boxed_bool(b);
                self.set_slot(d, r);
            }
            ToString => self.unary(h.tostring, d),
            ToPropertyKey => self.unary(h.to_property_key, d),
            ToNumeric => {
                // Identity on a number (int32 or double).
                let v = self.slot(d - 1);
                let is_num = self.is_number(v);
                self.fast_path(is_num, |_, _| {}, |g| g.unary(h.tonumeric, d));
            }
            Pos => {
                // Identity on a number.
                let v = self.slot(d - 1);
                let is_num = self.is_number(v);
                self.fast_path(is_num, |_, _| {}, |g| g.unary(h.pos, d));
            }
            ImplicitThis => self.unary(h.implicit_this, d),
            ObjWithProto => self.unary(h.obj_with_proto, d),
            OptimizeSpreadCall => self.unary(h.optimize_spread_call, d),
            CheckObjCoercible => self.check(h.check_obj_coercible, &[]),
            CheckClassHeritage => self.check(h.check_class_heritage, &[]),
            CheckThis => self.check(h.check_this, &[]),
            CheckThisReinit => self.check(h.check_this_reinit, &[]),
            CheckIsObj => {
                let kind = p.next_uint8().unwrap();
                let k = self.i32c(u32::from(kind));
                self.check(h.check_is_obj, &[k]);
            }
            CheckLexical | CheckAliasedLexical => {
                skip(p, op);
                let script = self.script_ptr();
                let pcv = self.i32c(self.pc.get());
                self.check(h.check_lexical, &[script, pcv]);
            }
            CheckReturn => {
                let thisv = self.slot(d - 1);
                let rval = self.load_i64(self.vp, self.layout.rval());
                let r = self.rt(h.check_return, &[thisv, rval]);
                self.set_slot(d - 1, r);
            }
            ThrowSetConst => {
                skip(p, op);
                let script = self.script_ptr();
                let pcv = self.i32c(self.pc.get());
                self.rt_throw(h.throw_set_const, &[script, pcv]);
            }
            ThrowMsg => {
                let kind = p.next_uint8().unwrap();
                let k = self.i32c(u32::from(kind));
                self.rt_throw(h.throw_msg, &[k]);
            }
            Throw => {
                let v = self.slot(d - 1);
                self.rt_throw(h.throw, &[v]);
            }
            ThrowWithStack => {
                let v = self.slot(d - 2);
                let s = self.slot(d - 1);
                self.rt_throw(h.throw_with_stack, &[v, s]);
            }

            // --- frame values ---
            Callee => {
                let c = self.load_i64(self.sp, 0);
                self.set_slot(d, c);
            }
            NewTarget => {
                let nt = self.load_i64(self.vp, self.layout.new_target());
                self.set_slot(d, nt);
            }
            FunctionThis => self.function_this(),
            GlobalThis => {
                let r = self.rt(h.global_this, &[]);
                self.set_slot(d, r);
            }
            ArgumentsLength => {
                let r = self.boxed_int32(self.argc);
                self.set_slot(d, r);
            }
            GetActualArg => {
                let i = self.slot(d - 1);
                let i = self.unop(Operator::I32WrapI64, i, Type::I32);
                let eight = self.i32c(8);
                let off = self.binop(Operator::I32Mul, i, eight, Type::I32);
                let a = self.binop(Operator::I32Add, self.sp, off, Type::I32);
                let v = self.load_i64(a, FrameLayout::ARGS);
                self.set_slot(d - 1, v);
            }
            Rest => {
                let nformal = u32::from(self.script.nargs).saturating_sub(1);
                let nf = self.i32c(nformal);
                let r = self.rt(h.rest, &[self.sp, self.argc, nf]);
                self.set_slot(d, r);
            }
            Arguments => self.arguments(),
            GetArg | GetFrameArg => {
                let n = u32::from(p.next_uint16().unwrap());
                let v = if op == GetArg && self.script.has_mapped_args {
                    let obj = self.load_i64(self.vp, self.layout.args_obj());
                    let i = self.i32c(n);
                    self.call(h.get_mapped_arg, &[obj, i], Some(Type::I64))
                        .unwrap()
                } else {
                    self.load_i64(self.sp, self.layout.arg(n))
                };
                self.set_slot(d, v);
            }
            SetArg => {
                let n = u32::from(p.next_uint16().unwrap());
                let v = self.slot(d - 1);
                if self.script.has_mapped_args {
                    let obj = self.load_i64(self.vp, self.layout.args_obj());
                    let i = self.i32c(n);
                    self.call(h.set_mapped_arg, &[obj, i, v], None);
                } else {
                    self.store_i64(self.sp, self.layout.arg(n), v);
                }
            }
            GetLocal => {
                let n = p.next_uint24().unwrap();
                let v = self.load_i64(self.vp, self.layout.local(n));
                self.set_slot(d, v);
            }
            SetLocal | InitLexical => {
                let n = p.next_uint24().unwrap();
                let v = self.slot(d - 1);
                self.store_i64(self.vp, self.layout.local(n), v);
            }
            GetRval => {
                let v = self.load_i64(self.vp, self.layout.rval());
                self.set_slot(d, v);
            }
            SetRval => {
                let v = self.slot(d - 1);
                self.store_i64(self.vp, self.layout.rval(), v);
            }

            // --- environments ---
            GetAliasedVar | GetAliasedDebugVar => {
                let hops = u32::from(p.next_uint16().unwrap());
                let s = p.next_uint24().unwrap();
                let env = self.env();
                let (hv, sv) = (self.i32c(hops), self.i32c(s));
                let v = self
                    .call(h.get_aliased, &[self.cx, env, hv, sv], Some(Type::I64))
                    .unwrap();
                self.set_slot(d, v);
            }
            SetAliasedVar | InitAliasedLexical => {
                let hops = u32::from(p.next_uint16().unwrap());
                let s = p.next_uint24().unwrap();
                let env = self.env();
                let (hv, sv) = (self.i32c(hops), self.i32c(s));
                let v = self.slot(d - 1);
                self.call(h.set_aliased, &[self.cx, env, hv, sv, v], None);
            }
            Lambda => {
                let fi = p.next_uint32().unwrap();
                let env = self.env();
                let script = self.script_ptr();
                let f = self.i32c(fi);
                let r = self.rt(h.lambda, &[env, script, f]);
                self.set_slot(d, r);
            }
            FunWithProto => {
                let fi = p.next_uint32().unwrap();
                let proto = self.slot(d - 1);
                let env = self.env();
                let script = self.script_ptr();
                let f = self.i32c(fi);
                let r = self.rt(h.fun_with_proto, &[env, proto, script, f]);
                self.set_slot(d - 1, r);
            }
            PushLexicalEnv | PushClassBodyEnv | PushVarEnv => {
                skip(p, op);
                let f = match op {
                    PushLexicalEnv => h.push_lexical_env,
                    PushClassBodyEnv => h.push_class_body_env,
                    _ => h.push_var_env,
                };
                let env = self.env();
                let script = self.script_ptr();
                let pcv = self.i32c(self.pc.get());
                let r = self.rt(f, &[env, script, pcv]);
                self.set_env(r);
            }
            EnterWith => {
                skip(p, op);
                let v = self.slot(d - 1);
                let env = self.env();
                let script = self.script_ptr();
                let pcv = self.i32c(self.pc.get());
                let r = self.rt(h.enter_with, &[env, v, script, pcv]);
                self.set_env(r);
            }
            FreshenLexicalEnv | RecreateLexicalEnv => {
                skip(p, op);
                let f = if op == FreshenLexicalEnv {
                    h.freshen_lexical_env
                } else {
                    h.recreate_lexical_env
                };
                let env = self.env();
                let r = self.rt(f, &[env]);
                self.set_env(r);
            }
            PopLexicalEnv | LeaveWith => {
                let env = self.env();
                let ptr = self.unop(Operator::I32WrapI64, env, Type::I32);
                let enclosing = self.load_i64(ptr, FIXED_SLOTS_BASE);
                self.set_env(enclosing);
            }
            SetFunName => {
                let prefix = p.next_uint8().unwrap();
                let name = self.slot(d - 1);
                let fun = self.slot(d - 2);
                let k = self.i32c(u32::from(prefix));
                self.rt(h.set_fun_name, &[fun, name, k]);
            }
            InitGLexical => {
                skip(p, op);
                let v = self.slot(d - 1);
                let script = self.script_ptr();
                let pcv = self.i32c(self.pc.get());
                self.rt(h.init_glexical, &[v, script, pcv]);
            }
            GetName => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let for_typeof = self.next_is_typeof(op);
                let env = self.env();
                let (av, tv) = (self.i32c(a), self.i32c(u32::from(for_typeof)));
                let r = self.rt(h.get_name, &[env, av, tv]);
                self.set_slot(d, r);
            }
            BindName | BindUnqualifiedName | DelName => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let f = match op {
                    BindName => h.bind_name,
                    BindUnqualifiedName => h.bind_unqualified_name,
                    _ => h.del_name,
                };
                let env = self.env();
                let av = self.i32c(a);
                let r = self.rt(f, &[env, av]);
                self.set_slot(d, r);
            }
            GetBoundName => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let env = self.slot(d - 1);
                let av = self.i32c(a);
                let r = self.rt(h.get_bound_name, &[env, av]);
                self.set_slot(d - 1, r);
            }
            BindVar => {
                let env = self.env();
                let r = self.rt(h.bind_var, &[env]);
                self.set_slot(d, r);
            }
            GlobalOrEvalDeclInstantiation => {
                let idx = p.next_uint32().unwrap();
                let script = self.script_ptr();
                let iv = self.i32c(idx);
                self.rt(h.global_decl_instantiation, &[script, iv]);
            }
            GetGName => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let for_typeof = self.next_is_typeof(op);
                let (av, tv) = (self.i32c(a), self.i32c(u32::from(for_typeof)));
                let r = self.rt(h.get_gname, &[av, tv]);
                self.set_slot(d, r);
            }
            BindUnqualifiedGName => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let av = self.i32c(a);
                let r = self.rt(h.bind_unqualified_gname, &[av]);
                self.set_slot(d, r);
            }
            SetGName | StrictSetGName | SetName | StrictSetName => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let strict = matches!(op, StrictSetGName | StrictSetName);
                let env = self.slot(d - 2);
                let v = self.slot(d - 1);
                let (av, sv) = (self.i32c(a), self.i32c(u32::from(strict)));
                self.rt(h.set_name, &[env, av, v, sv]);
                let v = self.slot(d - 1);
                self.set_slot(d - 2, v);
            }

            // --- stack manipulation ---
            Pop => {}
            PopN => {
                p.next_uint16().unwrap();
            }
            Dup => {
                let v = self.slot(d - 1);
                self.set_slot(d, v);
            }
            Dup2 => {
                let a = self.slot(d - 2);
                let b = self.slot(d - 1);
                self.set_slot(d, a);
                self.set_slot(d + 1, b);
            }
            DupAt => {
                let n = p.next_uint24().unwrap();
                let v = self.slot(d - 1 - n);
                self.set_slot(d, v);
            }
            Swap => {
                let a = self.slot(d - 2);
                let b = self.slot(d - 1);
                self.set_slot(d - 2, b);
                self.set_slot(d - 1, a);
            }
            Pick => {
                // Move slot d-1-n to the top, shifting the ones above down.
                let n = u32::from(p.next_uint8().unwrap());
                let v = self.slot(d - 1 - n);
                for k in (d - 1 - n)..(d - 1) {
                    let w = self.slot(k + 1);
                    self.set_slot(k, w);
                }
                self.set_slot(d - 1, v);
            }
            Unpick => {
                // Move the top down to slot d-1-n, shifting the ones there up.
                let n = u32::from(p.next_uint8().unwrap());
                let v = self.slot(d - 1);
                for k in ((d - 1 - n)..(d - 1)).rev() {
                    let w = self.slot(k);
                    self.set_slot(k + 1, w);
                }
                self.set_slot(d - 1 - n, v);
            }

            // --- arithmetic and comparison ---
            // Inline arms as in the portable baseline interpreter: int32
            // operands, then any numbers (as doubles), then the helper
            // (`number_arms`).
            Add | Sub | Mul | Div | Mod | BitAnd | BitOr | BitXor | Lsh | Rsh | Ursh => {
                let a = self.slot(d - 2);
                let b = self.slot(d - 1);
                let int: Option<Int32Op<'a>> = match op {
                    Add => Some(Self::add_i32),
                    Sub => Some(Self::sub_i32),
                    Mul => Some(Self::mul_i32),
                    Mod => Some(Self::mod_i32),
                    BitAnd => Some(|g, x, y, _| g.binop(Operator::I32And, x, y, Type::I32)),
                    BitOr => Some(|g, x, y, _| g.binop(Operator::I32Or, x, y, Type::I32)),
                    BitXor => Some(|g, x, y, _| g.binop(Operator::I32Xor, x, y, Type::I32)),
                    // Wasm masks shift counts to 5 bits, as JS does.
                    Lsh => Some(|g, x, y, _| g.binop(Operator::I32Shl, x, y, Type::I32)),
                    Rsh => Some(|g, x, y, _| g.binop(Operator::I32ShrS, x, y, Type::I32)),
                    Ursh => Some(Self::ursh_i32),
                    _ => None,
                };
                // Double `%` is fmod, which Wasm lacks: the helper does it.
                let num = match op {
                    Add => Some(Operator::F64Add),
                    Sub => Some(Operator::F64Sub),
                    Mul => Some(Operator::F64Mul),
                    Div => Some(Operator::F64Div),
                    _ => None,
                };
                let int_arm = int.map(|f| {
                    move |g: &mut Self, v: &[Value], bail| {
                        let r = f(g, v[0], v[1], bail);
                        g.boxed_int32(r)
                    }
                });
                let num_arm = num.map(|o| {
                    move |g: &mut Self, v: &[Value]| {
                        let r = g.binop(o, v[0], v[1], Type::F64);
                        g.box_number(r)
                    }
                });
                self.number_arms(
                    &[a, b],
                    int_arm.as_ref().map(|f| f as &IntArm<'_, 'a>),
                    num_arm.as_ref().map(|f| f as &NumArm<'_, 'a>),
                    |g| {
                        let r = if op == Add {
                            g.rt(h.add, &[a, b])
                        } else {
                            let k = g.i32c(binop_kind(op));
                            g.rt(h.binop, &[k, a, b])
                        };
                        g.set_slot(d - 2, r);
                    },
                );
            }
            Inc | Dec | Neg | BitNot => {
                let a = self.slot(d - 1);
                let int_arm = |g: &mut Self, v: &[Value], bail| {
                    let x = v[0];
                    let r = if op == BitNot {
                        let m1 = g.i32c(u32::MAX);
                        g.binop(Operator::I32Xor, x, m1, Type::I32)
                    } else {
                        // Inc and Dec overflow only from the extreme value;
                        // Neg of 0 is -0 and of INT32_MIN overflows.
                        let (limit, bin) = match op {
                            Inc => (i32::MAX as u32, Operator::I32Add),
                            Dec => (i32::MIN as u32, Operator::I32Sub),
                            _ => (i32::MIN as u32, Operator::I32Sub),
                        };
                        let l = g.i32c(limit);
                        let ovf = g.binop(Operator::I32Eq, x, l, Type::I32);
                        g.bail_if(ovf, bail);
                        if op == Neg {
                            let zero = g.unop(Operator::I32Eqz, x, Type::I32);
                            g.bail_if(zero, bail);
                            let z = g.i32c(0);
                            g.binop(Operator::I32Sub, z, x, Type::I32)
                        } else {
                            let one = g.i32c(1);
                            g.binop(bin, x, one, Type::I32)
                        }
                    };
                    g.boxed_int32(r)
                };
                let num_arm = |g: &mut Self, v: &[Value]| {
                    let r = match op {
                        Neg => g.unop(Operator::F64Neg, v[0], Type::F64),
                        _ => {
                            let one = g.f64c(1.0);
                            let bin = if op == Inc {
                                Operator::F64Add
                            } else {
                                Operator::F64Sub
                            };
                            g.binop(bin, v[0], one, Type::F64)
                        }
                    };
                    g.box_number(r)
                };
                self.number_arms(
                    &[a],
                    Some(&int_arm),
                    (op != BitNot).then_some(&num_arm as &NumArm<'_, 'a>),
                    |g| {
                        let r = match op {
                            Neg => g.rt(h.neg, &[a]),
                            _ => {
                                let k = g.i32c(binop_kind(op));
                                g.rt(h.binop, &[k, a, a])
                            }
                        };
                        g.set_slot(d - 1, r);
                    },
                );
            }
            Pow => self.binary(h.pow, &[], d),
            Lt | Gt | Le | Ge => {
                let (kind, icmp, fcmp) = match op {
                    Lt => (CMP_LT, Operator::I32LtS, Operator::F64Lt),
                    Gt => (CMP_GT, Operator::I32GtS, Operator::F64Gt),
                    Le => (CMP_LE, Operator::I32LeS, Operator::F64Le),
                    _ => (CMP_GE, Operator::I32GeS, Operator::F64Ge),
                };
                let a = self.slot(d - 2);
                let b = self.slot(d - 1);
                self.number_arms(
                    &[a, b],
                    Some(&|g: &mut Self, v: &[Value], _| {
                        let r = g.binop(icmp, v[0], v[1], Type::I32);
                        g.boxed_bool(r)
                    }),
                    Some(&|g: &mut Self, v: &[Value]| {
                        // False on NaN, as JS wants.
                        let r = g.binop(fcmp, v[0], v[1], Type::I32);
                        g.boxed_bool(r)
                    }),
                    |g| g.compare(kind, a, b),
                );
            }
            Eq | Ne | StrictEq | StrictNe => {
                let (kind, negate) = match op {
                    Eq => (CMP_EQ, false),
                    Ne => (CMP_NE, true),
                    StrictEq => (CMP_STRICTEQ, false),
                    _ => (CMP_STRICTNE, true),
                };
                let a = self.slot(d - 2);
                let b = self.slot(d - 1);
                let (inline, eq) = self.equality_inline(a, b);
                self.fast_path(
                    inline,
                    |g, _| {
                        let r = if negate {
                            g.unop(Operator::I32Eqz, eq, Type::I32)
                        } else {
                            eq
                        };
                        let r = g.boxed_bool(r);
                        g.set_slot(d - 2, r);
                    },
                    // Two numbers (at least one a double): loose and strict
                    // equality are both IEEE equality (NaN unequal, -0 == 0).
                    |g| {
                        g.number_arms(
                            &[a, b],
                            None,
                            Some(&|g: &mut Self, v: &[Value]| {
                                let o = if negate {
                                    Operator::F64Ne
                                } else {
                                    Operator::F64Eq
                                };
                                let r = g.binop(o, v[0], v[1], Type::I32);
                                g.boxed_bool(r)
                            }),
                            |g| g.compare(kind, a, b),
                        )
                    },
                );
            }
            Not => {
                let v = self.slot(d - 1);
                let (fast, truth) = self.truthy_inline(v);
                self.fast_path(
                    fast,
                    |g, _| {
                        let n = g.unop(Operator::I32Eqz, truth, Type::I32);
                        let r = g.boxed_bool(n);
                        g.set_slot(d - 1, r);
                    },
                    |g| {
                        let t = g.truthy(v);
                        let n = g.unop(Operator::I32Eqz, t, Type::I32);
                        let r = g.boxed_bool(n);
                        g.set_slot(d - 1, r);
                    },
                );
            }
            Typeof | TypeofExpr => {
                let v = self.slot(d - 1);
                let r = self
                    .call(h.typeof_, &[self.cx, v], Some(Type::I64))
                    .unwrap();
                self.set_slot(d - 1, r);
            }
            TypeofEq => {
                let operand = p.next_uint8().unwrap();
                let v = self.slot(d - 1);
                let o = self.i32c(u32::from(operand));
                let b = self
                    .call(h.typeof_eq, &[self.cx, v, o], Some(Type::I32))
                    .unwrap();
                let r = self.boxed_bool(b);
                self.set_slot(d - 1, r);
            }
            StrictConstantEq | StrictConstantNe => {
                let operand = p.next_uint16().unwrap();
                let v = self.slot(d - 1);
                let o = self.i32c(u32::from(operand));
                let mut b = self
                    .call(h.constant_strict_eq, &[self.cx, v, o], Some(Type::I32))
                    .unwrap();
                if op == StrictConstantNe {
                    let z = self.i32c(0);
                    b = self.binop(Operator::I32Eq, b, z, Type::I32);
                }
                let r = self.boxed_bool(b);
                self.set_slot(d - 1, r);
            }

            // --- control flow ---
            Goto => {
                let off = p.next_int32().unwrap();
                let t = self.branch_to(off);
                self.br(t);
            }
            JumpIfFalse | JumpIfTrue | And | Or => {
                let off = p.next_int32().unwrap();
                let v = self.slot(d - 1);
                let taken = self.branch_to(off);
                let next = Self::goto(self.block(self.next_pc(op)));
                if matches!(op, JumpIfTrue | Or) {
                    self.branch_truthy(v, taken, next);
                } else {
                    self.branch_truthy(v, next, taken);
                }
            }
            Case => {
                let off = p.next_int32().unwrap();
                let v = self.slot(d - 1);
                let taken = self.branch_to(off);
                let next = Self::goto(self.block(self.next_pc(op)));
                self.branch_truthy(v, taken, next);
            }
            Coalesce => {
                let off = p.next_int32().unwrap();
                let v = self.slot(d - 1);
                let u = self.tag_eq(v, TAG_UNDEFINED);
                let n = self.tag_eq(v, TAG_NULL);
                let nullish = self.binop(Operator::I32Or, u, n, Type::I32);
                let taken = self.branch_to(off);
                let next = Self::goto(self.block(self.next_pc(op)));
                self.cond_br(nullish, next, taken);
            }
            Default => {
                let off = p.next_int32().unwrap();
                let t = self.branch_to(off);
                self.br(t);
            }
            TableSwitch => self.table_switch(p)?,
            Return => {
                let v = self.slot(d - 1);
                self.ret(v);
            }
            RetRval => {
                let v = self.load_i64(self.vp, self.layout.rval());
                self.ret(v);
            }

            // --- calls ---
            Call | CallContent | CallIgnoresRv | CallIter | CallContentIter => {
                let argc = u32::from(p.next_uint16().unwrap());
                if matches!(op, CallIter | CallContentIter) {
                    self.call_op(h.call_iter, argc, argc + 2, &[]);
                } else {
                    self.call_direct_or_generic(argc);
                }
            }
            New | NewContent | SuperCall => {
                let argc = u32::from(p.next_uint16().unwrap());
                let nslots = self.i32c(NO_NSLOTS);
                let stamp = self.i32c(0);
                self.call_op(h.construct, argc, argc + 3, &[nslots, stamp]);
            }
            SpreadCall | SpreadNew | SpreadSuperCall => {
                let construct = op != SpreadCall;
                let need = if construct { 4 } else { 3 };
                let callee = self.slot(d - need);
                let thisv = self.slot(d - need + 1);
                let arr = self.slot(d - need + 2);
                let nt = if construct {
                    self.slot(d - 1)
                } else {
                    self.i64c(TAG_NULL << 32)
                };
                let c = self.i32c(u32::from(construct));
                let r = self.rt(h.spread_call, &[callee, thisv, arr, nt, c]);
                self.set_slot(d - need, r);
            }

            // --- properties and elements ---
            GetProp => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let recv = self.slot(d - 1);
                let av = self.i32c(a);
                let r = self.rt(h.get_property, &[recv, av]);
                self.set_slot(d - 1, r);
            }
            SetProp | StrictSetProp => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let recv = self.slot(d - 2);
                let v = self.slot(d - 1);
                let (av, sv) = (self.i32c(a), self.i32c(u32::from(op == StrictSetProp)));
                self.rt(h.set_property, &[recv, av, v, sv]);
                let v = self.slot(d - 1);
                self.set_slot(d - 2, v);
            }
            GetElem => {
                let a = self.slot(d - 2);
                let b = self.slot(d - 1);
                let obj = self.tag_eq(a, TAG_OBJECT);
                let int = self.tag_eq(b, TAG_INT32);
                let cond = self.binop(Operator::I32And, obj, int, Type::I32);
                self.fast_path(
                    cond,
                    |g, slow| {
                        let v = g.dense_element(a, b, slow);
                        g.set_slot(d - 2, v);
                    },
                    |g| {
                        let r = g.rt(h.get_element, &[a, b]);
                        g.set_slot(d - 2, r);
                    },
                );
            }
            SetElem | StrictSetElem => {
                let recv = self.slot(d - 3);
                let key = self.slot(d - 2);
                let v = self.slot(d - 1);
                let sv = self.i32c(u32::from(op == StrictSetElem));
                self.rt(h.set_element, &[recv, key, v, sv]);
                let v = self.slot(d - 1);
                self.set_slot(d - 3, v);
            }
            DelProp | StrictDelProp => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let v = self.slot(d - 1);
                let (av, sv) = (self.i32c(a), self.i32c(u32::from(op == StrictDelProp)));
                let r = self.rt(h.del_prop, &[v, av, sv]);
                self.set_slot(d - 1, r);
            }
            DelElem | StrictDelElem => {
                let sv = self.i32c(u32::from(op == StrictDelElem));
                self.binary(h.del_elem, &[sv], d);
            }
            In => self.binary(h.in_, &[], d),
            HasOwn => self.binary(h.has_own, &[], d),
            Instanceof => {
                let z = self.i32c(0);
                self.binary(h.instanceof_, &[z], d);
            }
            SuperBase => self.unary(h.super_base, d),
            SuperFun => self.unary(h.super_fun, d),
            GetPropSuper => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let recv = self.slot(d - 2);
                let base = self.slot(d - 1);
                let av = self.i32c(a);
                let r = self.rt(h.get_prop_super, &[recv, base, av]);
                self.set_slot(d - 2, r);
            }
            GetElemSuper => {
                let recv = self.slot(d - 3);
                let key = self.slot(d - 2);
                let base = self.slot(d - 1);
                let r = self.rt(h.get_elem_super, &[recv, key, base]);
                self.set_slot(d - 3, r);
            }
            SetPropSuper | StrictSetPropSuper => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let recv = self.slot(d - 3);
                let base = self.slot(d - 2);
                let v = self.slot(d - 1);
                let av = self.i32c(a);
                let sv = self.i32c(u32::from(op == StrictSetPropSuper));
                let r = self.rt(h.set_prop_super, &[recv, base, av, v, sv]);
                self.set_slot(d - 3, r);
            }
            SetElemSuper | StrictSetElemSuper => {
                let recv = self.slot(d - 4);
                let key = self.slot(d - 3);
                let base = self.slot(d - 2);
                let v = self.slot(d - 1);
                let sv = self.i32c(u32::from(op == StrictSetElemSuper));
                let r = self.rt(h.set_elem_super, &[recv, key, base, v, sv]);
                self.set_slot(d - 4, r);
            }

            // --- literals ---
            NewInit | NewObject => {
                skip(p, op);
                let z = self.i32c(0);
                let r = self.rt(h.new_object, &[z]);
                self.set_slot(d, r);
            }
            NewArray => {
                let len = p.next_uint32().unwrap();
                let (lv, z) = (self.i32c(len), self.i32c(0));
                let r = self.rt(h.new_array, &[lv, z]);
                self.set_slot(d, r);
            }
            InitProp | InitHiddenProp | InitLockedProp => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let attrs = match op {
                    InitProp => INIT_ATTR_ENUMERATE,
                    InitHiddenProp => INIT_ATTR_HIDDEN,
                    _ => INIT_ATTR_LOCKED,
                };
                let obj = self.slot(d - 2);
                let v = self.slot(d - 1);
                let (av, at, none) = (self.i32c(a), self.i32c(attrs), self.i32c(u32::MAX));
                self.rt(h.init_prop, &[obj, av, v, at, none]);
            }
            InitElem | InitHiddenElem | InitLockedElem => {
                let attrs = match op {
                    InitElem => INIT_ATTR_ENUMERATE,
                    InitHiddenElem => INIT_ATTR_HIDDEN,
                    _ => INIT_ATTR_LOCKED,
                };
                let obj = self.slot(d - 3);
                let key = self.slot(d - 2);
                let v = self.slot(d - 1);
                let at = self.i32c(attrs);
                self.rt(h.init_elem, &[obj, key, v, at]);
            }
            InitElemArray => {
                let index = p.next_uint32().unwrap();
                let obj = self.slot(d - 2);
                let v = self.slot(d - 1);
                let key = self.i64c((TAG_INT32 << 32) | u64::from(index));
                let at = self.i32c(INIT_ATTR_ENUMERATE);
                self.rt(h.init_elem, &[obj, key, v, at]);
            }
            InitElemInc => {
                let obj = self.slot(d - 3);
                let idx = self.slot(d - 2);
                let v = self.slot(d - 1);
                let at = self.i32c(INIT_ATTR_ENUMERATE);
                self.rt(h.init_elem, &[obj, idx, v, at]);
                // The index is an int32 (array literal positions are small).
                let idx = self.slot(d - 2);
                let i = self.unop(Operator::I32WrapI64, idx, Type::I32);
                let one = self.i32c(1);
                let n = self.binop(Operator::I32Add, i, one, Type::I32);
                let r = self.boxed_int32(n);
                self.set_slot(d - 2, r);
            }
            MutateProto => {
                let obj = self.slot(d - 2);
                let proto = self.slot(d - 1);
                self.rt(h.mutate_proto, &[obj, proto]);
            }
            InitHomeObject => {
                let f = self.slot(d - 2);
                let home = self.slot(d - 1);
                self.rt(h.init_home_object, &[f, home]);
            }
            InitPropGetter | InitHiddenPropGetter | InitPropSetter | InitHiddenPropSetter => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let kind = u32::from(matches!(op, InitPropSetter | InitHiddenPropSetter))
                    | (u32::from(matches!(op, InitHiddenPropGetter | InitHiddenPropSetter)) << 1);
                let obj = self.slot(d - 2);
                let f = self.slot(d - 1);
                let (av, kv) = (self.i32c(a), self.i32c(kind));
                self.rt(h.init_prop_getset, &[obj, av, f, kv]);
            }
            InitElemGetter | InitHiddenElemGetter | InitElemSetter | InitHiddenElemSetter => {
                let kind = u32::from(matches!(op, InitElemSetter | InitHiddenElemSetter))
                    | (u32::from(matches!(op, InitHiddenElemGetter | InitHiddenElemSetter)) << 1);
                let obj = self.slot(d - 3);
                let key = self.slot(d - 2);
                let f = self.slot(d - 1);
                let kv = self.i32c(kind);
                self.rt(h.init_elem_getset, &[obj, key, f, kv]);
            }
            NewPrivateName => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let av = self.i32c(a);
                let r = self.rt(h.new_private_name, &[av]);
                self.set_slot(d, r);
            }
            CheckPrivateField => {
                let cond = p.next_uint8().unwrap();
                let kind = p.next_uint8().unwrap();
                let obj = self.slot(d - 2);
                let key = self.slot(d - 1);
                let (cv, kv) = (self.i32c(u32::from(cond)), self.i32c(u32::from(kind)));
                let r = self.rt(h.check_private_field, &[obj, key, cv, kv]);
                self.set_slot(d, r);
            }

            // --- exceptions ---
            Exception => {
                let r = self.rt(h.exception, &[]);
                self.set_slot(d, r);
            }
            ExceptionAndStack => {
                let exc = self.top_addr(d);
                let stk = self.top_addr(d + 1);
                let gef = h.get_exception_for_finally;
                let ok = self
                    .call(gef, &[self.cx, exc, stk], Some(Type::I32))
                    .unwrap();
                self.branch_on_err(ok);
            }

            // --- iteration ---
            Iter => self.unary(h.iter_, d),
            MoreIter => {
                let it = self.slot(d - 1);
                let r = self
                    .call(h.more_iter, &[self.cx, it], Some(Type::I64))
                    .unwrap();
                self.set_slot(d, r);
            }
            IsNoIter => {
                let v = self.slot(d - 1);
                let m = self.i64c((TAG_MAGIC << 32) | MAGIC_NO_ITER_VALUE);
                let b = self.binop(Operator::I64Eq, v, m, Type::I32);
                let r = self.boxed_bool(b);
                self.set_slot(d, r);
            }
            EndIter => {
                let it = self.slot(d - 2);
                self.call(h.end_iter, &[self.cx, it], None);
            }
            OptimizeGetIterator => {
                let v = self.slot(d - 1);
                let b = self
                    .call(h.optimize_get_iterator, &[self.cx, v], Some(Type::I32))
                    .unwrap();
                let r = self.boxed_bool(b);
                self.set_slot(d - 1, r);
            }
            CloseIter => {
                let kind = p.next_uint8().unwrap();
                let it = self.slot(d - 1);
                let k = self.i32c(u32::from(kind));
                self.rt(h.close_iter, &[it, k]);
            }
            ToAsyncIter => self.binary(h.to_async_iter, &[], d),

            // --- generators and async ---
            Generator => {
                let callee = self.load_i64(self.sp, 0);
                let env = if self.needs_env {
                    self.env()
                } else {
                    self.i64c(UNDEF)
                };
                let r = self.rt(h.create_generator, &[callee, env]);
                self.set_slot(d, r);
            }
            InitialYield | Yield | Await => {
                let k = p.next_uint24().unwrap();
                self.suspend(op, k);
            }
            AfterYield => skip(p, op),
            FinalYieldRval => {
                let g = self.slot(d - 1);
                self.rt(h.gen_final, &[g]);
                let v = self.load_i64(self.vp, self.layout.rval());
                self.ret(v);
            }
            ResumeKind => {
                let kind = p.next_uint8().unwrap();
                self.push_const(d, (TAG_INT32 << 32) | u64::from(kind));
            }
            IsGenClosing => {
                let v = self.slot(d - 1);
                let m = self.i64c((TAG_MAGIC << 32) | MAGIC_GENERATOR_CLOSING);
                let b = self.binop(Operator::I64Eq, v, m, Type::I32);
                let r = self.boxed_bool(b);
                self.set_slot(d, r);
            }
            CheckResumeKind => {
                // [val, gen, kind] -> [val]: Next continues; Throw and
                // Return raise through the helper (Return by staging the
                // value as rval and raising the generator-closing magic).
                let kind = self.slot(d - 1);
                let kind = self.unop(Operator::I32WrapI64, kind, Type::I32);
                let is_next = self.unop(Operator::I32Eqz, kind, Type::I32);
                let raise = self.body.add_block();
                let cont = self.body.add_block();
                self.cond_br(is_next, Self::goto(cont), Self::goto(raise));
                self.cur = raise;
                self.live = true;
                let g = self.slot(d - 2);
                let v = self.slot(d - 3);
                let k = self.slot(d - 1);
                let k = self.unop(Operator::I32WrapI64, k, Type::I32);
                let rval = self.add_off(self.vp, self.layout.rval());
                let top = self.top_addr(d);
                self.call(
                    h.gen_check_resume,
                    &[self.cx, top, g, v, k, rval],
                    Some(Type::I32),
                );
                let t = self.exc_target(self.pc, d);
                self.br(t);
                self.cur = cont;
                self.live = true;
            }
            AsyncAwait | AsyncResolve => {
                let f = if op == AsyncAwait {
                    h.async_await
                } else {
                    h.async_resolve
                };
                let v = self.slot(d - 2);
                let g = self.slot(d - 1);
                let r = self.rt(f, &[g, v]);
                self.set_slot(d - 2, r);
            }
            AsyncReject => {
                let reason = self.slot(d - 3);
                let stack = self.slot(d - 2);
                let g = self.slot(d - 1);
                let r = self.rt(h.async_reject, &[g, reason, stack]);
                self.set_slot(d - 3, r);
            }
            CanSkipAwait => {
                let v = self.slot(d - 1);
                let r = self.rt(h.can_skip_await, &[v]);
                self.set_slot(d, r);
            }
            MaybeExtractAwaitValue => {
                let v = self.slot(d - 2);
                let can = self.slot(d - 1);
                let can = self.unop(Operator::I32WrapI64, can, Type::I32);
                let r = self.rt(h.maybe_extract_await, &[v, can]);
                self.set_slot(d - 2, r);
            }

            // --- the rest (docs/BASELINE.md §6) ---
            BigInt => {
                let idx = p.next_uint32().unwrap();
                let script = self.script_ptr();
                let iv = self.i32c(idx);
                let r = self.rt(h.bigint, &[script, iv]);
                self.set_slot(d, r);
            }
            NonSyntacticGlobalThis => {
                let env = self.env();
                let r = self.rt(h.non_syntactic_global_this, &[env]);
                self.set_slot(d, r);
            }
            SetIntrinsic => {
                skip(p, op);
                let script = self.script_ptr();
                let pcv = self.i32c(self.pc.get());
                let v = self.slot(d - 1);
                self.rt(h.set_intrinsic, &[script, pcv, v]);
            }
            EnvCallee => {
                let hops = match op.len() {
                    2 => u32::from(p.next_uint8().unwrap()),
                    _ => u32::from(p.next_uint16().unwrap()),
                };
                let env = self.env();
                let hv = self.i32c(hops);
                let r = self
                    .call(h.env_callee, &[self.cx, env, hv], Some(Type::I64))
                    .unwrap();
                self.set_slot(d, r);
            }
            Eval | StrictEval => {
                let argc = u32::from(p.next_uint16().unwrap());
                let need = argc + 2;
                let base = self.top_addr(d - need);
                let av = self.i32c(argc);
                let env = self.env();
                let script = self.script_ptr();
                let pcv = self.i32c(self.pc.get());
                let r = self.rt(h.eval, &[base, av, env, script, pcv]);
                self.set_slot(d - need, r);
            }
            SpreadEval | StrictSpreadEval => {
                let callee = self.slot(d - 3);
                let thisv = self.slot(d - 2);
                let arr = self.slot(d - 1);
                let env = self.env();
                let script = self.script_ptr();
                let pcv = self.i32c(self.pc.get());
                let r = self.rt(h.spread_eval, &[callee, thisv, arr, env, script, pcv]);
                self.set_slot(d - 3, r);
            }
            DynamicImport => {
                let spec = self.slot(d - 2);
                let opts = self.slot(d - 1);
                let script = self.script_ptr();
                let r = self.rt(h.dynamic_import, &[script, spec, opts]);
                self.set_slot(d - 2, r);
            }
            ImportMeta => {
                let script = self.script_ptr();
                let r = self.rt(h.import_meta, &[script]);
                self.set_slot(d, r);
            }
            GetImport => {
                skip(p, op);
                let env = self.env();
                let script = self.script_ptr();
                let pcv = self.i32c(self.pc.get());
                let r = self.rt(h.get_import, &[env, script, pcv]);
                self.set_slot(d, r);
            }
            AddDisposable => {
                let hint = p.next_uint8().unwrap();
                let env = self.env();
                let v = self.slot(d - 3);
                let method = self.slot(d - 2);
                let nc = self.slot(d - 1);
                let hv = self.i32c(u32::from(hint));
                self.rt(h.add_disposable, &[env, v, method, nc, hv]);
            }
            TakeDisposeCapability => {
                let env = self.env();
                let r = self.rt(h.take_dispose_capability, &[env]);
                self.set_slot(d, r);
            }
            CreateSuppressedError => {
                let e = self.slot(d - 2);
                let sup = self.slot(d - 1);
                let r = self.rt(h.create_suppressed_error, &[e, sup]);
                self.set_slot(d - 2, r);
            }
            Resume => {
                let g = self.slot(d - 3);
                let v = self.slot(d - 2);
                let k = self.slot(d - 1);
                let r = self.rt(h.resume, &[g, v, k]);
                self.set_slot(d - 3, r);
            }
            ForceInterpreter => return Err(super::FORCE_INTERPRETER.into()),
        }
        Ok(())
    }

    /// `InitialYield` (`[gen] ->`) / `Yield`, `Await` (`[rval, gen] ->`):
    /// save the locals and the live operands into the generator object
    /// under resume index `k`, and return to the caller -- the generator
    /// for `InitialYield`, the result value otherwise.
    fn suspend(&mut self, op: JSOp, k: u32) {
        let d = self.d;
        let g = self.slot(d - 1);
        let (rv, saved) = if op == JSOp::InitialYield {
            (g, d - 1)
        } else {
            (self.slot(d - 2), d - 2)
        };
        let env = if self.needs_env {
            self.env()
        } else {
            self.i64c(0)
        };
        let lp = self.add_off(self.vp, self.layout.local_base());
        let nl = self.i32c(self.layout.nlocals);
        let ops = self.add_off(self.vp, self.layout.operand_base());
        let (kv, dv) = (self.i32c(k), self.i32c(saved));
        let gs = self.h.gen_suspend;
        self.call(gs, &[self.cx, g, kv, lp, nl, ops, dv, env], Some(Type::I32));
        self.ret(rv);
    }

    // --- inline fast paths ------------------------------------------------------

    /// An inline fast path (`docs/BASELINE.md` §3.1): `fast` runs when
    /// `cond` holds and may branch to the slow block it is given, which
    /// runs `slow`, the op's ordinary lowering. Both arms leave their result
    /// in the frame and rejoin at a fresh block with no params, so nothing
    /// either arm computes is live after the op. Each op gets its own slow
    /// block, never a shared one (fan-in; see `error_return`).
    fn fast_path(
        &mut self,
        cond: Value,
        fast: impl FnOnce(&mut Self, Block),
        slow: impl FnOnce(&mut Self),
    ) {
        let fast_b = self.body.add_block();
        let slow_b = self.body.add_block();
        let join = self.body.add_block();
        self.cond_br(cond, Self::goto(fast_b), Self::goto(slow_b));
        (self.cur, self.live) = (fast_b, true);
        fast(self, slow_b);
        self.br(Self::goto(join));
        (self.cur, self.live) = (slow_b, true);
        slow(self);
        if self.live {
            self.br(Self::goto(join));
        }
        (self.cur, self.live) = (join, true);
    }

    /// Leave the fast path for `slow` when `cond` holds.
    fn bail_if(&mut self, cond: Value, slow: Block) {
        let cont = self.body.add_block();
        self.cond_br(cond, Self::goto(slow), Self::goto(cont));
        (self.cur, self.live) = (cont, true);
    }

    /// Leave the fast path for `slow` unless `cond` holds.
    fn bail_unless(&mut self, cond: Value, slow: Block) {
        let cont = self.body.add_block();
        self.cond_br(cond, Self::goto(cont), Self::goto(slow));
        (self.cur, self.live) = (cont, true);
    }

    /// Element `key` of `obj` (an object and an int32) when it is an
    /// initialized, non-hole dense element of a native object; else
    /// branches to `slow`. Pure reads: a typed array's dense
    /// initializedLength is 0, and a proxy fails the native check before
    /// `elements_` is read.
    fn dense_element(&mut self, obj: Value, key: Value, slow: Block) -> Value {
        let objptr = self.unop(Operator::I32WrapI64, obj, Type::I32);
        let shape = self.load_i32(objptr, SHAPE_OFFSET);
        let flags = self.load_i32(shape, SHAPE_IMMUTABLE_FLAGS_OFFSET);
        let bit = self.i32c(SHAPE_IS_NATIVE_BIT);
        let native = self.binop(Operator::I32And, flags, bit, Type::I32);
        self.bail_unless(native, slow);
        let elements = self.load_i32(objptr, OBJ_ELEMENTS_OFFSET);
        let back = self.i32c(ELEMENTS_INITLEN_BACK);
        let header = self.binop(Operator::I32Sub, elements, back, Type::I32);
        let initlen = self.load_i32(header, 0);
        // Unsigned, so a negative index fails too.
        let idx = self.unop(Operator::I32WrapI64, key, Type::I32);
        let in_bounds = self.binop(Operator::I32LtU, idx, initlen, Type::I32);
        self.bail_unless(in_bounds, slow);
        let eight = self.i32c(8);
        let off = self.binop(Operator::I32Mul, idx, eight, Type::I32);
        let addr = self.binop(Operator::I32Add, elements, off, Type::I32);
        let v = self.load_i64(addr, 0);
        let hole = self.tag_eq(v, TAG_MAGIC);
        self.bail_if(hole, slow);
        v
    }

    /// Whether `v` is a number: an int32, or a double (every high word
    /// below `TAG_CLEAR`).
    fn is_number(&mut self, v: Value) -> Value {
        let t = self.tag_of(v);
        let k = self.i32c(TAG_INT32 as u32);
        self.binop(Operator::I32LeU, t, k, Type::I32)
    }

    /// A numeric op's inline arms, in order: `int` on the int32 payloads
    /// when every operand is an int32 (it may bail to the next arm), `num`
    /// on the operands as doubles when every operand is a number, else
    /// `slow`, the op's helper call. The arms return the boxed result,
    /// stored over the operands. Each arm is optional.
    fn number_arms(
        &mut self,
        ops: &[Value],
        int: Option<&IntArm<'_, 'a>>,
        num: Option<&NumArm<'_, 'a>>,
        slow: impl FnOnce(&mut Self),
    ) {
        let k = self.d - u32::try_from(ops.len()).unwrap();
        let join = self.body.add_block();
        let slow_b = self.body.add_block();
        let num_b = if num.is_some() {
            self.body.add_block()
        } else {
            slow_b
        };
        if let Some(int) = int {
            let mut all = None;
            for &v in ops {
                let t = self.tag_eq(v, TAG_INT32);
                all = Some(match all {
                    Some(a) => self.binop(Operator::I32And, a, t, Type::I32),
                    None => t,
                });
            }
            let int_b = self.body.add_block();
            self.cond_br(all.unwrap(), Self::goto(int_b), Self::goto(num_b));
            (self.cur, self.live) = (int_b, true);
            let raw: Vec<Value> = ops
                .iter()
                .map(|&v| self.unop(Operator::I32WrapI64, v, Type::I32))
                .collect();
            let r = int(self, &raw, num_b);
            self.set_slot(k, r);
            self.br(Self::goto(join));
        } else {
            self.br(Self::goto(num_b));
        }
        if let Some(num) = num {
            (self.cur, self.live) = (num_b, true);
            let mut all = None;
            for &v in ops {
                let t = self.is_number(v);
                all = Some(match all {
                    Some(a) => self.binop(Operator::I32And, a, t, Type::I32),
                    None => t,
                });
            }
            self.bail_unless(all.unwrap(), slow_b);
            let fs: Vec<Value> = ops.iter().map(|&v| self.to_f64(v)).collect();
            let r = num(self, &fs);
            self.set_slot(k, r);
            self.br(Self::goto(join));
        }
        (self.cur, self.live) = (slow_b, true);
        slow(self);
        if self.live {
            self.br(Self::goto(join));
        }
        (self.cur, self.live) = (join, true);
    }

    fn f64c(&mut self, x: f64) -> Value {
        let ty = self.body.single_type_list(Type::F64);
        self.push_val(ValueDef::Operator(
            Operator::F64Const { value: x.to_bits() },
            Default::default(),
            ty,
        ))
    }

    /// A number (int32 or double) as an f64.
    fn to_f64(&mut self, v: Value) -> Value {
        let is_int = self.tag_eq(v, TAG_INT32);
        let low = self.unop(Operator::I32WrapI64, v, Type::I32);
        let fi = self.unop(Operator::F64ConvertI32S, low, Type::F64);
        let fd = self.unop(Operator::F64ReinterpretI64, v, Type::F64);
        self.select(Type::F64, fi, fd, is_int)
    }

    /// Box an f64 as the engine's `NumberValue` does: an int32 when it is
    /// one exactly (not -0), else a double, with NaN canonicalized (a
    /// non-canonical NaN could alias a boxed tag).
    fn box_number(&mut self, x: Value) -> Value {
        let i = self.unop(Operator::I32TruncSatF64S, x, Type::I32);
        let back = self.unop(Operator::F64ConvertI32S, i, Type::F64);
        let exact = self.binop(Operator::F64Eq, back, x, Type::I32);
        let bits = self.unop(Operator::I64ReinterpretF64, x, Type::I64);
        let negz = self.i64c(1 << 63);
        let not_negz = self.binop(Operator::I64Ne, bits, negz, Type::I32);
        let is_int = self.binop(Operator::I32And, exact, not_negz, Type::I32);
        let nan = self.binop(Operator::F64Ne, x, x, Type::I32);
        let canon = self.i64c(CANONICAL_NAN_BITS);
        let dbl = self.select(Type::I64, canon, bits, nan);
        let int = self.boxed_int32(i);
        self.select(Type::I64, int, dbl, is_int)
    }

    /// Whether the sign bit of `v` is set.
    fn is_neg(&mut self, v: Value) -> Value {
        let z = self.i32c(0);
        self.binop(Operator::I32LtS, v, z, Type::I32)
    }

    fn add_i32(&mut self, x: Value, y: Value, slow: Block) -> Value {
        let r = self.binop(Operator::I32Add, x, y, Type::I32);
        // Signed overflow: both operands' signs differ from the result's.
        let xr = self.binop(Operator::I32Xor, x, r, Type::I32);
        let yr = self.binop(Operator::I32Xor, y, r, Type::I32);
        let both = self.binop(Operator::I32And, xr, yr, Type::I32);
        let ovf = self.is_neg(both);
        self.bail_if(ovf, slow);
        r
    }

    fn sub_i32(&mut self, x: Value, y: Value, slow: Block) -> Value {
        let r = self.binop(Operator::I32Sub, x, y, Type::I32);
        // Signed overflow: the operands' signs differ, and the result's
        // differs from x's.
        let xy = self.binop(Operator::I32Xor, x, y, Type::I32);
        let xr = self.binop(Operator::I32Xor, x, r, Type::I32);
        let both = self.binop(Operator::I32And, xy, xr, Type::I32);
        let ovf = self.is_neg(both);
        self.bail_if(ovf, slow);
        r
    }

    fn mul_i32(&mut self, x: Value, y: Value, slow: Block) -> Value {
        let x64 = self.unop(Operator::I64ExtendI32S, x, Type::I64);
        let y64 = self.unop(Operator::I64ExtendI32S, y, Type::I64);
        let p = self.binop(Operator::I64Mul, x64, y64, Type::I64);
        let r = self.unop(Operator::I32WrapI64, p, Type::I32);
        let r64 = self.unop(Operator::I64ExtendI32S, r, Type::I64);
        let ovf = self.binop(Operator::I64Ne, p, r64, Type::I32);
        self.bail_if(ovf, slow);
        // A zero product with a negative operand is -0, a double.
        let z = self.i32c(0);
        let is_zero = self.binop(Operator::I32Eq, r, z, Type::I32);
        let xy = self.binop(Operator::I32Or, x, y, Type::I32);
        let neg = self.is_neg(xy);
        let neg_zero = self.binop(Operator::I32And, is_zero, neg, Type::I32);
        self.bail_if(neg_zero, slow);
        r
    }

    /// `x % y` for a non-negative `x` and a positive `y`: an int32, never
    /// -0 (the other signs are left to the next arm).
    fn mod_i32(&mut self, x: Value, y: Value, slow: Block) -> Value {
        let xn = self.is_neg(x);
        let z = self.i32c(0);
        let yp = self.binop(Operator::I32GtS, y, z, Type::I32);
        let bad = self.unop(Operator::I32Eqz, yp, Type::I32);
        let bad = self.binop(Operator::I32Or, xn, bad, Type::I32);
        self.bail_if(bad, slow);
        self.binop(Operator::I32RemS, x, y, Type::I32)
    }

    fn ursh_i32(&mut self, x: Value, y: Value, slow: Block) -> Value {
        let r = self.binop(Operator::I32ShrU, x, y, Type::I32);
        // A result of 2^31 or more is not an int32.
        let big = self.is_neg(r);
        self.bail_if(big, slow);
        r
    }

    /// ToBoolean's inline cases, decided from the tag: int32, boolean,
    /// undefined and null (the contiguous tags `TAG_INT32..=TAG_NULL`), and
    /// doubles. Returns (whether `v` is one of them, its truth value if so).
    fn truthy_inline(&mut self, v: Value) -> (Value, Value) {
        const _: () = assert!(
            TAG_BOOLEAN == TAG_INT32 + 1
                && TAG_UNDEFINED == TAG_INT32 + 2
                && TAG_NULL == TAG_INT32 + 3
        );
        let t = self.tag_of(v);
        let base = self.i32c(TAG_INT32 as u32);
        let rel = self.binop(Operator::I32Sub, t, base, Type::I32);
        let four = self.i32c(4);
        let tagged = self.binop(Operator::I32LtU, rel, four, Type::I32);
        // Int32 and boolean: a nonzero payload. Undefined and null: false.
        let two = self.i32c(2);
        let has_payload = self.binop(Operator::I32LtU, rel, two, Type::I32);
        let low = self.unop(Operator::I32WrapI64, v, Type::I32);
        let z = self.i32c(0);
        let nz = self.binop(Operator::I32Ne, low, z, Type::I32);
        let tagged_truth = self.binop(Operator::I32And, has_payload, nz, Type::I32);
        // A double: neither ±0 nor NaN, i.e. |x| > 0.
        let clear = self.i32c(TAG_CLEAR);
        let is_double = self.binop(Operator::I32LtU, t, clear, Type::I32);
        let x = self.unop(Operator::F64ReinterpretI64, v, Type::F64);
        let ax = self.unop(Operator::F64Abs, x, Type::F64);
        let fz = self.f64c(0.0);
        let double_truth = self.binop(Operator::F64Gt, ax, fz, Type::I32);
        let inline = self.binop(Operator::I32Or, tagged, is_double, Type::I32);
        let truth = self.select(Type::I32, double_truth, tagged_truth, is_double);
        (inline, truth)
    }

    /// Branch on ToBoolean(`v`): inline for the `truthy_inline` tags, else
    /// through the `to_boolean` helper.
    fn branch_truthy(&mut self, v: Value, if_true: BlockTarget, if_false: BlockTarget) {
        let (inline, truth) = self.truthy_inline(v);
        let fast_b = self.body.add_block();
        let slow_b = self.body.add_block();
        self.cond_br(inline, Self::goto(fast_b), Self::goto(slow_b));
        (self.cur, self.live) = (fast_b, true);
        self.cond_br(truth, if_true.clone(), if_false.clone());
        (self.cur, self.live) = (slow_b, true);
        let t = self.truthy(v);
        self.cond_br(t, if_true, if_false);
    }

    /// `==`/`===` decided inline: both values have the same tag, and it is
    /// int32, boolean, undefined, null or object. With one tag, loose and
    /// strict equality agree, and are identity of the raw bits (payloads
    /// of undefined and null are not compared). Doubles (NaN, -0),
    /// strings and BigInts are left to the helper. Returns (whether
    /// inline, equal if so).
    fn equality_inline(&mut self, a: Value, b: Value) -> (Value, Value) {
        let ta = self.tag_of(a);
        let tb = self.tag_of(b);
        let same = self.binop(Operator::I32Eq, ta, tb, Type::I32);
        let base = self.i32c(TAG_INT32 as u32);
        let rel = self.binop(Operator::I32Sub, ta, base, Type::I32);
        let four = self.i32c(4);
        let prim = self.binop(Operator::I32LtU, rel, four, Type::I32);
        let obj_k = self.i32c(TAG_OBJECT as u32);
        let obj = self.binop(Operator::I32Eq, ta, obj_k, Type::I32);
        let kind_ok = self.binop(Operator::I32Or, prim, obj, Type::I32);
        let inline = self.binop(Operator::I32And, same, kind_ok, Type::I32);
        let bits_eq = self.binop(Operator::I64Eq, a, b, Type::I32);
        let two = self.i32c(2);
        let unit = self.binop(Operator::I32GeU, rel, two, Type::I32);
        let unit = self.binop(Operator::I32And, unit, prim, Type::I32);
        let eq = self.binop(Operator::I32Or, bits_eq, unit, Type::I32);
        (inline, eq)
    }

    fn push_const(&mut self, k: u32, bits: u64) {
        let v = self.i64c(bits);
        self.set_slot(k, v);
    }

    /// `[a] -> [f(a)]`.
    fn unary(&mut self, f: Func, d: u32) {
        let a = self.slot(d - 1);
        let r = self.rt(f, &[a]);
        self.set_slot(d - 1, r);
    }

    /// `[a, b] -> [f(a, b, extra...)]`.
    fn binary(&mut self, f: Func, extra: &[Value], d: u32) {
        let a = self.slot(d - 2);
        let b = self.slot(d - 1);
        let mut args = vec![a, b];
        args.extend_from_slice(extra);
        let r = self.rt(f, &args);
        self.set_slot(d - 2, r);
    }

    /// `[a, b] -> [compare(kind, a, b)]` through the helper.
    fn compare(&mut self, kind: u32, a: Value, b: Value) {
        let k = self.i32c(kind);
        let r = self.rt(self.h.compare, &[k, a, b]);
        self.set_slot(self.d - 2, r);
    }

    /// A check on the top value, which stays: `helper(top value, extra...)`.
    fn check(&mut self, f: Func, extra: &[Value]) {
        let v = self.slot(self.d - 1);
        let mut args = vec![v];
        args.extend_from_slice(extra);
        self.rt(f, &args);
    }

    /// Whether the op after this one consumes a name lookup's result as
    /// `typeof` does (so an unbound name reads as undefined, not a
    /// ReferenceError).
    fn next_is_typeof(&self, op: JSOp) -> bool {
        let next = usize::try_from(self.next_pc(op).get()).unwrap();
        self.script
            .bytecode
            .get(next)
            .and_then(|&b| JSOp::from_byte(b))
            .is_some_and(|o| matches!(o, JSOp::Typeof | JSOp::TypeofEq))
    }

    /// A call whose `need` operands (callee, this, args[, new.target]) sit
    /// on the operand stack: the helper reads them in place as the
    /// callee's frame, and the result replaces them.
    fn call_op(&mut self, f: Func, argc: u32, need: u32, extra: &[Value]) {
        let d = self.d;
        let base = self.top_addr(d - need);
        let av = self.i32c(argc);
        let mut args = vec![base, av];
        args.extend_from_slice(extra);
        let r = self.rt(f, &args);
        self.set_slot(d - need, r);
    }

    /// A call that enters a compiled callee directly when it can: the
    /// callee's body through `call_indirect` (no C++ re-entry, so JS call
    /// depth is bounded by the NightStack, not the native stack), else the
    /// generic helper. The frame is the same either way: the callee's
    /// `[callee, this, args...]` sit on the operand stack.
    fn call_direct_or_generic(&mut self, argc: u32) {
        /// Headroom a compiled body may use past its actuals (the runtime
        /// entries' `kNightStackHeadroomSlots`).
        const HEADROOM: u32 = 64 * 1024;
        let d = self.d;
        let need = argc + 2;
        let base = self.top_addr(d - need);
        let top = self.top_addr(d);
        let callee = self.slot(d - need);
        let zero = self.i32c(0);
        let cls = {
            let args = self
                .body
                .arg_pool
                .from_iter([callee, zero, zero].into_iter());
            let tys = self
                .body
                .type_pool
                .from_iter([Type::I32, Type::I32, Type::I32].into_iter());
            self.push_val(ValueDef::Operator(
                Operator::Call {
                    function_index: self.h.call_classify,
                },
                args,
                tys,
            ))
        };
        let funcidx = self.push_val(ValueDef::PickOutput(cls, 0, Type::I32));
        let script = self.push_val(ValueDef::PickOutput(cls, 1, Type::I32));
        let limit_addr = self.i32c(self.h.night_stack_limit_base);
        let limit = self.load_i32(limit_addr, 0);
        let hi = self.add_off(top, 8 * (2 + argc) + HEADROOM);
        let fits = self.binop(Operator::I32LeU, hi, limit, Type::I32);
        let z = self.i32c(0);
        let compiled = self.binop(Operator::I32Ne, funcidx, z, Type::I32);
        let direct = self.binop(Operator::I32And, compiled, fits, Type::I32);
        let direct_blk = self.body.add_block();
        let generic_blk = self.body.add_block();
        let join = self.body.add_block();
        let ok = self.body.add_blockparam(join, Type::I32);
        self.cond_br(direct, Self::goto(direct_blk), Self::goto(generic_blk));

        self.cur = direct_blk;
        self.live = true;
        let argc_v = self.i32c(argc);
        let undef = self.i64c(UNDEF);
        // Bodies sit `N` table slots below their adapters (`wasm/mod.rs`).
        let off = self.i32c(u32::MAX);
        self.body_off_patches.push(off);
        let body_idx = self.binop(Operator::I32Sub, funcidx, off, Type::I32);
        let (base_d, top_d) = (self.top_addr(d - need), self.top_addr(d));
        let args = self
            .body
            .arg_pool
            .from_iter([self.cx, base_d, argc_v, top_d, script, undef, body_idx].into_iter());
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
        let ok_direct = self.unop(Operator::I32Eqz, err, Type::I32);
        self.br(BlockTarget {
            block: join,
            args: vec![ok_direct],
        });

        self.cur = generic_blk;
        self.live = true;
        let argc_v = self.i32c(argc);
        let ok_generic = self
            .call(self.h.call, &[self.cx, top, base, argc_v], Some(Type::I32))
            .unwrap();
        self.br(BlockTarget {
            block: join,
            args: vec![ok_generic],
        });

        self.cur = join;
        self.live = true;
        self.branch_on_err(ok);
        let top = self.top_addr(d);
        let r = self.load_i64(top, 0);
        self.set_slot(d - need, r);
    }

    fn function_this(&mut self) {
        let d = self.d;
        let thisv = self.load_i64(self.sp, FrameLayout::THIS);
        if self.script.strict {
            self.set_slot(d, thisv);
            return;
        }
        // Sloppy: an object is its own `this`; anything else is boxed (or
        // replaced by the global `this`).
        let is_obj = self.tag_eq(thisv, TAG_OBJECT);
        let obj_blk = self.body.add_block();
        let box_blk = self.body.add_block();
        let join = self.body.add_block();
        self.cond_br(is_obj, Self::goto(obj_blk), Self::goto(box_blk));
        self.cur = box_blk;
        self.live = true;
        let thisv2 = self.load_i64(self.sp, FrameLayout::THIS);
        let r = self.rt(self.h.box_nonstrict_this, &[thisv2]);
        self.set_slot(d, r);
        self.br(Self::goto(join));
        self.cur = obj_blk;
        self.live = true;
        let thisv3 = self.load_i64(self.sp, FrameLayout::THIS);
        self.set_slot(d, thisv3);
        self.br(Self::goto(join));
        self.cur = join;
        self.live = true;
    }

    /// `Arguments`: build the arguments object once per activation.
    fn arguments(&mut self) {
        let d = self.d;
        let cached = self.load_i64(self.vp, self.layout.args_obj());
        let is_undef = self.tag_eq(cached, TAG_UNDEFINED);
        let build = self.body.add_block();
        let join = self.body.add_block();
        self.cond_br(is_undef, Self::goto(build), Self::goto(join));
        self.cur = build;
        self.live = true;
        let f = self.h.arguments_;
        let r = self.rt(f, &[self.sp, self.argc]);
        self.store_i64(self.vp, self.layout.args_obj(), r);
        self.br(Self::goto(join));
        self.cur = join;
        self.live = true;
        let v = self.load_i64(self.vp, self.layout.args_obj());
        self.set_slot(d, v);
    }

    fn table_switch(&mut self, p: &mut BytecodeParser) -> R<()> {
        let default_off = p.next_int32().unwrap();
        let low = p.next_int32().unwrap();
        let high = p.next_int32().unwrap();
        let first_resume = p.next_uint24().unwrap();
        let d = self.d;
        let v = self.slot(d - 1);
        // An int32 or an int32-valued double selects a case; anything else
        // (including -0's tag-free friends) takes the default.
        let low_v = self.i32c(low as u32);
        let oob = self.i32c(u32::MAX);
        let is_int = self.tag_eq(v, TAG_INT32);
        let payload = self.unop(Operator::I32WrapI64, v, Type::I32);
        let v_int = self.binop(Operator::I32Sub, payload, low_v, Type::I32);
        let tag = self.tag_of(v);
        let int_tag = self.i32c(TAG_INT32 as u32);
        let is_dbl = self.binop(Operator::I32LtU, tag, int_tag, Type::I32);
        let f = self.unop(Operator::F64ReinterpretI64, v, Type::F64);
        let ti = self.unop(Operator::I32TruncSatF64S, f, Type::I32);
        let back = self.unop(Operator::F64ConvertI32S, ti, Type::F64);
        let exact = self.binop(Operator::F64Eq, back, f, Type::I32);
        let v_dbl = self.binop(Operator::I32Sub, ti, low_v, Type::I32);
        let v_dbl = self.select(Type::I32, v_dbl, oob, exact);
        let v_other = self.select(Type::I32, v_dbl, oob, is_dbl);
        let value = self.select(Type::I32, v_int, v_other, is_int);
        let count = usize::try_from((i64::from(high) - i64::from(low) + 1).max(0)).unwrap();
        let mut targets = Vec::with_capacity(count);
        for i in 0..count {
            let ri = usize::try_from(first_resume).unwrap() + i;
            let target_pc = *self
                .script
                .resume_offsets
                .get(ri)
                .ok_or_else(|| format!("TableSwitch resume index {ri} out of range"))?;
            targets.push(Self::goto(self.block(target_pc)));
        }
        let default = self.branch_to(default_off);
        self.terminate(Terminator::Select {
            value,
            targets,
            default,
        });
        Ok(())
    }
}

/// Whether the body keeps an env chain in its frame: it has env ops, or an
/// op whose helper reads the chain (direct eval, `EnvCallee`, module and
/// resource-management ops).
pub(crate) fn needs_env(script: &Script) -> bool {
    crate::wasm::translate::uses_env_ops(script)
        || script.parser().opcodes().any(|op| {
            matches!(
                op,
                JSOp::Eval
                    | JSOp::StrictEval
                    | JSOp::SpreadEval
                    | JSOp::StrictSpreadEval
                    | JSOp::NonSyntacticGlobalThis
                    | JSOp::EnvCallee
                    | JSOp::GetImport
                    | JSOp::AddDisposable
                    | JSOp::TakeDisposeCapability
            )
        })
}

fn skip(p: &mut BytecodeParser, op: JSOp) {
    let imm = usize::try_from(op.len()).unwrap() - 1;
    if imm > 0 {
        p.advance(imm).expect("operand bytes present");
    }
}

/// The scopes of `script` that own an environment object: the operands of
/// the ops that push one.
fn env_scopes_of(script: &Script) -> Vec<u32> {
    let mut out = Vec::new();
    let mut p = script.parser();
    while let Some(op) = p.next_op() {
        let len = usize::try_from(op.len()).unwrap();
        if matches!(
            op,
            JSOp::PushLexicalEnv | JSOp::PushClassBodyEnv | JSOp::PushVarEnv | JSOp::EnterWith
        ) {
            match p.next_uint32() {
                Some(idx) => out.push(idx),
                None => break,
            }
            if len > 5 && p.advance(len - 5).is_none() {
                break;
            }
        } else if len > 1 && p.advance(len - 1).is_none() {
            break;
        }
    }
    out
}
