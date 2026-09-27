//! The JSOps-to-MIR builder (`docs/MIR.md` §8), for the M2 subset: locals,
//! args, `this` and the operand stack as SSA values; int32 and double
//! arithmetic and compares, with the generic `js.*` ops as the fallback;
//! branches, loops and returns. Any other op declines the script, which
//! then runs in baseline alone.
//!
//! **Types.** Every frame slot has an abstract type: a raw `I32`, `F64` or
//! `Bool`, or a boxed `Val` with a tag set. Each bytecode basic block
//! starts from fixed entry types (its MIR block's params), and those come
//! from a fixpoint: the builder runs over the whole script, recording the
//! types that flow into every block; where they are wider than the block's
//! current entry types, the entry types widen and the builder runs again.
//! The run in which nothing widens is the result, so the type policy
//! exists once, in the emitting code. The widening lattice is small
//! (`I32 < F64`, and everything else joins to `Val` of the union of tags),
//! so the fixpoint comes quickly.
//!
//! **Guard-at-defs.** Formals with an `arg_types` claim are guarded at the
//! entry root: int32 to `I32`, numeric to `F64`. A failing guard exits to
//! baseline at pc 0.
//!
//! **Exits.** Every fallible op's `fail` edge exits at its own pc with the
//! state from before the op, since nothing observable has happened (§5.1's
//! resume rule), and every throwing op's `err` edge goes to its pc's throw
//! block (§5.3). Both are shared per pc and carry the whole frame, boxed.

use std::collections::BTreeMap;

use crate::bytecode::{BytecodeParser, JSOp, Script};
use crate::facts::Claim;
use crate::ids::{ArgIndex, Pc, ScriptId};
use crate::mir;
use crate::mir::func::{Edge, EdgeArg, FrameShape, LoopDecl, Root, RootKind};
use crate::mir::ops::{
    ArithOp, BitOp, Cc, ConstVal, F64Op, JsBinop, JsCc, JsUnop, MathFn, NumRepr, Opcode, UnboxKind,
};
use crate::mir::types::{
    KeyRange, LayoutClaim, LayoutState, ObjInfo, ObjKind, TagSet, Type as MType,
};
use crate::opsem::{PRIM_BIGINT, PRIM_INT32, PRIM_NULL, PRIM_UNDEFINED};
use crate::wasm::baseline::layout::{self, FrameLayout, StackDepths};
use crate::wasm::translate::TranslateCtx;

type R<T> = Result<T, String>;

/// A frame slot's abstract type.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Ty {
    I32,
    F64,
    Bool,
    Val(TagSet),
    /// A local, formal or rval that is dead here (never read before it is
    /// next written): no value, no block param. An exit passes it as
    /// `const.val dead`.
    Dead,
}

/// A number's raw representation, for arithmetic.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Num {
    I32,
    F64,
}

impl Ty {
    fn mir(self) -> MType {
        match self {
            Ty::I32 => MType::I32_TOP,
            Ty::F64 => MType::F64_TOP,
            Ty::Bool => MType::Bool,
            Ty::Val(t) => MType::val(t),
            Ty::Dead => unreachable!("a dead slot has no type"),
        }
    }

    fn tags(self) -> TagSet {
        match self {
            Ty::I32 => TagSet::INT32,
            Ty::F64 => TagSet::NUMBER,
            Ty::Bool => TagSet::BOOLEAN,
            Ty::Val(t) => t,
            Ty::Dead => TagSet::NONE,
        }
    }

    fn join(self, o: Ty) -> Ty {
        match (self, o) {
            (a, b) if a == b => a,
            (Ty::Dead, x) | (x, Ty::Dead) => x,
            (Ty::I32, Ty::F64) | (Ty::F64, Ty::I32) => Ty::F64,
            (a, b) => Ty::Val(a.tags().union(b.tags())),
        }
    }

    /// Whether a value of type `self` can be passed where `o` is expected
    /// (after `convert`). Anything fits a dead slot.
    fn fits(self, o: Ty) -> bool {
        o == Ty::Dead || (self != Ty::Dead && self.join(o) == o)
    }

    /// The raw number representation this type unboxes to without a
    /// check, if it is a number.
    fn num(self) -> Option<Num> {
        match self {
            Ty::I32 => Some(Num::I32),
            Ty::F64 => Some(Num::F64),
            Ty::Val(t) if t.is_nonempty_subset_of(TagSet::INT32) => Some(Num::I32),
            Ty::Val(t) if t.is_nonempty_subset_of(TagSet::NUMBER) => Some(Num::F64),
            _ => None,
        }
    }
}

/// A property access the analysis predicts: the receiver's layouts
/// `[lo, hi]`, whether the field's claim is backed by the stamp's TYPES
/// bit (a number), and whether it is int32-only.
#[derive(Clone, Copy, Debug)]
struct TypedSite {
    lo: u32,
    hi: u32,
    types: bool,
    int32: bool,
}

impl TypedSite {
    fn claim_ty(&self) -> MType {
        if self.types {
            MType::val(TagSet::NUMBER)
        } else {
            MType::VAL_TOP
        }
    }
}

/// A frame slot: the SSA value holding it now, and its type.
#[derive(Clone, Copy, Debug)]
struct Slot {
    v: mir::Value,
    ty: Ty,
}

impl Slot {
    /// A dead slot (`Ty::Dead`): its value is never used.
    fn dead() -> Slot {
        Slot {
            v: mir::Value::from_u32(u32::MAX),
            ty: Ty::Dead,
        }
    }
}

/// Build the MIR body for `script`, or decline with a reason.
pub fn build(
    ctx: &TranslateCtx,
    sid: ScriptId,
    script: &Script,
    is_global: bool,
) -> Result<(mir::Module, mir::Func), String> {
    if is_global {
        return Err("global script".into());
    }
    // A MIR script carries two bodies (MIR and baseline), and MIR bodies
    // are larger than baseline's per bytecode byte (exit blocks, block
    // params). An Emscripten-sized function would dominate the batch's
    // memory and compile time for little gain, so it stays in baseline.
    const MAX_MIR_BYTECODE: usize = 32 * 1024;
    if script.bytecode.len() > MAX_MIR_BYTECODE {
        return Err(format!(
            "too large for MIR ({} bytecode bytes)",
            script.bytecode.len()
        ));
    }
    if script.is_generator_or_async {
        return Err("generator or async".into());
    }
    if script.is_class_ctor {
        return Err("class constructor".into());
    }
    let fl = FrameLayout::of(script);
    if fl.rebase_vp || script.has_mapped_args {
        return Err("reads actuals".into());
    }
    if crate::wasm::baseline::needs_env(script) {
        return Err("env chain".into());
    }
    let depths = StackDepths::compute(script).map_err(|e| format!("stack depths ({e})"))?;
    let shape = Shape::of(ctx, sid, script, fl, depths)?;
    let mut table: BTreeMap<Pc, Vec<Ty>> = BTreeMap::new();
    // Within a run, a block's entry types join every forward edge into it
    // (`Run::pending`), so a run misses only what a loop's back edges
    // bring. Each rerun widens some loop header's entry types, and there
    // are finitely many widenings; the bound is a backstop.
    for _ in 0..256 {
        let mut run = Run::new(&shape, &table);
        run.build()?;
        if !run.widen {
            let mm = std::mem::take(&mut run.mm);
            return Ok((mm, run.finish()));
        }
        for (pc, tys) in run.out {
            let e = table.entry(pc).or_insert_with(|| tys.clone());
            for (a, b) in e.iter_mut().zip(&tys) {
                *a = a.join(*b);
            }
        }
    }
    Err("BUG: type fixpoint did not converge".into())
}

/// A decoded op.
#[derive(Clone, Copy, Debug)]
struct Op {
    pc: Pc,
    op: JSOp,
}

/// Backward liveness of the frame slots before the operand stack: `this`
/// (always live: the caller's frame), formals, locals and rval, per pc.
fn liveness(script: &Script, nargs: u32, nlocals: u32) -> BTreeMap<Pc, Vec<bool>> {
    let n = (2 + nargs + nlocals) as usize;
    let rval = n - 1;
    let succs = layout::successors(script);
    // Each op's (uses, defs) over slot indices.
    let effect = |pc: Pc, op: JSOp| -> (Option<usize>, Option<usize>) {
        let mut p = script.parser();
        p.advance(usize::try_from(pc.get()).unwrap() + 1)
            .expect("op in range");
        match op {
            JSOp::GetLocal => (
                Some(1 + nargs as usize + p.next_uint24().unwrap() as usize),
                None,
            ),
            JSOp::SetLocal | JSOp::InitLexical => (
                None,
                Some(1 + nargs as usize + p.next_uint24().unwrap() as usize),
            ),
            JSOp::GetArg => (Some(1 + usize::from(p.next_uint16().unwrap())), None),
            JSOp::SetArg => (None, Some(1 + usize::from(p.next_uint16().unwrap()))),
            JSOp::GetRval | JSOp::RetRval => (Some(rval), None),
            JSOp::SetRval => (None, Some(rval)),
            _ => (None, None),
        }
    };
    let mut live: BTreeMap<Pc, Vec<bool>> = succs.keys().map(|&pc| (pc, vec![false; n])).collect();
    let pcs: Vec<Pc> = succs.keys().copied().rev().collect();
    let mut changed = true;
    while changed {
        changed = false;
        for &pc in &pcs {
            let (op, ss) = &succs[&pc];
            let mut l = vec![false; n];
            for s in ss {
                if let Some(ls) = live.get(s) {
                    for (a, b) in l.iter_mut().zip(ls) {
                        *a |= *b;
                    }
                }
            }
            let (u, d) = effect(pc, *op);
            if let Some(d) = d.filter(|&d| d < n) {
                l[d] = false;
            }
            if let Some(u) = u.filter(|&u| u < n) {
                l[u] = true;
            }
            l[0] = true;
            if live[&pc] != l {
                live.insert(pc, l);
                changed = true;
            }
        }
    }
    live
}

/// The `Add`/`Sub` ops whose result is consumed, directly on the operand
/// stack within its basic block, only by truncating ops (ToInt32 of it)
/// or by other such adds and subs. A sum of int32s, and of such sums, is
/// exact as a double well within 2^53, and ToInt32 of it is the sum
/// modulo 2^32: the int32 wrapping add. (Not `Mul`: a double product can
/// round, which is what `Math.imul` is for.)
fn int32_demand(script: &Script, ops: &[Op]) -> std::collections::BTreeSet<Pc> {
    use std::collections::{BTreeMap, BTreeSet};
    let leaders = layout::leaders(script);
    // Per producer pc: its consumers' pcs, or `None` for a use the model
    // does not follow (a stack shuffle, a block boundary, a second use).
    let mut consumers: BTreeMap<Pc, Vec<Option<Pc>>> = BTreeMap::new();
    let mut stack: Vec<Option<Pc>> = vec![];
    for o in ops {
        if leaders.contains(&o.pc) {
            for p in stack.drain(..).flatten() {
                consumers.entry(p).or_default().push(None);
            }
        }
        let (Some(nuses), ndefs) = (o.op.nuses(), o.op.ndefs()) else {
            for p in stack.drain(..).flatten() {
                consumers.entry(p).or_default().push(None);
            }
            continue;
        };
        let nuses = nuses as usize;
        let simple = !matches!(
            o.op,
            JSOp::Dup | JSOp::Dup2 | JSOp::DupAt | JSOp::Swap | JSOp::Pick | JSOp::Unpick
        );
        if stack.len() < nuses {
            // Entered mid-stack (after a leader): the unknown values below.
            let missing = nuses - stack.len();
            stack.splice(0..0, std::iter::repeat_n(None, missing));
        }
        for p in stack.drain(stack.len() - nuses..).flatten() {
            consumers
                .entry(p)
                .or_default()
                .push(if simple { Some(o.pc) } else { None });
        }
        for _ in 0..ndefs {
            stack.push(if ndefs == 1 && simple {
                Some(o.pc)
            } else {
                None
            });
        }
    }
    for p in stack.drain(..).flatten() {
        consumers.entry(p).or_default().push(None);
    }
    let op_at: BTreeMap<Pc, JSOp> = ops.iter().map(|o| (o.pc, o.op)).collect();
    let truncating = |op: JSOp| {
        matches!(
            op,
            JSOp::BitOr
                | JSOp::BitAnd
                | JSOp::BitXor
                | JSOp::Lsh
                | JSOp::Rsh
                | JSOp::Ursh
                | JSOp::BitNot
        )
    };
    let mut ok: BTreeSet<Pc> = BTreeSet::new();
    // Consumers come after producers: walk backward so a consuming add's
    // verdict is known first.
    for o in ops.iter().rev() {
        if !matches!(o.op, JSOp::Add | JSOp::Sub) {
            continue;
        }
        let Some(cs) = consumers.get(&o.pc) else {
            continue;
        };
        let all = !cs.is_empty()
            && cs.iter().all(|c| match c {
                Some(c) => truncating(op_at[c]) || ok.contains(c),
                None => false,
            });
        if all {
            ok.insert(o.pc);
        }
    }
    ok
}

/// What the runs share: the script's decoded shape.
struct Shape<'a> {
    ctx: &'a TranslateCtx<'a>,
    sid: ScriptId,
    script: &'a Script,
    nargs: u32,
    nlocals: u32,
    depths: StackDepths,
    ops: Vec<Op>,
    leaders: std::collections::BTreeSet<Pc>,
    /// Loop intervals `[header, end)`.
    loops: BTreeMap<Pc, Pc>,
    /// Per pc, which of the frame's first `frame_len` slots (`this`,
    /// formals, locals, rval) are live on entry to the op there: read
    /// before they are next written, on some path.
    live: BTreeMap<Pc, Vec<bool>>,
    /// The `Add`/`Sub` ops whose result only ever reaches ToInt32 (`|`,
    /// `&`, `^`, shifts, or another such add or sub): their int32 form can
    /// wrap instead of checking for overflow (§10.6's numeric demand).
    wrap_ok: std::collections::BTreeSet<Pc>,
}

impl<'a> Shape<'a> {
    fn of(
        ctx: &'a TranslateCtx<'a>,
        sid: ScriptId,
        script: &'a Script,
        fl: FrameLayout,
        depths: StackDepths,
    ) -> R<Shape<'a>> {
        let mut ops = vec![];
        let len = script.bytecode.len();
        let mut p = script.parser();
        loop {
            let pc = Pc::new(u32::try_from(len - p.remaining()).unwrap());
            let Some(op) = p.next_op() else { break };
            ops.push(Op { pc, op });
            let imm = usize::try_from(op.len()).unwrap() - 1;
            if imm > 0 && p.advance(imm).is_none() {
                return Err(format!("truncated {op:?} at {pc}"));
            }
        }
        let loops = crate::wasm::translate::scan_loop_intervals(script)
            .into_iter()
            .map(|(h, e)| (Pc::new(h), Pc::new(e)))
            .collect();
        let live = liveness(script, fl.nargs, fl.nlocals);
        let wrap_ok = int32_demand(script, &ops);
        Ok(Shape {
            ctx,
            sid,
            script,
            nargs: fl.nargs,
            nlocals: fl.nlocals,
            depths,
            ops,
            leaders: layout::leaders(script),
            loops,
            live,
            wrap_ok,
        })
    }

    /// A parser positioned just after the opcode at `pc`.
    fn imms(&self, pc: Pc) -> BytecodeParser<'a> {
        let mut p = self.script.parser();
        p.advance(usize::try_from(pc.get()).unwrap() + 1)
            .expect("op in range");
        p
    }

    /// Whether the op after the one at `pc` consumes its result as
    /// `typeof` does (a name lookup then does not throw when unbound).
    fn next_is_typeof(&self, pc: Pc, op: JSOp) -> bool {
        let next = usize::try_from((pc + op.len()).get()).unwrap();
        self.script
            .bytecode
            .get(next)
            .and_then(|&b| JSOp::from_byte(b))
            .is_some_and(|o| matches!(o, JSOp::Typeof | JSOp::TypeofEq | JSOp::TypeofExpr))
    }

    /// The entry type the analysis predicts for formal `i` (guard-at-defs).
    fn arg_claim(&self, i: u32) -> Ty {
        let claim = self
            .ctx
            .facts
            .arg_types
            .get(&(self.sid, ArgIndex::new(i + 1)))
            .copied()
            .unwrap_or(Claim::NONE);
        let prims = claim.prims();
        if claim.is_none() || claim.is_object() || prims.is_empty() {
            Ty::Val(TagSet::ALL)
        } else if prims.subset_of(PRIM_INT32) {
            Ty::I32
        } else if prims.subset_of(crate::opsem::NUM) {
            Ty::F64
        } else {
            Ty::Val(TagSet::ALL)
        }
    }
}

/// One run of the builder over the script.
struct Run<'s, 'a> {
    s: &'s Shape<'a>,
    table: &'s BTreeMap<Pc, Vec<Ty>>,
    /// The types flowing into each block this run (joined).
    out: BTreeMap<Pc, Vec<Ty>>,
    f: mir::Func,
    /// The module tables the function references (its atoms).
    mm: mir::Module,
    blocks: BTreeMap<Pc, mir::Block>,
    preheaders: BTreeMap<Pc, mir::Block>,
    /// The entry types of every block entered so far this run.
    entry_types: BTreeMap<Pc, Vec<Ty>>,
    /// Edges to blocks not entered yet: a trampoline block per edge, with
    /// the frame's types there and the edge's source pc. Entering the
    /// block joins them into its entry types, then fills each trampoline
    /// with the conversions and the jump.
    pending: BTreeMap<Pc, Vec<(mir::Block, Vec<Ty>, Option<Pc>)>>,
    /// Whether a back edge brought types wider than its loop header's: the
    /// run is not the last.
    widen: bool,
    cur: mir::Block,
    /// Whether `cur` is open.
    live: bool,
    /// The frame: `this`, formals, locals, rval, then the operand stack.
    st: Vec<Slot>,
    /// The op being built, its state before it, and its shared exit and
    /// throw blocks.
    pc: Pc,
    pre: Vec<Slot>,
    exit_blk: Option<mir::Block>,
    throw_blk: Option<mir::Block>,
}

impl<'s, 'a> Run<'s, 'a> {
    fn new(s: &'s Shape<'a>, table: &'s BTreeMap<Pc, Vec<Ty>>) -> Run<'s, 'a> {
        let frame = FrameShape {
            formals: s.nargs,
            locals: s.nlocals,
            depths: BTreeMap::new(),
        };
        let mut f = mir::Func::new(s.sid, frame);
        let cur = f.add_block();
        Run {
            s,
            table,
            out: BTreeMap::new(),
            f,
            mm: mir::Module::default(),
            blocks: BTreeMap::new(),
            preheaders: BTreeMap::new(),
            entry_types: BTreeMap::new(),
            pending: BTreeMap::new(),
            widen: false,
            cur,
            live: true,
            st: vec![],
            pc: Pc::new(0),
            pre: vec![],
            exit_blk: None,
            throw_blk: None,
        }
    }

    fn finish(mut self) -> mir::Func {
        // Drop blocks nothing reaches (a run creates a block for every
        // leader with an entry type, and some are only reached from blocks
        // that turned out dead).
        let mut seen = std::collections::BTreeSet::new();
        let mut work: Vec<mir::Block> = self.f.roots.iter().map(|r| r.block).collect();
        while let Some(b) = work.pop() {
            if seen.insert(b) {
                work.extend(self.f.succs(b));
            }
        }
        self.f.layout.retain(|b| seen.contains(b));
        self.f.loops.retain(|l| seen.contains(&l.header));
        self.f
    }

    // --- emission ------------------------------------------------------------

    fn inst(&mut self, op: Opcode, args: Vec<mir::Value>, result: Option<MType>) -> mir::Value {
        let tys: Vec<MType> = result.into_iter().collect();
        let (_, rs) = self.f.add_inst(self.cur, op, args, &tys, vec![]);
        rs.first()
            .copied()
            .unwrap_or_else(|| mir::Value::from_u32(0))
    }

    fn term(&mut self, op: Opcode, args: Vec<mir::Value>, succs: Vec<Edge>) {
        self.f.add_inst(self.cur, op, args, &[], succs);
        self.live = false;
    }

    fn goto(block: mir::Block) -> Edge {
        Edge {
            block,
            args: vec![],
        }
    }

    fn new_block(&mut self) -> mir::Block {
        self.f.add_block()
    }

    /// Continue in `b` (opened by the caller's terminator).
    fn at(&mut self, b: mir::Block) {
        self.cur = b;
        self.live = true;
    }

    fn const_val(&mut self, c: ConstVal) -> mir::Value {
        let t = mir::ops::const_val_type(c);
        self.inst(Opcode::ConstVal(c), vec![], Some(t))
    }

    fn const_i32(&mut self, n: i32) -> mir::Value {
        let t = MType::i32_range(n.into(), n.into());
        self.inst(Opcode::ConstI32(n), vec![], Some(t))
    }

    fn const_f64(&mut self, x: f64) -> mir::Value {
        let t = MType::F64(mir::types::NumInfo::exact(x));
        self.inst(Opcode::ConstF64(x.to_bits()), vec![], Some(t))
    }

    fn weaken(&mut self, v: mir::Value, t: MType) -> mir::Value {
        if self.f.ty(v) == t {
            return v;
        }
        self.inst(Opcode::Weaken, vec![v], Some(t))
    }

    /// `x` as a boxed value, of type `Val(x.ty.tags())`.
    fn boxed(&mut self, x: Slot) -> mir::Value {
        let v = match x.ty {
            Ty::Val(_) => return x.v,
            _ => {
                let t = mir::ops::box_type(&self.f.ty(x.v)).expect("raw values box");
                self.inst(Opcode::Box, vec![x.v], Some(t))
            }
        };
        self.weaken(v, MType::val(x.ty.tags()))
    }

    /// `x` as `Val(⊤)`: what crosses into baseline.
    fn val_top(&mut self, x: Slot) -> mir::Value {
        let v = self.boxed(x);
        self.weaken(v, MType::VAL_TOP)
    }

    /// `x` converted to type `to`, which it fits.
    fn convert(&mut self, x: Slot, to: Ty) -> mir::Value {
        match (x.ty, to) {
            (a, b) if a == b => x.v,
            (Ty::I32, Ty::F64) => self.inst(Opcode::I32ToF64, vec![x.v], Some(MType::F64_TOP)),
            (_, Ty::Val(t)) => {
                let v = self.boxed(x);
                self.weaken(v, MType::val(t))
            }
            (a, b) => unreachable!("convert {a:?} to {b:?}"),
        }
    }

    fn as_i32(&mut self, x: Slot) -> mir::Value {
        match x.ty {
            Ty::I32 => x.v,
            Ty::Val(_) => self.inst(
                Opcode::Unbox(UnboxKind::I32),
                vec![x.v],
                Some(MType::I32_TOP),
            ),
            t => unreachable!("as_i32 {t:?}"),
        }
    }

    fn as_f64(&mut self, x: Slot) -> mir::Value {
        match x.ty {
            Ty::F64 => x.v,
            Ty::I32 => self.inst(Opcode::I32ToF64, vec![x.v], Some(MType::F64_TOP)),
            Ty::Val(_) => self.inst(
                Opcode::Unbox(UnboxKind::F64Num),
                vec![x.v],
                Some(MType::F64_TOP),
            ),
            t => unreachable!("as_f64 {t:?}"),
        }
    }

    /// A number as an int32, by ToInt32.
    fn to_int32(&mut self, x: Slot) -> mir::Value {
        match x.ty.num() {
            Some(Num::I32) => self.as_i32(x),
            _ => {
                let f = self.as_f64(x);
                self.inst(Opcode::ToInt32, vec![f], Some(MType::I32_TOP))
            }
        }
    }

    // --- exits ---------------------------------------------------------------

    /// The frame `st` as exit operands at `pc`, all `Val(⊤)`, recording the
    /// stack depth there.
    fn exit_operands(&mut self, pc: Pc, st: &[Slot]) -> Vec<mir::Value> {
        let depth = st.len() - self.frame_len();
        self.f
            .frame
            .depths
            .insert(pc, u32::try_from(depth).unwrap());
        // A slot dead at the exit's pc goes as `const.val dead`: baseline
        // never reads it before writing it, so the frame keeps whatever
        // (valid) value it has.
        let live = self.s.live.get(&pc).cloned();
        let mut dead = None;
        let mut ops = vec![];
        for (i, &x) in st.iter().enumerate() {
            let is_dead = x.ty == Ty::Dead || live.as_ref().is_some_and(|l| i < l.len() && !l[i]);
            if is_dead {
                let d = *dead.get_or_insert_with(|| self.const_val(ConstVal::Dead));
                ops.push(d);
            } else {
                ops.push(self.val_top(x));
            }
        }
        ops
    }

    fn exit_op(&self, pc: Pc, throw: bool) -> Opcode {
        let (nargs, nlocals) = (self.s.nargs, self.s.nlocals);
        if throw {
            Opcode::ExitThrow { pc, nargs, nlocals }
        } else {
            Opcode::Exit { pc, nargs, nlocals }
        }
    }

    /// The op's shared exit (or throw) block: the state before the op.
    fn exit_block(&mut self, throw: bool) -> mir::Block {
        let slot = if throw { self.throw_blk } else { self.exit_blk };
        if let Some(b) = slot {
            return b;
        }
        let saved = (self.cur, self.live);
        let b = self.new_block();
        self.at(b);
        let pre = self.pre.clone();
        let ops = self.exit_operands(self.pc, &pre);
        let op = self.exit_op(self.pc, throw);
        self.term(op, ops, vec![]);
        (self.cur, self.live) = saved;
        if throw {
            self.throw_blk = Some(b);
        } else {
            self.exit_blk = Some(b);
        }
        b
    }

    /// Guard-at-defs (§8) for the result of the op just built, on top of
    /// the stack: guard it to the analysis's prediction `claim`. The op has
    /// happened, so a failure exits at `next`, the successor pc, with the
    /// result unguarded on the stack (§5.1's resume rule).
    fn guard_result(&mut self, claim: crate::facts::Claim, next: Pc) {
        let prims = claim.prims();
        if claim.is_none() || claim.is_object() || prims.is_empty() {
            return;
        }
        let (op, ty) = if prims.subset_of(PRIM_INT32) {
            (Opcode::GuardUnbox(UnboxKind::I32), Ty::I32)
        } else if prims.subset_of(crate::opsem::NUM) {
            (Opcode::GuardUnbox(UnboxKind::F64Num), Ty::F64)
        } else {
            return;
        };
        let x = self.top();
        if !matches!(x.ty, Ty::Val(_)) {
            return;
        }
        let depth = self.st.len() - self.frame_len();
        if self.s.depths.at(next) != Some(u32::try_from(depth).unwrap()) {
            return;
        }
        let st = self.st.clone();
        let saved = (self.cur, self.live);
        let fail = self.new_block();
        self.at(fail);
        let ops = self.exit_operands(next, &st);
        let eop = self.exit_op(next, false);
        self.term(eop, ops, vec![]);
        (self.cur, self.live) = saved;
        let ok = self.new_block();
        let p = self.f.add_param(ok, ty.mir());
        self.term(
            op,
            vec![x.v],
            vec![
                Edge {
                    block: ok,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(fail),
            ],
        );
        self.at(ok);
        self.st.pop();
        self.push(p, ty);
    }

    fn site(&self, pc: Pc) -> crate::ids::Site {
        crate::ids::Site::new(self.s.sid, pc)
    }

    /// A fallible check: continue on success with its output (of type
    /// `out`), exit at the op's pc on failure.
    fn guard(&mut self, op: Opcode, args: Vec<mir::Value>, out: MType) -> mir::Value {
        let ok = self.new_block();
        let p = self.f.add_param(ok, out);
        let fail = self.exit_block(false);
        self.term(
            op,
            args,
            vec![
                Edge {
                    block: ok,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(fail),
            ],
        );
        self.at(ok);
        p
    }

    /// The atom for gcthing `index` (a name), in the module's table.
    fn atom(&mut self, index: u32) -> R<mir::entity::AtomId> {
        let gc = *self
            .s
            .script
            .gcthings
            .get(usize::try_from(index).unwrap())
            .ok_or_else(|| format!("name index {index} out of range"))?;
        match self.s.ctx.source.object(gc) {
            crate::source::SourceObject::String(s) => Ok(self.mm.intern_atom(s.chars())),
            _ => Err(format!("name index {index} is not a string")),
        }
    }

    /// The analysis's layout prediction for the property access at `pc`
    /// (`prop_sites`), with its field recorded in the module's layouts;
    /// `None` without one, or when it disagrees with another site's
    /// description of the same slot.
    fn typed_site(&mut self, pc: Pc, name: mir::entity::AtomId) -> Option<TypedSite> {
        let ps = self
            .s
            .ctx
            .prop_sites_in
            .get(&crate::ids::Site::new(self.s.sid, pc))?;
        let prims = ps.claim.prims();
        // TYPES maintains only numberness today (§4.6): a claim is a
        // number claim, and only where the receivers can carry the bit.
        let types = !ps.claim.is_none()
            && ps.shallow_possible
            && !prims.is_empty()
            && prims.subset_of(crate::opsem::NUM);
        let site = TypedSite {
            lo: ps.layout_id,
            hi: ps.hi_layout_id,
            types,
            int32: types && prims.subset_of(PRIM_INT32),
        };
        let claim = site.claim_ty();
        let slot = usize::try_from(ps.slot).unwrap();
        for k in site.lo..=site.hi {
            let l = self
                .mm
                .layouts
                .entry(crate::ids::LayoutKey::new(k))
                .or_default();
            if l.fields.len() <= slot {
                l.fields.resize(slot + 1, None);
            }
            match &l.fields[slot] {
                None => {
                    l.fields[slot] = Some(mir::module::FieldDef { name, claim });
                }
                Some(f) if f.name == name && f.claim == claim => {}
                Some(_) => return None,
            }
        }
        Some(site)
    }

    /// Guard a receiver to an object of the site's layouts (§4.3): an
    /// object tag test, then the stamp compare, both exiting at the op's
    /// pc on failure.
    fn guard_layout(&mut self, recv: Slot, site: &TypedSite) -> mir::Value {
        let x = self.boxed(recv);
        let o = self.guard(Opcode::GuardUnbox(UnboxKind::Obj), vec![x], MType::OBJ_TOP);
        let keys = KeyRange {
            lo: crate::ids::LayoutKey::new(site.lo),
            hi: crate::ids::LayoutKey::new(site.hi),
        };
        let t = MType::Obj(ObjInfo {
            layout: Some(LayoutClaim {
                keys,
                types: site.types,
                state: LayoutState::Published,
            }),
            ..ObjInfo::TOP
        });
        self.guard(
            Opcode::GuardLayout {
                keys,
                types: site.types,
            },
            vec![o],
            t,
        )
    }

    /// A generic op with a static kill (`ok`, `err`): the builder attaches
    /// its prediction witness (§4.5), which for a generic op is "may kill
    /// anything".
    fn js_static(&mut self, op: Opcode, args: Vec<mir::Value>, out: MType) -> mir::Value {
        let ok = self.new_block();
        let p = self.f.add_param(ok, out);
        let err = self.exit_block(true);
        let (inst, _) = self.f.add_inst(
            self.cur,
            op,
            args,
            &[],
            vec![
                Edge {
                    block: ok,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(err),
            ],
        );
        self.f.witnesses[inst] = Some(mir::func::Witness {
            may_kill: mir::types::KillPattern::ALL,
        });
        self.live = false;
        self.at(ok);
        p
    }

    /// A generic op with no output: both success edges continue; an
    /// exception goes to the op's throw block.
    fn js_void(&mut self, op: Opcode, args: Vec<mir::Value>) {
        let ok = self.new_block();
        let err = self.exit_block(true);
        self.term(
            op,
            args,
            vec![Self::goto(ok), Self::goto(ok), Self::goto(err)],
        );
        self.at(ok);
    }

    /// A generic op: both success edges continue with its output (of type
    /// `out`); an exception goes to the op's throw block.
    fn js(&mut self, op: Opcode, args: Vec<mir::Value>, out: MType) -> mir::Value {
        let ok = self.new_block();
        let p = self.f.add_param(ok, out);
        let err = self.exit_block(true);
        let e = Edge {
            block: ok,
            args: vec![EdgeArg::Out(0)],
        };
        self.term(op, args, vec![e.clone(), e, Self::goto(err)]);
        self.at(ok);
        p
    }

    // --- control flow ----------------------------------------------------------

    /// The MIR block for leader `pc`, entered from `from` (a pc, or `None`
    /// for the entry root): a loop's preheader when the edge comes from
    /// outside the loop.
    fn block_for(&mut self, pc: Pc, from: Option<Pc>) -> Option<mir::Block> {
        let tys = self.entry_types.get(&pc)?.clone();
        let make = |r: &mut Self| {
            let b = r.new_block();
            for t in tys.iter().filter(|&&t| t != Ty::Dead) {
                r.f.add_param(b, t.mir());
            }
            b
        };
        let h = match self.blocks.get(&pc) {
            Some(&b) => b,
            None => {
                let b = make(self);
                self.blocks.insert(pc, b);
                b
            }
        };
        let Some(&end) = self.s.loops.get(&pc) else {
            return Some(h);
        };
        if from.is_some_and(|f| f >= pc && f < end) {
            return Some(h);
        }
        if let Some(&p) = self.preheaders.get(&pc) {
            return Some(p);
        }
        let p = make(self);
        self.preheaders.insert(pc, p);
        self.f.loops.push(LoopDecl {
            header: h,
            preheader: p,
        });
        let saved = (self.cur, self.live);
        self.at(p);
        let args = self.f.blocks[p]
            .params
            .iter()
            .map(|&v| EdgeArg::Value(v))
            .collect();
        self.term(Opcode::Jump, vec![], vec![Edge { block: h, args }]);
        (self.cur, self.live) = saved;
        Some(p)
    }

    /// The edge from the current point (the op at `from`) to leader `to`.
    /// - `to` not entered yet (a forward edge): a trampoline that `to`'s
    ///   entry fills in.
    /// - `to` entered (a loop's back edge): convert the frame to its entry
    ///   types. `None` when they are narrower than the frame's: the run is
    ///   then not the last (`widen`), and the edge is left out.
    fn edge_to(&mut self, to: Pc, from: Option<Pc>) -> Option<Edge> {
        let tys: Vec<Ty> = self.st.iter().map(|x| x.ty).collect();
        match self.out.get_mut(&to) {
            Some(o) => {
                for (a, b) in o.iter_mut().zip(&tys) {
                    *a = a.join(*b);
                }
            }
            None => {
                self.out.insert(to, tys.clone());
            }
        }
        let Some(want) = self.entry_types.get(&to).cloned() else {
            let t = self.new_block();
            let args = self
                .st
                .clone()
                .iter()
                .filter(|x| x.ty != Ty::Dead)
                .map(|x| {
                    self.f.add_param(t, x.ty.mir());
                    EdgeArg::Value(x.v)
                })
                .collect();
            self.pending.entry(to).or_default().push((t, tys, from));
            return Some(Edge { block: t, args });
        };
        if want.len() != tys.len() || !tys.iter().zip(&want).all(|(a, b)| a.fits(*b)) {
            self.widen = true;
            return None;
        }
        let block = self.block_for(to, from)?;
        let st = self.st.clone();
        let args = st
            .iter()
            .zip(&want)
            .filter(|(_, &t)| t != Ty::Dead)
            .map(|(&x, &t)| EdgeArg::Value(self.convert(x, t)))
            .collect();
        Some(Edge { block, args })
    }

    fn jump_to(&mut self, to: Pc, from: Option<Pc>) {
        match self.edge_to(to, from) {
            Some(e) => self.term(Opcode::Jump, vec![], vec![e]),
            None => self.term(Opcode::Unreachable, vec![], vec![]),
        }
    }

    /// Branch on raw bool `c` to leaders `then` and `els`.
    fn branch(&mut self, c: mir::Value, then: Pc, els: Pc) {
        let from = Some(self.pc);
        match (self.edge_to(then, from), self.edge_to(els, from)) {
            (Some(t), Some(e)) => self.term(Opcode::Br, vec![c], vec![t, e]),
            _ => self.term(Opcode::Unreachable, vec![], vec![]),
        }
    }

    /// ToBoolean of `x` as a raw bool.
    fn truthy(&mut self, x: Slot) -> mir::Value {
        match x.ty {
            Ty::Dead => unreachable!("a dead slot is never read"),
            Ty::Bool => x.v,
            Ty::I32 => {
                let z = self.const_i32(0);
                self.inst(
                    Opcode::Cmp(NumRepr::I32, Cc::Ne),
                    vec![x.v, z],
                    Some(MType::Bool),
                )
            }
            // Neither ±0 nor NaN: |x| > 0.
            Ty::F64 => {
                let a = self.inst(Opcode::Math(MathFn::Abs), vec![x.v], Some(MType::F64_TOP));
                let z = self.const_f64(0.0);
                self.inst(
                    Opcode::Cmp(NumRepr::F64, Cc::Gt),
                    vec![a, z],
                    Some(MType::Bool),
                )
            }
            Ty::Val(_) => self.inst(Opcode::JsToBool, vec![x.v], Some(MType::Bool)),
        }
    }

    /// Whether boxed `x`'s tag is in `tags`, as a raw bool: a `guard.tags`
    /// whose failure edge merges back rather than exiting.
    fn tag_test(&mut self, x: mir::Value, tags: TagSet) -> mir::Value {
        let (t, e, j) = (self.new_block(), self.new_block(), self.new_block());
        let p = self.f.add_param(j, MType::Bool);
        self.f.add_param(t, MType::val(tags));
        self.term(
            Opcode::GuardTags(tags),
            vec![x],
            vec![
                Edge {
                    block: t,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(e),
            ],
        );
        for (b, val) in [(t, true), (e, false)] {
            self.at(b);
            let k = self.inst(Opcode::ConstBool(val), vec![], Some(MType::Bool));
            self.term(
                Opcode::Jump,
                vec![],
                vec![Edge {
                    block: j,
                    args: vec![EdgeArg::Value(k)],
                }],
            );
        }
        self.at(j);
        p
    }

    /// `!c` for a raw bool: a diamond.
    fn not(&mut self, c: mir::Value) -> mir::Value {
        let (t, e, j) = (self.new_block(), self.new_block(), self.new_block());
        let p = self.f.add_param(j, MType::Bool);
        self.term(Opcode::Br, vec![c], vec![Self::goto(t), Self::goto(e)]);
        for (b, val) in [(t, false), (e, true)] {
            self.at(b);
            let k = self.inst(Opcode::ConstBool(val), vec![], Some(MType::Bool));
            self.term(
                Opcode::Jump,
                vec![],
                vec![Edge {
                    block: j,
                    args: vec![EdgeArg::Value(k)],
                }],
            );
        }
        self.at(j);
        p
    }

    // --- the stack -------------------------------------------------------------

    fn push(&mut self, v: mir::Value, ty: Ty) {
        self.st.push(Slot { v, ty });
    }

    fn pop(&mut self) -> Slot {
        self.st.pop().expect("stack underflow")
    }

    fn top(&self) -> Slot {
        *self.st.last().expect("empty stack")
    }

    /// Slots before the operand stack: `this`, formals, locals, rval.
    fn frame_len(&self) -> usize {
        (2 + self.s.nargs + self.s.nlocals) as usize
    }

    fn arg_ix(&self, n: u32) -> usize {
        1 + n as usize
    }

    fn local_ix(&self, n: u32) -> usize {
        1 + (self.s.nargs + n) as usize
    }

    fn rval_ix(&self) -> usize {
        1 + (self.s.nargs + self.s.nlocals) as usize
    }

    // --- the walk ---------------------------------------------------------------

    fn build(&mut self) -> R<()> {
        self.entry();
        let ops = self.s.ops.clone();
        let mut i = 0;
        while i < ops.len() {
            let Op { pc, op } = ops[i];
            if self.s.leaders.contains(&pc) {
                if self.live {
                    let from = if i > 0 { Some(ops[i - 1].pc) } else { None };
                    self.jump_to(pc, from);
                }
                if let Some(tys) = self.enter(pc) {
                    let b = self.block_for(pc, Some(pc)).unwrap();
                    let mut params = self.f.blocks[b].params.clone().into_iter();
                    self.st = tys
                        .iter()
                        .map(|&ty| match ty {
                            Ty::Dead => Slot::dead(),
                            ty => Slot {
                                v: params.next().unwrap(),
                                ty,
                            },
                        })
                        .collect();
                    self.at(b);
                }
            }
            if self.live {
                if self.s.depths.at(pc)
                    != Some(u32::try_from(self.st.len() - self.frame_len()).unwrap())
                {
                    return Err(format!("BUG: stack depth at {pc} disagrees"));
                }
                self.pc = pc;
                self.pre = self.st.clone();
                self.exit_blk = None;
                self.throw_blk = None;
                self.op(op)?;
            }
            i += 1;
        }
        if self.live {
            self.term(Opcode::Unreachable, vec![], vec![]);
        }
        let headers: Vec<Pc> = self.preheaders.keys().copied().collect();
        for h in headers {
            if self.wants_onramp(h) {
                self.onramp_root(h);
            }
        }
        Ok(())
    }

    /// The onramp-root policy (`docs/BASELINE.md` §7): every outermost
    /// loop gets a root, which needs no code duplication. An inner loop's
    /// root side-enters every loop around it, which waffle's reducifier
    /// pays for by duplicating code, so it gets one only when its
    /// outermost enclosing loop is small.
    fn wants_onramp(&self, h: Pc) -> bool {
        let outer = self
            .s
            .loops
            .iter()
            .filter(|&(&hh, &e)| hh < h && h < e)
            .map(|(&hh, &e)| e.get() - hh.get())
            .max();
        match outer {
            None => true,
            Some(len) => len <= self.s.ctx.opts.inner_onramp_bytes(),
        }
    }

    /// The onramp root `O` for loop header `h` (§5.2): the frame at `h`,
    /// all `Val(⊤)`, guarded up to the preheader's param types. On
    /// success it enters the preheader; on failure it re-deopts at `h`
    /// with its own params.
    fn onramp_root(&mut self, h: Pc) {
        let tys = self.entry_types[&h].clone();
        let p = self.preheaders[&h];
        let o = self.new_block();
        self.f.roots.push(Root {
            kind: RootKind::Onramp(h),
            block: o,
        });
        let params: Vec<mir::Value> = tys
            .iter()
            .map(|_| self.f.add_param(o, MType::VAL_TOP))
            .collect();
        let depth = tys.len() - self.frame_len();
        self.f.frame.depths.insert(h, u32::try_from(depth).unwrap());
        let fail = self.new_block();
        self.at(fail);
        let (nargs, nlocals) = (self.s.nargs, self.s.nlocals);
        self.term(
            Opcode::Exit {
                pc: h,
                nargs,
                nlocals,
            },
            params.clone(),
            vec![],
        );
        self.at(o);
        let mut args = vec![];
        for (&v, &t) in params.iter().zip(&tys) {
            let op = match t {
                Ty::Dead => continue,
                Ty::I32 => Some(Opcode::GuardUnbox(UnboxKind::I32)),
                Ty::F64 => Some(Opcode::GuardUnbox(UnboxKind::F64Num)),
                Ty::Bool => Some(Opcode::GuardUnbox(UnboxKind::Bool)),
                Ty::Val(tags) if tags == TagSet::ALL => None,
                Ty::Val(tags) => Some(Opcode::GuardTags(tags)),
            };
            let Some(op) = op else {
                args.push(EdgeArg::Value(v));
                continue;
            };
            let ok = self.new_block();
            let out = self.f.add_param(ok, t.mir());
            self.term(
                op,
                vec![v],
                vec![
                    Edge {
                        block: ok,
                        args: vec![EdgeArg::Out(0)],
                    },
                    Self::goto(fail),
                ],
            );
            self.at(ok);
            args.push(EdgeArg::Value(out));
        }
        self.term(Opcode::Jump, vec![], vec![Edge { block: p, args }]);
    }

    /// Enter leader `pc`: its entry types are the table's (what back edges
    /// brought in earlier runs) joined with every forward edge of this run.
    /// Fills the pending trampolines. `None` if nothing reaches it.
    fn enter(&mut self, pc: Pc) -> Option<Vec<Ty>> {
        let pending = self.pending.remove(&pc).unwrap_or_default();
        let mut tys = self.table.get(&pc).cloned();
        for (_, t, _) in &pending {
            tys = Some(match tys {
                None => t.clone(),
                Some(mut a) => {
                    for (x, y) in a.iter_mut().zip(t) {
                        *x = x.join(*y);
                    }
                    a
                }
            });
        }
        let mut tys = tys?;
        self.s.depths.at(pc)?;
        // Slots dead here take no param.
        let live = &self.s.live[&pc];
        for (t, &l) in tys.iter_mut().zip(live) {
            if !l {
                *t = Ty::Dead;
            }
        }
        self.entry_types.insert(pc, tys.clone());
        let saved = (self.cur, self.live);
        for (t, ttys, from) in pending {
            let target = self.block_for(pc, from).unwrap();
            self.at(t);
            let params = self.f.blocks[t].params.clone();
            let mut params = params.into_iter();
            let mut args = vec![];
            for (&from_ty, &to_ty) in ttys.iter().zip(&tys) {
                let v = if from_ty == Ty::Dead {
                    None
                } else {
                    params.next()
                };
                if to_ty == Ty::Dead {
                    continue;
                }
                let v = v.expect("a slot live at a block is live on each edge into it");
                args.push(EdgeArg::Value(self.convert(Slot { v, ty: from_ty }, to_ty)));
            }
            self.term(
                Opcode::Jump,
                vec![],
                vec![Edge {
                    block: target,
                    args,
                }],
            );
        }
        (self.cur, self.live) = saved;
        Some(tys)
    }

    /// The entry root: callee, `this`, formals. Formals with a claim are
    /// guarded at their definition; locals and rval start undefined.
    fn entry(&mut self) {
        let b0 = self.cur;
        self.f.roots.push(Root {
            kind: RootKind::Entry,
            block: b0,
        });
        let callee = MType::Obj(ObjInfo::kind(ObjKind::Function(Some(self.s.sid))));
        self.f.add_param(b0, callee);
        let this = self.f.add_param(b0, MType::VAL_TOP);
        let all = Ty::Val(TagSet::ALL);
        self.st.push(Slot { v: this, ty: all });
        for _ in 0..self.s.nargs {
            let v = self.f.add_param(b0, MType::VAL_TOP);
            self.st.push(Slot { v, ty: all });
        }
        let undef = self.const_val(ConstVal::Undefined);
        let uty = Ty::Val(TagSet::prims(PRIM_UNDEFINED));
        for _ in 0..=self.s.nlocals {
            self.st.push(Slot { v: undef, ty: uty });
        }
        self.pc = Pc::new(0);
        self.pre = self.st.clone();
        for i in 0..self.s.nargs {
            let (op, ty) = match self.s.arg_claim(i) {
                Ty::I32 => (Opcode::GuardUnbox(UnboxKind::I32), Ty::I32),
                Ty::F64 => (Opcode::GuardUnbox(UnboxKind::F64Num), Ty::F64),
                _ => continue,
            };
            let ix = self.arg_ix(i);
            let v = self.guard(op, vec![self.st[ix].v], ty.mir());
            self.st[ix] = Slot { v, ty };
        }
        self.jump_to(Pc::new(0), None);
    }

    fn op(&mut self, op: JSOp) -> R<()> {
        use JSOp::*;
        let pc = self.pc;
        let mut p = self.s.imms(pc);
        let int_ty = Ty::I32;
        match op {
            // (`DebugLeaveLexicalEnv` only matters with an env chain, which
            // MIR declines.)
            Nop | Lineno | JumpTarget | LoopHead | NopDestructuring | NopIsAssignOp
            | DebugLeaveLexicalEnv => {}

            Undefined => {
                let v = self.const_val(ConstVal::Undefined);
                self.push(v, Ty::Val(TagSet::prims(PRIM_UNDEFINED)));
            }
            Null => {
                let v = self.const_val(ConstVal::Null);
                self.push(v, Ty::Val(TagSet::prims(PRIM_NULL)));
            }
            True | False => {
                let v = self.inst(Opcode::ConstBool(op == True), vec![], Some(MType::Bool));
                self.push(v, Ty::Bool);
            }
            Zero | One | Int8 | Uint16 | Uint24 | Int32 => {
                let n: i32 = match op {
                    Zero => 0,
                    One => 1,
                    Int8 => p.next_int8().unwrap().into(),
                    Uint16 => p.next_uint16().unwrap().into(),
                    Uint24 => p.next_uint24().unwrap() as i32,
                    _ => p.next_int32().unwrap(),
                };
                let v = self.const_i32(n);
                self.push(v, int_ty);
            }
            Double => {
                let x = f64::from_bits(p.next_uint64().unwrap());
                let v = self.const_f64(x);
                self.push(v, Ty::F64);
            }
            Uninitialized => {
                let v = self.const_val(ConstVal::Uninitialized);
                self.push(v, Ty::Val(TagSet::MAGIC));
            }
            Void => {
                self.pop();
                let v = self.const_val(ConstVal::Undefined);
                self.push(v, Ty::Val(TagSet::prims(PRIM_UNDEFINED)));
            }

            // --- frame ---
            GetLocal => {
                let n = p.next_uint24().unwrap();
                let x = self.st[self.local_ix(n)];
                self.st.push(x);
            }
            SetLocal | InitLexical => {
                let n = p.next_uint24().unwrap();
                let ix = self.local_ix(n);
                self.st[ix] = self.top();
            }
            GetArg => {
                let n = u32::from(p.next_uint16().unwrap());
                let x = self.st[self.arg_ix(n)];
                self.st.push(x);
            }
            SetArg => {
                let n = u32::from(p.next_uint16().unwrap());
                let ix = self.arg_ix(n);
                self.st[ix] = self.top();
            }
            GetRval => {
                let x = self.st[self.rval_ix()];
                self.st.push(x);
            }
            SetRval => {
                let x = self.pop();
                let ix = self.rval_ix();
                self.st[ix] = x;
            }
            CheckLexical => {
                // The top may be the TDZ sentinel only if its type admits
                // magic; then guard it away (baseline throws on failure).
                let x = self.top();
                if let Ty::Val(t) = x.ty {
                    if t.magic {
                        let js = TagSet { magic: false, ..t };
                        if js.is_empty() {
                            return Err("CheckLexical of a sure TDZ value".into());
                        }
                        let v = self.guard(Opcode::GuardTags(js), vec![x.v], MType::val(js));
                        self.st.pop();
                        self.push(v, Ty::Val(js));
                    }
                }
            }

            // --- stack ---
            Pop => {
                self.pop();
            }
            PopN => {
                let n = p.next_uint16().unwrap();
                for _ in 0..n {
                    self.pop();
                }
            }
            Dup => {
                let x = self.top();
                self.st.push(x);
            }
            Dup2 => {
                let n = self.st.len();
                let (a, b) = (self.st[n - 2], self.st[n - 1]);
                self.st.push(a);
                self.st.push(b);
            }
            DupAt => {
                let n = p.next_uint24().unwrap() as usize;
                let x = self.st[self.st.len() - 1 - n];
                self.st.push(x);
            }
            Swap => {
                let n = self.st.len();
                self.st.swap(n - 1, n - 2);
            }
            Pick => {
                let n = usize::from(p.next_uint8().unwrap());
                let ix = self.st.len() - 1 - n;
                let x = self.st.remove(ix);
                self.st.push(x);
            }
            Unpick => {
                let n = usize::from(p.next_uint8().unwrap());
                let x = self.pop();
                let ix = self.st.len() - n;
                self.st.insert(ix, x);
            }

            // --- arithmetic ---
            Add | Sub | Mul => {
                let b = self.pop();
                let a = self.pop();
                let arith = match op {
                    Add => ArithOp::Add,
                    Sub => ArithOp::Sub,
                    _ => ArithOp::Mul,
                };
                match (a.ty.num(), b.ty.num()) {
                    (Some(Num::I32), Some(Num::I32))
                        if arith != ArithOp::Mul && self.s.wrap_ok.contains(&pc) =>
                    {
                        // Only ToInt32 of the result is ever observed.
                        let (x, y) = (self.as_i32(a), self.as_i32(b));
                        let r = self.inst(Opcode::I32Wrap(arith), vec![x, y], Some(MType::I32_TOP));
                        self.push(r, Ty::I32);
                    }
                    (Some(Num::I32), Some(Num::I32)) => {
                        let (x, y) = (self.as_i32(a), self.as_i32(b));
                        let r = self.guard(Opcode::I32Ovf(arith), vec![x, y], MType::I32_TOP);
                        self.push(r, Ty::I32);
                    }
                    (Some(_), Some(_)) => {
                        let (x, y) = (self.as_f64(a), self.as_f64(b));
                        let fop = match arith {
                            ArithOp::Add => F64Op::Add,
                            ArithOp::Sub => F64Op::Sub,
                            ArithOp::Mul => F64Op::Mul,
                        };
                        let r = self.inst(Opcode::F64Arith(fop), vec![x, y], Some(MType::F64_TOP));
                        self.push(r, Ty::F64);
                    }
                    _ => {
                        let (x, y) = (self.boxed(a), self.boxed(b));
                        let (jop, tags) = match op {
                            Add => (
                                Opcode::JsAdd,
                                TagSet::prims(crate::opsem::NUM | PRIM_BIGINT)
                                    .union(TagSet::STRING),
                            ),
                            Sub => (
                                Opcode::JsBinop(JsBinop::Sub),
                                TagSet::prims(crate::opsem::NUM | PRIM_BIGINT),
                            ),
                            _ => (
                                Opcode::JsBinop(JsBinop::Mul),
                                TagSet::prims(crate::opsem::NUM | PRIM_BIGINT),
                            ),
                        };
                        let r = self.js(jop, vec![x, y], MType::val(tags));
                        self.push(r, Ty::Val(tags));
                    }
                }
            }
            Div => {
                let b = self.pop();
                let a = self.pop();
                if a.ty.num().is_some() && b.ty.num().is_some() {
                    let (x, y) = (self.as_f64(a), self.as_f64(b));
                    let r = self.inst(
                        Opcode::F64Arith(F64Op::Div),
                        vec![x, y],
                        Some(MType::F64_TOP),
                    );
                    self.push(r, Ty::F64);
                } else {
                    self.js_binop(JsBinop::Div, a, b);
                }
            }
            Mod | Pow => {
                let b = self.pop();
                let a = self.pop();
                let k = if op == Mod {
                    JsBinop::Mod
                } else {
                    JsBinop::Pow
                };
                self.js_binop(k, a, b);
            }
            BitAnd | BitOr | BitXor | Lsh | Rsh => {
                let b = self.pop();
                let a = self.pop();
                if a.ty.num().is_some() && b.ty.num().is_some() {
                    let (x, y) = (self.to_int32(a), self.to_int32(b));
                    let bop = match op {
                        BitAnd => BitOp::And,
                        BitOr => BitOp::Or,
                        BitXor => BitOp::Xor,
                        Lsh => BitOp::Shl,
                        _ => BitOp::Shr,
                    };
                    let r = self.inst(Opcode::I32Bit(bop), vec![x, y], Some(MType::I32_TOP));
                    self.push(r, Ty::I32);
                } else {
                    let k = match op {
                        BitAnd => JsBinop::BitAnd,
                        BitOr => JsBinop::BitOr,
                        BitXor => JsBinop::BitXor,
                        Lsh => JsBinop::Lsh,
                        _ => JsBinop::Rsh,
                    };
                    self.js_binop(k, a, b);
                }
            }
            Ursh => {
                let b = self.pop();
                let a = self.pop();
                if a.ty.num().is_some() && b.ty.num().is_some() {
                    let (x, y) = (self.to_int32(a), self.to_int32(b));
                    let t = MType::int_range(0, u32::MAX.into());
                    let r = self.inst(Opcode::I32Ushr, vec![x, y], Some(t));
                    let f = self.inst(Opcode::IntToF64, vec![r], Some(MType::F64_TOP));
                    self.push(f, Ty::F64);
                } else {
                    self.js_binop(JsBinop::Ursh, a, b);
                }
            }
            Inc | Dec => {
                let a = self.pop();
                match a.ty.num() {
                    Some(Num::I32) => {
                        let x = self.as_i32(a);
                        let one = self.const_i32(1);
                        let k = if op == Inc {
                            ArithOp::Add
                        } else {
                            ArithOp::Sub
                        };
                        let r = self.guard(Opcode::I32Ovf(k), vec![x, one], MType::I32_TOP);
                        self.push(r, Ty::I32);
                    }
                    Some(Num::F64) => {
                        let x = self.as_f64(a);
                        let one = self.const_f64(1.0);
                        let k = if op == Inc { F64Op::Add } else { F64Op::Sub };
                        let r = self.inst(Opcode::F64Arith(k), vec![x, one], Some(MType::F64_TOP));
                        self.push(r, Ty::F64);
                    }
                    None => {
                        let u = if op == Inc { JsUnop::Inc } else { JsUnop::Dec };
                        self.js_unop(u, a);
                    }
                }
            }
            Neg => {
                let a = self.pop();
                match a.ty.num() {
                    // -x as x * -1: fails on INT32_MIN and on 0 (-0).
                    Some(Num::I32) => {
                        let x = self.as_i32(a);
                        let m1 = self.const_i32(-1);
                        let r =
                            self.guard(Opcode::I32Ovf(ArithOp::Mul), vec![x, m1], MType::I32_TOP);
                        self.push(r, Ty::I32);
                    }
                    Some(Num::F64) => {
                        let x = self.as_f64(a);
                        let r = self.inst(Opcode::F64Neg, vec![x], Some(MType::F64_TOP));
                        self.push(r, Ty::F64);
                    }
                    None => self.js_unop(JsUnop::Neg, a),
                }
            }
            BitNot => {
                let a = self.pop();
                if a.ty.num().is_some() {
                    let x = self.to_int32(a);
                    let m1 = self.const_i32(-1);
                    let r = self.inst(
                        Opcode::I32Bit(BitOp::Xor),
                        vec![x, m1],
                        Some(MType::I32_TOP),
                    );
                    self.push(r, Ty::I32);
                } else {
                    self.js_unop(JsUnop::BitNot, a);
                }
            }
            Pos | ToNumeric => {
                let a = self.top();
                if a.ty.num().is_none() {
                    self.pop();
                    if op == Pos {
                        self.js_unop(JsUnop::Pos, a);
                    } else {
                        let tags = TagSet::prims(crate::opsem::NUM | PRIM_BIGINT);
                        let x = self.boxed(a);
                        let r = self.js(Opcode::JsToNumeric, vec![x], MType::val(tags));
                        self.push(r, Ty::Val(tags));
                    }
                }
            }

            // --- compares ---
            Lt | Le | Gt | Ge | Eq | Ne | StrictEq | StrictNe => {
                let b = self.pop();
                let a = self.pop();
                let (cc, jcc) = match op {
                    Lt => (Cc::Lt, JsCc::Lt),
                    Le => (Cc::Le, JsCc::Le),
                    Gt => (Cc::Gt, JsCc::Gt),
                    Ge => (Cc::Ge, JsCc::Ge),
                    Eq => (Cc::Eq, JsCc::Eq),
                    Ne => (Cc::Ne, JsCc::Ne),
                    StrictEq => (Cc::Eq, JsCc::StrictEq),
                    _ => (Cc::Ne, JsCc::StrictNe),
                };
                let r = match (a.ty.num(), b.ty.num()) {
                    (Some(Num::I32), Some(Num::I32)) => {
                        let (x, y) = (self.as_i32(a), self.as_i32(b));
                        self.inst(Opcode::Cmp(NumRepr::I32, cc), vec![x, y], Some(MType::Bool))
                    }
                    (Some(_), Some(_)) => {
                        let (x, y) = (self.as_f64(a), self.as_f64(b));
                        self.inst(Opcode::Cmp(NumRepr::F64, cc), vec![x, y], Some(MType::Bool))
                    }
                    _ => {
                        let (x, y) = (self.boxed(a), self.boxed(b));
                        self.js(Opcode::JsCompare(jcc), vec![x, y], MType::Bool)
                    }
                };
                self.push(r, Ty::Bool);
            }
            Not => {
                let a = self.pop();
                let t = self.truthy(a);
                let r = self.not(t);
                self.push(r, Ty::Bool);
            }

            // --- control ---
            Goto => {
                let off = p.next_int32().unwrap();
                self.jump_to(pc.branch(off), Some(pc));
            }
            JumpIfFalse | JumpIfTrue => {
                let off = p.next_int32().unwrap();
                let c = self.pop();
                let t = self.truthy(c);
                let (target, next) = (pc.branch(off), pc + op.len());
                if op == JumpIfTrue {
                    self.branch(t, target, next);
                } else {
                    self.branch(t, next, target);
                }
            }
            And | Or => {
                let off = p.next_int32().unwrap();
                let c = self.top();
                let t = self.truthy(c);
                let (target, next) = (pc.branch(off), pc + op.len());
                if op == Or {
                    self.branch(t, target, next);
                } else {
                    self.branch(t, next, target);
                }
            }
            Return => {
                let x = self.pop();
                let v = self.boxed(x);
                self.term(Opcode::Return, vec![v], vec![]);
            }
            RetRval => {
                let x = self.st[self.rval_ix()];
                let v = self.boxed(x);
                self.term(Opcode::Return, vec![v], vec![]);
            }

            FunctionThis => {
                let x = self.st[0];
                if self.s.script.strict || x.ty.tags().is_nonempty_subset_of(TagSet::OBJECT) {
                    self.st.push(x);
                } else {
                    // Sloppy: an object `this` is itself; anything else is
                    // boxed (null and undefined become the global `this`).
                    let obj = TagSet::OBJECT;
                    let (t, e, j) = (self.new_block(), self.new_block(), self.new_block());
                    let p = self.f.add_param(t, MType::val(obj));
                    let r = self.f.add_param(j, MType::val(obj));
                    let v = self.boxed(x);
                    self.term(
                        Opcode::GuardTags(obj),
                        vec![v],
                        vec![
                            Edge {
                                block: t,
                                args: vec![EdgeArg::Out(0)],
                            },
                            Self::goto(e),
                        ],
                    );
                    self.at(t);
                    self.term(
                        Opcode::Jump,
                        vec![],
                        vec![Edge {
                            block: j,
                            args: vec![EdgeArg::Value(p)],
                        }],
                    );
                    self.at(e);
                    let b = self.js(Opcode::JsBoxThis, vec![v], MType::val(obj));
                    self.term(
                        Opcode::Jump,
                        vec![],
                        vec![Edge {
                            block: j,
                            args: vec![EdgeArg::Value(b)],
                        }],
                    );
                    self.at(j);
                    self.push(r, Ty::Val(obj));
                }
            }
            String => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let s = self.inst(
                    Opcode::ConstStr(a),
                    vec![],
                    Some(MType::Str(mir::types::StrInfo { atom: Some(a) })),
                );
                let x = Slot {
                    v: s,
                    ty: Ty::Val(TagSet::STRING),
                };
                let t = mir::ops::box_type(&self.f.ty(s)).expect("strings box");
                let v = self.inst(Opcode::Box, vec![x.v], Some(t));
                let v = self.weaken(v, MType::val(TagSet::STRING));
                self.push(v, Ty::Val(TagSet::STRING));
            }
            BindUnqualifiedGName => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let r = self.js(Opcode::JsBindGName(a), vec![], MType::val(TagSet::OBJECT));
                self.push(r, Ty::Val(TagSet::OBJECT));
            }
            SetGName | StrictSetGName => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let v = self.pop();
                let env = self.pop();
                let (e, y) = (self.boxed(env), self.boxed(v));
                self.js_void(Opcode::JsSetName(a, op == StrictSetGName), vec![e, y]);
                self.st.push(v);
            }
            TableSwitch => {
                let default_off = p.next_int32().unwrap();
                let low = p.next_int32().unwrap();
                let high = p.next_int32().unwrap();
                let first = p.next_uint24().unwrap() as usize;
                let x = self.pop();
                let n = usize::try_from((i64::from(high) - i64::from(low) + 1).max(0)).unwrap();
                let default = pc.branch(default_off);
                let mut targets = vec![];
                for k in 0..n {
                    let t = *self
                        .s
                        .script
                        .resume_offsets
                        .get(first + k)
                        .ok_or("TableSwitch resume index out of range")?;
                    targets.push(t);
                }
                // An int32, or a double that is exactly one, selects a case;
                // anything else takes the default.
                let i = match x.ty {
                    Ty::I32 => x.v,
                    Ty::F64 | Ty::Val(_) => {
                        let f = match x.ty {
                            Ty::F64 => x.v,
                            _ => {
                                let d = self.new_block();
                                let o = self.f.add_param(d, MType::F64_TOP);
                                let Some(de) = self.edge_to(default, Some(pc)) else {
                                    self.term(Opcode::Unreachable, vec![], vec![]);
                                    return Ok(());
                                };
                                self.term(
                                    Opcode::GuardUnbox(UnboxKind::F64Num),
                                    vec![x.v],
                                    vec![
                                        Edge {
                                            block: d,
                                            args: vec![EdgeArg::Out(0)],
                                        },
                                        de,
                                    ],
                                );
                                self.at(d);
                                o
                            }
                        };
                        // -0 selects case 0 as +0 does: `x + 0` is +0 for
                        // either zero and `x` otherwise.
                        let z = self.const_f64(0.0);
                        let f = self.inst(
                            Opcode::F64Arith(F64Op::Add),
                            vec![f, z],
                            Some(MType::F64_TOP),
                        );
                        let d = self.new_block();
                        let o = self.f.add_param(d, MType::I32_TOP);
                        let Some(de) = self.edge_to(default, Some(pc)) else {
                            self.term(Opcode::Unreachable, vec![], vec![]);
                            return Ok(());
                        };
                        self.term(
                            Opcode::F64ToIntExact,
                            vec![f],
                            vec![
                                Edge {
                                    block: d,
                                    args: vec![EdgeArg::Out(0)],
                                },
                                de,
                            ],
                        );
                        self.at(d);
                        o
                    }
                    Ty::Bool => {
                        self.jump_to(default, Some(pc));
                        return Ok(());
                    }
                    Ty::Dead => unreachable!("a dead slot is never read"),
                };
                let lo = self.const_i32(low);
                let idx = self.inst(
                    Opcode::I32Wrap(ArithOp::Sub),
                    vec![i, lo],
                    Some(MType::I32_TOP),
                );
                let mut edges = vec![];
                for t in targets.into_iter().chain([default]) {
                    match self.edge_to(t, Some(pc)) {
                        Some(e) => edges.push(e),
                        None => {
                            self.term(Opcode::Unreachable, vec![], vec![]);
                            return Ok(());
                        }
                    }
                }
                self.term(Opcode::Switch(u32::try_from(n).unwrap()), vec![idx], edges);
            }
            Case => {
                // [lval, cond]: true pops both and jumps; false keeps lval.
                let off = p.next_int32().unwrap();
                let c = self.pop();
                let t = self.truthy(c);
                let (target, next) = (pc.branch(off), pc + op.len());
                let ne = self.edge_to(next, Some(pc));
                let lval = self.pop();
                let te = self.edge_to(target, Some(pc));
                self.st.push(lval);
                match (te, ne) {
                    (Some(te), Some(ne)) => self.term(Opcode::Br, vec![t], vec![te, ne]),
                    _ => self.term(Opcode::Unreachable, vec![], vec![]),
                }
            }
            Default => {
                let off = p.next_int32().unwrap();
                self.pop();
                self.jump_to(pc.branch(off), Some(pc));
            }
            StrictConstantEq | StrictConstantNe => {
                let operand = p.next_uint16().unwrap();
                let a = self.pop();
                let x = self.boxed(a);
                let mut r = self.inst(
                    Opcode::JsConstantStrictEq(operand),
                    vec![x],
                    Some(MType::Bool),
                );
                if op == StrictConstantNe {
                    r = self.not(r);
                }
                self.push(r, Ty::Bool);
            }
            IsNullOrUndefined => {
                // [v] -> [v, v is null or undefined], decided by the tags
                // when they say, else by a tag test merging both ways.
                let a = self.top();
                let nullish = TagSet::prims(PRIM_NULL | PRIM_UNDEFINED);
                let tags = a.ty.tags();
                let r = if tags.subset_of(nullish) {
                    self.inst(Opcode::ConstBool(true), vec![], Some(MType::Bool))
                } else if tags.intersect(nullish).is_empty() {
                    self.inst(Opcode::ConstBool(false), vec![], Some(MType::Bool))
                } else {
                    let x = self.boxed(a);
                    self.tag_test(x, nullish)
                };
                self.push(r, Ty::Bool);
            }
            TypeofEq => {
                let operand = p.next_uint8().unwrap();
                let a = self.pop();
                let x = self.boxed(a);
                let r = self.inst(Opcode::JsTypeofEq(operand), vec![x], Some(MType::Bool));
                self.push(r, Ty::Bool);
            }

            // --- generic names, properties, elements and calls ---
            GetGName => {
                if self.s.next_is_typeof(pc, op) {
                    return Err("GetGName for typeof".into());
                }
                let a = self.atom(p.next_uint32().unwrap())?;
                let r = self.js_static(Opcode::JsGetName(a), vec![], MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
            }
            GetProp => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let recv = self.pop();
                if let Some(site) = self.typed_site(pc, a) {
                    // The predicted layout: guard the receiver's class
                    // locally, then load the field (§4.3).
                    let o = self.guard_layout(recv, &site);
                    let claim = site.claim_ty();
                    let r = self.js(Opcode::LoadField(a), vec![o], claim);
                    if site.int32 {
                        let v =
                            self.guard(Opcode::GuardUnbox(UnboxKind::I32), vec![r], MType::I32_TOP);
                        self.push(v, Ty::I32);
                    } else {
                        let tags = if site.types {
                            TagSet::NUMBER
                        } else {
                            TagSet::ALL
                        };
                        self.push(r, Ty::Val(tags));
                    }
                } else {
                    let x = self.boxed(recv);
                    let r = self.js(Opcode::JsGetProp(a), vec![x], MType::VAL_TOP);
                    self.push(r, Ty::Val(TagSet::ALL));
                    let claim = self.s.ctx.facts.field_sites.get(&self.site(pc)).copied();
                    self.guard_result(claim.unwrap_or_default(), pc + op.len());
                }
            }
            SetProp | StrictSetProp
                if {
                    let v = self.top();
                    v.ty.num().is_some()
                } =>
            {
                let a = self.atom(p.next_uint32().unwrap())?;
                match self.typed_site(pc, a).filter(|s| s.types) {
                    Some(site) => {
                        // A number into a field claimed as a number: the
                        // store keeps the claim, so no conformance check,
                        // and a number over a number needs no barriers.
                        let v = self.pop();
                        let recv = self.pop();
                        let o = self.guard_layout(recv, &site);
                        let x = self.boxed(v);
                        let x = self.weaken(x, MType::val(TagSet::NUMBER));
                        self.js_void(Opcode::StoreField(a), vec![o, x]);
                        self.st.push(v);
                    }
                    None => {
                        let v = self.pop();
                        let recv = self.pop();
                        let (x, y) = (self.boxed(recv), self.boxed(v));
                        self.js_void(Opcode::JsSetProp(a, op == StrictSetProp), vec![x, y]);
                        self.st.push(v);
                    }
                }
            }
            SetProp | StrictSetProp => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let v = self.pop();
                let recv = self.pop();
                let (x, y) = (self.boxed(recv), self.boxed(v));
                self.js_void(Opcode::JsSetProp(a, op == StrictSetProp), vec![x, y]);
                self.st.push(v);
            }
            GetElem => {
                let key = self.pop();
                let recv = self.pop();
                let (x, k) = (self.boxed(recv), self.boxed(key));
                let r = self.js(Opcode::JsGetElem, vec![x, k], MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
                let claim = self.s.ctx.facts.elem_sites.get(&self.site(pc)).copied();
                self.guard_result(claim.unwrap_or_default(), pc + op.len());
            }
            SetElem | StrictSetElem => {
                let v = self.pop();
                let key = self.pop();
                let recv = self.pop();
                let (x, k, y) = (self.boxed(recv), self.boxed(key), self.boxed(v));
                self.js_void(Opcode::JsSetElem(op == StrictSetElem), vec![x, k, y]);
                self.st.push(v);
            }
            Call | CallIgnoresRv | CallContent => {
                let argc = usize::from(p.next_uint16().unwrap());
                let n = self.st.len();
                let operands: Vec<Slot> = self.st.drain(n - argc - 2..).collect();
                let vals: Vec<mir::Value> = operands.into_iter().map(|x| self.boxed(x)).collect();
                let r = self.js(Opcode::Call, vals, MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
                let claim = self.s.ctx.facts.call_types.get(&self.site(pc)).copied();
                self.guard_result(claim.unwrap_or_default(), pc + op.len());
            }

            op => return Err(format!("{op:?}")),
        }
        Ok(())
    }

    fn js_binop(&mut self, k: JsBinop, a: Slot, b: Slot) {
        let (x, y) = (self.boxed(a), self.boxed(b));
        let tags = match k {
            JsBinop::Ursh => TagSet::NUMBER,
            JsBinop::BitAnd | JsBinop::BitOr | JsBinop::BitXor | JsBinop::Lsh | JsBinop::Rsh => {
                TagSet::prims(PRIM_INT32 | PRIM_BIGINT)
            }
            _ => TagSet::prims(crate::opsem::NUM | PRIM_BIGINT),
        };
        let r = self.js(Opcode::JsBinop(k), vec![x, y], MType::val(tags));
        self.push(r, Ty::Val(tags));
    }

    fn js_unop(&mut self, u: JsUnop, a: Slot) {
        let x = self.boxed(a);
        let tags = match u {
            JsUnop::Pos => TagSet::NUMBER,
            _ => TagSet::prims(crate::opsem::NUM | PRIM_BIGINT),
        };
        let r = self.js(Opcode::JsUnop(u), vec![x], MType::val(tags));
        self.push(r, Ty::Val(tags));
    }
}
