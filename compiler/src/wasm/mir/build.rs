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
    ArithOp, BitOp, Cc, ConstVal, F64Op, JsBinop, JsCc, JsUnop, MathFn, NumRepr, Opcode, RtOp,
    UnboxKind,
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
    /// An object of one of `keys`' layouts, with its TYPES bit if the
    /// flag says so: the raw object (`obj{L…}`), proven by a guard that
    /// dominates (§4.3). The slot keeps the proof across joins and loops,
    /// so the field accesses through it take no guard of their own.
    Obj(KeyRange, bool),
    /// An object proven of `keys`' layouts before a fence that may have
    /// changed that (a call, a generic op): the raw object (`obj`). A
    /// field access through it guards the layout again, exiting on a miss
    /// (identity rarely changes), and refines the slot back to `Obj`.
    ObjHint(KeyRange),
    /// A native object (`obj{Native}`, raw): its elements are addressable
    /// (`load_elem`, `store_elem`). Immutable, so no fence kills it.
    Native,
    /// A typed array of this kind (`obj{TypedArray(k)}`, raw): its
    /// elements are `load_ta`/`store_ta`. Immutable.
    Ta(crate::opsem::TaKind),
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
            Ty::Obj(keys, types) => MType::Obj(ObjInfo {
                layout: Some(LayoutClaim {
                    keys,
                    types,
                    state: LayoutState::Published,
                }),
                ..ObjInfo::TOP
            }),
            Ty::ObjHint(_) => MType::OBJ_TOP,
            Ty::Native => MType::Obj(ObjInfo::kind(ObjKind::Native)),
            Ty::Ta(k) => MType::Obj(ObjInfo::kind(ObjKind::TypedArray(k))),
            Ty::Dead => unreachable!("a dead slot has no type"),
        }
    }

    fn tags(self) -> TagSet {
        match self {
            Ty::I32 => TagSet::INT32,
            Ty::F64 => TagSet::NUMBER,
            Ty::Bool => TagSet::BOOLEAN,
            Ty::Val(t) => t,
            Ty::Obj(..) | Ty::ObjHint(_) | Ty::Native | Ty::Ta(_) => TagSet::OBJECT,
            Ty::Dead => TagSet::NONE,
        }
    }

    fn join(self, o: Ty) -> Ty {
        match (self, o) {
            (a, b) if a == b => a,
            (Ty::Dead, x) | (x, Ty::Dead) => x,
            (Ty::I32, Ty::F64) | (Ty::F64, Ty::I32) => Ty::F64,
            (Ty::Obj(k1, t1), Ty::Obj(k2, t2)) => Ty::Obj(k1.hull(&k2), t1 && t2),
            (Ty::Obj(k1, _) | Ty::ObjHint(k1), Ty::Obj(k2, _) | Ty::ObjHint(k2)) => {
                Ty::ObjHint(k1.hull(&k2))
            }
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

/// The representation a numeric claim is speculated in (§8's
/// guard-at-defs): int32 for an int32-only claim; with `int_first`, also
/// for a number claim with int32 in it that is not flagged double-first
/// (the order bbv's typed-load ladder tries), exiting on a double; f64
/// for other number claims. `None` for anything else. Int-first suits
/// formals, element and name reads (indices, digits, counters: crypto's
/// am3 gains 17%); property reads and call results often hold doubles
/// the claim does not flag (raytrace's vectors), and an exit per double
/// costs far more than the ToInt32s int-first saves.
const SPECULATE_INT_FIRST: bool = true;

/// Whether the generic runtime ops (`js.rt`, `js.throw`, `js.typeof`)
/// are built.
const RT_OPS: bool = true;

/// Whether `T.apply(this, arguments)` forwards the actuals.
const APPLY_FWD: bool = true;

/// Whether scripts that read their actuals are built.
const ACTUALS: bool = true;

fn num_claim_ty(claim: crate::facts::Claim, int_first: bool) -> Option<Ty> {
    let prims = claim.prims();
    if claim.is_none() || claim.is_object() || prims.is_empty() {
        None
    } else if prims.subset_of(PRIM_INT32)
        || (SPECULATE_INT_FIRST
            && int_first
            && prims.subset_of(crate::opsem::NUM)
            && prims.intersects(PRIM_INT32)
            && !claim.double_first())
    {
        Some(Ty::I32)
    } else if prims.subset_of(crate::opsem::NUM) {
        Some(Ty::F64)
    } else {
        None
    }
}

/// Whether every field of layout `k` has a number claim (so its objects
/// keep the TYPES bit through engine-path stores); false for a layout no
/// constructor describes.
fn numeric_layout(ctx: &crate::wasm::translate::TranslateCtx<'_>, k: u32) -> bool {
    let mut rows = ctx
        .stamp_ctors_in
        .values()
        .chain(ctx.construct_sites_in.values())
        .filter(|si| si.layout_id == k)
        .peekable();
    rows.peek().is_some()
        && rows.all(|si| {
            si.masks.iter().all(|m| {
                let p = m.prims();
                !p.is_empty() && p.subset_of(crate::opsem::NUM)
            })
        })
}

impl<'a> Shape<'a> {
    /// Whether callee `k` is small enough to inline at `pc` among
    /// `ntargets` targets: bbv's caps, 150 bytes of bytecode for one
    /// target (200 in a loop), 500 each for several.
    fn fits_site(&self, k: ScriptId, pc: Pc, ntargets: usize) -> bool {
        let in_loop = self.loops.iter().any(|(&h, &e)| h <= pc && pc < e);
        let cap = match (ntargets, in_loop) {
            (1, false) => 150,
            (1, true) => 200,
            _ => crate::constants::MAX_INLINE_POLY_BYTES,
        };
        matches!(
            self.ctx.source.object(crate::source::SourceObjectId::new(k.get())),
            crate::source::SourceObject::Script(ks) if ks.bytecode.len() <= cap
        )
    }

    /// Whether nothing in the script catches or closes on a throw (only
    /// loop notes; not a generator): baseline's landing for any throw is
    /// its error return, which reads nothing of the frame.
    fn throws_uncaught(&self) -> bool {
        !self.script.is_generator_or_async
            && self
                .script
                .try_notes
                .iter()
                .all(|t| t.kind == crate::bytecode::TryNoteKind::Loop)
    }

    /// Callee `k` built for inlining here (§5.5), if it may be: an
    /// inline-eligible script that is not this one, not a constructor
    /// that stamps its `this`, and small enough once built.
    fn callee(&self, k: ScriptId) -> Option<std::rc::Rc<super::inline::Callee>> {
        if let Some(c) = self.callees.borrow().get(&k) {
            return c.clone();
        }
        let c = self.build_callee(k).map(std::rc::Rc::new);
        self.callees.borrow_mut().insert(k, c.clone());
        c
    }

    fn build_callee(&self, k: ScriptId) -> Option<super::inline::Callee> {
        if self.inline_depth >= MAX_INLINE_DEPTH || k == self.sid {
            return None;
        }
        let names = self.names?;
        let crate::source::SourceObject::Script(ks) =
            self.ctx.source.object(crate::source::SourceObjectId::new(k.get()))
        else {
            return None;
        };
        // A stamping constructor or an init delegate stamps `this` at its
        // returns, which an inlined copy's returns would skip.
        if !super::inline_eligible(self.ctx, ks) || self.ctx.deleg_restamps_in.contains_key(&k) {
            return None;
        }
        let (mut mm, f) = build_at(self.ctx, names, k, ks, false, self.inline_depth + 1).ok()?;
        if f.insts.len() > MAX_INLINE_INSTS {
            return None;
        }
        mm.script_addrs.insert(k, ks.addr);
        let max_depth = StackDepths::compute(ks).ok()?.max;
        Some(super::inline::Callee { mm, f, max_depth })
    }
}

/// A property access the analysis predicts: the receiver's layouts
/// `[lo, hi]`, and whether the field's claim is backed by the stamp's
/// TYPES bit (a number).
#[derive(Clone, Copy, Debug)]
struct TypedSite {
    lo: u32,
    hi: u32,
    types: bool,
    /// The analysis's value claim, to guard at the def when the stamp
    /// does not back it (`!types`).
    claim: crate::facts::Claim,
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
pub fn build<'a>(
    ctx: &'a TranslateCtx<'a>,
    names: &'a crate::ids::Names,
    sid: ScriptId,
    script: &'a Script,
    is_global: bool,
) -> Result<(mir::Module, mir::Func), String> {
    build_at(ctx, names, sid, script, is_global, 0)
}

/// Element accesses the analysis predicts on arrays, with int32 keys, are
/// `load_elem`/`store_elem` on a native receiver.
const NATIVE_ELEMS: bool = true;

/// Element accesses the analysis predicts on typed arrays are
/// `load_ta`/`store_ta`.
const TA_ELEMS: bool = true;

/// A loop-invariant array's receiver guard is hoisted to the loop's entry.
const HOIST_NATIVE: bool = true;

/// Scripts whose mapped `arguments` alias formals are built: the formals
/// are read and written through the object.
const MAPPED_ARGS: bool = true;

/// `new` of a site's one constructor is inlined.
const INLINE_CONSTRUCT: bool = true;

/// Typed field accesses exit on a dirty IC arm rather than rejoin.
const DIRTY_EXITS: bool = true;

/// Generic ops keep proven layouts on their clean edge (`js_keep`).
const KEEP_ON_CLEAN: bool = true;

/// Guard a method's `this` to its predicted layouts at `FunctionThis`.
const THIS_ENTRY_GUARD: bool = true;

/// How deep inlining nests: a caller's callees, and theirs.
const MAX_INLINE_DEPTH: u32 = 4;
/// The most MIR instructions a callee may have to be inlined.
const MAX_INLINE_INSTS: usize = 2000;
/// The most call sites one function inlines into (bbv's per-caller splice
/// cap: past a few sites the code growth costs more than the calls).
const MAX_INLINE_SITES: u32 = 8;
/// The most callee instructions one function splices in, over all its
/// sites: a body past wasm's function size limit fails the module.
const MAX_INLINE_TOTAL_INSTS: usize = 6000;
/// The most targets a call site inlines (a guard chain on the script).
const MAX_INLINE_TARGETS: usize = 4;

/// `build`, as the callee of an inlining `depth` levels down.
fn build_at<'a>(
    ctx: &'a TranslateCtx<'a>,
    names: &'a crate::ids::Names,
    sid: ScriptId,
    script: &'a Script,
    is_global: bool,
    depth: u32,
) -> Result<(mir::Module, mir::Func), String> {
    if is_global {
        return Err("global script".into());
    }
    // A MIR script carries two bodies (MIR and baseline). An
    // Emscripten-sized function would dominate the batch's memory and
    // compile time for little gain, so it stays in baseline.
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
    // A mapped arguments object aliases the formals. With no formals there
    // is nothing to alias, and the object (made by the runtime, which maps
    // by the callee) is an unmapped one plus `callee`: scheme runtimes'
    // variadic `sc_list`, prototype.js's `Class.create` wrapper.
    if script.has_mapped_args && script.nargs > 0 && !MAPPED_ARGS {
        return Err("mapped arguments".into());
    }
    if !ACTUALS && fl.rebase_vp {
        return Err("reads actuals".into());
    }
    // The env chain is fixed for the whole activation (§5.1): the callee's
    // own environment, or the one the entry makes (`env_setup`); an op
    // that pushes a scope declines on its own.
    let depths = StackDepths::compute(script).map_err(|e| format!("stack depths ({e})"))?;
    let mut shape = Shape::of(ctx, sid, script, fl, depths)?;
    shape.names = Some(names);
    shape.apply_fwd = crate::wasm::translate::compute_apply_fwd_pcs(script, &ctx.facts.apply_sites, sid.get())
        .filter(|s| APPLY_FWD && !s.is_empty());
    shape.inline_depth = depth;
    for (i, &gc) in script.gcthings.iter().enumerate() {
        if gc.is_other() {
            continue;
        }
        if let crate::source::SourceObject::String(s) = ctx.source.object(gc) {
            let Some(n) = names.lookup(s.chars()) else {
                continue;
            };
            let i = u32::try_from(i).unwrap();
            if let Some(fg) = ctx.fused_gnames.get(&n) {
                shape.fused.insert(i, *fg);
            }
            if let Some(c) = ctx.facts.gname_types.get(&n) {
                shape.gname_types.insert(i, *c);
            }
        }
    }
    let mut table: BTreeMap<Pc, Vec<Ty>> = BTreeMap::new();
    // Loop-header slots guarded on the way into their loop (§10.2).
    let mut hoist: BTreeMap<(Pc, usize), Ty> = BTreeMap::new();
    // Within a run, a block's entry types join every forward edge into it
    // (`Run::pending`), so a run misses only what a loop's back edges
    // bring. Each rerun widens some loop header's entry types, and there
    // are finitely many widenings; the bound is a backstop.
    for _ in 0..256 {
        let mut run = Run::new(&shape, &table, &hoist);
        run.build()?;
        let new_hoists: Vec<((Pc, usize), Ty)> = run
            .hoist_req
            .iter()
            .filter(|(k, _)| !hoist.contains_key(k))
            .map(|(&k, &t)| (k, t))
            .collect();
        if !run.widen && new_hoists.is_empty() {
            let mm = std::mem::take(&mut run.mm);
            return Ok((mm, run.finish()));
        }
        let out = std::mem::take(&mut run.out);
        drop(run);
        if !new_hoists.is_empty() {
            // Entry types only widen across runs: a narrower header starts
            // them over (the hoist set only grows, so this terminates).
            hoist.extend(new_hoists);
            table.clear();
            continue;
        }
        for (pc, tys) in out {
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
            JSOp::GetArg | JSOp::GetFrameArg => (Some(1 + usize::from(p.next_uint16().unwrap())), None),
            JSOp::SetArg => (None, Some(1 + usize::from(p.next_uint16().unwrap()))),
            JSOp::GetRval | JSOp::RetRval => (Some(rval), None),
            JSOp::SetRval => (None, Some(rval)),
            _ => (None, None),
        }
    };
    // Exception edges: an op a catch or finally covers may throw to its
    // handler, which baseline, resumed by an exit, can reach with the
    // frame as the exit wrote it.
    let handlers: Vec<(Pc, u32, Pc)> = script
        .try_notes
        .iter()
        .filter(|t| matches!(t.kind, crate::bytecode::TryNoteKind::Catch | crate::bytecode::TryNoteKind::Finally))
        .map(|t| (t.start, t.length, t.start + t.length))
        .collect();
    let mut live: BTreeMap<Pc, Vec<bool>> = succs.keys().map(|&pc| (pc, vec![false; n])).collect();
    let pcs: Vec<Pc> = succs.keys().copied().rev().collect();
    let mut changed = true;
    while changed {
        changed = false;
        for &pc in &pcs {
            let (op, ss) = &succs[&pc];
            let mut l = vec![false; n];
            let exc = handlers
                .iter()
                .filter(|&&(start, len, _)| pc >= start && pc < start + len)
                .map(|&(_, _, h)| h);
            for s in ss.iter().copied().chain(exc).collect::<Vec<_>>().iter() {
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
    /// Per gcthing index naming a fused global: its fuse and literal.
    fused: BTreeMap<u32, crate::wasm::translate::FusedGname>,
    /// Per gcthing index naming a global: the analysis's likely type
    /// (`gname_types`), guarded at the def.
    gname_types: BTreeMap<u32, crate::facts::Claim>,
    names: Option<&'a crate::ids::Names>,
    /// The `T.apply(this, arguments)` sites whose arguments object is
    /// never observed (bbv's `compute_apply_fwd_pcs`), if the script has
    /// them.
    apply_fwd: Option<rustc_hash::FxHashSet<Pc>>,
    /// How deep in inlining this build is (0: a script's own).
    inline_depth: u32,
    /// Callees built for inlining, by script; `None` if one cannot be.
    callees: std::cell::RefCell<BTreeMap<ScriptId, Option<std::rc::Rc<super::inline::Callee>>>>,
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
            fused: BTreeMap::new(),
            gname_types: BTreeMap::new(),
            names: None,
            apply_fwd: None,
            inline_depth: 0,
            callees: Default::default(),
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
    /// A formal some call leaves out takes none: its `undefined` would
    /// fail the entry guard on every such call.
    fn arg_claim(&self, i: u32) -> Ty {
        if self.ctx.facts.omitted_formals.contains(&(self.sid, i)) {
            return Ty::Val(TagSet::ALL);
        }
        let claim = self
            .ctx
            .facts
            .arg_types
            .get(&(self.sid, ArgIndex::new(i + 1)))
            .copied()
            .unwrap_or(Claim::NONE);
        num_claim_ty(claim, true).unwrap_or(Ty::Val(TagSet::ALL))
    }
}

/// One run of the builder over the script.
struct Run<'s, 'a> {
    s: &'s Shape<'a>,
    table: &'s BTreeMap<Pc, Vec<Ty>>,
    /// Loop-header slots this run guards on the way into their loop, to
    /// their narrow type (`Native`, `Ta`).
    hoist: &'s BTreeMap<(Pc, usize), Ty>,
    /// Loop-header slots whose back edges bring a narrow object type where
    /// the header has a `Val`: guarded on entry in the next run.
    hoist_req: BTreeMap<(Pc, usize), Ty>,
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
    /// The value standing for the elided arguments object at an apply
    /// forward site (`apply_forward`), if `Arguments` has run.
    args_placeholder: Option<mir::Value>,
    /// The local the placeholder was stored into (the `arguments` binding,
    /// written once: `compute_apply_fwd_pcs`); tracked by slot, since
    /// block params rename the value.
    args_local: Option<usize>,
    /// The op being built, its state before it, and its shared exit and
    /// throw blocks.
    pc: Pc,
    pre: Vec<Slot>,
    exit_blk: Option<mir::Block>,
    throw_blk: Option<mir::Block>,
    /// Call sites this run has inlined into (`MAX_INLINE_SITES`), and the
    /// callee instructions they spliced (`MAX_INLINE_TOTAL_INSTS`).
    inline_sites: u32,
    inline_insts: usize,
    /// This op's fence renamings of `Obj` values (`fence_params`), for
    /// `repush`.
    renames: Vec<(mir::Value, Slot)>,
    /// The pc after the op being built (`js_keep`'s exits).
    next_pc: Option<Pc>,
}

impl<'s, 'a> Run<'s, 'a> {
    fn new(
        s: &'s Shape<'a>,
        table: &'s BTreeMap<Pc, Vec<Ty>>,
        hoist: &'s BTreeMap<(Pc, usize), Ty>,
    ) -> Run<'s, 'a> {
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
            hoist,
            hoist_req: BTreeMap::new(),
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
            args_placeholder: None,
            args_local: None,
            pc: Pc::new(0),
            pre: vec![],
            exit_blk: None,
            throw_blk: None,
            renames: vec![],
            next_pc: None,
            inline_sites: 0,
            inline_insts: 0,
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
        self.retain_locals(&op);
        let tys: Vec<MType> = result.into_iter().collect();
        let (_, rs) = self.f.add_inst(self.cur, op, args, &tys, vec![]);
        rs.first()
            .copied()
            .unwrap_or_else(|| mir::Value::from_u32(0))
    }

    fn term(&mut self, op: Opcode, args: Vec<mir::Value>, mut succs: Vec<Edge>) {
        self.retain_locals(&op);
        self.fence_params(&op, &args, &mut succs);
        self.f.add_inst(self.cur, op, args, &[], succs);
        self.live = false;
    }

    /// A terminator that may change what an `Obj` slot proves (a call, a
    /// generic op: it kills layout claims on an edge the build continues
    /// on) weakens each such slot's value to `obj` first, in the current
    /// block (§5's fence rule), and the slot continues as `ObjHint`.
    /// Operands the op popped are renamed the same way (`repush`). Throw
    /// exits need nothing: they only box.
    fn fence_params(&mut self, op: &Opcode, args: &[mir::Value], succs: &mut [Edge]) {
        let _ = succs;
        let tys: Vec<MType> = args.iter().map(|&v| self.f.ty(v)).collect();
        let fx = mir::ops::effects(op, &tys, &self.mm);
        if !matches!(
            op.kill_site(&fx),
            mir::ops::KillSite::OkEdge | mir::ops::KillSite::DirtyEdge
        ) {
            return;
        }
        let mut done: Vec<(mir::Value, Slot)> = vec![];
        let olds: Vec<Slot> = self.st.iter().chain(&self.pre).copied().collect();
        for x in olds {
            let Ty::Obj(k, _) = x.ty else { continue };
            if !fx.kill.matches(&x.ty.mir()) || done.iter().any(|&(v, _)| v == x.v) {
                continue;
            }
            let y = Slot {
                v: self.weaken(x.v, MType::OBJ_TOP),
                ty: Ty::ObjHint(k),
            };
            done.push((x.v, y));
        }
        if done.is_empty() {
            return;
        }
        for (v, y) in done {
            for x in self.st.iter_mut().chain(self.pre.iter_mut()).filter(|x| x.v == v) {
                *x = y;
            }
            self.renames.push((v, y));
        }
        // An exit at this op's pc made before the fence may be reached
        // after it: the next one is made from the renamed state.
        self.exit_blk = None;
    }

    /// Push `x`, an operand this op popped, back: as its fence renamed it,
    /// if one did (`fence_params`).
    fn repush(&mut self, x: Slot) {
        let y = self
            .renames
            .iter()
            .rev()
            .find(|(v, _)| *v == x.v)
            .map_or(x, |&(_, y)| y);
        self.st.push(y);
    }

    /// `x`, as `ObjHint` if it is an `Obj`.
    fn demote(&mut self, x: Slot) -> Slot {
        match x.ty {
            Ty::Obj(k, _) => Slot {
                v: self.weaken(x.v, MType::OBJ_TOP),
                ty: Ty::ObjHint(k),
            },
            _ => x,
        }
    }

    /// Whether this function may inline one more site whose callees add
    /// `insts` instructions (`MAX_INLINE_SITES`, `MAX_INLINE_TOTAL_INSTS`),
    /// counting it if so.
    fn inline_budget(&mut self, insts: usize) -> bool {
        if self.inline_sites >= MAX_INLINE_SITES || self.inline_insts + insts > MAX_INLINE_TOTAL_INSTS {
            return false;
        }
        self.inline_sites += 1;
        self.inline_insts += insts;
        true
    }

    /// At a layout constructor's return, the first stamp of its completed
    /// `this` (a no-op unless `this` is still under construction, so a
    /// call without `new` stamps nothing); an inlined copy stamps too.
    fn ctor_stamp(&mut self) {
        let Some(si) = self.s.ctx.stamp_ctors_in.get(&self.s.sid) else {
            return;
        };
        let op = Opcode::CtorStamp(
            si.layout_id,
            u32::try_from(si.fields.len()).unwrap(),
            crate::wasm::bbv::ctor_stamp_keep_bits(si),
        );
        let t = self.boxed(self.st[0]);
        self.inst(op, vec![t], None);
    }

    /// Whether the script's formals are its mapped `arguments` object's.
    fn mapped(&self) -> bool {
        self.s.script.has_mapped_args && self.s.nargs > 0
    }

    /// Every `Obj` slot, as `ObjHint`: in the state and in this op's
    /// pre-state (which its exits are made from; exits made before are
    /// dropped, an inlined callee's reaching its caller's through
    /// `exit.inline`), for `repush` too.
    fn demote_objs(&mut self) {
        let mut done: Vec<(mir::Value, Slot)> = vec![];
        let olds: Vec<Slot> = self.st.iter().chain(&self.pre).copied().collect();
        for x in olds {
            let Ty::Obj(k, _) = x.ty else { continue };
            if done.iter().any(|&(v, _)| v == x.v) {
                continue;
            }
            let y = Slot {
                v: self.weaken(x.v, MType::OBJ_TOP),
                ty: Ty::ObjHint(k),
            };
            done.push((x.v, y));
        }
        if done.is_empty() {
            return;
        }
        for (v, y) in done {
            for x in self.st.iter_mut().chain(self.pre.iter_mut()).filter(|x| x.v == v) {
                *x = y;
            }
            self.renames.push((v, y));
        }
        self.exit_blk = None;
        self.throw_blk = None;
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

    /// Before an op that may GC: write each managed local (formal, local,
    /// rval) to the frame, where the GC sees it. A local's value then stays
    /// alive until the local is overwritten, as in baseline, whose frame
    /// holds it (a `WeakMap` key held only by a dead local must survive);
    /// MIR otherwise roots only what is live. Emitted before every such op:
    /// the lowering writes them only where the op can GC (a slow path, or
    /// the call), and drops a store of what the frame holds on the path.
    fn retain_locals(&mut self, op: &Opcode) {
        use mir::ops::SuccRole;
        let may_gc = op.roles().iter().any(|r| matches!(r, SuccRole::Err | SuccRole::OkDirty));
        if may_gc {
            self.retain_all();
        }
    }

    /// `retain_locals` unconditionally: before an inlined callee, whose
    /// GC points are its own ops.
    fn retain_all(&mut self) {
        for ix in 1..self.frame_len().min(self.st.len()) {
            let x = self.st[ix];
            let managed = matches!(x.ty, Ty::Val(_) | Ty::Obj(..) | Ty::ObjHint(_) | Ty::Native | Ty::Ta(_));
            if !managed {
                continue;
            }
            self.f.add_inst(self.cur, Opcode::FrameStore(u32::try_from(ix).unwrap()), vec![x.v], &[], vec![]);
        }
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

    /// `x` converted to type `to`, which it fits.
    fn convert(&mut self, x: Slot, to: Ty) -> mir::Value {
        match (x.ty, to) {
            (a, b) if a == b => x.v,
            (Ty::I32, Ty::F64) => self.inst(Opcode::I32ToF64, vec![x.v], Some(MType::F64_TOP)),
            (Ty::Obj(..), Ty::Obj(..) | Ty::ObjHint(_)) | (Ty::ObjHint(_), Ty::ObjHint(_)) => {
                self.weaken(x.v, to.mir())
            }
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
        // Baseline has no elided arguments object: an exit whose state
        // holds the placeholder makes the real one first (into the frame
        // slots that hold it, and in the operands), at the exit's own cost.
        let mut st = st.to_vec();
        let ph = self.args_placeholder;
        let holds = |i: usize, x: &Slot| Some(x.v) == ph || Some(i) == self.args_local;
        if ph.is_some() && st.iter().enumerate().any(|(i, x)| holds(i, x)) {
            let ok = self.new_block();
            let obj = self.f.add_param(ok, MType::val(TagSet::OBJECT));
            let err = self.new_block();
            self.retain_locals(&Opcode::ArgsObject);
            let (t, _) = self.f.add_inst(
                self.cur,
                Opcode::ArgsObject,
                vec![],
                &[],
                vec![
                    Edge {
                        block: ok,
                        args: vec![EdgeArg::Out(0)],
                    },
                    Self::goto(err),
                ],
            );
            self.f.witnesses[t] = Some(mir::func::Witness {
                may_kill: mir::types::KillPattern::ALL,
            });
            // Out of memory making it: throw with the state as it is.
            self.at(err);
            let saved = self.args_placeholder.take();
            let ops = self.exit_operands(pc, &st);
            let eop = self.exit_op(pc, true);
            self.term(eop, ops, vec![]);
            self.args_placeholder = saved;
            self.at(ok);
            for (i, x) in st.iter_mut().enumerate() {
                if Some(x.v) == ph || Some(i) == self.args_local {
                    if self.write_through(i) {
                        self.inst(Opcode::FrameStore(u32::try_from(i).unwrap()), vec![obj], None);
                    }
                    *x = Slot {
                        v: obj,
                        ty: Ty::Val(TagSet::OBJECT),
                    };
                }
            }
        }
        let st = &st[..];
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
            // A written-through slot is already in the frame.
            let in_frame = self.write_through(i);
            let is_dead = in_frame
                || x.ty == Ty::Dead
                || live.as_ref().is_some_and(|l| i < l.len() && !l[i]);
            if is_dead {
                let d = *dead.get_or_insert_with(|| self.const_val(ConstVal::Dead));
                ops.push(d);
            } else {
                // As it is: the lowering boxes it at the exit hub.
                ops.push(x.v);
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
        let ops = if throw && self.s.throws_uncaught() {
            // Baseline's landing for it only returns the error: no state.
            self.f
                .frame
                .depths
                .insert(self.pc, u32::try_from(pre.len() - self.frame_len()).unwrap());
            let d = self.const_val(ConstVal::Dead);
            vec![d; pre.len()]
        } else {
            self.exit_operands(self.pc, &pre)
        };
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
    fn guard_result(&mut self, claim: crate::facts::Claim, next: Pc, int_first: bool) {
        let prims = claim.prims();
        if claim.is_none() || claim.is_object() || prims.is_empty() {
            return;
        }
        let (op, ty) = match num_claim_ty(claim, int_first) {
            Some(Ty::I32) => (Opcode::GuardUnbox(UnboxKind::I32), Ty::I32),
            Some(Ty::F64) => (Opcode::GuardUnbox(UnboxKind::F64Num), Ty::F64),
            _ => return,
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

    /// A method's `this`, guarded once to the layouts the analysis
    /// predicts for it (`this_layouts`), exiting here (nothing has
    /// happened yet) on a miss. Its field accesses then fold their own
    /// guards into this one while no fence intervenes (§10.1), and their
    /// IC fallbacks go with them.
    fn guard_this_layout(&mut self) {
        if !THIS_ENTRY_GUARD {
            return;
        }
        let ctx = self.s.ctx;
        let sid = self.s.sid;
        let Some(&(lo, hi)) = ctx.facts.this_layouts.get(&sid) else {
            return;
        };
        // A constructor's `this` is still being built.
        if ctx.stamp_ctors_in.contains_key(&sid)
            || ctx.deleg_restamps_in.contains_key(&sid)
            || ctx.this_layouts_in.get(&sid).is_some_and(|l| l.init_home)
        {
            return;
        }
        let x = self.top();
        let v = self.boxed(x);
        let o = self.guard(Opcode::GuardUnbox(UnboxKind::Obj), vec![v], MType::OBJ_TOP);
        let keys = KeyRange { lo, hi };
        let ty = Ty::Obj(keys, false);
        let g = self.guard(Opcode::GuardLayout { keys, types: false }, vec![o], ty.mir());
        self.st.pop();
        self.push(g, ty);
    }

    /// Boxed `v` as narrow object type `t` (`Native`, `Ta`): unboxed, then
    /// its kind guarded, branching to `fail` on a miss.
    fn guard_narrow(&mut self, v: mir::Value, t: Ty, fail: mir::Block) -> mir::Value {
        let kind = match t {
            Ty::Native => ObjKind::Native,
            Ty::Ta(k) => ObjKind::TypedArray(k),
            t => unreachable!("guard_narrow to {t:?}"),
        };
        let ok = self.new_block();
        let u = self.f.add_param(ok, MType::OBJ_TOP);
        self.term(
            Opcode::GuardUnbox(UnboxKind::Obj),
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
        let ok = self.new_block();
        let o = self.f.add_param(ok, t.mir());
        self.term(
            Opcode::GuardKind(kind),
            vec![u],
            vec![
                Edge {
                    block: ok,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(fail),
            ],
        );
        self.at(ok);
        o
    }

    /// An element access at `pc` the analysis predicts on a typed array of
    /// kind k (`ta_elem_sites`), with an int32 key: the receiver as that
    /// typed array (proven by its slot, or guarded here, exiting on a
    /// miss, every slot holding it refined), the raw index and the kind.
    /// Not a Uint32Array (its elements are not int32s).
    fn ta_elem(&mut self, pc: Pc, recv: Slot, key: Slot) -> Option<(mir::Value, mir::Value, crate::opsem::TaKind)> {
        let k = match recv.ty {
            Ty::Ta(k) => k,
            _ => *self.s.ctx.facts.ta_elem_sites.get(&self.site(pc))?,
        };
        if !TA_ELEMS || k == crate::opsem::TaKind::Uint32 || key.ty.num() != Some(Num::I32) {
            return None;
        }
        let o = match recv.ty {
            Ty::Ta(_) => recv.v,
            Ty::Obj(..) | Ty::ObjHint(_) | Ty::Native => {
                self.guard(Opcode::GuardKind(ObjKind::TypedArray(k)), vec![recv.v], Ty::Ta(k).mir())
            }
            Ty::Val(t) if TagSet::OBJECT.subset_of(t) => {
                let u = self.guard(Opcode::GuardUnbox(UnboxKind::Obj), vec![recv.v], MType::OBJ_TOP);
                let o = self.guard(Opcode::GuardKind(ObjKind::TypedArray(k)), vec![u], Ty::Ta(k).mir());
                for x in self.st.iter_mut() {
                    if x.v == recv.v {
                        *x = Slot { v: o, ty: Ty::Ta(k) };
                    }
                }
                o
            }
            _ => return None,
        };
        let i = self.as_i32(key);
        Some((o, i, k))
    }

    /// An element access at `pc` the analysis predicts on an array with an
    /// int32 key: the receiver as a native object (proven by its slot, or
    /// guarded here, exiting on a miss, and every slot holding it then
    /// refined) and the raw index. `None` for anything else.
    fn native_elem(&mut self, pc: Pc, recv: Slot, key: Slot) -> Option<(mir::Value, mir::Value)> {
        // The analysis saw the site read numbers or objects (not a
        // string's characters), or write, or knows the array's class.
        let site = self.site(pc);
        let facts = &self.s.ctx.facts;
        let predicted = self.s.ctx.array_elem_in.contains_key(&site)
            || facts.elem_write_sites.contains_key(&site)
            || facts.elem_sites.get(&site).is_some_and(|c| {
                c.is_object() || (!c.prims().is_empty() && c.prims().subset_of(crate::opsem::NUM))
            });
        if !NATIVE_ELEMS
            || (recv.ty != Ty::Native && !predicted)
            || key.ty.num() != Some(Num::I32)
            || !TagSet::OBJECT.subset_of(recv.ty.tags())
        {
            return None;
        }
        let i = self.as_i32(key);
        let o = match recv.ty {
            Ty::Native => recv.v,
            Ty::Obj(..) | Ty::ObjHint(_) => self.guard(
                Opcode::GuardKind(ObjKind::Native),
                vec![recv.v],
                Ty::Native.mir(),
            ),
            Ty::Val(_) => {
                let u = self.guard(Opcode::GuardUnbox(UnboxKind::Obj), vec![recv.v], MType::OBJ_TOP);
                let o = self.guard(Opcode::GuardKind(ObjKind::Native), vec![u], Ty::Native.mir());
                for x in self.st.iter_mut() {
                    if x.v == recv.v {
                        *x = Slot { v: o, ty: Ty::Native };
                    }
                }
                o
            }
            _ => return None,
        };
        Some((o, i))
    }

    /// Receiver `recv` of a typed site, when its slot type proves the
    /// site's layouts: the object (for an `ObjHint`, guarded again,
    /// exiting here on a miss, and every slot holding it refined), and
    /// the site as it applies to it: with TYPES only if the slot has the
    /// bit proven (a site that would guard for the bit reads under
    /// identity alone, and its claim is guarded at the def).
    fn proven_recv(&mut self, recv: Slot, site: &TypedSite) -> Option<(mir::Value, TypedSite)> {
        let (keys, types) = match recv.ty {
            Ty::Obj(keys, types) => (keys, Some(types)),
            Ty::ObjHint(keys) => (keys, None),
            _ => return None,
        };
        let want = KeyRange {
            lo: crate::ids::LayoutKey::new(site.lo),
            hi: crate::ids::LayoutKey::new(site.hi),
        };
        if !want.contains(&keys) {
            return None;
        }
        let site = TypedSite {
            types: site.types && types == Some(true),
            ..*site
        };
        let o = match types {
            Some(_) => recv.v,
            None => {
                let ty = Ty::Obj(keys, false);
                let g = self.guard(Opcode::GuardLayout { keys, types: false }, vec![recv.v], ty.mir());
                for x in self.st.iter_mut() {
                    if x.v == recv.v {
                        *x = Slot { v: g, ty };
                    }
                }
                g
            }
        };
        Some((o, site))
    }

    /// A fused global's read (§3): while its fuse is armed the read is the
    /// literal, else exit here. False (nothing emitted) for a literal that
    /// is not a primitive constant.
    fn fused_gname(&mut self, name: mir::entity::AtomId, fg: crate::wasm::translate::FusedGname) -> bool {
        use crate::wasm::translate::{TAG_BOOLEAN, TAG_CLEAR, TAG_INT32, TAG_NULL, TAG_UNDEFINED};
        let (tag, payload) = (fg.boxed >> 32, fg.boxed as u32);
        if !(tag == TAG_INT32
            || tag < u64::from(TAG_CLEAR)
            || tag == TAG_BOOLEAN
            || tag == TAG_NULL
            || tag == TAG_UNDEFINED)
        {
            return false;
        }
        let found = self.mm.fuses.iter().find(|(_, d)| d.addr == fg.fuse_addr).map(|(f, _)| f);
        let fid = match found {
            Some(f) => f,
            None => self.mm.fuses.push(mir::module::FuseDef {
                name: self.mm.atoms[name].to_string(),
                addr: fg.fuse_addr,
            }),
        };
        self.guard(Opcode::CheckFuse(fid), vec![], MType::Fact(mir::types::FactKind::Fuse(fid)));
        let (v, ty) = if tag == TAG_INT32 {
            (self.const_i32(payload as i32), Ty::I32)
        } else if tag < u64::from(TAG_CLEAR) {
            (self.const_f64(f64::from_bits(fg.boxed)), Ty::F64)
        } else if tag == TAG_BOOLEAN {
            (self.inst(Opcode::ConstBool(payload != 0), vec![], Some(MType::Bool)), Ty::Bool)
        } else if tag == TAG_NULL {
            (self.const_val(ConstVal::Null), Ty::Val(TagSet::prims(PRIM_NULL)))
        } else {
            (self.const_val(ConstVal::Undefined), Ty::Val(TagSet::prims(PRIM_UNDEFINED)))
        };
        self.push(v, ty);
        true
    }

    /// The environment `hops` links up the chain from the activation's
    /// (which is fixed: see `build`).
    fn env_at(&mut self, hops: u16) -> mir::Value {
        let env = MType::Obj(ObjInfo::kind(ObjKind::Env));
        let mut e = self.inst(Opcode::EnvCurrent, vec![], Some(env.clone()));
        for _ in 0..hops {
            e = self.inst(Opcode::EnvParent, vec![e], Some(env.clone()));
        }
        e
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
        // Outside bbv every store goes through the engine, which drops the
        // bit on any non-number store to any field, so it survives only on
        // layouts whose fields are all numbers.
        let types = !ps.claim.is_none()
            && ps.shallow_possible
            && !prims.is_empty()
            && prims.subset_of(crate::opsem::NUM)
            && (ps.layout_id..=ps.hi_layout_id).all(|k| numeric_layout(self.s.ctx, k));
        let site = TypedSite {
            lo: ps.layout_id,
            hi: ps.hi_layout_id,
            types,
            claim: ps.claim,
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

    /// Guard boxed receiver `x` to an object of the site's layouts (§4.3):
    /// an object tag test, then the stamp compare, branching to `fallback`
    /// (no params) when either fails.
    fn guard_layout_or(&mut self, x: mir::Value, site: &TypedSite, fallback: mir::Block) -> mir::Value {
        let ob = self.new_block();
        let o = self.f.add_param(ob, MType::OBJ_TOP);
        self.term(
            Opcode::GuardUnbox(UnboxKind::Obj),
            vec![x],
            vec![
                Edge {
                    block: ob,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(fallback),
            ],
        );
        self.at(ob);
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
        let lb = self.new_block();
        let lo = self.f.add_param(lb, t);
        self.term(
            Opcode::GuardLayout {
                keys,
                types: site.types,
            },
            vec![o],
            vec![
                Edge {
                    block: lb,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(fallback),
            ],
        );
        self.at(lb);
        lo
    }

    /// A generic op with a static kill (`ok`, `err`): the builder attaches
    /// its prediction witness (§4.5), which for a generic op is "may kill
    /// anything".
    fn js_static(&mut self, op: Opcode, args: Vec<mir::Value>, out: MType) -> mir::Value {
        let ok = self.new_block();
        let p = self.f.add_param(ok, out);
        let err = self.exit_block(true);
        let mut succs = vec![
            Edge {
                block: ok,
                args: vec![EdgeArg::Out(0)],
            },
            Self::goto(err),
        ];
        self.retain_locals(&op);
        self.fence_params(&op, &args, &mut succs);
        let (inst, _) = self.f.add_inst(self.cur, op, args, &[], succs);
        self.f.witnesses[inst] = Some(mir::func::Witness {
            may_kill: mir::types::KillPattern::ALL,
        });
        self.live = false;
        self.at(ok);
        p
    }

    /// A generic op with no output: both success edges continue; an
    /// exception goes to the op's throw block.
    /// A typed field access (`load_field`/`store_field`) whose `ok_dirty`
    /// edge (its IC arm reported dirt: a SLOTS miss) exits at `next`, the
    /// successor pc, with `post` on the stack (the op has happened). The
    /// clean path then keeps every fact, so the accesses after it fold
    /// their guards (§4.2). Returns the result, if `out`. Without a stack
    /// depth at `next`, both edges continue, as `js` has them.
    fn js_dirty_exits(
        &mut self,
        op: Opcode,
        args: Vec<mir::Value>,
        out: Option<MType>,
        next: Pc,
        post: Option<Slot>,
    ) -> Option<mir::Value> {
        let ok = self.new_block();
        let p = out.map(|t| self.f.add_param(ok, t));
        let depth = self.st.len() - self.frame_len() + usize::from(post.is_some() || out.is_some());
        let dirty = if DIRTY_EXITS && self.s.depths.at(next) == Some(u32::try_from(depth).unwrap()) {
            let saved = (self.cur, self.live);
            let b = self.new_block();
            let dp = out.map(|_| self.f.add_param(b, MType::VAL_TOP));
            // The dirty edge is a fence: `Obj` slots reach the exit
            // through weaker params (`fence_params`).
            let mut objs: Vec<(mir::Value, mir::Value)> = vec![];
            for x in &self.st {
                if matches!(x.ty, Ty::Obj(..)) && !objs.iter().any(|&(v, _)| v == x.v) {
                    objs.push((x.v, self.f.add_param(b, MType::OBJ_TOP)));
                }
            }
            self.at(b);
            let mut st = self.st.clone();
            for x in st.iter_mut() {
                if let (Ty::Obj(k, _), Some(&(_, p))) = (x.ty, objs.iter().find(|&&(v, _)| v == x.v)) {
                    *x = Slot {
                        v: p,
                        ty: Ty::ObjHint(k),
                    };
                }
            }
            let post = post.map(|x| match (x.ty, objs.iter().find(|&&(v, _)| v == x.v)) {
                (Ty::Obj(k, _), Some(&(_, p))) => Slot {
                    v: p,
                    ty: Ty::ObjHint(k),
                },
                _ => x,
            });
            match (dp, post) {
                (Some(v), _) => st.push(Slot {
                    v,
                    ty: Ty::Val(TagSet::ALL),
                }),
                (None, Some(x)) => st.push(x),
                (None, None) => {}
            }
            let ops = self.exit_operands(next, &st);
            let eop = self.exit_op(next, false);
            self.term(eop, ops, vec![]);
            (self.cur, self.live) = saved;
            let mut args: Vec<EdgeArg> = dp.map(|_| vec![EdgeArg::Out(0)]).unwrap_or_default();
            args.extend(objs.iter().map(|&(v, _)| EdgeArg::Value(v)));
            Edge { block: b, args }
        } else {
            Edge {
                block: ok,
                args: p.map(|_| vec![EdgeArg::Out(0)]).unwrap_or_default(),
            }
        };
        let clean = Edge {
            block: ok,
            args: p.map(|_| vec![EdgeArg::Out(0)]).unwrap_or_default(),
        };
        let err = self.exit_block(true);
        // Not `term`: the dirty edge's params are made above, and the
        // clean edge is no fence.
        self.retain_locals(&op);
        self.f.add_inst(self.cur, op, args, &[], vec![clean, dirty, Self::goto(err)]);
        self.live = false;
        self.at(ok);
        p
    }

    /// `js_void` for an op that leaves `post` on the stack (a store's
    /// value), keeping facts on its clean edge (`js_keep`).
    fn js_void_keep(&mut self, op: Opcode, args: Vec<mir::Value>, post: Slot) {
        if self.js_keep(op, args.clone(), None, Some(post)).is_none() {
            self.js_void(op, args);
        }
    }

    /// A generic op that keeps the frame's proven layouts on its clean
    /// edge (bbv's epoch keep: the lowering takes `ok_clean` when the
    /// stamp epoch did not move across the op's helper, so no class word
    /// was demoted), its dirty edge exiting at the next pc with the op's
    /// result (`out`) or the value it leaves (`post`). Only where there is
    /// something to keep and the stack at the next pc is this op's
    /// result; else `None`, and the caller fences as before.
    fn js_keep(
        &mut self,
        op: Opcode,
        args: Vec<mir::Value>,
        out: Option<MType>,
        post: Option<Slot>,
    ) -> Option<Option<mir::Value>> {
        use mir::ops::KillSite;
        if !KEEP_ON_CLEAN {
            return None;
        }
        let next = self.next_pc?;
        if !self.st.iter().chain(&self.pre).any(|x| matches!(x.ty, Ty::Obj(..))) {
            return None;
        }
        let tys: Vec<MType> = args.iter().map(|&v| self.f.ty(v)).collect();
        let fx = mir::ops::effects(&op, &tys, &self.mm);
        if op.kill_site(&fx) != KillSite::DirtyEdge {
            return None;
        }
        let depth = self.st.len() - self.frame_len() + usize::from(post.is_some() || out.is_some());
        if self.s.depths.at(next) != Some(u32::try_from(depth).ok()?) {
            return None;
        }
        let out_ty = match out {
            None => None,
            Some(MType::Bool) => Some(Ty::Bool),
            Some(MType::Val(v)) => Some(Ty::Val(v.tags)),
            Some(_) => return None,
        };
        let ok = self.new_block();
        let p = out.map(|t| self.f.add_param(ok, t));
        let saved = (self.cur, self.live);
        let b = self.new_block();
        let dp = out.map(|t| self.f.add_param(b, t));
        // The dirty edge is a fence: `Obj` slots reach the exit through
        // weaker params.
        let mut objs: Vec<(mir::Value, mir::Value)> = vec![];
        for x in &self.st {
            if matches!(x.ty, Ty::Obj(..)) && !objs.iter().any(|&(v, _)| v == x.v) {
                objs.push((x.v, self.f.add_param(b, MType::OBJ_TOP)));
            }
        }
        self.at(b);
        let weaker = |x: Slot, objs: &[(mir::Value, mir::Value)]| match (x.ty, objs.iter().find(|&&(v, _)| v == x.v)) {
            (Ty::Obj(k, _), Some(&(_, p))) => Slot {
                v: p,
                ty: Ty::ObjHint(k),
            },
            _ => x,
        };
        let mut st: Vec<Slot> = self.st.iter().map(|&x| weaker(x, &objs)).collect();
        match (dp, post) {
            (Some(v), _) => st.push(Slot {
                v,
                ty: out_ty.unwrap(),
            }),
            (None, Some(x)) => st.push(weaker(x, &objs)),
            (None, None) => {}
        }
        let ops = self.exit_operands(next, &st);
        let eop = self.exit_op(next, false);
        self.term(eop, ops, vec![]);
        (self.cur, self.live) = saved;
        let mut dargs: Vec<EdgeArg> = dp.map(|_| vec![EdgeArg::Out(0)]).unwrap_or_default();
        dargs.extend(objs.iter().map(|&(v, _)| EdgeArg::Value(v)));
        let dirty = Edge { block: b, args: dargs };
        let clean = Edge {
            block: ok,
            args: p.map(|_| vec![EdgeArg::Out(0)]).unwrap_or_default(),
        };
        let err = self.exit_block(true);
        self.retain_locals(&op);
        self.f.add_inst(self.cur, op, args, &[], vec![clean, dirty, Self::goto(err)]);
        self.live = false;
        self.at(ok);
        Some(p)
    }

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

    /// A call whose predicted targets are inlined (§5.5): the callee
    /// guarded to each target's script in turn, each target's MIR spliced
    /// in on its hit; the ordinary call when none matches. Returns the
    /// result, at the continuation.
    fn inline_call(
        &mut self,
        targets: &[(ScriptId, std::rc::Rc<super::inline::Callee>)],
        vals: &[mir::Value],
        fallback: Option<(Opcode, Vec<mir::Value>)>,
    ) -> mir::Value {
        // The spliced callees' fences know nothing of this frame's `Obj`
        // slots: they continue as `ObjHint` through it.
        self.demote_objs();
        let join = self.new_block();
        let result = self.f.add_param(join, MType::VAL_TOP);
        let err = self.exit_block(true);
        let generic = self.new_block();
        let obj_b = self.new_block();
        let obj = self.f.add_param(obj_b, MType::OBJ_TOP);
        self.term(
            Opcode::GuardUnbox(UnboxKind::Obj),
            vec![vals[0]],
            vec![
                Edge {
                    block: obj_b,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(generic),
            ],
        );
        self.at(obj_b);
        for (k, callee) in targets {
            let hit = self.new_block();
            let kt = MType::Obj(ObjInfo::kind(ObjKind::Function(Some(*k))));
            let kobj = self.f.add_param(hit, kt);
            let miss = self.new_block();
            self.term(
                Opcode::GuardScript(*k),
                vec![obj],
                vec![
                    Edge {
                        block: hit,
                        args: vec![EdgeArg::Out(0)],
                    },
                    Self::goto(miss),
                ],
            );
            self.at(hit);
            let nformals = callee.f.frame.formals as usize;
            let mut operands = vec![kobj, vals[1]];
            let undef = self.const_val(ConstVal::Undefined);
            for i in 0..nformals {
                operands.push(vals.get(2 + i).copied().unwrap_or(undef));
            }
            let saved_mm = self.mm.clone();
            let saved_frames = self.f.inline_frames.len();
            self.retain_all();
            match super::inline::splice(&mut self.mm, &mut self.f, callee, 0, hit, &operands, None, join, err) {
                Ok(()) => {
                    self.mm.script_addrs.insert(*k, callee.mm.script_addrs[k]);
                }
                Err(_) => {
                    // Not this one after all: the hit takes the ordinary call.
                    self.mm = saved_mm;
                    self.f.inline_frames.truncate(saved_frames);
                    self.term(Opcode::Jump, vec![], vec![Self::goto(generic)]);
                }
            }
            self.at(miss);
        }
        self.term(Opcode::Jump, vec![], vec![Self::goto(generic)]);
        self.at(generic);
        let e = Edge {
            block: join,
            args: vec![EdgeArg::Out(0)],
        };
        let (op, args) = fallback.unwrap_or((Opcode::Call, vals.to_vec()));
        self.term(op, args, vec![e.clone(), e, Self::goto(err)]);
        self.at(join);
        result
    }

    /// `new F(args…)` of the site's one constructor inlined (§5.5): with
    /// the callee that script's function, `this` is made as a direct
    /// construct makes it (`create_this`), the body is spliced with its
    /// frame's new.target, and the result is the body's value if an
    /// object, else `this`; any other callee takes the generic construct.
    /// Operands `callee, is_constructing, args…, new.target`.
    fn inline_construct(
        &mut self,
        k: ScriptId,
        callee: &std::rc::Rc<super::inline::Callee>,
        vals: &[mir::Value],
        nslots: u32,
        word: u32,
    ) -> mir::Value {
        self.demote_objs();
        let nt = vals[vals.len() - 1];
        let join = self.new_block();
        let result = self.f.add_param(join, MType::val(TagSet::OBJECT));
        let err = self.exit_block(true);
        let generic = self.new_block();
        let obj_b = self.new_block();
        let obj = self.f.add_param(obj_b, MType::OBJ_TOP);
        self.term(
            Opcode::GuardUnbox(UnboxKind::Obj),
            vec![vals[0]],
            vec![
                Edge {
                    block: obj_b,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(generic),
            ],
        );
        self.at(obj_b);
        let hit = self.new_block();
        let kt = MType::Obj(ObjInfo::kind(ObjKind::Function(Some(k))));
        let kobj = self.f.add_param(hit, kt);
        self.term(
            Opcode::GuardScript(k),
            vec![obj],
            vec![
                Edge {
                    block: hit,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(generic),
            ],
        );
        self.at(hit);
        // Not a constructor (an arrow function, a method): the generic
        // construct throws.
        let is_ctor = self.inst(Opcode::FnIsCtor, vec![kobj], Some(MType::Bool));
        let ctor = self.new_block();
        self.term(Opcode::Br, vec![is_ctor], vec![Self::goto(ctor), Self::goto(generic)]);
        self.at(ctor);
        let this = self.js_static(Opcode::CreateThis(nslots, word), vec![vals[0], nt], MType::val(TagSet::OBJECT));
        let nformals = callee.f.frame.formals as usize;
        let nargs = vals.len() - 3;
        let mut operands = vec![kobj, this];
        let undef = self.const_val(ConstVal::Undefined);
        for i in 0..nformals {
            operands.push(if i < nargs { vals[2 + i] } else { undef });
        }
        // The body's value, then the construct's result rule.
        let ret = self.new_block();
        let r = self.f.add_param(ret, MType::VAL_TOP);
        let saved_mm = self.mm.clone();
        let saved_frames = self.f.inline_frames.len();
        let here = self.cur;
        self.retain_all();
        match super::inline::splice(&mut self.mm, &mut self.f, callee, 0, here, &operands, Some(nt), ret, err) {
            Ok(()) => {
                self.mm.script_addrs.insert(k, callee.mm.script_addrs[&k]);
                self.live = false;
                self.at(ret);
                let t = self.new_block();
                self.term(
                    Opcode::GuardTags(TagSet::OBJECT),
                    vec![r],
                    vec![
                        Edge {
                            block: join,
                            args: vec![EdgeArg::Out(0)],
                        },
                        Self::goto(t),
                    ],
                );
                self.at(t);
                self.term(
                    Opcode::Jump,
                    vec![],
                    vec![Edge {
                        block: join,
                        args: vec![EdgeArg::Value(this)],
                    }],
                );
            }
            Err(_) => {
                self.mm = saved_mm;
                self.f.inline_frames.truncate(saved_frames);
                self.term(Opcode::Jump, vec![], vec![Self::goto(generic)]);
            }
        }
        self.at(generic);
        let e = Edge {
            block: join,
            args: vec![EdgeArg::Out(0)],
        };
        self.term(Opcode::Construct(nslots, word), vals.to_vec(), vec![e.clone(), e, Self::goto(err)]);
        self.at(join);
        result
    }

    /// `target.apply(this, arguments)` at a proven forward site (bbv's
    /// `compute_apply_fwd_pcs`: the arguments object feeds only such calls,
    /// so it was never made), operands `apply, target, this, placeholder`.
    /// With the `.apply` the pristine builtin, the site's known targets
    /// are inlined, their formals read from this frame's actuals; any other
    /// target, or another `.apply`, forwards through the runtime.
    fn apply_forward(&mut self, vals: &[mir::Value]) -> mir::Value {
        let site = self.site(self.pc);
        let facts = &self.s.ctx.facts;
        let sids: Vec<ScriptId> = match facts.apply_targets.get(&site) {
            Some(&k) => vec![k],
            None => facts.apply_target_sets.get(&site).cloned().unwrap_or_default(),
        };
        let targets: Vec<(ScriptId, std::rc::Rc<super::inline::Callee>)> = sids
            .iter()
            .take(MAX_INLINE_TARGETS + 1)
            .filter_map(|&k| Some((k, self.s.callee(k)?)))
            .collect();
        let helper = (Opcode::ApplyFwd, vec![vals[0], vals[1], vals[2]]);
        if targets.is_empty() || targets.len() > MAX_INLINE_TARGETS {
            return self.js(helper.0, helper.1, MType::VAL_TOP);
        }
        // Arms with fences meet at `join`: `Obj` slots go in as `ObjHint`.
        self.demote_objs();
        let join = self.new_block();
        let result = self.f.add_param(join, MType::VAL_TOP);
        let (fast, slow) = (self.new_block(), self.new_block());
        let is_apply = self.inst(
            Opcode::JsIsBuiltin(crate::wasm::translate::BC_FUN_APPLY),
            vec![vals[0]],
            Some(MType::Bool),
        );
        self.term(Opcode::Br, vec![is_apply], vec![Self::goto(fast), Self::goto(slow)]);
        self.at(fast);
        let n = targets.iter().map(|(_, c)| c.f.frame.formals).max().unwrap_or(0);
        let mut call = vec![vals[1], vals[2]];
        for k in 0..n {
            call.push(self.inst(Opcode::ActualArgOr(k), vec![], Some(MType::VAL_TOP)));
        }
        let r = self.inline_call(&targets, &call, Some(helper.clone()));
        self.term(
            Opcode::Jump,
            vec![],
            vec![Edge {
                block: join,
                args: vec![EdgeArg::Value(r)],
            }],
        );
        self.at(slow);
        let r = self.js(helper.0, helper.1, MType::VAL_TOP);
        self.term(
            Opcode::Jump,
            vec![],
            vec![Edge {
                block: join,
                args: vec![EdgeArg::Value(r)],
            }],
        );
        self.at(join);
        result
    }

    /// A generic op: both success edges continue with its output (of type
    /// `out`); an exception goes to the op's throw block.
    fn js(&mut self, op: Opcode, args: Vec<mir::Value>, out: MType) -> mir::Value {
        if let Some(r) = self.js_keep(op, args.clone(), Some(out), None) {
            return r.unwrap();
        }
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
        if HOIST_NATIVE && self.s.loops.contains_key(&to) {
            for (i, (&a, &b)) in tys.iter().zip(&want).enumerate() {
                if matches!(a, Ty::Native | Ty::Ta(_)) && matches!(b, Ty::Val(t) if TagSet::OBJECT.subset_of(t)) {
                    self.hoist_req.insert((to, i), a);
                }
            }
        }
        let block = self.block_for(to, from)?;
        let st = self.st.clone();
        let args = st
            .iter()
            .zip(&want)
            .enumerate()
            .filter(|(_, (_, &t))| t != Ty::Dead)
            .map(|(_, (&x, &t))| EdgeArg::Value(self.convert(x, t)))
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
            Ty::Obj(..) | Ty::ObjHint(_) | Ty::Native | Ty::Ta(_) => {
                self.inst(Opcode::ConstBool(true), vec![], Some(MType::Bool))
            }
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
    /// `x == null`: null or undefined, or an object that emulates
    /// `undefined`.
    fn loose_nullish(&mut self, x: Slot) -> mir::Value {
        let tags = x.ty.tags();
        let nullish = TagSet::prims(PRIM_NULL | PRIM_UNDEFINED);
        let v = self.boxed(x);
        if tags.intersect(TagSet::OBJECT).is_empty() {
            return self.tag_test(v, nullish);
        }
        let (o, prim, j) = (self.new_block(), self.new_block(), self.new_block());
        let r = self.f.add_param(j, MType::Bool);
        let ob = self.f.add_param(o, MType::OBJ_TOP);
        self.term(
            Opcode::GuardUnbox(UnboxKind::Obj),
            vec![v],
            vec![
                Edge {
                    block: o,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(prim),
            ],
        );
        self.at(o);
        let e = self.inst(Opcode::ObjEmulatesUndef, vec![ob], Some(MType::Bool));
        self.term(
            Opcode::Jump,
            vec![],
            vec![Edge {
                block: j,
                args: vec![EdgeArg::Value(e)],
            }],
        );
        self.at(prim);
        let t = self.tag_test(v, nullish);
        self.term(
            Opcode::Jump,
            vec![],
            vec![Edge {
                block: j,
                args: vec![EdgeArg::Value(t)],
            }],
        );
        self.at(j);
        r
    }

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

    /// Whether frame slot `ix` is written through: only the formals of a
    /// mapped `arguments`, which aliases them. Its frame copy then always
    /// holds its value, so exits leave it (§5.1). Everything else stays in
    /// its own representation, and exits write it.
    fn write_through(&self, ix: usize) -> bool {
        self.mapped() && ix >= 1 && ix <= self.s.nargs as usize
    }

    /// Assign frame slot `ix`, writing it through to the frame.
    fn set_frame_slot(&mut self, ix: usize, x: Slot) {
        if self.args_placeholder == Some(x.v) {
            self.args_local = Some(ix);
        }
        if x.ty != Ty::Dead && self.write_through(ix) {
            self.inst(Opcode::FrameStore(u32::try_from(ix).unwrap()), vec![x.v], None);
        }
        self.st[ix] = x;
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
                self.renames.clear();
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
            // Inlined callees make the loops around it bigger than their
            // bytecode says, and the duplication with them.
            Some(_) if !self.f.inline_frames.is_empty() => false,
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
                Ty::ObjHint(_) => Some(Opcode::GuardUnbox(UnboxKind::Obj)),
                Ty::Native | Ty::Ta(_) => {
                    let o = self.guard_narrow(v, t, fail);
                    args.push(EdgeArg::Value(o));
                    continue;
                }
                Ty::Obj(keys, types) => {
                    // Unbox, then the layout.
                    let ok = self.new_block();
                    let o = self.f.add_param(ok, MType::OBJ_TOP);
                    self.term(
                        Opcode::GuardUnbox(UnboxKind::Obj),
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
                    let ok = self.new_block();
                    let out = self.f.add_param(ok, t.mir());
                    self.term(
                        Opcode::GuardLayout { keys, types },
                        vec![o],
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
                    continue;
                }
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
        // Slots guarded on the way into the loop (§10.2): native objects in
        // the loop, however they came in.
        for (i, t) in tys.iter_mut().enumerate() {
            if let Some(&n) = self.hoist.get(&(pc, i)) {
                if matches!(*t, Ty::Val(u) if TagSet::OBJECT.subset_of(u)) {
                    *t = n;
                }
            }
        }
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
            // The edge's frame, for a hoisted guard's exit (at `pc`,
            // before the loop runs).
            let frame: Vec<Slot> = {
                let mut ps = self.f.blocks[t].params.clone().into_iter();
                ttys.iter()
                    .map(|&ty| match ty {
                        Ty::Dead => Slot::dead(),
                        ty => Slot {
                            v: ps.next().unwrap(),
                            ty,
                        },
                    })
                    .collect()
            };
            let mut exit_b = None;
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
                if matches!((from_ty, to_ty), (Ty::Val(_), Ty::Native | Ty::Ta(_))) {
                    let fail = *exit_b.get_or_insert_with(|| {
                        let here = self.cur;
                        let b = self.new_block();
                        self.at(b);
                        let ops = self.exit_operands(pc, &frame);
                        let eop = self.exit_op(pc, false);
                        self.term(eop, ops, vec![]);
                        self.at(here);
                        b
                    });
                    let o = self.guard_narrow(v, to_ty, fail);
                    args.push(EdgeArg::Value(o));
                    continue;
                }
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
        if self.mapped() {
            // First, before anything can exit: baseline, resumed, reads
            // the formals through it.
            self.js_static(Opcode::ArgsObject, vec![], MType::val(TagSet::OBJECT));
        }
        for i in 0..self.s.nargs {
            if self.mapped() {
                break;
            }
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
        self.next_pc = Some(pc + op.len());
        let mut p = self.s.imms(pc);
        let int_ty = Ty::I32;
        match op {
            // (`DebugLeaveLexicalEnv` only matters with lexical
            // environments, which MIR declines.)
            Nop | Lineno | JumpTarget | LoopHead | NopDestructuring | NopIsAssignOp
            | DebugLeaveLexicalEnv => {}
            // A try block's code is ordinary code: a throw in it exits
            // (`exit.throw`) and baseline takes the pc's handler. The catch
            // code, entered only by a throw, is never reached here.
            Try | TryDestructuring => {}

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
                let x = self.top();
                self.set_frame_slot(ix, x);
            }
            // With an unmapped `arguments` (or none to map), a formal's
            // frame slot is the formal.
            // A mapped `arguments` object aliases the formals: they are
            // its (baseline's reads and writes too).
            GetArg if self.mapped() => {
                let n = u32::from(p.next_uint16().unwrap());
                let v = self.inst(Opcode::ArgsMapped(n), vec![], Some(MType::VAL_TOP));
                self.push(v, Ty::Val(TagSet::ALL));
            }
            GetArg | GetFrameArg => {
                let n = u32::from(p.next_uint16().unwrap());
                let x = self.st[self.arg_ix(n)];
                self.st.push(x);
            }
            ToString if RT_OPS => {
                // A string is its own ToString.
                let v = self.top();
                if !v.ty.tags().is_nonempty_subset_of(TagSet::STRING) {
                    let v = self.pop();
                    let x = self.boxed(v);
                    let r = self.js(Opcode::JsRt(RtOp::ToString), vec![x], MType::val(TagSet::STRING));
                    self.push(r, Ty::Val(TagSet::STRING));
                }
            }
            BuiltinObject if RT_OPS => {
                let kind = u32::from(p.next_uint8().unwrap());
                let r = self.js(Opcode::JsRt(RtOp::BuiltinObject(kind)), vec![], MType::val(TagSet::OBJECT));
                self.push(r, Ty::Val(TagSet::OBJECT));
            }
            Symbol if RT_OPS => {
                let code = u32::from(p.next_uint8().unwrap());
                let sym = TagSet::prims(crate::opsem::PRIM_SYMBOL);
                let r = self.js(Opcode::JsRt(RtOp::Symbol(code)), vec![], MType::val(sym));
                self.push(r, Ty::Val(sym));
            }
            GetIntrinsic if RT_OPS => {
                // A realm constant, from its cell once armed (bbv's
                // `emit_get_intrinsic`).
                let a = self.atom(p.next_uint32().unwrap())?;
                let r = self.js(Opcode::JsRt(RtOp::Intrinsic(a)), vec![], MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
            }
            RegExp if RT_OPS => {
                let idx = p.next_uint32().unwrap();
                let r = self.js(Opcode::JsRt(RtOp::RegExp(idx)), vec![], MType::val(TagSet::OBJECT));
                self.push(r, Ty::Val(TagSet::OBJECT));
            }
            InitPropGetter | InitHiddenPropGetter | InitPropSetter | InitHiddenPropSetter if RT_OPS => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let kind = u32::from(matches!(op, InitPropSetter | InitHiddenPropSetter))
                    | (u32::from(matches!(op, InitHiddenPropGetter | InitHiddenPropSetter)) << 1);
                let f = self.pop();
                let o = self.top();
                let (x, y) = (self.boxed(o), self.boxed(f));
                self.js_void(Opcode::JsRt(RtOp::InitPropGetSet(a, kind)), vec![x, y]);
            }
            SetArg if self.mapped() => {
                let n = u32::from(p.next_uint16().unwrap());
                let x = self.top();
                let v = self.boxed(x);
                self.inst(Opcode::ArgsMappedSet(n), vec![v], None);
            }
            SetArg => {
                let n = u32::from(p.next_uint16().unwrap());
                let ix = self.arg_ix(n);
                let x = self.top();
                self.set_frame_slot(ix, x);
            }
            GetRval => {
                let x = self.st[self.rval_ix()];
                self.st.push(x);
            }
            SetRval => {
                let x = self.pop();
                let ix = self.rval_ix();
                self.set_frame_slot(ix, x);
            }
            GetAliasedVar | GetAliasedDebugVar => {
                let hops = p.next_uint16().unwrap();
                let slot = p.next_uint24().unwrap();
                let e = self.env_at(hops);
                let v = self.inst(
                    Opcode::EnvLoad(crate::ids::EnvSlot::new(slot)),
                    vec![e],
                    Some(MType::VAL_TOP),
                );
                self.push(v, Ty::Val(TagSet::ALL));
                let claim = self.s.ctx.facts.aliased_sites.get(&self.site(pc)).copied();
                self.guard_result(claim.unwrap_or_default(), pc + op.len(), true);
            }
            SetAliasedVar | InitAliasedLexical => {
                let hops = p.next_uint16().unwrap();
                let slot = p.next_uint24().unwrap();
                let x = self.top();
                let v = self.boxed(x);
                let e = self.env_at(hops);
                self.inst(Opcode::EnvStore(crate::ids::EnvSlot::new(slot)), vec![e, v], None);
            }
            Lambda => {
                let index = p.next_uint32().unwrap();
                let e = self.env_at(0);
                let r = self.js_static(Opcode::JsLambda(index), vec![e], MType::val(TagSet::OBJECT));
                self.push(r, Ty::Val(TagSet::OBJECT));
            }
            CheckLexical | CheckAliasedLexical => {
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
                        // Neither operand a BigInt or an object (whose
                        // valueOf might give one): a Number, or a TypeError.
                        // For `+`, neither a string or an object either (no
                        // concatenation) for a numeric result.
                        let free = |s: Slot, t: TagSet| s.ty.tags().intersect(t).is_empty();
                        let big = TagSet::prims(PRIM_BIGINT).union(TagSet::OBJECT);
                        let no_big = free(a, big) || free(b, big);
                        let strish = TagSet::STRING.union(TagSet::OBJECT);
                        let numeric = TagSet::prims(crate::opsem::NUM | PRIM_BIGINT);
                        let arith = if no_big { TagSet::NUMBER } else { numeric };
                        let (jop, tags) = match op {
                            Add if free(a, strish) && free(b, strish) => (Opcode::JsAdd, arith),
                            Add => (Opcode::JsAdd, numeric.union(TagSet::STRING)),
                            Sub => (Opcode::JsBinop(JsBinop::Sub), arith),
                            _ => (Opcode::JsBinop(JsBinop::Mul), arith),
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
                // Against a null or undefined constant: tag tests, which
                // run no user code (no fence), as bbv's.
                let nullish = |t: Ty| {
                    let tags = t.tags();
                    !tags.is_empty() && tags.subset_of(TagSet::prims(PRIM_NULL | PRIM_UNDEFINED))
                };
                let equality = matches!(op, Eq | Ne | StrictEq | StrictNe);
                let konst = if equality && nullish(b.ty) {
                    Some((a, b))
                } else if equality && nullish(a.ty) {
                    Some((b, a))
                } else {
                    None
                };
                if let Some((x, k)) = konst {
                    let r = if matches!(op, StrictEq | StrictNe) {
                        let v = self.boxed(x);
                        self.tag_test(v, k.ty.tags())
                    } else {
                        self.loose_nullish(x)
                    };
                    let r = if matches!(op, Ne | StrictNe) { self.not(r) } else { r };
                    self.push(r, Ty::Bool);
                    return Ok(());
                }
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
                self.ctor_stamp();
                self.term(Opcode::Return, vec![v], vec![]);
            }
            RetRval => {
                let x = self.st[self.rval_ix()];
                let v = self.boxed(x);
                self.ctor_stamp();
                self.term(Opcode::Return, vec![v], vec![]);
            }

            FunctionThis => {
                let x = self.st[0];
                if self.s.script.strict || x.ty.tags().is_nonempty_subset_of(TagSet::OBJECT) {
                    self.st.push(x);
                } else {
                    // Sloppy: an object `this` is itself; anything else is
                    // boxed (null and undefined become the global `this`).
                    self.demote_objs();
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
                self.guard_this_layout();
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
                self.js_void_keep(Opcode::JsSetName(a, op == StrictSetGName), vec![e, y], v);
                self.repush(v);
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
                    Ty::Bool | Ty::Obj(..) | Ty::ObjHint(_) | Ty::Native | Ty::Ta(_) => {
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
                let index = p.next_uint32().unwrap();
                let a = self.atom(index)?;
                if let Some(&fg) = self.s.fused.get(&index) {
                    if self.fused_gname(a, fg) {
                        return Ok(());
                    }
                }
                let r = self.js_static(Opcode::JsGetName(a), vec![], MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
                if let Some(&claim) = self.s.gname_types.get(&index) {
                    self.guard_result(claim, pc + op.len(), true);
                }
            }
            GetProp => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let recv = self.pop();
                let site = self.typed_site(pc, a);
                if let Some((o, site)) = site.and_then(|site| self.proven_recv(recv, &site)) {
                    let r = self
                        .js_dirty_exits(Opcode::LoadField(a), vec![o], Some(site.claim_ty()), pc + op.len(), None)
                        .unwrap();
                    let r = self.weaken(r, MType::VAL_TOP);
                    self.push(r, Ty::Val(TagSet::ALL));
                    self.guard_result(site.claim, pc + op.len(), false);
                } else if let Some(site) = site {
                    // The predicted layout: guard the receiver's class
                    // locally, then load the field (§4.3). A receiver of
                    // another layout reads through the IC instead of
                    // exiting: a prediction that is wrong for some receivers
                    // must not send the rest of the activation to baseline
                    // every time. The claim is guarded after the join. The
                    // IC arm is a fence: `Obj` slots meet as `ObjHint`.
                    self.demote_objs();
                    let x = self.boxed(recv);
                    let join = self.new_block();
                    let jr = self.f.add_param(join, MType::VAL_TOP);
                    let generic = self.new_block();
                    let o = self.guard_layout_or(x, &site, generic);
                    let r = self
                        .js_dirty_exits(Opcode::LoadField(a), vec![o], Some(site.claim_ty()), pc + op.len(), None)
                        .unwrap();
                    let r = self.weaken(r, MType::VAL_TOP);
                    self.term(
                        Opcode::Jump,
                        vec![],
                        vec![Edge {
                            block: join,
                            args: vec![EdgeArg::Value(r)],
                        }],
                    );
                    self.at(generic);
                    let r = self.js(Opcode::JsGetProp(a), vec![x], MType::VAL_TOP);
                    self.term(
                        Opcode::Jump,
                        vec![],
                        vec![Edge {
                            block: join,
                            args: vec![EdgeArg::Value(r)],
                        }],
                    );
                    self.at(join);
                    self.push(jr, Ty::Val(TagSet::ALL));
                    self.guard_result(site.claim, pc + op.len(), false);
                } else {
                    let x = self.boxed(recv);
                    let r = self.js(Opcode::JsGetProp(a), vec![x], MType::VAL_TOP);
                    self.push(r, Ty::Val(TagSet::ALL));
                    let claim = self.s.ctx.facts.field_sites.get(&self.site(pc)).copied();
                    self.guard_result(claim.unwrap_or_default(), pc + op.len(), false);
                }
            }
            SetProp | StrictSetProp => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let v = self.pop();
                let recv = self.pop();
                let num = v.ty.num().is_some();
                // A field of the predicted layout: a number into a field
                // the stamp's TYPES claims as one keeps the claim (no
                // conformance check, and a number over a number needs no
                // barriers); without a TYPES claim, any value, and the
                // store's own check keeps the object's bits.
                let site = self.typed_site(pc, a).filter(|s| num || !s.types);
                let proven = site.and_then(|site| self.proven_recv(recv, &site));
                // The IC arm of an unproven typed store is a fence the two
                // arms meet after: `Obj` slots (and the value, pushed back
                // after it) go in as `ObjHint`.
                let v = if site.is_some() && proven.is_none() {
                    self.demote_objs();
                    self.demote(v)
                } else {
                    v
                };
                match site {
                    Some(_) if proven.is_some() => {
                        let (o, site) = proven.unwrap();
                        let mut x = self.boxed(v);
                        if site.types {
                            x = self.weaken(x, MType::val(TagSet::NUMBER));
                        }
                        self.js_dirty_exits(Opcode::StoreField(a), vec![o, x], None, pc + op.len(), Some(v));
                    }
                    Some(site) => {
                        // As for a typed read: another layout's receiver
                        // stores through the IC rather than exiting.
                        let r = self.boxed(recv);
                        let join = self.new_block();
                        let generic = self.new_block();
                        let o = self.guard_layout_or(r, &site, generic);
                        let mut x = self.boxed(v);
                        if site.types {
                            x = self.weaken(x, MType::val(TagSet::NUMBER));
                        }
                        self.js_dirty_exits(Opcode::StoreField(a), vec![o, x], None, pc + op.len(), Some(v));
                        self.term(Opcode::Jump, vec![], vec![Self::goto(join)]);
                        self.at(generic);
                        let y = self.boxed(v);
                        self.js_void(Opcode::JsSetProp(a, op == StrictSetProp), vec![r, y]);
                        self.term(Opcode::Jump, vec![], vec![Self::goto(join)]);
                        self.at(join);
                    }
                    None => {
                        let (x, y) = (self.boxed(recv), self.boxed(v));
                        self.js_void_keep(Opcode::JsSetProp(a, op == StrictSetProp), vec![x, y], v);
                    }
                }
                self.repush(v);
            }
            GetElem => {
                let key = self.pop();
                let recv = self.pop();
                let ta = self.ta_elem(pc, recv, key);
                let r = if let Some((o, i, k)) = ta {
                    // The element inline, as a boxed number; out of
                    // bounds, the generic op.
                    self.demote_objs();
                    let (ok, generic, join) = (self.new_block(), self.new_block(), self.new_block());
                    let raw = if k.is_float() { MType::F64_TOP } else { MType::I32_TOP };
                    let p = self.f.add_param(ok, raw);
                    let jr = self.f.add_param(join, MType::VAL_TOP);
                    self.term(
                        Opcode::LoadTa,
                        vec![o, i],
                        vec![
                            Edge {
                                block: ok,
                                args: vec![EdgeArg::Out(0)],
                            },
                            Self::goto(generic),
                        ],
                    );
                    self.at(ok);
                    let ty = if k.is_float() { Ty::F64 } else { Ty::I32 };
                    let b = self.boxed(Slot { v: p, ty });
                    let b = self.weaken(b, MType::VAL_TOP);
                    self.term(
                        Opcode::Jump,
                        vec![],
                        vec![Edge {
                            block: join,
                            args: vec![EdgeArg::Value(b)],
                        }],
                    );
                    self.at(generic);
                    let (x, kb) = (self.boxed(recv), self.boxed(key));
                    let r = self.js(Opcode::JsGetElem, vec![x, kb], MType::VAL_TOP);
                    self.term(
                        Opcode::Jump,
                        vec![],
                        vec![Edge {
                            block: join,
                            args: vec![EdgeArg::Value(r)],
                        }],
                    );
                    self.at(join);
                    Some(jr)
                } else {
                    None
                };
                let r = if let Some(r) = r {
                    r
                } else {
                match self.native_elem(pc, recv, key) {
                    Some((o, i)) => {
                        // A dense element inline; out of bounds or a
                        // hole, the generic op.
                        self.demote_objs();
                        let (ok, generic, join) = (self.new_block(), self.new_block(), self.new_block());
                        let p = self.f.add_param(ok, MType::VAL_TOP);
                        let jr = self.f.add_param(join, MType::VAL_TOP);
                        self.term(
                            Opcode::LoadElem,
                            vec![o, i],
                            vec![
                                Edge {
                                    block: ok,
                                    args: vec![EdgeArg::Out(0)],
                                },
                                Self::goto(generic),
                            ],
                        );
                        self.at(ok);
                        self.term(
                            Opcode::Jump,
                            vec![],
                            vec![Edge {
                                block: join,
                                args: vec![EdgeArg::Value(p)],
                            }],
                        );
                        self.at(generic);
                        let (x, k) = (self.boxed(recv), self.boxed(key));
                        let r = self.js(Opcode::JsGetElem, vec![x, k], MType::VAL_TOP);
                        self.term(
                            Opcode::Jump,
                            vec![],
                            vec![Edge {
                                block: join,
                                args: vec![EdgeArg::Value(r)],
                            }],
                        );
                        self.at(join);
                        jr
                    }
                    None => {
                        let (x, k) = (self.boxed(recv), self.boxed(key));
                        self.js(Opcode::JsGetElem, vec![x, k], MType::VAL_TOP)
                    }
                }
                };
                self.push(r, Ty::Val(TagSet::ALL));
                let claim = self.s.ctx.facts.elem_sites.get(&self.site(pc)).copied();
                self.guard_result(claim.unwrap_or_default(), pc + op.len(), true);
            }
            SetElem | StrictSetElem => {
                let v = self.pop();
                let key = self.pop();
                let recv = self.pop();
                // The value as the kind stores it, raw: an int32 for an
                // integer kind (Uint8Clamped clamps it), a number for a
                // float one. A value of unknown type is unboxed at run
                // time, as bbv's typed-array store arm does; a miss (or a
                // double into an integer kind) takes the generic op.
                let ta = self.ta_elem(pc, recv, key).and_then(|(o, i, k)| match (k.is_float(), v.ty.num()) {
                    (true, Some(_)) => Some((o, i, k, Some(self.as_f64(v)))),
                    (false, Some(Num::I32)) => Some((o, i, k, Some(self.as_i32(v)))),
                    (_, None) if !matches!(v.ty, Ty::Dead) => Some((o, i, k, None)),
                    _ => None,
                });
                if let Some((o, i, k, raw)) = ta {
                    self.demote_objs();
                    let v = self.demote(v);
                    let (ok, generic, join) = (self.new_block(), self.new_block(), self.new_block());
                    let raw = match raw {
                        Some(r) => r,
                        None => {
                            let (kind, ty) = if k.is_float() {
                                (UnboxKind::F64Num, MType::F64_TOP)
                            } else {
                                (UnboxKind::I32, MType::I32_TOP)
                            };
                            let unboxed = self.new_block();
                            let r = self.f.add_param(unboxed, ty);
                            let y = self.boxed(v);
                            self.term(
                                Opcode::GuardUnbox(kind),
                                vec![y],
                                vec![
                                    Edge {
                                        block: unboxed,
                                        args: vec![EdgeArg::Out(0)],
                                    },
                                    Self::goto(generic),
                                ],
                            );
                            self.at(unboxed);
                            r
                        }
                    };
                    self.term(
                        Opcode::StoreTa,
                        vec![o, i, raw],
                        vec![Self::goto(ok), Self::goto(generic)],
                    );
                    self.at(ok);
                    self.term(Opcode::Jump, vec![], vec![Self::goto(join)]);
                    self.at(generic);
                    let (x, kb, y) = (self.boxed(recv), self.boxed(key), self.boxed(v));
                    self.js_void(Opcode::JsSetElem(op == StrictSetElem), vec![x, kb, y]);
                    self.term(Opcode::Jump, vec![], vec![Self::goto(join)]);
                    self.at(join);
                    self.st.push(v);
                } else {
                match self.native_elem(pc, recv, key) {
                    Some((o, i)) => {
                        // A dense overwrite inline; else the generic op.
                        self.demote_objs();
                        let v = self.demote(v);
                        let y = self.boxed(v);
                        let (ok, generic, join) = (self.new_block(), self.new_block(), self.new_block());
                        self.term(
                            Opcode::StoreElem,
                            vec![o, i, y],
                            vec![Self::goto(ok), Self::goto(generic)],
                        );
                        self.at(ok);
                        self.term(Opcode::Jump, vec![], vec![Self::goto(join)]);
                        self.at(generic);
                        let (x, k) = (self.boxed(recv), self.boxed(key));
                        self.js_void(Opcode::JsSetElem(op == StrictSetElem), vec![x, k, y]);
                        self.term(Opcode::Jump, vec![], vec![Self::goto(join)]);
                        self.at(join);
                        self.st.push(v);
                    }
                    None => {
                        let (x, k, y) = (self.boxed(recv), self.boxed(key), self.boxed(v));
                        self.js_void_keep(Opcode::JsSetElem(op == StrictSetElem), vec![x, k, y], v);
                        self.repush(v);
                    }
                }
                }
            }
            // Generic operations through their runtime helpers.
            Instanceof | In | HasOwn if RT_OPS => {
                let b = self.pop();
                let a = self.pop();
                let (x, y) = (self.boxed(a), self.boxed(b));
                let r = match op {
                    Instanceof => RtOp::Instanceof,
                    In => RtOp::In,
                    _ => RtOp::HasOwn,
                };
                let v = self.js(Opcode::JsRt(r), vec![x, y], MType::val(TagSet::BOOLEAN));
                self.push(v, Ty::Val(TagSet::BOOLEAN));
            }
            DelProp | StrictDelProp if RT_OPS => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let o = self.pop();
                let x = self.boxed(o);
                let r = RtOp::DelProp(a, op == StrictDelProp);
                let v = self.js(Opcode::JsRt(r), vec![x], MType::val(TagSet::BOOLEAN));
                self.push(v, Ty::Val(TagSet::BOOLEAN));
            }
            DelElem | StrictDelElem if RT_OPS => {
                let k = self.pop();
                let o = self.pop();
                let (x, y) = (self.boxed(o), self.boxed(k));
                let r = RtOp::DelElem(op == StrictDelElem);
                let v = self.js(Opcode::JsRt(r), vec![x, y], MType::val(TagSet::BOOLEAN));
                self.push(v, Ty::Val(TagSet::BOOLEAN));
            }
            NewInit | NewObject if RT_OPS => {
                let v = self.js(Opcode::JsRt(RtOp::NewObject), vec![], MType::val(TagSet::OBJECT));
                self.push(v, Ty::Val(TagSet::OBJECT));
            }
            NewArray if RT_OPS => {
                let len = p.next_uint32().unwrap();
                let v = self.js(Opcode::JsRt(RtOp::NewArray(len)), vec![], MType::val(TagSet::OBJECT));
                self.push(v, Ty::Val(TagSet::OBJECT));
            }
            InitProp | InitHiddenProp | InitLockedProp if RT_OPS => {
                // [obj, v] -> [obj]
                use crate::wasm::bbv::abi::{INIT_ATTR_ENUMERATE, INIT_ATTR_HIDDEN, INIT_ATTR_LOCKED};
                let a = self.atom(p.next_uint32().unwrap())?;
                let attrs = match op {
                    InitProp => INIT_ATTR_ENUMERATE,
                    InitHiddenProp => INIT_ATTR_HIDDEN,
                    _ => INIT_ATTR_LOCKED,
                };
                let v = self.pop();
                let o = self.top();
                let (x, y) = (self.boxed(o), self.boxed(v));
                self.js_void(Opcode::JsRt(RtOp::InitProp(a, attrs)), vec![x, y]);
            }
            InitElem | InitHiddenElem | InitLockedElem if RT_OPS => {
                // [obj, key, v] -> [obj]
                use crate::wasm::bbv::abi::{INIT_ATTR_ENUMERATE, INIT_ATTR_HIDDEN, INIT_ATTR_LOCKED};
                let attrs = match op {
                    InitElem => INIT_ATTR_ENUMERATE,
                    InitHiddenElem => INIT_ATTR_HIDDEN,
                    _ => INIT_ATTR_LOCKED,
                };
                let v = self.pop();
                let k = self.pop();
                let o = self.top();
                let (x, y, z) = (self.boxed(o), self.boxed(k), self.boxed(v));
                self.js_void(Opcode::JsRt(RtOp::InitElem(attrs)), vec![x, y, z]);
            }
            InitElemArray if RT_OPS => {
                // [obj, v] -> [obj]
                let index = p.next_uint32().unwrap();
                let v = self.pop();
                let o = self.top();
                let k = self.const_val(ConstVal::Int32(index as i32));
                let (x, z) = (self.boxed(o), self.boxed(v));
                let e = crate::wasm::bbv::abi::INIT_ATTR_ENUMERATE;
                self.js_void(Opcode::JsRt(RtOp::InitElem(e)), vec![x, k, z]);
            }
            ToPropertyKey if RT_OPS => {
                // An int32, a string or a symbol is its own key.
                let x = self.top();
                let keyish = TagSet::INT32.union(TagSet::STRING).union(TagSet::prims(crate::opsem::PRIM_SYMBOL));
                if !x.ty.tags().is_nonempty_subset_of(keyish) {
                    let x = self.pop();
                    let v = self.boxed(x);
                    let r = self.js(Opcode::JsRt(RtOp::ToPropertyKey), vec![v], MType::VAL_TOP);
                    self.push(r, Ty::Val(TagSet::ALL));
                }
            }
            Typeof | TypeofExpr if RT_OPS => {
                let a = self.pop();
                let x = self.boxed(a);
                let v = self.inst(Opcode::JsTypeof, vec![x], Some(MType::val(TagSet::STRING)));
                self.push(v, Ty::Val(TagSet::STRING));
            }
            Throw if RT_OPS => {
                let a = self.pop();
                let x = self.boxed(a);
                let err = self.exit_block(true);
                self.retain_locals(&Opcode::JsThrow);
                let (t, _) = self.f.add_inst(self.cur, Opcode::JsThrow, vec![x], &[], vec![Self::goto(err)]);
                self.live = false;
                self.f.witnesses[t] = Some(mir::func::Witness {
                    may_kill: mir::types::KillPattern::ALL,
                });
            }
            // The actuals (the frame's variable region is past them: the
            // lowering's `vp`).
            Arguments => {
                if self.s.apply_fwd.is_some() {
                    // Only forwarded (`apply_forward`): never made, unless an
                    // exit needs it (`exit_operands`). A value of its own,
                    // so no other undefined is mistaken for it.
                    let v = self.const_val(ConstVal::Undefined);
                    self.args_placeholder = Some(v);
                    self.push(v, Ty::Val(TagSet::prims(PRIM_UNDEFINED)));
                } else {
                    let v = self.js_static(Opcode::ArgsObject, vec![], MType::val(TagSet::OBJECT));
                    self.push(v, Ty::Val(TagSet::OBJECT));
                }
            }
            Rest => {
                let nformal = self.s.nargs.saturating_sub(1);
                let v = self.js_static(Opcode::RestArray(nformal), vec![], MType::val(TagSet::OBJECT));
                self.push(v, Ty::Val(TagSet::OBJECT));
            }
            ArgumentsLength => {
                let v = self.inst(Opcode::ArgsLength, vec![], Some(MType::I32_TOP));
                self.push(v, Ty::I32);
            }
            GetActualArg => {
                let i = self.pop();
                if i.ty != Ty::I32 {
                    return Err("GetActualArg of a non-int32 index".into());
                }
                let v = self.inst(Opcode::ActualArg, vec![i.v], Some(MType::VAL_TOP));
                self.push(v, Ty::Val(TagSet::ALL));
            }
            IsConstructing => {
                let v = self.const_val(ConstVal::IsConstructing);
                self.push(v, Ty::Val(TagSet::MAGIC));
            }
            New | NewContent => {
                // [callee, this, args…, new.target] -> [object]
                let argc = usize::from(p.next_uint16().unwrap());
                let n = self.st.len();
                let operands: Vec<Slot> = self.st.drain(n - argc - 3..).collect();
                let vals: Vec<mir::Value> = operands.into_iter().map(|x| self.boxed(x)).collect();
                let site = self.site(pc);
                let mono = match self.s.ctx.facts.scripted_targets(site) {
                    [s] => Some(*s),
                    _ => None,
                };
                let nslots = crate::wasm::bbv::construct_nslots(self.s.ctx, mono, site);
                let word = crate::wasm::bbv::construct_alloc_word(self.s.ctx, mono, site);
                let callee = mono
                    .filter(|&k| self.s.fits_site(k, pc, 1))
                    .and_then(|k| Some((k, self.s.callee(k)?)));
                let r = match callee {
                    Some((k, c)) if INLINE_CONSTRUCT && self.inline_budget(c.f.insts.len()) => {
                        self.inline_construct(k, &c, &vals, nslots, word)
                    }
                    _ => self.js(Opcode::Construct(nslots, word), vals, MType::val(TagSet::OBJECT)),
                };
                self.push(r, Ty::Val(TagSet::OBJECT));
            }
            Call | CallIgnoresRv | CallContent => {
                let argc = usize::from(p.next_uint16().unwrap());
                let n = self.st.len();
                let operands: Vec<Slot> = self.st.drain(n - argc - 2..).collect();
                let vals: Vec<mir::Value> = operands.into_iter().map(|x| self.boxed(x)).collect();
                let sids = self.s.ctx.facts.scripted_targets(self.site(pc));
                let n = sids.len();
                let targets: Vec<(ScriptId, std::rc::Rc<super::inline::Callee>)> = sids
                    .iter()
                    .take(MAX_INLINE_TARGETS + 1)
                    .filter(|&&k| self.s.fits_site(k, pc, n))
                    .filter_map(|&k| Some((k, self.s.callee(k)?)))
                    .collect();
                let r = if argc == 2 && self.s.apply_fwd.as_ref().is_some_and(|f| f.contains(&pc)) {
                    self.apply_forward(&vals)
                } else if targets.is_empty()
                    || targets.len() > MAX_INLINE_TARGETS
                    || !self.inline_budget(targets.iter().map(|(_, c)| c.f.insts.len()).sum())
                {
                    self.js(Opcode::Call, vals, MType::VAL_TOP)
                } else {
                    self.inline_call(&targets, &vals, None)
                };
                self.push(r, Ty::Val(TagSet::ALL));
                let claim = self.s.ctx.facts.call_types.get(&self.site(pc)).copied();
                self.guard_result(claim.unwrap_or_default(), pc + op.len(), false);
            }

            op => return Err(format!("{op:?}")),
        }
        Ok(())
    }

    fn js_binop(&mut self, k: JsBinop, a: Slot, b: Slot) {
        let (x, y) = (self.boxed(a), self.boxed(b));
        // A BigInt result needs both operands BigInt after ToNumeric; an
        // operand that is no BigInt and no object (whose valueOf might
        // give one) makes it a Number, or a TypeError for mixing.
        let big_free = |s: Slot| {
            s.ty
                .tags()
                .intersect(TagSet::prims(PRIM_BIGINT).union(TagSet::OBJECT))
                .is_empty()
        };
        let no_big = big_free(a) || big_free(b);
        let tags = match k {
            JsBinop::Ursh => TagSet::NUMBER,
            JsBinop::BitAnd | JsBinop::BitOr | JsBinop::BitXor | JsBinop::Lsh | JsBinop::Rsh if no_big => {
                TagSet::INT32
            }
            JsBinop::BitAnd | JsBinop::BitOr | JsBinop::BitXor | JsBinop::Lsh | JsBinop::Rsh => {
                TagSet::prims(PRIM_INT32 | PRIM_BIGINT)
            }
            _ if no_big => TagSet::NUMBER,
            _ => TagSet::prims(crate::opsem::NUM | PRIM_BIGINT),
        };
        let r = self.js(Opcode::JsBinop(k), vec![x, y], MType::val(tags));
        if tags == TagSet::INT32 {
            // Always an int32: unboxed, the guard never fails.
            let i = self.guard(Opcode::GuardUnbox(UnboxKind::I32), vec![r], MType::I32_TOP);
            self.push(i, Ty::I32);
        } else {
            self.push(r, Ty::Val(tags));
        }
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
