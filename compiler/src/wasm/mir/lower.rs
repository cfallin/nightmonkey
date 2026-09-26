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

use crate::mir;
use crate::mir::func::{Edge, EdgeArg, RootKind};
use crate::mir::ops::{
    frame_parts, ArithOp, BitOp, Cc, ConstVal, F64Op, JsBinop, JsCc, JsUnop, NumRepr, Opcode,
    UnboxKind,
};
use crate::mir::types::{Machine, TagSet, Type as MType};
use crate::opsem::{
    PRIM_BIGINT, PRIM_BOOLEAN, PRIM_DOUBLE, PRIM_INT32, PRIM_NULL, PRIM_STRING, PRIM_SYMBOL,
    PRIM_UNDEFINED,
};
use crate::wasm::baseline::layout::{
    FrameLayout, ResumeMode, ResumeWord, ARGC_FLAGS, ARGC_RESUME_BIT,
};
use crate::wasm::bbv::abi::{
    BINOP_BITAND, BINOP_BITNOT, BINOP_BITOR, BINOP_BITXOR, BINOP_DEC, BINOP_DIV, BINOP_INC,
    BINOP_LSH, BINOP_MOD, BINOP_MUL, BINOP_RSH, BINOP_SUB, BINOP_URSH, CMP_EQ, CMP_GE, CMP_GT,
    CMP_LE, CMP_LT, CMP_NE, CMP_STRICTEQ, CMP_STRICTNE, FLAGS_ALL,
};
use crate::wasm::translate::{
    Helpers, TAG_BIGINT_HI, TAG_BOOLEAN, TAG_CLEAR, TAG_INT32, TAG_MAGIC, TAG_NULL, TAG_OBJECT,
    TAG_STRING, TAG_SYMBOL, TAG_UNDEFINED,
};

type R<T> = Result<T, String>;

const UNDEF: u64 = TAG_UNDEFINED << 32;

/// `JS::GenericNaN()`'s bits.
const CANONICAL_NAN_BITS: u64 = 0x7FF8_0000_0000_0000;

/// A lowered MIR function.
pub struct Lowered {
    pub body: FunctionBody,
    /// `Call` placeholders for the script's baseline body, one per exit.
    pub baseline_calls: Vec<Value>,
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

/// The waffle type a MIR type lowers to (`None` for a ghost).
fn machine(t: &MType) -> Option<Type> {
    match t.repr().machine() {
        Machine::I32 => Some(Type::I32),
        Machine::I64 => Some(Type::I64),
        Machine::F64 => Some(Type::F64),
        Machine::None => None,
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
    /// Where the rooting slots start, in bytes above `sp`: just past the
    /// padded formals.
    root_base: u32,
    baseline_calls: Vec<Value>,
}

/// Lower `f` (a function of `mm`, whose baseline frame is `layout`) into a
/// new body of `m`.
pub fn lower(
    m: &mut Module,
    h: Helpers,
    _mm: &mir::Module,
    f: &mir::Func,
    layout: FrameLayout,
) -> R<Lowered> {
    if layout.rebase_vp {
        return Err("lowering: a script that reads its actuals".into());
    }
    let body = FunctionBody::new(m, h.night_abi_sig2);
    let entry = body.entry;
    let p = |i: usize| body.blocks[entry].params[i].1;
    let (cx, sp, argc, retval_out, script_param, new_target) = (p(0), p(1), p(2), p(3), p(4), p(5));
    let root_base = FrameLayout::ARGS + 8 * layout.nargs;
    let mut l = Lower {
        h,
        f,
        layout,
        body,
        cur: entry,
        cx,
        sp,
        argc,
        retval_out,
        script_param,
        new_target,
        blocks: BTreeMap::new(),
        live_in: BTreeMap::new(),
        carried: BTreeMap::new(),
        vmap: BTreeMap::new(),
        root_base,
        baseline_calls: vec![],
    };
    l.run()?;
    Ok(Lowered {
        body: l.body,
        baseline_calls: l.baseline_calls,
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

    /// Blocks reachable from the entry root. (Onramp roots are M3.)
    fn reachable(&self) -> BTreeSet<mir::Block> {
        let mut seen = BTreeSet::new();
        let mut work: Vec<mir::Block> = self
            .f
            .roots
            .iter()
            .filter(|r| r.kind == RootKind::Entry)
            .map(|r| r.block)
            .collect();
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
        for &b in &f.layout {
            if !reach.contains(&b) {
                continue;
            }
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

    /// The entry: pad the formals the caller did not pass with undefined
    /// (the frame below the rooting slots must hold valid Values), then
    /// enter the entry root with callee, `this` and the formals.
    fn entry(&mut self) -> R<()> {
        let flags = self.i32c(!ARGC_FLAGS);
        self.argc = self.bin(Operator::I32And, self.argc, flags, Type::I32);
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

    /// Call may-GC helper `f(cx, top, args...)` with every value in `live`
    /// rooted, reloading them afterwards. Returns the helper's i32 status
    /// and the boxed result it wrote at `top`.
    fn gc_call(&mut self, f: Func, args: &[Value], live: &[mir::Value]) -> R<(Value, Value)> {
        for (i, &v) in live.iter().enumerate() {
            let t = self.ty(v);
            let w = self.get(v)?;
            let b = self.boxed(&t, w)?;
            let off = self.root_base + 8 * u32::try_from(i).unwrap();
            self.store_i64(self.sp, off, b);
        }
        let top_off = self.root_base + 8 * u32::try_from(live.len()).unwrap();
        let top = self.add_off(self.sp, top_off);
        let mut full = vec![self.cx, top];
        full.extend_from_slice(args);
        let ok = self.call1(f, &full, Type::I32);
        for (i, &v) in live.iter().enumerate() {
            let t = self.ty(v);
            let off = self.root_base + 8 * u32::try_from(i).unwrap();
            let raw = self.load_i64(self.sp, off);
            let w = self.unboxed_managed(&t, raw);
            self.vmap.insert(v, w);
        }
        let result = self.load_i64(self.sp, top_off);
        Ok((ok, result))
    }

    // --- instructions ------------------------------------------------------------------

    fn def(&mut self, inst: mir::Inst, v: Value) {
        let r = self.f.insts[inst].results[0];
        self.vmap.insert(r, v);
    }

    fn inst(&mut self, inst: mir::Inst) -> R<()> {
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
            Opcode::JsToBool => {
                // A leaf: no GC, no JS.
                let tb = self.h.to_boolean;
                let v = self.call1(tb, &[self.cx, a[0]], Type::I32);
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
                self.exit(ResumeWord { pc, mode }, &a, nargs, nlocals)?;
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
            | Opcode::JsToNumeric => self.js_op(inst, &d.op, &a)?,
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
    fn guard(&mut self, inst: mir::Inst, ok: Value, outs: &[Value]) -> R<()> {
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

    /// Write the baseline frame for `w` from an exit's operands (`this`,
    /// formals, locals, rval, stack; all boxed), then run the baseline body
    /// from there and return its result.
    fn exit(&mut self, w: ResumeWord, ops: &[Value], nargs: u32, nlocals: u32) -> R<()> {
        let fp = frame_parts(ops, nargs, nlocals).ok_or("lowering: malformed exit")?;
        let (sp, vp) = (self.sp, self.sp);
        let l = self.layout;
        self.store_i64(sp, FrameLayout::THIS, *fp.this);
        for (i, &v) in fp.args.iter().enumerate() {
            self.store_i64(sp, l.arg(u32::try_from(i).unwrap()), v);
        }
        for (j, &v) in fp.locals.iter().enumerate() {
            self.store_i64(vp, l.local(u32::try_from(j).unwrap()), v);
        }
        self.store_i64(vp, l.rval(), *fp.rval);
        for (k, &v) in fp.stack.iter().enumerate() {
            self.store_i64(vp, l.operand(u32::try_from(k).unwrap()), v);
        }
        // The fixed slots, as the prologue would have set them. MIR declines
        // scripts with an env chain or an arguments object.
        let undef = self.i64c(UNDEF);
        self.store_i64(vp, l.env(), undef);
        self.store_i64(vp, l.args_obj(), undef);
        self.store_i64(vp, l.new_target(), self.new_target);
        let word = self.i64c((TAG_INT32 << 32) | u64::from(w.encode() as u32));
        self.store_i64(vp, l.resume(), word);
        let bit = self.i32c(ARGC_RESUME_BIT);
        let argc = self.bin(Operator::I32Or, self.argc, bit, Type::I32);
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
        Ok(())
    }
}
