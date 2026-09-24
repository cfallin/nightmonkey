//! The MIR validator.
//!
//! Every invariant an optimization relies on is structural (MIR.md §0),
//! and this is where the structure is checked. There is no flow typing:
//! a value's type is the one it was defined with, and the checks below
//! are what make that type true wherever the value is used. The eight
//! families, in the order they run:
//!
//! 1. **Structure**: one terminator per block, at the end; successors
//!    exist and match the op's shape; edge arity; roots; reducibility.
//! 2. **Dominance**, over every root at once (a virtual super-root).
//! 3. **Edge subtyping**: args and outputs within the param's type.
//! 4. **Operand types**: the op's rule accepts its operands, and declared
//!    result types are supertypes of the rule's.
//! 5. **Fences**: nothing of a killed type is live across a fence, except
//!    through a weaker-typed param on a fence edge.
//! 6. **Predicted or dynamic**: every static kill is covered by the op's
//!    prediction witness; kills on `ok_dirty` edges are exempt.
//! 7. **Raw across GC**: no `Raw` value is live across a may-GC op.
//! 8. **Boundary**: exits and onramp roots carry exactly the frame, all
//!    `Val(⊤)`; every loop has a unique preheader.
//!
//! A structural failure stops the run (later checks assume a well-formed
//! CFG); the other families all run and report every error they find.

use std::collections::{BTreeMap, BTreeSet};

use crate::mir::entity::{Block, EntityMap, Inst, Value};
use crate::mir::func::{EdgeArg, Func, RootKind, ValueDef};
use crate::mir::module::Module;
use crate::mir::ops::{effects, signature, Effects, KillSite, Opcode, Sig, SuccRole};
use crate::mir::print::{kill_str, mnemonic, type_str_in};
use crate::mir::types::{is_subtype, ObjInfo, ObjKind, Type};

/// Which family of check an error comes from.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Check {
    Structure,
    Dominance,
    EdgeType,
    OperandType,
    Fence,
    Prediction,
    RawGc,
    Boundary,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct VerifyError {
    pub check: Check,
    pub block: Option<Block>,
    pub msg: String,
}

impl std::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.block {
            Some(b) => write!(f, "{:?} in {b}: {}", self.check, self.msg),
            None => write!(f, "{:?}: {}", self.check, self.msg),
        }
    }
}

struct Verifier<'a> {
    m: &'a Module,
    f: &'a Func,
    errors: Vec<VerifyError>,
    /// The block each instruction sits in (layout blocks only).
    inst_block: EntityMap<Inst, Option<Block>>,
    preds: BTreeMap<Block, Vec<Block>>,
    /// Reverse postorder from the virtual root; unreachable blocks absent.
    rpo: Vec<Block>,
    rpo_index: BTreeMap<Block, usize>,
    /// Immediate dominators; roots map to `None` (the virtual root).
    idom: BTreeMap<Block, Option<Block>>,
    sigs: EntityMap<Inst, Option<Sig>>,
    live_in: BTreeMap<Block, BTreeSet<Value>>,
}

impl<'a> Verifier<'a> {
    fn err(&mut self, check: Check, block: Option<Block>, msg: String) {
        self.errors.push(VerifyError { check, block, msg });
    }

    fn ty(&self, v: Value) -> Type {
        self.f.values[v].ty
    }

    fn ts(&self, t: &Type) -> String {
        type_str_in(Some(self.m), t)
    }

    fn vt(&self, v: Value) -> String {
        format!("{v} ({})", self.ts(&self.ty(v)))
    }

    // --- 1. structure ---------------------------------------------------

    fn structure(&mut self) {
        let f = self.f;
        let in_layout: BTreeSet<Block> = f.layout.iter().copied().collect();
        if in_layout.len() != f.layout.len() {
            self.err(
                Check::Structure,
                None,
                "a block appears twice in the layout".into(),
            );
        }
        let n_entry = f.roots.iter().filter(|r| r.kind == RootKind::Entry).count();
        if n_entry != 1 {
            self.err(
                Check::Structure,
                None,
                format!("expected one entry root, found {n_entry}"),
            );
        }
        let mut seen_roots = BTreeSet::new();
        for r in &f.roots {
            if !in_layout.contains(&r.block) {
                self.err(
                    Check::Structure,
                    None,
                    format!("root {} is not in the layout", r.block),
                );
            }
            if !seen_roots.insert(r.block) {
                self.err(
                    Check::Structure,
                    None,
                    format!("{} is a root twice", r.block),
                );
            }
        }
        for &b in &f.layout {
            let insts = &f.blocks[b].insts;
            if insts.is_empty() {
                self.err(Check::Structure, Some(b), "block has no terminator".into());
                continue;
            }
            for (i, &inst) in insts.iter().enumerate() {
                if let Some(prev) = self.inst_block[inst] {
                    self.err(
                        Check::Structure,
                        Some(b),
                        format!("{inst} also appears in {prev}"),
                    );
                }
                self.inst_block[inst] = Some(b);
                let d = &f.insts[inst];
                let last = i + 1 == insts.len();
                if d.op.is_terminator() && !last {
                    self.err(
                        Check::Structure,
                        Some(b),
                        format!("terminator {} is not the last instruction", mnemonic(&d.op)),
                    );
                }
                if last && !d.op.is_terminator() {
                    self.err(Check::Structure, Some(b), "block has no terminator".into());
                }
                let roles = d.op.roles();
                if d.succs.len() != roles.len() {
                    self.err(
                        Check::Structure,
                        Some(b),
                        format!(
                            "{} has {} successor(s), expected {}",
                            mnemonic(&d.op),
                            d.succs.len(),
                            roles.len()
                        ),
                    );
                    continue;
                }
                for (role, e) in roles.iter().zip(&d.succs) {
                    if !in_layout.contains(&e.block) {
                        self.err(
                            Check::Structure,
                            Some(b),
                            format!(
                                "{} targets {}, which is not in the function",
                                role.name(),
                                e.block
                            ),
                        );
                        continue;
                    }
                    let np = f.blocks[e.block].params.len();
                    if e.args.len() != np {
                        self.err(
                            Check::Structure,
                            Some(b),
                            format!(
                                "edge {} to {} passes {} arg(s), but it has {np} param(s)",
                                role.name(),
                                e.block,
                                e.args.len()
                            ),
                        );
                    }
                    if !role.carries_outputs()
                        && e.args.iter().any(|a| matches!(a, EdgeArg::Out(_)))
                    {
                        self.err(
                            Check::Structure,
                            Some(b),
                            format!(
                                "the {} edge cannot carry outputs of {}",
                                role.name(),
                                mnemonic(&d.op)
                            ),
                        );
                    }
                }
                for (k, &v) in d.results.iter().enumerate() {
                    if f.values[v].def != ValueDef::Result(inst, k as u32) {
                        self.err(
                            Check::Structure,
                            Some(b),
                            format!("{v}'s definition does not name {inst}"),
                        );
                    }
                }
            }
            for (k, &v) in f.blocks[b].params.iter().enumerate() {
                if f.values[v].def != ValueDef::Param(b, k as u32) {
                    self.err(
                        Check::Structure,
                        Some(b),
                        format!("{v}'s definition does not name {b}"),
                    );
                }
            }
        }
    }

    // --- 2. CFG, dominance, loops ------------------------------------------

    fn cfg(&mut self) {
        let f = self.f;
        for &b in &f.layout {
            self.preds.entry(b).or_default();
        }
        for &b in &f.layout {
            for s in f.succs(b) {
                self.preds.entry(s).or_default().push(b);
            }
        }
        for r in &f.roots {
            if !self.preds[&r.block].is_empty() {
                self.err(
                    Check::Structure,
                    Some(r.block),
                    "a root has predecessors".to_string(),
                );
            }
        }
        // Postorder DFS from the virtual root: roots in order.
        let mut visited = BTreeSet::new();
        let mut post = vec![];
        for r in &f.roots {
            if visited.contains(&r.block) {
                continue;
            }
            visited.insert(r.block);
            let mut stack = vec![(r.block, f.succs(r.block), 0usize)];
            while let Some((b, succs, i)) = stack.last_mut() {
                if *i < succs.len() {
                    let s = succs[*i];
                    *i += 1;
                    if visited.insert(s) {
                        let ss = f.succs(s);
                        stack.push((s, ss, 0));
                    }
                } else {
                    post.push(*b);
                    stack.pop();
                }
            }
        }
        post.reverse();
        self.rpo = post;
        self.rpo_index = self.rpo.iter().enumerate().map(|(i, &b)| (b, i)).collect();
        // Cooper-Harvey-Kennedy over the virtual root.
        let roots: BTreeSet<Block> = f.roots.iter().map(|r| r.block).collect();
        let mut idom: BTreeMap<Block, Option<Option<Block>>> = BTreeMap::new();
        for &r in &roots {
            idom.insert(r, Some(None));
        }
        let rpo_index = &self.rpo_index;
        // Walk up the idom chain; `None` is the virtual root.
        let intersect =
            |idom: &BTreeMap<Block, Option<Option<Block>>>, a: Option<Block>, b: Option<Block>| {
                let (mut a, mut b) = (a, b);
                while a != b {
                    match (a, b) {
                        (None, _) | (_, None) => return None,
                        (Some(x), Some(y)) => {
                            if rpo_index[&x] > rpo_index[&y] {
                                a = idom[&x].unwrap();
                            } else {
                                b = idom[&y].unwrap();
                            }
                        }
                    }
                }
                a
            };
        let mut changed = true;
        while changed {
            changed = false;
            for &b in &self.rpo {
                if roots.contains(&b) {
                    continue;
                }
                let mut new: Option<Option<Block>> = None;
                for &p in &self.preds[&b] {
                    if idom.get(&p).is_some_and(|d| d.is_some()) {
                        new = Some(match new {
                            None => Some(p),
                            Some(cur) => intersect(&idom, cur, Some(p)),
                        });
                    }
                }
                if idom.get(&b) != Some(&new) {
                    idom.insert(b, new);
                    changed = true;
                }
            }
        }
        self.idom = idom
            .into_iter()
            .filter_map(|(b, d)| d.map(|d| (b, d)))
            .collect();
    }

    fn dominates(&self, a: Block, b: Block) -> bool {
        let mut cur = Some(b);
        while let Some(x) = cur {
            if x == a {
                return true;
            }
            cur = self.idom.get(&x).copied().flatten();
        }
        false
    }

    fn reachable(&self, b: Block) -> bool {
        self.rpo_index.contains_key(&b)
    }

    /// Where a value is defined: its block and position (-1 for params).
    fn def_point(&self, v: Value) -> Option<(Block, isize)> {
        match self.f.values.get(v)?.def {
            ValueDef::Param(b, _) => Some((b, -1)),
            ValueDef::Result(inst, _) => {
                let b = self.inst_block[inst]?;
                let pos = self.f.blocks[b].insts.iter().position(|&i| i == inst)?;
                Some((b, pos as isize))
            }
            ValueDef::Unused => None,
        }
    }

    fn dominance(&mut self) {
        let f = self.f;
        for &b in &self.rpo.clone() {
            for (pos, &inst) in f.blocks[b].insts.iter().enumerate() {
                let d = &f.insts[inst];
                let edge_vals = d.succs.iter().flat_map(|e| {
                    e.args.iter().filter_map(|a| match a {
                        EdgeArg::Value(v) => Some(*v),
                        EdgeArg::Out(_) => None,
                    })
                });
                for v in d.args.iter().copied().chain(edge_vals) {
                    match self.def_point(v) {
                        None => self.err(
                            Check::Dominance,
                            Some(b),
                            format!("{v} is used but not defined"),
                        ),
                        Some((db, dpos)) => {
                            let ok = self.reachable(db)
                                && self.dominates(db, b)
                                && (db != b || dpos < pos as isize);
                            if !ok {
                                self.err(
                                    Check::Dominance,
                                    Some(b),
                                    format!("use of {v} in {} is not dominated by its definition in {db}", mnemonic(&d.op)),
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    /// Back edges must go to dominating headers (reducibility), and each
    /// header has exactly one other predecessor, which jumps only to it.
    fn loops(&mut self) {
        let mut headers: BTreeMap<Block, Vec<Block>> = BTreeMap::new();
        for &b in &self.rpo.clone() {
            for s in self.f.succs(b) {
                if self.rpo_index[&s] <= self.rpo_index[&b] {
                    if self.dominates(s, b) {
                        headers.entry(s).or_default().push(b);
                    } else {
                        self.err(
                            Check::Structure,
                            Some(b),
                            format!("edge {b} -> {s} makes the CFG irreducible"),
                        );
                    }
                }
            }
        }
        for (h, latches) in headers {
            let entries: Vec<Block> = self.preds[&h]
                .iter()
                .copied()
                .filter(|p| self.reachable(*p) && !latches.contains(p))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            match entries.as_slice() {
                [p] => {
                    if self.f.succs(*p) != vec![h] {
                        self.err(
                            Check::Boundary,
                            Some(h),
                            format!("loop preheader {p} must jump only to its header {h}"),
                        );
                    }
                }
                _ => {
                    let names: Vec<String> = entries.iter().map(|b| b.to_string()).collect();
                    self.err(
                        Check::Boundary,
                        Some(h),
                        format!(
                            "loop header {h} needs a unique preheader; its entries are [{}]",
                            names.join(", ")
                        ),
                    );
                }
            }
        }
    }

    // --- 3, 4. types ------------------------------------------------------

    fn types(&mut self) {
        let f = self.f;
        for &b in &self.rpo.clone() {
            for &inst in &f.blocks[b].insts {
                let d = &f.insts[inst];
                let arg_tys: Vec<Type> = d.args.iter().map(|&v| self.ty(v)).collect();
                let sig = match signature(&d.op, &arg_tys, self.m) {
                    Ok(s) => s,
                    Err(e) => {
                        self.err(
                            Check::OperandType,
                            Some(b),
                            format!("{}: {e}", mnemonic(&d.op)),
                        );
                        continue;
                    }
                };
                if sig.results.len() != d.results.len() {
                    self.err(
                        Check::OperandType,
                        Some(b),
                        format!(
                            "{} defines {} result(s), expected {}",
                            mnemonic(&d.op),
                            d.results.len(),
                            sig.results.len()
                        ),
                    );
                } else {
                    for (&v, rule) in d.results.iter().zip(&sig.results) {
                        if !is_subtype(rule, &self.ty(v)) {
                            self.err(
                                Check::OperandType,
                                Some(b),
                                format!(
                                    "{}: result {} is not a supertype of the rule's {}",
                                    mnemonic(&d.op),
                                    self.vt(v),
                                    self.ts(rule)
                                ),
                            );
                        }
                    }
                }
                for (role, e) in f.succ_edges(inst) {
                    let params = &f.blocks[e.block].params;
                    for (a, &p) in e.args.iter().zip(params) {
                        let (what, t) = match *a {
                            EdgeArg::Value(v) => (v.to_string(), self.ty(v)),
                            EdgeArg::Out(k) => match sig.outputs.get(k as usize) {
                                Some(t) => (format!("output %{k}"), *t),
                                None => {
                                    self.err(
                                        Check::EdgeType,
                                        Some(b),
                                        format!("{} has no output %{k}", mnemonic(&d.op)),
                                    );
                                    continue;
                                }
                            },
                        };
                        if !is_subtype(&t, &self.ty(p)) {
                            let why = if t.repr() != self.ty(p).repr() {
                                " (different representations)"
                            } else {
                                ""
                            };
                            self.err(
                                Check::EdgeType,
                                Some(b),
                                format!(
                                    "{} edge to {}: {what} ({}) is not a subtype of param {}{why}",
                                    role.name(),
                                    e.block,
                                    self.ts(&t),
                                    self.vt(p)
                                ),
                            );
                        }
                    }
                }
                self.sigs[inst] = Some(sig);
            }
        }
    }

    // --- liveness -----------------------------------------------------------

    fn edge_uses(&self, inst: Inst) -> Vec<Value> {
        self.f.insts[inst]
            .succs
            .iter()
            .flat_map(|e| e.args.iter())
            .filter_map(|a| match a {
                EdgeArg::Value(v) => Some(*v),
                EdgeArg::Out(_) => None,
            })
            .collect()
    }

    /// Standard backward liveness. Edge args are uses at the terminator;
    /// params are defined at their block's entry. Ghosts count.
    fn liveness(&mut self) {
        let f = self.f;
        let mut changed = true;
        while changed {
            changed = false;
            for &b in self.rpo.iter().rev() {
                let mut live = self.live_out(b);
                for &inst in f.blocks[b].insts.iter().rev() {
                    self.step_back(inst, &mut live);
                }
                for p in &f.blocks[b].params {
                    live.remove(p);
                }
                if self.live_in.get(&b) != Some(&live) {
                    self.live_in.insert(b, live);
                    changed = true;
                }
            }
        }
    }

    fn live_out(&self, b: Block) -> BTreeSet<Value> {
        let mut out = BTreeSet::new();
        for s in self.f.succs(b) {
            if let Some(l) = self.live_in.get(&s) {
                out.extend(l.iter().copied());
            }
        }
        out
    }

    /// Move `live` from after `inst` to before it.
    fn step_back(&self, inst: Inst, live: &mut BTreeSet<Value>) {
        let d = &self.f.insts[inst];
        for r in &d.results {
            live.remove(r);
        }
        live.extend(d.args.iter().copied());
        live.extend(self.edge_uses(inst));
    }

    // --- 5, 6, 7. fences, predictions, GC -------------------------------------

    /// A shared throw block: no params, only upcasts and constants, ending
    /// in `exit.throw`. Nothing in one relies on a killable component, so
    /// an `err` edge into one need not weaken (§5.3: it has no params).
    fn is_throw_block(&self, b: Block) -> bool {
        let bd = &self.f.blocks[b];
        bd.params.is_empty()
            && bd.insts.iter().enumerate().all(|(i, &inst)| {
                let op = &self.f.insts[inst].op;
                if i + 1 == bd.insts.len() {
                    matches!(op, Opcode::ExitThrow { .. })
                } else {
                    matches!(
                        op,
                        Opcode::Box
                            | Opcode::Weaken
                            | Opcode::ConstVal(_)
                            | Opcode::ConstI32(_)
                            | Opcode::ConstF64(_)
                            | Opcode::ConstBool(_)
                            | Opcode::ConstObj(_)
                            | Opcode::ConstStr(_)
                    )
                }
            })
    }

    fn fences(&mut self) {
        let f = self.f;
        for &b in &self.rpo.clone() {
            let mut live = self.live_out(b);
            // Walk backward so `live` is the set live after each inst.
            for &inst in f.blocks[b].insts.iter().rev() {
                let d = &f.insts[inst];
                let arg_tys: Vec<Type> = d.args.iter().map(|&v| self.ty(v)).collect();
                let fx = effects(&d.op, &arg_tys, self.m);
                let site = d.op.kill_site(&fx);
                let name = mnemonic(&d.op);
                let across: Vec<Value> = live
                    .iter()
                    .copied()
                    .filter(|v| !d.results.contains(v))
                    .collect();
                if site == KillSite::Op {
                    for &v in &across {
                        if fx.kill.matches(&self.ty(v)) {
                            let msg = format!(
                                "{} is live across {name}, which kills {{{}}}",
                                self.vt(v),
                                kill_str(&fx.kill)
                            );
                            self.err(Check::Fence, Some(b), msg);
                        }
                    }
                }
                if matches!(site, KillSite::OkEdge | KillSite::DirtyEdge) {
                    self.fence_edges(b, inst, &fx, site);
                }
                if matches!(site, KillSite::Op | KillSite::OkEdge) {
                    let covered = f.witness(inst).is_some_and(|w| w.may_kill.covers(&fx.kill));
                    if !covered {
                        let have = f.witness(inst).map_or("no witness".to_string(), |w| {
                            format!("!pred{{{}}}", kill_str(&w.may_kill))
                        });
                        self.err(
                            Check::Prediction,
                            Some(b),
                            format!(
                                "{name} statically kills {{{}}}, which its prediction does not cover ({have})",
                                kill_str(&fx.kill)
                            ),
                        );
                    }
                }
                if fx.may_gc {
                    self.raw_across_gc(b, inst, &fx, &across);
                }
                self.step_back(inst, &mut live);
            }
        }
    }

    fn fence_edges(&mut self, b: Block, inst: Inst, fx: &Effects, site: KillSite) {
        let f = self.f;
        let fence_role = if site == KillSite::DirtyEdge {
            SuccRole::OkDirty
        } else {
            SuccRole::Ok
        };
        let name = mnemonic(&f.insts[inst].op);
        for (role, e) in f.succ_edges(inst) {
            let is_fence =
                role == fence_role || (role == SuccRole::Err && !self.is_throw_block(e.block));
            if !is_fence {
                continue;
            }
            let live_in = self.live_in.get(&e.block).cloned().unwrap_or_default();
            for v in live_in {
                if fx.kill.matches(&self.ty(v)) {
                    let msg = format!(
                        "{} is live into {} across the {} edge of {name}, which kills {{{}}}",
                        self.vt(v),
                        e.block,
                        role.name(),
                        kill_str(&fx.kill)
                    );
                    self.err(Check::Fence, Some(b), msg);
                }
            }
            for (a, &p) in e.args.iter().zip(&f.blocks[e.block].params) {
                if let EdgeArg::Value(v) = a {
                    if fx.kill.matches(&self.ty(p)) {
                        let msg = format!(
                            "{v} flows across the {} edge of {name} into param {}, which keeps a component it kills ({{{}}}); weaken the param",
                            role.name(),
                            self.vt(p),
                            kill_str(&fx.kill)
                        );
                        self.err(Check::Fence, Some(b), msg);
                    }
                }
            }
        }
    }

    fn raw_across_gc(&mut self, b: Block, inst: Inst, _fx: &Effects, across: &[Value]) {
        let f = self.f;
        let name = mnemonic(&f.insts[inst].op);
        let is_raw = |v: &Value| matches!(f.values[*v].ty, Type::Raw(_));
        let mut bad: BTreeSet<Value> = BTreeSet::new();
        if !f.insts[inst].op.is_terminator() {
            bad.extend(across.iter().copied().filter(is_raw));
        } else {
            for e in &f.insts[inst].succs {
                if let Some(l) = self.live_in.get(&e.block) {
                    bad.extend(l.iter().copied().filter(is_raw));
                }
                for a in &e.args {
                    if let EdgeArg::Value(v) = a {
                        if is_raw(v) {
                            bad.insert(*v);
                        }
                    }
                }
            }
        }
        for v in bad {
            let msg = format!("raw pointer {} is live across may-GC {name}", self.vt(v));
            self.err(Check::RawGc, Some(b), msg);
        }
    }

    // --- 8. boundary ------------------------------------------------------------

    fn boundary(&mut self) {
        let f = self.f;
        for &b in &self.rpo.clone() {
            for &inst in &f.blocks[b].insts {
                let d = &f.insts[inst];
                let Some((pc, nargs, nlocals)) = d.op.exit_shape() else {
                    continue;
                };
                let name = mnemonic(&d.op);
                if nargs != f.frame.formals || nlocals != f.frame.locals {
                    self.err(
                        Check::Boundary,
                        Some(b),
                        format!(
                            "{name} pc={pc} carries {nargs} arg(s) and {nlocals} local(s); the frame has {} and {}",
                            f.frame.formals, f.frame.locals
                        ),
                    );
                }
                match f.frame.exit_arity(pc) {
                    None => self.err(
                        Check::Boundary,
                        Some(b),
                        format!("{name}: no stack depth is recorded for pc {pc}"),
                    ),
                    Some(n) if n != d.args.len() => {
                        let depth = f.frame.depths[&pc];
                        self.err(
                            Check::Boundary,
                            Some(b),
                            format!(
                                "{name} pc={pc} carries {} operand(s); the frame needs {n} (stack depth {depth})",
                                d.args.len()
                            ),
                        );
                    }
                    Some(_) => {}
                }
                for &v in &d.args {
                    if !self.ty(v).is_val_top() {
                        self.err(
                            Check::Boundary,
                            Some(b),
                            format!(
                                "{name} operand {} must be val (⊤); upcast it first",
                                self.vt(v)
                            ),
                        );
                    }
                }
            }
        }
        for r in &f.roots {
            let params = &f.blocks[r.block].params;
            match r.kind {
                RootKind::Entry => {
                    let want = 2 + f.frame.formals as usize;
                    if params.len() != want {
                        self.err(
                            Check::Boundary,
                            Some(r.block),
                            format!("entry root takes {} param(s); expected callee, this and {} formal(s)", params.len(), f.frame.formals),
                        );
                        continue;
                    }
                    // The callee is this script's function, whatever else is known.
                    let callee = Type::Obj(ObjInfo::kind(ObjKind::Function(Some(f.script))));
                    let t0 = self.ty(params[0]);
                    if !(t0.is_val_top() || is_subtype(&callee, &t0)) {
                        self.err(
                            Check::Boundary,
                            Some(r.block),
                            format!(
                                "entry callee param {} claims more than the callee's identity",
                                self.vt(params[0])
                            ),
                        );
                    }
                    for &p in &params[1..] {
                        if !self.ty(p).is_val_top() {
                            self.err(
                                Check::Boundary,
                                Some(r.block),
                                format!("entry param {} must be val (⊤)", self.vt(p)),
                            );
                        }
                    }
                }
                RootKind::Onramp(pc) => {
                    match f.frame.exit_arity(pc) {
                        None => self.err(
                            Check::Boundary,
                            Some(r.block),
                            format!("onramp root: no stack depth is recorded for pc {pc}"),
                        ),
                        Some(n) if n != params.len() => self.err(
                            Check::Boundary,
                            Some(r.block),
                            format!(
                                "onramp root at pc {pc} takes {} param(s); the frame needs {n}",
                                params.len()
                            ),
                        ),
                        Some(_) => {}
                    }
                    for &p in params {
                        if !self.ty(p).is_val_top() {
                            self.err(
                                Check::Boundary,
                                Some(r.block),
                                format!("onramp param {} must be val (⊤)", self.vt(p)),
                            );
                        }
                    }
                }
            }
        }
    }
}

/// Check `f` (a function of `m`). Returns every error found.
pub fn verify(m: &Module, f: &Func) -> Result<(), Vec<VerifyError>> {
    let mut v = Verifier {
        m,
        f,
        errors: vec![],
        inst_block: EntityMap::new(),
        preds: BTreeMap::new(),
        rpo: vec![],
        rpo_index: BTreeMap::new(),
        idom: BTreeMap::new(),
        sigs: EntityMap::new(),
        live_in: BTreeMap::new(),
    };
    v.structure();
    if v.errors.is_empty() {
        v.cfg();
    }
    if v.errors.is_empty() {
        v.loops();
        v.dominance();
        v.types();
        v.liveness();
        v.fences();
        v.boundary();
    }
    if v.errors.is_empty() {
        Ok(())
    } else {
        Err(v.errors)
    }
}

/// Check every function of `m`.
pub fn verify_module(m: &Module) -> Result<(), Vec<VerifyError>> {
    let errors: Vec<VerifyError> = m
        .funcs
        .iter()
        .filter_map(|f| verify(m, f).err())
        .flatten()
        .collect();
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}
