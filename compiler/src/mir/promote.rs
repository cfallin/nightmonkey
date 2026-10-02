//! Loop-carried caching of memory locations (MIR-MEMORY.md §10, the
//! owner's "materialize once, then cache"; KICKOFF-8 item 4).
//!
//! A location a loop reads and writes through one base from before the
//! loop is loaded once in the preheader and carried around the loop as a
//! block param: its reads are the carried value, its writes replace it.
//! Memory is brought up to date where something else may observe it: a
//! may-be-dirty value is written back before an op that may read the
//! location (a call, an `exit.inline`, a generic op, an alias of it) and
//! on every edge leaving the loop (exits included); after an op that may
//! write it, the value is reloaded. The fast path then touches no memory.
//!
//! Locations: closure variables (`env.load`/`env.store` of an environment
//! object from before the loop) and fields (`load_slot`/`store_slot`
//! through an object from before the loop, with a receiver from before it
//! proving the slot and TYPES, whose claim nothing in the loop kills).
//! The params go on every block of the loop and `forward_params` prunes
//! the ones whose incoming values agree.

use std::collections::{BTreeMap, BTreeSet};

use crate::ids::EnvSlot;
use crate::mir::entity::{AtomId, Block, Inst, Value};
use crate::mir::func::{Edge, EdgeArg, Func};
use crate::mir::mem::{root, writes_on};
use crate::mir::module::{Module, Region};
use crate::mir::ops::{effects, signature, KillSite, Opcode, SuccRole};
use crate::mir::opt::{def_block, replace_values, Cfg};
use crate::mir::types::{is_subtype, Type};

/// What is cached of the object.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Env(EnvSlot),
    Field(AtomId),
}

/// One cached location of object `base` (a value from before the loop;
/// accesses through any value with its root).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Loc {
    base: Value,
    kind: Kind,
}

impl Loc {
    /// Whether `op` reads (`Some(false)`) or writes (`Some(true)`) this
    /// kind of location.
    fn access(self, op: &Opcode) -> Option<bool> {
        match (self.kind, *op) {
            (Kind::Env(s), Opcode::EnvLoad(t)) if s == t => Some(false),
            (Kind::Field(n), Opcode::LoadSlot(t)) if n == t => Some(false),
            (Kind::Env(s), Opcode::EnvStore(t)) if s == t => Some(true),
            (Kind::Field(n), Opcode::StoreSlot(t)) if n == t => Some(true),
            _ => None,
        }
    }

    fn load(self) -> Opcode {
        match self.kind {
            Kind::Env(s) => Opcode::EnvLoad(s),
            Kind::Field(n) => Opcode::LoadSlot(n),
        }
    }

    fn store(self) -> Opcode {
        match self.kind {
            Kind::Env(s) => Opcode::EnvStore(s),
            Kind::Field(n) => Opcode::StoreSlot(n),
        }
    }
}

/// What an instruction of the loop is to the location.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Role {
    /// A read through the base: the carried value.
    Read,
    /// A write through the base (its value operand): the new carried value.
    Write,
    /// Anything else: memory must be current before it if it may read the
    /// location, and the value reloaded after it if it may write it.
    Other,
}

/// Promote every promotable location of every loop, once each; returns
/// how many. Runs after `optimize`'s fixpoint (its own write-backs and
/// reloads are accesses it must not promote again).
pub fn promote_all(m: &Module, f: &mut Func) -> usize {
    let mut done: Vec<(Block, Loc)> = vec![];
    let mut n = 0;
    while n < 64 && promote(m, f, &mut done) {
        n += 1;
    }
    n
}

/// Promote one location of one loop (the CFG changes), recording it.
fn promote(m: &Module, f: &mut Func, done: &mut Vec<(Block, Loc)>) -> bool {
    let cfg = Cfg::new(f);
    let mut preds: BTreeMap<Block, Vec<Block>> = BTreeMap::new();
    let mut tpreds: BTreeMap<Block, Vec<Inst>> = BTreeMap::new();
    for &b in &f.layout {
        if let Some(t) = f.terminator(b) {
            for e in &f.insts[t].succs {
                preds.entry(e.block).or_default().push(b);
                let p = tpreds.entry(e.block).or_default();
                if !p.contains(&t) {
                    p.push(t);
                }
            }
        }
    }
    let mut inst_block = BTreeMap::new();
    for &b in &f.layout {
        for &i in &f.blocks[b].insts {
            inst_block.insert(i, b);
        }
    }
    for li in 0..f.loops.len() {
        let l = f.loops[li].clone();
        let (h, p0) = (l.header, l.preheader);
        let Some(pt) = f.terminator(p0) else { continue };
        if f.insts[pt].op != Opcode::Jump || f.succs(p0) != vec![h] {
            continue;
        }
        let mut body: BTreeSet<Block> = BTreeSet::new();
        body.insert(h);
        let latches: Vec<Block> = preds
            .get(&h)
            .map(|ps| ps.iter().copied().filter(|&q| cfg.dominates(h, q)).collect())
            .unwrap_or_default();
        let mut work = latches.clone();
        while let Some(b) = work.pop() {
            if body.insert(b) {
                work.extend(preds.get(&b).into_iter().flatten().copied().filter(|&q| cfg.reachable(q)));
            }
        }
        if latches.is_empty() || body.contains(&p0) || !body.iter().all(|&b| cfg.dominates(p0, b)) {
            continue;
        }
        // Every block of the loop is entered from the loop or the
        // preheader only (an onramp into the body has no cached value).
        if body.iter().any(|b| f.roots.iter().any(|r| r.block == *b)) {
            continue;
        }
        let outside = |v: Value| def_block(f, v, &inst_block).is_some_and(|b| !body.contains(&b));
        // Candidates: locations read and written through a base from
        // before the loop.
        let mut cands: Vec<(Loc, usize, usize)> = vec![];
        for &b in &body {
            for &i in &f.blocks[b].insts {
                let d = &f.insts[i];
                let (kind, write) = match d.op {
                    Opcode::EnvLoad(s) => (Kind::Env(s), false),
                    Opcode::EnvStore(s) => (Kind::Env(s), true),
                    Opcode::LoadSlot(n) => (Kind::Field(n), false),
                    Opcode::StoreSlot(n) => (Kind::Field(n), true),
                    _ => continue,
                };
                let base = root(f, d.args[0], &tpreds);
                if !outside(base) {
                    continue;
                }
                let loc = Loc { base, kind };
                match cands.iter_mut().find(|(c, _, _)| *c == loc) {
                    Some(c) => {
                        if write {
                            c.2 += 1
                        } else {
                            c.1 += 1
                        }
                    }
                    None => cands.push((loc, usize::from(!write), usize::from(write))),
                }
            }
        }
        // Blocks outside the loop with an edge into it: only the
        // preheader, and unreachable ones (which go).
        let strays: Vec<Block> = f
            .layout
            .iter()
            .copied()
            .filter(|&b| b != p0 && !body.contains(&b) && f.succs(b).iter().any(|s| body.contains(s)))
            .collect();
        if strays.iter().any(|&b| cfg.reachable(b)) {
            continue;
        }
        for (loc, reads, writes) in cands {
            if reads == 0 || writes == 0 || done.contains(&(h, loc)) {
                continue;
            }
            for &b in &strays {
                f.blocks[b].insts.clear();
                f.add_inst(b, Opcode::Unreachable, vec![], &[], vec![]);
            }
            if promote_one(m, f, &cfg, &body, h, p0, loc, &tpreds) {
                done.push((h, loc));
                return true;
            }
        }
    }
    false
}

#[allow(clippy::too_many_arguments)]
fn promote_one(
    m: &Module,
    f: &mut Func,
    cfg: &Cfg,
    body: &BTreeSet<Block>,
    h: Block,
    p0: Block,
    loc: Loc,
    tpreds: &BTreeMap<Block, Vec<Inst>>,
) -> bool {
    // The value the new loads and stores go through: the environment
    // itself, or a receiver from before the loop whose type proves the
    // field's slot and TYPES (any access's, else none).
    let acc = match loc.kind {
        Kind::Env(_) => {
            if !matches!(f.values[loc.base].ty, Type::Obj(o) if o.kind == crate::mir::types::ObjKind::Env) {
                return false;
            }
            loc.base
        }
        Kind::Field(n) => {
            let mut found = None;
            for &b in body {
                for &i in &f.blocks[b].insts {
                    let d = &f.insts[i];
                    if loc.access(&d.op).is_none() || root(f, d.args[0], tpreds) != loc.base {
                        continue;
                    }
                    let r = d.args[0];
                    let outside = match f.values[r].def {
                        crate::mir::func::ValueDef::Param(pb, _) => !body.contains(&pb),
                        crate::mir::func::ValueDef::Result(ri, _) => {
                            !body.iter().any(|&bb| f.blocks[bb].insts.contains(&ri))
                        }
                        _ => false,
                    };
                    if outside && f.values[r].ty.obj_info().is_some_and(|o| o.layout.is_some_and(|c| c.types))
                        && signature(&Opcode::LoadSlot(n), &[f.values[r].ty], m).is_ok()
                    {
                        found = Some(r);
                    }
                }
            }
            let Some(r) = found else { return false };
            r
        }
    };
    let region = match loc.kind {
        Kind::Env(s) => Region::Env(s),
        Kind::Field(name) => Region::Field {
            name,
            keys: f.values[acc].ty.obj_info().and_then(|o| o.layout).map(|c| c.keys),
        },
    };
    // The receiver's claim must hold in the whole loop: nothing in it
    // kills it on an edge that stays in it.
    if let Kind::Field(_) = loc.kind {
        let aty = f.values[acc].ty;
        for &b in body {
            for &i in &f.blocks[b].insts {
                let d = &f.insts[i];
                let tys: Vec<Type> = d.args.iter().map(|&v| f.values[v].ty).collect();
                let fx = effects(&d.op, &tys, m);
                if fx.kill.is_empty() || !fx.kill.matches(&aty) {
                    continue;
                }
                let stays = |roles: &[SuccRole]| {
                    f.succ_edges(i).any(|(r, e)| roles.contains(&r) && body.contains(&e.block))
                };
                let kills = match d.op.kill_site(&fx) {
                    KillSite::None => false,
                    KillSite::Op => true,
                    KillSite::OkEdge => stays(&[SuccRole::Ok, SuccRole::Err]),
                    KillSite::DirtyEdge => stays(&[SuccRole::OkDirty, SuccRole::Err]),
                };
                if kills {
                    return false;
                }
            }
        }
    }
    // The carried value's type: what a load through `acc` gives.
    let ty = match loc.kind {
        Kind::Env(_) => Type::VAL_TOP,
        Kind::Field(_) => match signature(&loc.load(), &[f.values[acc].ty], m) {
            Ok(sig) => sig.results[0],
            Err(_) => return false,
        },
    };
    // Ours: an access through the base whose types agree with the carried
    // value (a read whose result it can be, a write of a value it can
    // hold); an access through a differently typed view stays a memory op
    // (written back before, reloaded after).
    let role = |f: &Func, i: Inst| -> Role {
        let d = &f.insts[i];
        if loc.access(&d.op).is_none() || root(f, d.args[0], tpreds) != loc.base {
            return Role::Other;
        }
        match loc.access(&d.op) {
            Some(false) if is_subtype(&ty, &f.values[d.results[0]].ty) => Role::Read,
            Some(true) if is_subtype(&f.values[d.args[1]].ty, &ty) => Role::Write,
            _ => Role::Other,
        }
    };
    // Something to carry: an own read and an own write.
    let (mut nr, mut nw) = (0, 0);
    for &b in body {
        for &i in &f.blocks[b].insts {
            match role(f, i) {
                Role::Read => nr += 1,
                Role::Write => nw += 1,
                Role::Other => {}
            }
        }
    }
    if nr == 0 || nw == 0 {
        return false;
    }
    let fx_of = |f: &Func, i: Inst| {
        let d = &f.insts[i];
        let tys: Vec<Type> = d.args.iter().map(|&v| f.values[v].ty).collect();
        effects(&d.op, &tys, m)
    };
    // The trade: each own access saved is a load or a store; each op in
    // the loop that may observe or change the location (on a path that
    // stays in it) costs at most a write-back and a reload. Carry it only
    // where the saving is larger.
    let barriers = body
        .iter()
        .flat_map(|&b| f.blocks[b].insts.iter().copied())
        .filter(|&i| {
            if role(f, i) != Role::Other {
                return false;
            }
            let d = &f.insts[i];
            // Exits leave the loop, and an `exit.inline` is an inlined
            // callee's failure: cold by construction.
            if matches!(d.op, Opcode::Exit { .. } | Opcode::ExitThrow { .. } | Opcode::Return | Opcode::ExitInline { .. }) {
                return false;
            }
            let fx = fx_of(f, i);
            fx.reads.iter().chain(&fx.writes).any(|r| r.overlaps(&region))
        })
        .count();
    if barriers >= nr + nw {
        return false;
    }
    // Whether an op (other than ours) may read the location: its reads,
    // and every exit (baseline resumes and may read anything).
    let may_read = |f: &Func, i: Inst| -> bool {
        let d = &f.insts[i];
        if matches!(
            d.op,
            Opcode::Exit { .. } | Opcode::ExitThrow { .. } | Opcode::GenSuspend { .. } | Opcode::Return | Opcode::ExitInline { .. }
        ) {
            return true;
        }
        let fx = fx_of(f, i);
        fx.reads.iter().any(|r| r.overlaps(&region)) || fx.writes.iter().any(|r| r.overlaps(&region))
    };
    let base = acc;
    // The frame of the loop's code (write-backs take each site's own).
    let pt = f.terminator(p0).unwrap();
    let frame0 = f.inst_frame[pt];
    // Dirty on entry to each block (a write since the last write-back),
    // forward over the loop; the header starts clean.
    let rpo: Vec<Block> = cfg.rpo.iter().copied().filter(|b| body.contains(b)).collect();
    let mut dirty_in: BTreeMap<Block, bool> = BTreeMap::new();
    dirty_in.insert(h, false);
    let mut changed = true;
    while changed {
        changed = false;
        for &b in &rpo {
            let mut d = dirty_in.get(&b).copied().unwrap_or(false);
            for &i in &f.blocks[b].insts {
                match role(f, i) {
                    Role::Write => d = true,
                    Role::Read => {}
                    Role::Other => {
                        if may_read(f, i) {
                            d = false;
                        }
                    }
                }
            }
            for s in f.succs(b) {
                if body.contains(&s) {
                    let old = dirty_in.get(&s).copied().unwrap_or(false);
                    if d && !old {
                        dirty_in.insert(s, true);
                        changed = true;
                    }
                }
            }
        }
    }
    // The carried value: a param on every block of the loop.
    let mut carried: BTreeMap<Block, Value> = BTreeMap::new();
    for &b in body {
        carried.insert(b, f.add_param(b, ty));
    }
    // The preheader loads it.
    let jump = f.blocks[p0].insts.pop().unwrap();
    let (load, rs) = f.add_inst(p0, loc.load(), vec![base], &[ty], vec![]);
    f.inst_frame[load] = frame0;
    f.blocks[p0].insts.push(jump);
    let init = rs[0];
    // Edges into a loop block pass the carried value; from the preheader,
    // the load.
    for e in f.insts[jump].succs.iter_mut() {
        if e.block == h {
            e.args.push(EdgeArg::Value(init));
        }
    }
    let mut subst: BTreeMap<Value, Value> = BTreeMap::new();
    let mut dead: BTreeSet<Inst> = BTreeSet::new();
    for &b in &rpo {
        let mut cur = carried[&b];
        let mut d = dirty_in.get(&b).copied().unwrap_or(false);
        let insts = f.blocks[b].insts.clone();
        let mut out: Vec<Inst> = vec![];
        for &i in &insts {
            let is_term = f.insts[i].op.is_terminator();
            match role(f, i) {
                Role::Read => {
                    subst.insert(f.insts[i].results[0], cur);
                    dead.insert(i);
                    continue;
                }
                Role::Write => {
                    cur = f.insts[i].args[1];
                    d = true;
                    dead.insert(i);
                    continue;
                }
                Role::Other => {}
            }
            let reads = may_read(f, i);
            if reads && d {
                let frame = f.inst_frame[i];
                let (wb, _) = f.add_inst(b, loc.store(), vec![base, cur], &[], vec![]);
                f.blocks[b].insts.pop();
                f.inst_frame[wb] = frame;
                out.push(wb);
                d = false;
            }
            out.push(i);
            if is_term {
                continue;
            }
            // A non-terminator that may write the location: reload.
            let fx = fx_of(f, i);
            if fx.writes.iter().any(|r| r.overlaps(&region)) {
                let frame = f.inst_frame[i];
                let (rl, rr) = f.add_inst(b, loc.load(), vec![base], &[ty], vec![]);
                f.blocks[b].insts.pop();
                f.inst_frame[rl] = frame;
                out.push(rl);
                cur = rr[0];
                d = false;
            }
        }
        f.blocks[b].insts = out;
        // The terminator's edges: into the loop, the carried value (after
        // a reload where the edge may write it); out of it, a write-back
        // where dirty.
        let Some(t) = f.terminator(b) else { continue };
        let fx = fx_of(f, t);
        let frame = f.inst_frame[t];
        let roles: Vec<_> = f.succ_edges(t).map(|(r, _)| r).collect();
        for (k, r) in roles.into_iter().enumerate() {
            let target = f.insts[t].succs[k].block;
            let writes = writes_on(f, m, t, &fx, Some(r)).iter().any(|w| w.overlaps(&region));
            if body.contains(&target) {
                if writes {
                    // Split: reload on the edge.
                    let nb = split_edge(f, t, k);
                    let j = f.terminator(nb).unwrap();
                    let (rl, rr) = f.add_inst(nb, loc.load(), vec![base], &[ty], vec![]);
                    f.inst_frame[rl] = frame;
                    let jl = f.blocks[nb].insts.len();
                    f.blocks[nb].insts.swap(jl - 1, jl - 2);
                    f.insts[j].succs[0].args.push(EdgeArg::Value(rr[0]));
                } else {
                    f.insts[t].succs[k].args.push(EdgeArg::Value(cur));
                }
            } else if d && !writes {
                // Leaving the loop with a dirty value: write it back on the
                // edge (a write of the location by the op itself, on this
                // edge, supersedes it).
                let nb = split_edge(f, t, k);
                let (wb, _) = f.add_inst(nb, loc.store(), vec![base, cur], &[], vec![]);
                f.inst_frame[wb] = frame;
                let jl = f.blocks[nb].insts.len();
                f.blocks[nb].insts.swap(jl - 1, jl - 2);
            }
        }
    }
    for b in f.layout.clone() {
        f.blocks[b].insts.retain(|i| !dead.contains(i));
    }
    replace_values(f, &subst);
    true
}

/// Split edge `k` of terminator `t`: a new block that jumps on to the old
/// target with the edge's args, received as its params.
fn split_edge(f: &mut Func, t: Inst, k: usize) -> Block {
    let e = f.insts[t].succs[k].clone();
    let nb = f.add_block();
    let mut args = vec![];
    let mut new_edge_args = vec![];
    // Every arg through a param of the target's type: the edge keeps
    // whatever it weakens (a fence edge's kill applies on it).
    for a in &e.args {
        let ty = f.values[f.blocks[e.block].params[args.len()]].ty;
        let p = f.add_param(nb, ty);
        new_edge_args.push(*a);
        args.push(EdgeArg::Value(p));
    }
    let frame = f.inst_frame[t];
    let (j, _) = f.add_inst(nb, Opcode::Jump, vec![], &[], vec![Edge { block: e.block, args }]);
    f.inst_frame[j] = frame;
    f.insts[t].succs[k] = Edge {
        block: nb,
        args: new_edge_args,
    };
    nb
}
