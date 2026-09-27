//! MIR optimization passes (MIR.md §10).
//!
//! - [`fold_guards`]: guard folding (§10.1), by type and by availability.
//! - [`forward_params`]: a param of a block with one predecessor is the
//!   value that predecessor passes.
//! - [`optimize`]: both, to a fixpoint.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::mir::entity::{Block, Inst, Value};
use crate::mir::func::{Edge, EdgeArg, Func, ValueDef};
use crate::mir::module::Module;
use crate::mir::ops::{effects, signature, KillSite, Opcode, SuccRole};
use crate::mir::types::{is_subtype, Type};

/// A guard's identity: its op (with its static params) and its operand.
type GuardKey = (Opcode, Value);

fn is_guard(op: &Opcode) -> bool {
    matches!(
        op,
        Opcode::GuardUnbox(_)
            | Opcode::GuardTags(_)
            | Opcode::GuardKind(_)
            | Opcode::GuardLayout { .. }
            | Opcode::GuardSingleton(_)
            | Opcode::GuardScript(_)
    )
}

/// Predecessors, reverse postorder from the roots, and immediate
/// dominators (over a virtual root above every root).
struct Cfg {
    rpo: Vec<Block>,
    /// Pre/post numbers in the dominator tree.
    dom: BTreeMap<Block, (u32, u32)>,
}

impl Cfg {
    fn new(f: &Func) -> Cfg {
        let mut preds: BTreeMap<Block, Vec<Block>> = BTreeMap::new();
        for &b in &f.layout {
            preds.entry(b).or_default();
            for s in f.succs(b) {
                preds.entry(s).or_default().push(b);
            }
        }
        let mut seen = BTreeSet::new();
        let mut post = vec![];
        for r in &f.roots {
            if !seen.insert(r.block) {
                continue;
            }
            let mut stack = vec![(r.block, f.succs(r.block), 0usize)];
            while let Some((b, succs, i)) = stack.last_mut() {
                if *i < succs.len() {
                    let s = succs[*i];
                    *i += 1;
                    if seen.insert(s) {
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
        let rpo = post;
        let index: BTreeMap<Block, usize> = rpo.iter().enumerate().map(|(i, &b)| (b, i)).collect();
        let roots: BTreeSet<Block> = f.roots.iter().map(|r| r.block).collect();
        // Cooper-Harvey-Kennedy; `None` is the virtual root.
        let mut idom: BTreeMap<Block, Option<Block>> = BTreeMap::new();
        for &r in &roots {
            idom.insert(r, None);
        }
        let intersect = |idom: &BTreeMap<Block, Option<Block>>, a: Block, b: Block| {
            let (mut a, mut b) = (Some(a), Some(b));
            while a != b {
                match (a, b) {
                    (Some(x), Some(y)) => {
                        if index[&x] > index[&y] {
                            a = idom[&x];
                        } else {
                            b = idom[&y];
                        }
                    }
                    _ => return None,
                }
            }
            a
        };
        let mut changed = true;
        while changed {
            changed = false;
            for &b in &rpo {
                if roots.contains(&b) {
                    continue;
                }
                let mut new: Option<Option<Block>> = None;
                for &p in &preds[&b] {
                    if !idom.contains_key(&p) {
                        continue;
                    }
                    new = Some(match new {
                        None => Some(p),
                        Some(None) => None,
                        Some(Some(cur)) => intersect(&idom, cur, p),
                    });
                }
                if let Some(n) = new {
                    if idom.get(&b) != Some(&n) {
                        idom.insert(b, n);
                        changed = true;
                    }
                }
            }
        }
        let mut children: BTreeMap<Option<Block>, Vec<Block>> = BTreeMap::new();
        for (&b, &d) in &idom {
            children.entry(d).or_default().push(b);
        }
        let mut dom = BTreeMap::new();
        let mut n = 0u32;
        let mut pre = BTreeMap::new();
        let mut stack: Vec<(Block, bool)> = children
            .get(&None)
            .map(|c| c.iter().rev().map(|&b| (b, false)).collect())
            .unwrap_or_default();
        while let Some((b, done)) = stack.pop() {
            if done {
                dom.insert(b, (pre[&b], n));
                n += 1;
                continue;
            }
            pre.insert(b, n);
            n += 1;
            stack.push((b, true));
            if let Some(c) = children.get(&Some(b)) {
                stack.extend(c.iter().rev().map(|&c| (c, false)));
            }
        }
        Cfg { rpo, dom }
    }

    fn dominates(&self, a: Block, b: Block) -> bool {
        match (self.dom.get(&a), self.dom.get(&b)) {
            (Some(&(ap, aq)), Some(&(bp, bq))) => ap <= bp && bq <= aq,
            _ => false,
        }
    }
}

/// Where a value is defined: its block.
fn def_block(f: &Func, v: Value, inst_block: &BTreeMap<Inst, Block>) -> Option<Block> {
    match f.values[v].def {
        ValueDef::Param(b, _) => Some(b),
        ValueDef::Result(i, _) => inst_block.get(&i).copied(),
        ValueDef::Unused => None,
    }
}

/// The value a guard's `ok` edge hands its successor as output 0: the
/// param receiving it.
fn ok_output(f: &Func, ok: &Edge) -> Option<Value> {
    let k = ok.args.iter().position(|a| *a == EdgeArg::Out(0))?;
    Some(f.blocks[ok.block].params[k])
}

/// Run the passes to a fixpoint: each folded guard leaves its `ok`
/// block's param a copy of a known value, which exposes the next guard
/// on it to folding. Returns how many guards folded.
pub fn optimize(m: &Module, f: &mut Func) -> usize {
    let mut total = 0;
    loop {
        let n = fold_guards(m, f);
        forward_params(f);
        total += n;
        if n == 0 {
            return total;
        }
    }
}

/// Replace each param of a (non-root) block with a single predecessor
/// edge by the value that edge passes, when it passes a value (not a
/// terminator output). The value's type is at most the param's, so every
/// use stays well-typed.
pub fn forward_params(f: &mut Func) {
    let roots: BTreeSet<Block> = f.roots.iter().map(|r| r.block).collect();
    let mut incoming: BTreeMap<Block, Vec<(Inst, usize)>> = BTreeMap::new();
    for &b in &f.layout {
        if let Some(t) = f.terminator(b) {
            for (k, e) in f.insts[t].succs.iter().enumerate() {
                incoming.entry(e.block).or_default().push((t, k));
            }
        }
    }
    let mut subst: BTreeMap<Value, Value> = BTreeMap::new();
    for &b in &f.layout {
        if roots.contains(&b) {
            continue;
        }
        let Some([(t, k)]) = incoming.get(&b).map(|v| v.as_slice()) else {
            continue;
        };
        let (t, k) = (*t, *k);
        let edge = f.insts[t].succs[k].clone();
        let params = f.blocks[b].params.clone();
        let mut keep_params = vec![];
        let mut keep_args = vec![];
        for (&p, &a) in params.iter().zip(&edge.args) {
            match a {
                EdgeArg::Value(v) if v != p => {
                    subst.insert(p, v);
                }
                a => {
                    keep_params.push(p);
                    keep_args.push(a);
                }
            }
        }
        if keep_params.len() != params.len() {
            f.blocks[b].params = keep_params;
            f.insts[t].succs[k].args = keep_args;
            for (n, &p) in f.blocks[b].params.clone().iter().enumerate() {
                f.values[p].def = ValueDef::Param(b, n as u32);
            }
        }
    }
    if subst.is_empty() {
        return;
    }
    let resolve = |mut v: Value| {
        while let Some(&w) = subst.get(&v) {
            v = w;
        }
        v
    };
    let insts: Vec<Inst> = f
        .layout
        .iter()
        .flat_map(|&b| f.blocks[b].insts.clone())
        .collect();
    for i in insts {
        let d = &mut f.insts[i];
        for a in &mut d.args {
            *a = resolve(*a);
        }
        for e in &mut d.succs {
            for a in &mut e.args {
                if let EdgeArg::Value(v) = a {
                    *v = resolve(*v);
                }
            }
        }
    }
    for p in subst.keys() {
        f.values[*p].def = ValueDef::Unused;
    }
}

/// Guard folding (§10.1). A guard is redundant when:
/// - **by type:** its operand's type already proves it; or
/// - **by availability:** the same guard on the same operand succeeded on
///   every path to it, with no fence since that kills its output's type,
///   and that guard's output dominates it.
///
/// Either way it becomes a `jump` to its `ok` successor carrying the
/// known value (unboxed first when the guard would unbox). Its `fail`
/// edge goes away. Returns how many guards folded. The validator checks
/// the result.
pub fn fold_guards(m: &Module, f: &mut Func) -> usize {
    let cfg = Cfg::new(f);
    let mut inst_block = BTreeMap::new();
    for &b in &f.layout {
        for &i in &f.blocks[b].insts {
            inst_block.insert(i, b);
        }
    }
    // Available guards on block entry, by forward dataflow. `None` is
    // "not yet computed" (top); roots start empty.
    let mut avail_in: BTreeMap<Block, Option<HashMap<GuardKey, Value>>> = BTreeMap::new();
    for r in &f.roots {
        avail_in.insert(r.block, Some(HashMap::new()));
    }
    let edge_out = |f: &Func, b: Block, avail: &HashMap<GuardKey, Value>| {
        // What each successor edge of `b` hands on.
        let mut out: Vec<(Block, HashMap<GuardKey, Value>)> = vec![];
        let mut cur = avail.clone();
        let insts = &f.blocks[b].insts;
        for (idx, &i) in insts.iter().enumerate() {
            let d = &f.insts[i];
            let tys: Vec<Type> = d.args.iter().map(|&v| f.values[v].ty).collect();
            let fx = effects(&d.op, &tys, m);
            let site = d.op.kill_site(&fx);
            if site == KillSite::Op {
                cur.retain(|_, v| !fx.kill.matches(&f.values[*v].ty));
            }
            if idx + 1 != insts.len() {
                continue;
            }
            for (role, e) in f.succ_edges(i) {
                let mut a = cur.clone();
                let fence = matches!(
                    (site, role),
                    (KillSite::OkEdge, SuccRole::Ok | SuccRole::Err)
                        | (KillSite::DirtyEdge, SuccRole::OkDirty | SuccRole::Err)
                );
                if fence {
                    a.retain(|_, v| !fx.kill.matches(&f.values[*v].ty));
                }
                if role == SuccRole::Ok && is_guard(&d.op) {
                    if let Some(v) = ok_output(f, e) {
                        a.insert((d.op, d.args[0]), v);
                    }
                }
                out.push((e.block, a));
            }
        }
        out
    };
    let mut changed = true;
    while changed {
        changed = false;
        for &b in &cfg.rpo {
            let Some(Some(inb)) = avail_in.get(&b).cloned() else {
                continue;
            };
            for (s, a) in edge_out(f, b, &inb) {
                let merged = match avail_in.get(&s).cloned().flatten() {
                    None if !f.roots.iter().any(|r| r.block == s) => a,
                    None => HashMap::new(),
                    Some(old) => old
                        .into_iter()
                        .filter(|(k, v)| a.get(k) == Some(v))
                        .collect(),
                };
                if avail_in.get(&s).cloned().flatten().as_ref() != Some(&merged) {
                    avail_in.insert(s, Some(merged));
                    changed = true;
                }
            }
        }
    }
    // Rewrite.
    let mut folded = 0;
    for &b in &cfg.rpo.clone() {
        let Some(t) = f.terminator(b) else { continue };
        let d = f.insts[t].clone();
        if !is_guard(&d.op) {
            continue;
        }
        let x = d.args[0];
        let xt = f.values[x].ty;
        let ok = d.succs[0].clone();
        let Some(outp) = ok_output(f, &ok) else {
            continue;
        };
        let want = f.values[outp].ty;
        // By type: the operand's own type proves the guard.
        let by_type: Option<(Option<Opcode>, Type)> = match signature(&d.op, &[xt], m) {
            Ok(sig) => {
                let out = sig.outputs[0];
                match d.op {
                    Opcode::GuardUnbox(k) => {
                        let unbox = signature(&Opcode::Unbox(k), &[xt], m).ok();
                        unbox.map(|s| (Some(Opcode::Unbox(k)), s.results[0]))
                    }
                    _ if is_subtype(&xt, &out) || xt == out => Some((None, xt)),
                    _ => None,
                }
            }
            Err(_) => None,
        };
        let known: Option<(Option<Opcode>, Value, Type)> = match by_type {
            Some((op, t)) => Some((op, x, t)),
            None => {
                // A guard ends its block, so what reaches it is the
                // block's entry set.
                let avail = avail_in.get(&b).cloned().flatten().unwrap_or_default();
                match avail.get(&(d.op, x)) {
                    Some(&v1) => {
                        let db = def_block(f, v1, &inst_block);
                        (db.is_some_and(|db| db != b && cfg.dominates(db, b)))
                            .then(|| (None, v1, f.values[v1].ty))
                    }
                    None => None,
                }
            }
        };
        let Some((unbox, v, vt)) = known else {
            continue;
        };
        if !(is_subtype(&vt, &want)) {
            continue;
        }
        // Replace the guard with (an unbox and) a jump.
        f.blocks[b].insts.pop();
        let v = match unbox {
            Some(op) => {
                let (_, rs) = f.add_inst(b, op, vec![x], &[vt], vec![]);
                rs[0]
            }
            None => v,
        };
        let args = ok
            .args
            .iter()
            .map(|a| match a {
                EdgeArg::Out(0) => EdgeArg::Value(v),
                a => *a,
            })
            .collect();
        f.add_inst(
            b,
            Opcode::Jump,
            vec![],
            &[],
            vec![Edge {
                block: ok.block,
                args,
            }],
        );
        folded += 1;
    }
    folded
}
