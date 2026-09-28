//! MIR optimization passes (MIR.md §10).
//!
//! - [`fold_guards`]: guard folding (§10.1), by type and by availability.
//! - [`forward_params`]: a param of a block with one predecessor is the
//!   value that predecessor passes.
//! - [`cse_loads`]: a field load of a field already loaded (or stored)
//!   through the same object, with nothing in between that may write it,
//!   is that value.
//! - [`licm`]: loop-invariant code motion of pure ops and of reads no
//!   op in the loop may write, into the loop's preheader.
//! - [`optimize`]: all, to a fixpoint.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::mir::entity::{Block, Inst, Value};
use crate::mir::func::{Edge, EdgeArg, Func, ValueDef};
use crate::mir::module::Module;
use crate::mir::ops::{effects, signature, KillSite, Opcode, SuccRole};
use crate::mir::types::{is_subtype, Type};

/// A guard's identity: its op (with its static params) and its operand.
type GuardKey = (Opcode, Value);

/// Whether edge `k` of terminator `t` is a fence that kills a component
/// of `v`'s type.
fn fence_kills(m: &Module, f: &Func, t: Inst, k: usize, v: Value) -> bool {
    let d = &f.insts[t];
    let tys: Vec<Type> = d.args.iter().map(|&a| f.values[a].ty).collect();
    let fx = effects(&d.op, &tys, m);
    let fence_role = match d.op.kill_site(&fx) {
        KillSite::OkEdge => SuccRole::Ok,
        KillSite::DirtyEdge => SuccRole::OkDirty,
        KillSite::Op => return fx.kill.matches(&f.values[v].ty),
        KillSite::None => return false,
    };
    let role = d.op.roles().get(k).copied();
    (role == Some(fence_role) || role == Some(SuccRole::Err)) && fx.kill.matches(&f.values[v].ty)
}

/// A guard's operand up to unboxing: `unbox` is a pure function of its
/// operand, so guards on two unboxings of one value are the same guard.
fn canon(f: &Func, v: Value) -> Value {
    match f.values[v].def {
        ValueDef::Result(i, 0) if matches!(f.insts[i].op, Opcode::Unbox(_)) => f.insts[i].args[0],
        _ => v,
    }
}

fn is_guard(op: &Opcode) -> bool {
    matches!(
        op,
        Opcode::GuardUnbox(_)
            | Opcode::GuardTags(_)
            | Opcode::GuardKind(_)
            | Opcode::GuardLayout { .. }
            | Opcode::GuardSingleton(_)
            | Opcode::GuardScript(_)
            | Opcode::CheckFuse(_)
    )
}

/// The operand a guard is keyed by: its operand up to unboxing, or, for
/// an operand-less check (`check.fuse`), a stand-in.
fn guard_arg(f: &Func, d: &crate::mir::func::InstData) -> Value {
    match d.args.first() {
        Some(&a) => canon(f, a),
        None => Value::from_u32(u32::MAX),
    }
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
        let n = fold_guards(m, f)
            + if CSE_LOADS { cse_loads(m, f) } else { 0 }
            + if LICM { licm(m, f) } else { 0 };
        forward_params(m, f);
        total += n;
        if n == 0 {
            return total;
        }
    }
}

/// Replace each param of a (non-root) block that every incoming edge
/// passes the same value (or the param itself, around a loop) by that
/// value, when it is a value (not a terminator output). The value's type
/// is at most the param's, so every use stays well-typed. Not across a
/// fence edge that kills a component of the value's type: that param is
/// what weakens it (§5's fence rule). To a fixpoint: forwarding one param
/// can make another redundant.
pub fn forward_params(m: &Module, f: &mut Func) {
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
    let resolve = |subst: &BTreeMap<Value, Value>, mut v: Value| {
        while let Some(&w) = subst.get(&v) {
            v = w;
        }
        v
    };
    loop {
        let mut changed = false;
        for &b in &f.layout {
            if roots.contains(&b) {
                continue;
            }
            let Some(inc) = incoming.get(&b) else { continue };
            let params = f.blocks[b].params.clone();
            let mut drop = vec![];
            for (n, &p) in params.iter().enumerate() {
                let mut only: Option<Value> = None;
                let mut ok = true;
                for &(t, k) in inc {
                    match f.insts[t].succs[k].args[n] {
                        EdgeArg::Value(v) => {
                            let v = resolve(&subst, v);
                            if v == p {
                                continue;
                            }
                            if fence_kills(m, f, t, k, v) {
                                ok = false;
                                break;
                            }
                            if only.is_some_and(|o| o != v) {
                                ok = false;
                                break;
                            }
                            only = Some(v);
                        }
                        _ => {
                            ok = false;
                            break;
                        }
                    }
                }
                if let (true, Some(v)) = (ok, only) {
                    subst.insert(p, v);
                    drop.push(n);
                }
            }
            if drop.is_empty() {
                continue;
            }
            changed = true;
            let keep = |n: &usize| !drop.contains(n);
            f.blocks[b].params = params
                .iter()
                .enumerate()
                .filter(|(n, _)| keep(n))
                .map(|(_, &p)| p)
                .collect();
            for &(t, k) in inc {
                let args = std::mem::take(&mut f.insts[t].succs[k].args);
                f.insts[t].succs[k].args = args
                    .into_iter()
                    .enumerate()
                    .filter(|(n, _)| keep(n))
                    .map(|(_, a)| a)
                    .collect();
            }
            for (n, &p) in f.blocks[b].params.clone().iter().enumerate() {
                f.values[p].def = ValueDef::Param(b, n as u32);
            }
        }
        if !changed {
            break;
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
            // A fuse can blow wherever JS runs, and blowing one bumps no
            // epoch: its check is not kept across such an op, clean edge
            // or not.
            if fx.may_run_js {
                cur.retain(|(op, _), _| !matches!(op, Opcode::CheckFuse(_)));
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
                        a.insert((d.op, guard_arg(f, d)), v);
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
        let x = d.args.first().copied();
        let ok = d.succs[0].clone();
        let Some(outp) = ok_output(f, &ok) else {
            continue;
        };
        let want = f.values[outp].ty;
        // By type: the operand's own type proves the guard.
        let by_type: Option<(Option<Opcode>, Type)> = match x.map(|x| (x, f.values[x].ty)) {
            None => None,
            Some((_, xt)) => match signature(&d.op, &[xt], m) {
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
            },
        };
        let known: Option<(Option<Opcode>, Value, Type)> = match (by_type, x) {
            (Some((op, t)), Some(x)) => Some((op, x, t)),
            _ => {
                // A guard ends its block, so what reaches it is the
                // block's entry set.
                // The same guard, or one of its kind on the same value
                // whose output implies this one's (a layout within the
                // range guarded here).
                let avail = avail_in.get(&b).cloned().flatten().unwrap_or_default();
                let cx = guard_arg(f, &d);
                let mut hits: Vec<Value> = avail
                    .iter()
                    .filter(|((op, y), v1)| {
                        *y == cx
                            && (*op == d.op
                                || (std::mem::discriminant(op) == std::mem::discriminant(&d.op)
                                    && is_subtype(&f.values[**v1].ty, &want)))
                    })
                    .map(|(_, &v1)| v1)
                    .collect();
                hits.sort();
                hits.into_iter().find_map(|v1| {
                    let db = def_block(f, v1, &inst_block);
                    (db.is_some_and(|db| db != b && cfg.dominates(db, b)))
                        .then(|| (None, v1, f.values[v1].ty))
                })
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
        let v = match (unbox, x) {
            (Some(op), Some(x)) => {
                let (_, rs) = f.add_inst(b, op, vec![x], &[vt], vec![]);
                rs[0]
            }
            _ => v,
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

/// Whether field loads are made redundant by earlier loads and stores.
const CSE_LOADS: bool = true;

/// A field's identity for [`cse_loads`]: its name and the object (up to
/// unboxing) it is reached through.
type LoadKey = (crate::mir::entity::AtomId, Value);

/// Redundant field loads (§10.1's availability, over the heap): a
/// `load_field` of a field that a dominating `load_field` read, or a
/// `store_field` wrote, through the same object, with no instruction in
/// between whose effects may write that field (any object's: two values
/// may be one object), is the value read or written. It becomes a `jump`
/// to its clean successor with that value. The clean edge only: a load's
/// dirty edge reports the engine ran, and a store's value is the field's
/// only on its clean edge (a setter may have run on the others).
pub fn cse_loads(m: &Module, f: &mut Func) -> usize {
    use crate::mir::module::Region;
    let cfg = Cfg::new(f);
    let mut inst_block = BTreeMap::new();
    for &b in &f.layout {
        for &i in &f.blocks[b].insts {
            inst_block.insert(i, b);
        }
    }
    let mut avail_in: BTreeMap<Block, Option<HashMap<LoadKey, Value>>> = BTreeMap::new();
    for r in &f.roots {
        avail_in.insert(r.block, Some(HashMap::new()));
    }
    let edge_out = |f: &Func, b: Block, avail: &HashMap<LoadKey, Value>| {
        let mut out: Vec<(Block, HashMap<LoadKey, Value>)> = vec![];
        let mut cur = avail.clone();
        let insts = &f.blocks[b].insts;
        for (idx, &i) in insts.iter().enumerate() {
            let d = &f.insts[i];
            let tys: Vec<Type> = d.args.iter().map(|&v| f.values[v].ty).collect();
            let fx = effects(&d.op, &tys, m);
            for w in &fx.writes {
                cur.retain(|(name, _), _| {
                    !w.overlaps(&Region::Field {
                        name: *name,
                        keys: None,
                    })
                });
            }
            if idx + 1 != insts.len() {
                continue;
            }
            for (role, e) in f.succ_edges(i) {
                let mut a = cur.clone();
                if role == SuccRole::OkClean {
                    match d.op {
                        Opcode::LoadField(name) => {
                            if let Some(v) = ok_output(f, e) {
                                a.insert((name, canon(f, d.args[0])), v);
                            }
                        }
                        Opcode::StoreField(name) => {
                            a.insert((name, canon(f, d.args[0])), d.args[1]);
                        }
                        _ => {}
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
    let mut folded = 0;
    for &b in &cfg.rpo.clone() {
        let Some(t) = f.terminator(b) else { continue };
        let d = f.insts[t].clone();
        let Opcode::LoadField(name) = d.op else { continue };
        let clean = d.succs[0].clone();
        let Some(outp) = ok_output(f, &clean) else {
            continue;
        };
        let want = f.values[outp].ty;
        let avail = avail_in.get(&b).cloned().flatten().unwrap_or_default();
        let Some(&v) = avail.get(&(name, canon(f, d.args[0]))) else {
            continue;
        };
        let dominated = def_block(f, v, &inst_block).is_some_and(|db| db != b && cfg.dominates(db, b));
        let vt = f.values[v].ty;
        if !dominated || !(is_subtype(&vt, &want) || vt == want) {
            continue;
        }
        f.blocks[b].insts.pop();
        let args = clean
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
                block: clean.block,
                args,
            }],
        );
        folded += 1;
    }
    folded
}

/// Whether loop-invariant ops are hoisted.
const LICM: bool = true;

/// Loop-invariant code motion (MIR.md §10.2, over effects): a
/// non-terminator in a loop that writes nothing, cannot GC, throw or kill
/// facts, reads only regions no instruction in the loop may write, and
/// whose operands are all defined outside the loop (or hoisted), moves to
/// the end of the loop's preheader. Such an op is safe to run once before
/// the loop even where the loop would not have reached it. Constants stay
/// (nothing to save). Returns how many moved.
pub fn licm(m: &Module, f: &mut Func) -> usize {
    let cfg = Cfg::new(f);
    let mut preds: BTreeMap<Block, Vec<Block>> = BTreeMap::new();
    for &b in &f.layout {
        for s in f.succs(b) {
            preds.entry(s).or_default().push(b);
        }
    }
    let mut inst_block = BTreeMap::new();
    for &b in &f.layout {
        for &i in &f.blocks[b].insts {
            inst_block.insert(i, b);
        }
    }
    let mut moved = 0;
    for l in f.loops.clone() {
        let (h, p) = (l.header, l.preheader);
        // The natural loop: back from the header's in-loop predecessors.
        let mut body: BTreeSet<Block> = BTreeSet::new();
        body.insert(h);
        let mut work: Vec<Block> = preds
            .get(&h)
            .map(|ps| ps.iter().copied().filter(|&q| cfg.dominates(h, q)).collect())
            .unwrap_or_default();
        while let Some(b) = work.pop() {
            if body.insert(b) {
                work.extend(preds.get(&b).into_iter().flatten().copied());
            }
        }
        // An onramp into a loop nested in this one enters its body past
        // the preheader: then nothing can be hoisted there.
        if body.contains(&p) || f.terminator(p).is_none() || !body.iter().all(|&b| cfg.dominates(p, b)) {
            continue;
        }
        let mut writes = vec![];
        for &b in &body {
            for &i in &f.blocks[b].insts {
                let d = &f.insts[i];
                let tys: Vec<Type> = d.args.iter().map(|&v| f.values[v].ty).collect();
                writes.extend(effects(&d.op, &tys, m).writes);
            }
        }
        let mut hoisted: BTreeSet<Value> = BTreeSet::new();
        let outside = |v: Value, hoisted: &BTreeSet<Value>| {
            hoisted.contains(&v)
                || match f.values[v].def {
                    ValueDef::Param(b, _) => !body.contains(&b),
                    ValueDef::Result(i, _) => inst_block.get(&i).is_some_and(|b| !body.contains(b)),
                    ValueDef::Unused => false,
                }
        };
        let frame = f.inst_frame[f.terminator(p).unwrap()];
        let mut picks: Vec<(Block, Inst)> = vec![];
        for &b in cfg.rpo.iter().filter(|b| body.contains(b)) {
            for &i in &f.blocks[b].insts {
                let d = &f.insts[i];
                if !d.succs.is_empty() || d.op.is_terminator() {
                    continue;
                }
                if matches!(d.op, Opcode::ConstVal(_) | Opcode::ConstI32(_) | Opcode::ConstF64(_) | Opcode::ConstBool(_)) {
                    continue;
                }
                // An inlined callee's frame exists only once entered: its
                // frame-relative ops stay in it.
                if f.inst_frame[i] != frame {
                    continue;
                }
                let tys: Vec<Type> = d.args.iter().map(|&v| f.values[v].ty).collect();
                let fx = effects(&d.op, &tys, m);
                let quiet = fx.writes.is_empty() && !fx.may_gc && !fx.may_throw && !fx.may_run_js && fx.kill.is_empty();
                if !quiet || fx.reads.iter().any(|r| writes.iter().any(|w| w.overlaps(r))) {
                    continue;
                }
                if !matches!(fx.flags, crate::mir::ops::FlagsEffect::Bits(b) if b == crate::mir::ops::FlagBits::NONE) {
                    continue;
                }
                if !d.args.iter().all(|&v| outside(v, &hoisted)) {
                    continue;
                }
                // A managed result live across the whole loop is rooted at
                // each of its GC points: only the environment reads, whose
                // reload is the saving.
                let env_read = matches!(d.op, Opcode::EnvCurrent | Opcode::EnvParent | Opcode::EnvLoad(_));
                if !env_read && d.results.iter().any(|&r| f.values[r].ty.repr().is_managed()) {
                    continue;
                }
                hoisted.extend(d.results.iter().copied());
                picks.push((b, i));
            }
        }
        for (b, i) in picks {
            f.blocks[b].insts.retain(|&x| x != i);
            let pos = f.blocks[p].insts.len() - 1;
            f.blocks[p].insts.insert(pos, i);
            inst_block.insert(i, p);
            moved += 1;
        }
    }
    moved
}
