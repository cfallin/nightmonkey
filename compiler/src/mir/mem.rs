//! Memory optimizations over abstract locations (docs/MIR-MEMORY.md).
//!
//! - [`mem_vn`]: memory versions (the last writer of each location on
//!   every path to a point), value numbering of heap reads by the version
//!   they read, and store-to-load forwarding (§3.1, §3.2).

use std::collections::{BTreeMap, HashMap};

use crate::mir::entity::{Block, Inst, Value};
use crate::mir::func::{Edge, EdgeArg, Func, ValueDef};
use crate::mir::module::{Module, Region};
use crate::mir::ops::{effects, slot_of, Effects, Opcode, SuccRole};
use crate::mir::opt::{def_block, is_guard, ok_output, replace_values, Cfg};
use crate::mir::types::{is_subtype, Type};

/// What last wrote a location, on every path to a point: nothing since
/// the function's entry, one instruction, or different writers on
/// different paths into a block.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Version {
    Entry,
    Inst(Inst),
    Phi(Block),
}

/// The heap reads `mem_vn` numbers: a function of their receiver and the
/// memory they read. `load_field` (the IC form) only on its clean edge.
fn vn_read(op: &Opcode) -> bool {
    matches!(
        op,
        Opcode::LoadSlot(_) | Opcode::LoadField(_) | Opcode::LengthArray | Opcode::LengthTa
    )
}

/// The locations an instruction writes, on its successor edge `role`
/// (`None`: a non-terminator). A dirty or err edge reports that the
/// engine ran something the op's summary does not cover (a getter, a
/// setter): it writes `Unknown`, except a `store_field` whose receiver
/// proves the slot, whose dirty edge only demoted the class's TYPES.
pub(crate) fn writes_on(f: &Func, m: &Module, i: Inst, fx: &Effects, role: Option<SuccRole>) -> Vec<Region> {
    let d = &f.insts[i];
    match role {
        Some(SuccRole::OkDirty | SuccRole::Err) => {
            let slotted_store = match d.op {
                Opcode::StoreField(name) => {
                    f.values[d.args[0]].ty.obj_info().is_some_and(|o| slot_of(o, name, m).is_some())
                }
                _ => false,
            };
            if slotted_store && role == Some(SuccRole::OkDirty) {
                fx.writes.clone()
            } else {
                vec![Region::Unknown]
            }
        }
        _ => fx.writes.clone(),
    }
}

/// The object a value is, up to representation and proof: through
/// `unbox`, `box`, `weaken`, and a guard's output (a param of a block
/// whose only way in is that guard's `ok` edge). Two values with one root
/// are one object.
fn root(f: &Func, mut v: Value, preds: &BTreeMap<Block, Vec<Inst>>) -> Value {
    for _ in 0..64 {
        match f.values[v].def {
            ValueDef::Result(i, 0) if matches!(f.insts[i].op, Opcode::Unbox(_) | Opcode::Box | Opcode::Weaken) => {
                v = f.insts[i].args[0];
            }
            ValueDef::Param(b, k) => {
                let Some(&[t]) = preds.get(&b).map(|p| p.as_slice()) else {
                    return v;
                };
                let d = &f.insts[t];
                let into: Vec<&Edge> = d.succs.iter().filter(|e| e.block == b).collect();
                if into.len() != 1 {
                    return v;
                }
                match (into[0].args.get(k as usize), d.args.first()) {
                    (Some(EdgeArg::Out(0)), Some(&a)) if is_guard(&d.op) || matches!(d.op, Opcode::GuardCtor { .. }) => {
                        v = a;
                    }
                    _ => return v,
                }
            }
            _ => return v,
        }
    }
    v
}

/// The allocation instruction that made `v`'s root, if one did: a fresh
/// object no value defined before it can be.
fn alloc_of(f: &Func, r: Value, preds: &BTreeMap<Block, Vec<Inst>>) -> Option<Inst> {
    let ValueDef::Param(b, k) = f.values[r].def else { return None };
    let &[t] = preds.get(&b)?.as_slice() else { return None };
    let d = &f.insts[t];
    let fresh = matches!(
        d.op,
        Opcode::JsRt(crate::mir::ops::RtOp::NewObject(_) | crate::mir::ops::RtOp::NewArray(_))
            | Opcode::LitNew(_)
            | Opcode::CreateThis(..)
            | Opcode::JsLambda(_)
            | Opcode::ArgsObject
            | Opcode::RestArray(_)
    );
    let e = d.succs.iter().find(|e| e.block == b)?;
    (fresh && e.args.get(k as usize) == Some(&EdgeArg::Out(0))).then_some(t)
}

/// Memory value numbering (MIR-MEMORY.md §3.1, §3.2).
///
/// A forward dataflow gives each location a function's heap reads touch
/// its version at every point: the last writer on every path, or the
/// block where paths with different writers meet. A read is keyed by its
/// op, its receiver's root and the versions of what it reads; a repeat
/// whose first occurrence dominates it is that value. A `load_slot` or
/// `load_field` whose version is a slotted `store_field` or `init_field`
/// through the same object takes the stored value; past a store through a
/// receiver that cannot be the same object (a fresh allocation made after
/// the load's receiver was defined), it asks the version before that
/// store. Returns how many reads it removed.
pub fn mem_vn(m: &Module, f: &mut Func) -> usize {
    let cfg = Cfg::new(f);
    let mut inst_block: BTreeMap<Inst, Block> = BTreeMap::new();
    let mut preds: BTreeMap<Block, Vec<Inst>> = BTreeMap::new();
    for &b in &f.layout {
        for &i in &f.blocks[b].insts {
            inst_block.insert(i, b);
        }
        if let Some(t) = f.terminator(b) {
            for e in &f.insts[t].succs {
                let p = preds.entry(e.block).or_default();
                if !p.contains(&t) {
                    p.push(t);
                }
            }
        }
    }
    // The locations the numbered reads touch.
    let mut locs: Vec<Region> = vec![];
    let fx_of = |f: &Func, i: Inst| {
        let d = &f.insts[i];
        let tys: Vec<Type> = d.args.iter().map(|&v| f.values[v].ty).collect();
        effects(&d.op, &tys, m)
    };
    for &b in &cfg.rpo {
        for &i in &f.blocks[b].insts {
            if vn_read(&f.insts[i].op) {
                for r in fx_of(f, i).reads {
                    if !locs.contains(&r) {
                        locs.push(r);
                    }
                }
            }
        }
    }
    if locs.is_empty() {
        return 0;
    }
    // Per block, the versions on entry.
    let apply = |st: &mut Vec<Version>, ws: &[Region], i: Inst, prev: &mut Option<&mut HashMap<(Inst, usize), Version>>| {
        for w in ws {
            for (k, l) in locs.iter().enumerate() {
                if w.overlaps(l) {
                    if let Some(p) = prev.as_deref_mut() {
                        p.entry((i, k)).or_insert(st[k]);
                    }
                    st[k] = Version::Inst(i);
                }
            }
        }
    };
    let mut ins: BTreeMap<Block, Vec<Version>> = BTreeMap::new();
    for r in &f.roots {
        ins.insert(r.block, vec![Version::Entry; locs.len()]);
    }
    let mut changed = true;
    while changed {
        changed = false;
        for &b in &cfg.rpo {
            let Some(mut st) = ins.get(&b).cloned() else { continue };
            let insts = f.blocks[b].insts.clone();
            for &i in &insts {
                let fx = fx_of(f, i);
                if f.insts[i].succs.is_empty() {
                    apply(&mut st, &writes_on(f, m, i, &fx, None), i, &mut None);
                    continue;
                }
                for (role, e) in f.succ_edges(i) {
                    let mut s2 = st.clone();
                    apply(&mut s2, &writes_on(f, m, i, &fx, Some(role)), i, &mut None);
                    let merged = match ins.get(&e.block) {
                        None => s2,
                        Some(old) => old
                            .iter()
                            .zip(&s2)
                            .map(|(&a, &b2)| if a == b2 { a } else { Version::Phi(e.block) })
                            .collect(),
                    };
                    if ins.get(&e.block) != Some(&merged) {
                        ins.insert(e.block, merged);
                        changed = true;
                    }
                }
            }
        }
    }
    // Rewrite: walk each block from its entry versions.
    type Key = (Opcode, Value, Vec<Version>);
    let mut first: HashMap<Key, (Value, Block)> = HashMap::new();
    let mut prev: HashMap<(Inst, usize), Version> = HashMap::new();
    let mut subst: BTreeMap<Value, Value> = BTreeMap::new();
    let mut jumps: Vec<(Block, Inst, Value)> = vec![];
    // First pass: the versions each store replaced (for the clobber walk).
    for &b in &cfg.rpo {
        let Some(mut st) = ins.get(&b).cloned() else { continue };
        for &i in &f.blocks[b].insts {
            let fx = fx_of(f, i);
            // A terminator ends the block: its first edge's writes (the
            // clean one's) are the ones a version walk past it asks for.
            let ws = writes_on(f, m, i, &fx, f.insts[i].op.roles().first().copied());
            apply(&mut st, &ws, i, &mut Some(&mut prev));
        }
    }
    let loc_of = |f: &Func, i: Inst| -> Vec<usize> {
        let fx = fx_of(f, i);
        fx.reads.iter().filter_map(|r| locs.iter().position(|l| l == r)).collect()
    };
    let mut removed = 0;
    for &b in &cfg.rpo {
        let Some(mut st) = ins.get(&b).cloned() else { continue };
        for &i in &f.blocks[b].insts.clone() {
            let d = f.insts[i].clone();
            if vn_read(&d.op) {
                // The value this read produces: its result, or a
                // `load_field`'s clean output.
                let out = if d.succs.is_empty() {
                    d.results.first().copied()
                } else {
                    ok_output(f, &d.succs[0])
                };
                let recv = root(f, d.args[0], &preds);
                let ks = loc_of(f, i);
                let vs: Vec<Version> = ks.iter().map(|&k| st[k]).collect();
                // Forwarding from a store through the same object.
                let mut known: Option<Value> = None;
                if let (Opcode::LoadSlot(name) | Opcode::LoadField(name), [k]) = (d.op, ks.as_slice()) {
                    let mut v = st[*k];
                    for _ in 0..32 {
                        let Version::Inst(s) = v else { break };
                        let sd = &f.insts[s];
                        let stored = match sd.op {
                            Opcode::StoreField(n) | Opcode::InitField(n) if n == name => {
                                let slotted = f.values[sd.args[0]].ty.obj_info().is_some_and(|o| slot_of(o, n, m).is_some());
                                slotted.then(|| (sd.args[0], sd.args[1]))
                            }
                            // A literal's own property, which the load
                            // reads wherever it finds it.
                            Opcode::LitInit(n, _) if n == name => Some((sd.args[0], sd.args[1])),
                            _ => None,
                        };
                        let Some((srecv, sval)) = stored else { break };
                        let sroot = root(f, srecv, &preds);
                        if sroot == recv {
                            known = Some(sval);
                            break;
                        }
                        let fresh_after = alloc_of(f, sroot, &preds).is_some_and(|a| {
                            let ab = inst_block[&a];
                            def_block(f, recv, &inst_block).is_some_and(|rb| rb != ab && cfg.dominates(rb, ab))
                        });
                        if !fresh_after {
                            break;
                        }
                        match prev.get(&(s, *k)) {
                            Some(&p) => v = p,
                            None => break,
                        }
                    }
                }
                if let (Some(out), Some(val)) = (out, known) {
                    if is_subtype(&f.values[val].ty, &f.values[out].ty) || f.values[val].ty == f.values[out].ty {
                        if d.succs.is_empty() {
                            subst.insert(out, val);
                        } else {
                            jumps.push((b, i, val));
                        }
                        removed += 1;
                        continue;
                    }
                }
                if let Some(out) = out {
                    let key = (d.op.clone(), recv, vs);
                    match first.get(&key) {
                        Some(&(v, vb))
                            if v != out
                                && (vb == b || cfg.dominates(vb, b))
                                && (is_subtype(&f.values[v].ty, &f.values[out].ty) || f.values[v].ty == f.values[out].ty)
                                && f.values[v].ty.killable_components().is_empty() =>
                        {
                            if d.succs.is_empty() {
                                subst.insert(out, v);
                            } else {
                                jumps.push((b, i, v));
                            }
                            removed += 1;
                        }
                        Some(_) => {}
                        None => {
                            let ob = def_block(f, out, &inst_block).unwrap_or(b);
                            first.insert(key, (out, ob));
                        }
                    }
                }
            }
            let fx = fx_of(f, i);
            let ws = writes_on(f, m, i, &fx, d.op.roles().first().copied());
            apply(&mut st, &ws, i, &mut None);
        }
    }
    // Terminator reads (`load_field`) become jumps to their clean edge.
    for (b, t, v) in jumps {
        let d = f.insts[t].clone();
        let clean = d.succs[0].clone();
        let frame = f.inst_frame[t];
        f.blocks[b].insts.pop();
        let args = clean
            .args
            .iter()
            .map(|a| match a {
                EdgeArg::Out(0) => EdgeArg::Value(v),
                a => *a,
            })
            .collect();
        let (j, _) = f.add_inst(b, Opcode::Jump, vec![], &[], vec![Edge { block: clean.block, args }]);
        f.inst_frame[j] = frame;
    }
    replace_values(f, &subst);
    removed
}

