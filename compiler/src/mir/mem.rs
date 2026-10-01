//! Memory optimizations over abstract locations (docs/MIR-MEMORY.md).
//!
//! - [`mem_vn`]: memory versions (the last writer of each location on
//!   every path to a point), value numbering of heap reads by the version
//!   they read, and store-to-load forwarding (§3.1, §3.2).

use std::collections::{BTreeMap, BTreeSet, HashMap};

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
/// memory they read. `load_field` (the IC form) only on its clean edge,
/// `getprop.data` on its `ok` one.
fn vn_read(op: &Opcode) -> bool {
    matches!(
        op,
        Opcode::LoadSlot(_) | Opcode::LoadField(_) | Opcode::GetPropData(_) | Opcode::LengthArray | Opcode::LengthTa
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

/// A use of a value: operand `idx` of an instruction, or argument `arg`
/// of successor edge `succ` of a terminator.
#[derive(Clone, Copy, Debug)]
enum Use {
    Arg(Inst, usize),
    Edge(Inst, usize, usize),
}

/// Every use of every value in the reachable blocks.
fn uses_of(f: &Func, cfg: &Cfg) -> HashMap<Value, Vec<Use>> {
    let mut uses: HashMap<Value, Vec<Use>> = HashMap::new();
    for &b in &cfg.rpo {
        for &i in &f.blocks[b].insts {
            let d = &f.insts[i];
            for (k, &a) in d.args.iter().enumerate() {
                uses.entry(a).or_default().push(Use::Arg(i, k));
            }
            for (s, e) in d.succs.iter().enumerate() {
                for (k, a) in e.args.iter().enumerate() {
                    if let EdgeArg::Value(v) = a {
                        uses.entry(*v).or_default().push(Use::Edge(i, s, k));
                    }
                }
            }
        }
    }
    uses
}

/// Remove param `k` of block `b`, and the argument each edge into `b`
/// passes for it.
fn drop_param(f: &mut Func, b: Block, k: usize) {
    let p = f.blocks[b].params.remove(k);
    f.values[p].def = ValueDef::Unused;
    for (n, &q) in f.blocks[b].params.clone().iter().enumerate() {
        f.values[q].def = ValueDef::Param(b, u32::try_from(n).unwrap());
    }
    for bb in f.layout.clone() {
        if let Some(t) = f.terminator(bb) {
            for e in &mut f.insts[t].succs {
                if e.block == b {
                    e.args.remove(k);
                }
            }
        }
    }
}

/// A field of a virtual object at a point: not yet added, one value on
/// every path, or different values on different paths.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum FieldState {
    Absent,
    Val(Value),
    Conflict,
}

/// The fields of one virtual object at a point, in row order.
fn meet_fields(a: &[FieldState], b: &[FieldState]) -> Vec<FieldState> {
    a.iter().zip(b).map(|(&x, &y)| if x == y { x } else { FieldState::Conflict }).collect()
}

/// Scalar replacement of literal objects that do not escape
/// (MIR-MEMORY.md §5). An object `lit.new` made, all of whose uses are its
/// inits and stamp, slot loads and slotted stores through it, guards its
/// allocation proves, conversions, retaining frame stores and the operands
/// of exits (in any frame), and block params that only
/// it reaches, does not exist at run time: each field is the value last
/// stored, each load that value, and each exit that has it as an operand
/// rebuilds it first from the fields added so far. (A `frame.store` only
/// retains a local for the GC; an exit carries the frame's live locals.)
/// Returns how many objects it replaced.
pub fn sroa(m: &Module, f: &mut Func) -> usize {
    let mut n = 0;
    loop {
        let cfg = Cfg::new(f);
        let allocs: Vec<Inst> = cfg
            .rpo
            .iter()
            .filter_map(|&b| f.terminator(b))
            .filter(|&t| matches!(f.insts[t].op, Opcode::LitNew(_)))
            .collect();
        let mut any = false;
        for t in allocs {
            if replace_one(m, f, &cfg, t) {
                n += 1;
                any = true;
                // The CFG changed under the rest.
                break;
            }
        }
        if !any {
            return n;
        }
    }
}

/// `sroa` for the object allocation `t` makes, if it does not escape.
fn replace_one(m: &Module, f: &mut Func, cfg: &Cfg, t: Inst) -> bool {
    use crate::mir::ops::UnboxKind;
    use crate::mir::types::{ObjKind, TagSet};
    let d = f.insts[t].clone();
    let Opcode::LitNew(nslots) = d.op else { return false };
    let ok = d.succs[0].clone();
    let Some(k0) = ok.args.iter().position(|a| *a == EdgeArg::Out(0)) else { return false };
    let obj = f.blocks[ok.block].params[k0];
    let mut preds: BTreeMap<Block, Vec<Inst>> = BTreeMap::new();
    for &b in &cfg.rpo {
        if let Some(tt) = f.terminator(b) {
            for e in &f.insts[tt].succs {
                preds.entry(e.block).or_default().push(tt);
            }
        }
    }
    if preds.get(&ok.block).map(Vec::as_slice) != Some(&[t]) {
        return false;
    }
    // An allocation on an exit's path (one this pass rebuilt) is where it
    // is needed already: every path from it only inits and leaves.
    let mut tail = BTreeSet::new();
    let mut work = vec![ok.block];
    let mut exit_only = true;
    while let Some(b) = work.pop() {
        if !tail.insert(b) {
            continue;
        }
        match f.terminator(b).map(|x| f.insts[x].op) {
            // (Another object's rebuild may precede the same exit.)
            Some(Opcode::LitNew(_) | Opcode::LitInit(..) | Opcode::Jump) => work.extend(f.succs(b)),
            Some(Opcode::Exit { .. } | Opcode::ExitThrow { .. } | Opcode::Unreachable) => {}
            _ => {
                exit_only = false;
                break;
            }
        }
    }
    if exit_only {
        return false;
    }
    let uses = uses_of(f, cfg);
    // The object's values and uses, classified; any other use escapes it.
    let mut vals: BTreeSet<Value> = BTreeSet::from([obj]);
    let mut work = vec![obj];
    let mut word: Option<u32> = None;
    let mut key: Option<crate::ids::LayoutKey> = None;
    let (mut stamps, mut inits, mut stores, mut loads, mut guards, mut convs, mut fstores) =
        (vec![], vec![], vec![], vec![], vec![], vec![], vec![]);
    let mut exits: BTreeSet<Inst> = BTreeSet::new();
    let mut layout_guards: Vec<(Inst, crate::mir::types::KeyRange)> = vec![];
    // Uses that would expose the object: they escape it where they can
    // run (below).
    let mut escapes: Vec<Inst> = vec![];
    while let Some(u) = work.pop() {
        for &us in uses.get(&u).map(Vec::as_slice).unwrap_or(&[]) {
            match us {
                Use::Arg(i, idx) => {
                    let di = &f.insts[i];
                    let formals = f.frame_shape(f.inst_frame[i]).formals;
                    let add = |v: Value, vals: &mut BTreeSet<Value>, work: &mut Vec<Value>| {
                        if vals.insert(v) {
                            work.push(v);
                        }
                    };
                    match di.op {
                        Opcode::Unbox(UnboxKind::Obj) | Opcode::Box | Opcode::Weaken => {
                            convs.push(i);
                            add(di.results[0], &mut vals, &mut work);
                        }
                        Opcode::GuardUnbox(UnboxKind::Obj) | Opcode::GuardTags(_) | Opcode::GuardKind(_) | Opcode::GuardLayout { .. } => {
                            let passes = match di.op {
                                Opcode::GuardTags(tags) => TagSet::OBJECT.subset_of(tags),
                                Opcode::GuardKind(k) => matches!(k, ObjKind::Plain | ObjKind::Native | ObjKind::Any),
                                Opcode::GuardLayout { keys, types, .. } => {
                                    layout_guards.push((i, keys));
                                    !types
                                }
                                _ => true,
                            };
                            if !passes {
                                escapes.push(i);
                                continue;
                            }
                            guards.push(i);
                            if let Some(v) = ok_output(f, &di.succs[0]) {
                                add(v, &mut vals, &mut work);
                            }
                        }
                        Opcode::StampFresh(w) => {
                            word = Some(w);
                            stamps.push(i);
                        }
                        Opcode::LitInit(_, k) if idx == 0 => {
                            key = Some(k);
                            inits.push(i);
                        }
                        Opcode::StoreField(name)
                            if idx == 0
                                && f.values[di.args[0]].ty.obj_info().is_some_and(|o| slot_of(o, name, m).is_some()) =>
                        {
                            stores.push(i)
                        }
                        Opcode::LoadSlot(_) => loads.push(i),
                        // A retaining store (in its frame; a mapped formal's
                        // is the `arguments` object's slot, which is real).
                        Opcode::FrameStore(k) if k > formals => fstores.push(i),
                        // Exits of any frame: an inlined callee's writes its
                        // frame, and finishes it in baseline.
                        Opcode::Exit { .. } | Opcode::ExitThrow { .. } | Opcode::ExitInline { .. } => {
                            exits.insert(i);
                        }
                        _ => escapes.push(i),
                    }
                }
                Use::Edge(i, s, a) => {
                    let p = f.blocks[f.insts[i].succs[s].block].params[a];
                    if vals.insert(p) {
                        work.push(p);
                    }
                }
            }
        }
    }
    let (Some(word), Some(key)) = (word, key) else { return false };
    if layout_guards.iter().any(|(_, keys)| !keys.contains(&crate::mir::types::KeyRange::one(key))) {
        return false;
    }
    // Where the code can go if the object does not escape: its guards
    // pass (the class word its allocation wrote is the one they test, and
    // nothing else can reach the object to change it). Uses only their
    // failures reach do not count; if none of the rest escapes it, the
    // assumption holds.
    let mut inst_block: BTreeMap<Inst, Block> = BTreeMap::new();
    for &b in &cfg.rpo {
        for &i in &f.blocks[b].insts {
            inst_block.insert(i, b);
        }
    }
    let mut reach: BTreeSet<Block> = BTreeSet::new();
    let mut work: Vec<Block> = f.roots.iter().map(|r| r.block).collect();
    while let Some(b) = work.pop() {
        if !reach.insert(b) {
            continue;
        }
        match f.terminator(b) {
            Some(tt) if guards.contains(&tt) => work.push(f.insts[tt].succs[0].block),
            _ => work.extend(f.succs(b)),
        }
    }
    let live = |i: &Inst| reach.contains(&inst_block[i]);
    if escapes.iter().any(live) {
        return false;
    }
    for v in [&mut stamps, &mut inits, &mut stores, &mut loads, &mut guards, &mut convs, &mut fstores] {
        v.retain(live);
    }
    exits.retain(live);
    // A param is the object only where every edge into it passes it; a
    // root's params come from the frame.
    for &v in &vals {
        if let ValueDef::Param(b, k) = f.values[v].def {
            if v == obj {
                continue;
            }
            if f.roots.iter().any(|r| r.block == b) {
                return false;
            }
            for &p in preds.get(&b).map(Vec::as_slice).unwrap_or(&[]) {
                if !live(&p) {
                    continue;
                }
                for e in f.insts[p].succs.iter().filter(|e| e.block == b) {
                    match e.args[k as usize] {
                        EdgeArg::Value(x) if vals.contains(&x) => {}
                        EdgeArg::Out(_) if is_guard(&f.insts[p].op) && guards.contains(&p) => {}
                        _ => return false,
                    }
                }
            }
        }
    }
    if f.loops.iter().any(|l| l.entry.as_ref().is_some_and(|e| e.state.iter().any(|v| vals.contains(v)))) {
        return false;
    }
    // The row: the inits' names, in order; each once.
    let mut row: Vec<crate::mir::entity::AtomId> = vec![];
    let rpo_pos: BTreeMap<Block, usize> = cfg.rpo.iter().enumerate().map(|(i, &b)| (b, i)).collect();
    let mut ordered_inits = inits.clone();
    ordered_inits.sort_by_key(|i| rpo_pos[&inst_block[i]]);
    for &i in &ordered_inits {
        let Opcode::LitInit(name, _) = f.insts[i].op else { unreachable!() };
        if row.contains(&name) {
            return false;
        }
        row.push(name);
    }
    let field_ix = |name| row.iter().position(|&r| r == name);
    // Field states, forward over the blocks the allocation dominates.
    // What a terminator's edge `s` adds: an init's or store's value.
    let edge_def = |f: &Func, i: Inst, s: usize| -> Option<(usize, Value)> {
        let di = &f.insts[i];
        match di.op {
            Opcode::LitInit(name, _) if s == 0 && inits.contains(&i) => field_ix(name).map(|x| (x, di.args[1])),
            Opcode::StoreField(name) if s < 2 && stores.contains(&i) => field_ix(name).map(|x| (x, di.args[1])),
            _ => None,
        }
    };
    let mut ins: BTreeMap<Block, Vec<FieldState>> = BTreeMap::new();
    ins.insert(ok.block, vec![FieldState::Absent; row.len()]);
    let mut changed = true;
    while changed {
        changed = false;
        for &b in &cfg.rpo {
            if !cfg.dominates(ok.block, b) || !reach.contains(&b) {
                continue;
            }
            let Some(st) = ins.get(&b).cloned() else { continue };
            for &i in &f.blocks[b].insts {
                for (s, e) in f.insts[i].succs.iter().enumerate() {
                    let mut s2 = st.clone();
                    if let Some((x, v)) = edge_def(f, i, s) {
                        s2[x] = FieldState::Val(v);
                    }
                    let merged = match ins.get(&e.block) {
                        None => s2,
                        Some(old) => meet_fields(old, &s2),
                    };
                    if ins.get(&e.block) != Some(&merged) {
                        ins.insert(e.block, merged);
                        changed = true;
                    }
                }
            }
        }
    }
    // Check every load and exit against the states, and plan.
    let mut subst: BTreeMap<Value, Value> = BTreeMap::new();
    let mut mats: Vec<(Inst, Vec<Value>)> = vec![];
    for &b in &cfg.rpo {
        if !cfg.dominates(ok.block, b) || !reach.contains(&b) {
            continue;
        }
        let Some(st) = ins.get(&b) else { continue };
        for &i in &f.blocks[b].insts {
            let di = &f.insts[i];
            if loads.contains(&i) {
                let Opcode::LoadSlot(name) = di.op else { unreachable!() };
                let Some(FieldState::Val(v)) = field_ix(name).map(|x| st[x]) else { return false };
                let r = di.results[0];
                if !(is_subtype(&f.values[v].ty, &f.values[r].ty) || f.values[v].ty == f.values[r].ty) {
                    return false;
                }
                subst.insert(r, v);
            }
            if exits.contains(&i) {
                // The fields added so far: a prefix of the row.
                let fv: Vec<Value> = st
                    .iter()
                    .map_while(|s| match *s {
                        FieldState::Val(v) => Some(v),
                        _ => None,
                    })
                    .collect();
                if st[fv.len()..].iter().any(|s| *s != FieldState::Absent) {
                    return false;
                }
                mats.push((i, fv));
            }
        }
    }
    // Rewrite. Exits first: they read the fields.
    let unreachable = f.add_block();
    f.add_inst(unreachable, Opcode::Unreachable, vec![], &[], vec![]);
    for (e, fv) in mats {
        let b = inst_block[&e];
        let pos = f.blocks[b].insts.iter().position(|&x| x == e).unwrap();
        let tail: Vec<Inst> = f.blocks[b].insts.split_off(pos);
        debug_assert_eq!(tail, vec![e]);
        let frame = f.inst_frame[e];
        let first = f.insts.len();
        let mut cur = b;
        let nb = f.add_block();
        let mv = f.add_param(nb, Type::val(TagSet::OBJECT));
        f.add_inst(cur, Opcode::LitNew(nslots), vec![], &[], vec![
            Edge { block: nb, args: vec![EdgeArg::Out(0)] },
            Edge { block: unreachable, args: vec![] },
        ]);
        cur = nb;
        f.add_inst(cur, Opcode::StampFresh(word), vec![mv], &[], vec![]);
        for (x, &v) in fv.iter().enumerate() {
            let next = f.add_block();
            f.add_inst(cur, Opcode::LitInit(row[x], key), vec![mv, v], &[], vec![
                Edge { block: next, args: vec![] },
                Edge { block: unreachable, args: vec![] },
            ]);
            cur = next;
        }
        for a in &mut f.insts[e].args {
            if vals.contains(a) {
                *a = mv;
            }
        }
        f.blocks[cur].insts.push(e);
        for k in first..f.insts.len() {
            f.inst_frame[Inst::from_u32(u32::try_from(k).unwrap())] = frame;
        }
    }
    // The object's params go (and the arguments edges pass them).
    let params: Vec<(Block, Value)> = vals
        .iter()
        .filter_map(|&v| match f.values[v].def {
            ValueDef::Param(b, _) => Some((b, v)),
            _ => None,
        })
        .collect();
    for (b, v) in params {
        if let Some(k) = f.blocks[b].params.iter().position(|&p| p == v) {
            drop_param(f, b, k);
        }
    }
    // Terminators through the object become jumps to their success edge.
    for &i in inits.iter().chain(&stores).chain(&guards).chain(std::iter::once(&t)) {
        let b = inst_block[&i];
        let e = f.insts[i].succs[0].clone();
        let frame = f.inst_frame[i];
        let pos = f.blocks[b].insts.iter().position(|&x| x == i).unwrap();
        f.blocks[b].insts.remove(pos);
        let (j, _) = f.add_inst(b, Opcode::Jump, vec![], &[], vec![e]);
        f.inst_frame[j] = frame;
    }
    // And the rest of its uses go.
    let dead: BTreeSet<Inst> = stamps.iter().chain(&convs).chain(&fstores).chain(&loads).copied().collect();
    for b in f.layout.clone() {
        f.blocks[b].insts.retain(|i| !dead.contains(i));
    }
    replace_values(f, &subst);
    for &v in &vals {
        f.values[v].def = ValueDef::Unused;
    }
    // What only the guards' failures reached is dead, and may still name
    // the object's values: nothing left in it.
    for b in f.layout.clone() {
        if cfg.reachable(b) && !reach.contains(&b) {
            f.blocks[b].insts.clear();
            f.add_inst(b, Opcode::Unreachable, vec![], &[], vec![]);
        }
    }
    true
}
