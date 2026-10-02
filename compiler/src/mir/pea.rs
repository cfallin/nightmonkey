//! Partial escape analysis of literal objects (MIR-MEMORY.md §10, the
//! owner's "materialize once").
//!
//! A `lit.new` object that `sroa` cannot replace because it escapes
//! somewhere stays virtual until it escapes: on every path, the first
//! escape materializes it (a `lit.new`, its stamp and its inits of the
//! fields' current values), and from there on it is that one real object:
//! every later use, every later escape and every exit gets the same
//! reference (identity is observable). Before it, its field reads are the
//! values last written, its guards pass, and an exit rebuilds it, as
//! `sroa`'s do. A merge of a virtual path and a real one materializes on
//! the virtual edge.
//!
//! The ops inserted are infallible (a pass has no frame state to exit
//! with): the allocation, stamp and inits (their err edges, an OOM, are
//! unreachable as `sroa`'s rebuilds' are) and a typed view of the object
//! (its layout claim, asserted: the object was just made with it). The
//! view stays typed until an op or a fence edge kills a component of it
//! (the call it escaped into may reshape it); from there it is weakened to
//! what no kill touches. Real code keeps its own loads, stores and guards,
//! through the real object; `promote` then caches what loops read and
//! write.
//!
//! v1 limits, each declining the object: a field that has different values
//! on different paths where it is needed (no field params yet), an escape
//! before every field is added, an object meeting another value at a
//! param.

use std::collections::{BTreeMap, BTreeSet};

use crate::mir::entity::{Block, Inst, Value};
use crate::mir::func::{Edge, EdgeArg, Func, ValueDef};
use crate::mir::module::Module;
use crate::mir::ops::{effects, signature, slot_of, KillSite, Opcode, SuccRole, UnboxKind};
use crate::mir::opt::{ok_output, replace_values, Cfg};
use crate::mir::types::{is_subtype, KeyRange, KillPattern, LayoutClaim, LayoutState, ObjKind, TagSet, Type};

/// Allocations `pea` examines per function. Each attempt scans the whole
/// function, so a function with hundreds of literals (a jit-test's 16k
/// instructions grew to 39k) would take minutes; `promote` has the same cap.
const MAX_TRIES: usize = 64;

/// Run over the function's `lit.new`s (up to `MAX_TRIES`), in reverse
/// postorder; returns how many objects it made partially virtual.
pub fn pea(m: &Module, f: &mut Func) -> usize {
    let mut n = 0;
    let mut tried: BTreeSet<Inst> = BTreeSet::new();
    // A declined object changes nothing, so the CFG (and the candidates
    // in its order) holds until one is rewritten.
    let mut cfg: Option<Cfg> = None;
    for _ in 0..MAX_TRIES {
        let c = cfg.get_or_insert_with(|| Cfg::new(f));
        let Some(t) = c
            .rpo
            .iter()
            .filter_map(|&b| f.terminator(b))
            .find(|&t| matches!(f.insts[t].op, Opcode::LitNew(_)) && !tried.contains(&t))
        else {
            break;
        };
        tried.insert(t);
        let before = f.insts.len();
        if pea_one(m, f, c, t, &mut tried) {
            n += 1;
            cfg = None;
        }
        // The objects it materializes are real from their birth: trying
        // them again would virtualize what it just materialized.
        tried.extend((before..f.insts.len()).map(|k| Inst::from_u32(u32::try_from(k).unwrap())));
    }
    n
}

/// A field's value at a point of the virtual part.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Field {
    Absent,
    Val(Value),
    Conflict,
}

fn meet(a: &[Field], b: &[Field]) -> Vec<Field> {
    a.iter().zip(b).map(|(&x, &y)| if x == y { x } else { Field::Conflict }).collect()
}

/// What a use of the object is.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum UseKind {
    Init,
    Stamp,
    Load,
    Store,
    /// A guard its allocation passes (output: an alias).
    Guard,
    /// `unbox`/`box`/`weaken` (result: an alias).
    Conv,
    FrameStore,
    /// An exit that does not return: rebuilt while virtual.
    Exit,
    /// `inline.enter`: a frame slot, overwritten by the callee's exits.
    Enter,
    Escape,
}

#[allow(clippy::too_many_lines)]
fn pea_one(m: &Module, f: &mut Func, cfg: &Cfg, t: Inst, tried: &mut BTreeSet<Inst>) -> bool {
    let d = f.insts[t].clone();
    let Opcode::LitNew(nslots) = d.op else { return false };
    let ok = d.succs[0].clone();
    let Some(k0) = ok.args.iter().position(|a| *a == EdgeArg::Out(0)) else { return false };
    let obj = f.blocks[ok.block].params[k0];
    let mut preds: BTreeMap<Block, Vec<Inst>> = BTreeMap::new();
    let mut bpreds: BTreeMap<Block, Vec<Block>> = BTreeMap::new();
    for &b in &cfg.rpo {
        if let Some(tt) = f.terminator(b) {
            for e in &f.insts[tt].succs {
                let p = preds.entry(e.block).or_default();
                if !p.contains(&tt) {
                    p.push(tt);
                }
                let q = bpreds.entry(e.block).or_default();
                if !q.contains(&b) {
                    q.push(b);
                }
            }
        }
    }
    if preds.get(&ok.block).map(Vec::as_slice) != Some(&[t]) {
        return false;
    }
    let mut inst_block: BTreeMap<Inst, Block> = BTreeMap::new();
    for &b in &cfg.rpo {
        for &i in &f.blocks[b].insts {
            inst_block.insert(i, b);
        }
    }
    // The object's aliases and their uses.
    let mut uses_of: BTreeMap<Value, Vec<(Inst, usize)>> = BTreeMap::new();
    let mut edge_uses: BTreeMap<Value, Vec<(Inst, usize, usize)>> = BTreeMap::new();
    for &b in &cfg.rpo {
        for &i in &f.blocks[b].insts {
            for (k, &a) in f.insts[i].args.iter().enumerate() {
                uses_of.entry(a).or_default().push((i, k));
            }
            for (s, e) in f.insts[i].succs.iter().enumerate() {
                for (k, a) in e.args.iter().enumerate() {
                    if let EdgeArg::Value(v) = a {
                        edge_uses.entry(*v).or_default().push((i, s, k));
                    }
                }
            }
        }
    }
    let mut vals: BTreeSet<Value> = BTreeSet::from([obj]);
    let mut work = vec![obj];
    let mut kinds: BTreeMap<Inst, UseKind> = BTreeMap::new();
    let mut word = None;
    let mut key = None;
    let mut layout_guard_ok = true;
    while let Some(u) = work.pop() {
        for &(i, idx) in uses_of.get(&u).map(Vec::as_slice).unwrap_or(&[]) {
            let di = &f.insts[i];
            let add = |v: Value, vals: &mut BTreeSet<Value>, work: &mut Vec<Value>| {
                if vals.insert(v) {
                    work.push(v);
                }
            };
            let formals = f.frame_shape(f.inst_frame[i]).formals;
            let kind = match di.op {
                Opcode::Unbox(UnboxKind::Obj) | Opcode::Box | Opcode::Weaken => {
                    add(di.results[0], &mut vals, &mut work);
                    UseKind::Conv
                }
                Opcode::GuardUnbox(UnboxKind::Obj) | Opcode::GuardTags(_) | Opcode::GuardKind(_) | Opcode::GuardLayout { .. } => {
                    let passes = match di.op {
                        Opcode::GuardTags(tags) => TagSet::OBJECT.subset_of(tags),
                        Opcode::GuardKind(k) => matches!(k, ObjKind::Plain | ObjKind::Native | ObjKind::Any),
                        Opcode::GuardLayout { types, .. } => !types,
                        _ => true,
                    };
                    if let Opcode::GuardLayout { keys, .. } = di.op {
                        if key.is_some_and(|k| !keys.contains(&KeyRange::one(k))) {
                            layout_guard_ok = false;
                        }
                    }
                    if passes {
                        if let Some(v) = ok_output(f, &di.succs[0]) {
                            add(v, &mut vals, &mut work);
                        }
                        UseKind::Guard
                    } else {
                        UseKind::Escape
                    }
                }
                Opcode::StampFresh(w) => {
                    word = Some(w);
                    UseKind::Stamp
                }
                Opcode::LitInit(_, k) if idx == 0 => {
                    key = Some(k);
                    UseKind::Init
                }
                Opcode::StoreSlot(name) | Opcode::StoreField(name)
                    if idx == 0 && f.values[di.args[0]].ty.obj_info().is_some_and(|o| slot_of(o, name, m).is_some()) =>
                {
                    UseKind::Store
                }
                Opcode::LoadSlot(_) => UseKind::Load,
                Opcode::FrameStore(k) if k > formals => UseKind::FrameStore,
                Opcode::Exit { .. } | Opcode::ExitThrow { .. } => UseKind::Exit,
                Opcode::InlineEnter => UseKind::Enter,
                _ => UseKind::Escape,
            };
            // An op using the object twice keeps the strongest reading.
            let e = kinds.entry(i).or_insert(kind);
            if kind == UseKind::Escape {
                *e = UseKind::Escape;
            }
        }
        for &(i, s, k) in edge_uses.get(&u).map(Vec::as_slice).unwrap_or(&[]) {
            let p = f.blocks[f.insts[i].succs[s].block].params[k];
            if vals.insert(p) {
                work.push(p);
            }
        }
    }
    let (Some(word), Some(key)) = (word, key) else { return false };
    if !layout_guard_ok {
        return false;
    }
    // A param is the object only where every edge into it passes an alias.
    for &v in &vals {
        if let ValueDef::Param(b, k) = f.values[v].def {
            if v == obj {
                continue;
            }
            if f.roots.iter().any(|r| r.block == b) {
                return false;
            }
            for &p in preds.get(&b).map(Vec::as_slice).unwrap_or(&[]) {
                for e in f.insts[p].succs.iter().filter(|e| e.block == b) {
                    match e.args[k as usize] {
                        EdgeArg::Value(x) if vals.contains(&x) => {}
                        EdgeArg::Out(_) if kinds.get(&p) == Some(&UseKind::Guard) => {}
                        _ => return false,
                    }
                }
            }
        }
    }
    if f.loops.iter().any(|l| l.entry.as_ref().is_some_and(|e| e.state.iter().any(|v| vals.contains(v)))) {
        return false;
    }
    let escapes: BTreeSet<Inst> = kinds.iter().filter(|(_, k)| **k == UseKind::Escape).map(|(&i, _)| i).collect();
    if escapes.is_empty() {
        // `sroa`'s case (or something it declined for its own reasons).
        return false;
    }
    // The region: blocks the allocation dominates, reachable with its
    // guards passing.
    let mut region: BTreeSet<Block> = BTreeSet::new();
    let mut work: Vec<Block> = vec![ok.block];
    while let Some(b) = work.pop() {
        if !cfg.dominates(ok.block, b) || !region.insert(b) {
            continue;
        }
        match f.terminator(b) {
            Some(tt) if kinds.get(&tt) == Some(&UseKind::Guard) => work.push(f.insts[tt].succs[0].block),
            _ => work.extend(f.succs(b)),
        }
    }
    // Every use is in it (one past it would see a stale object).
    if kinds.keys().any(|i| inst_block.get(i).is_none_or(|b| !region.contains(b)) && !escapes.contains(i)) {
        return false;
    }
    if escapes.iter().any(|i| inst_block.get(i).is_none_or(|b| !region.contains(b))) {
        return false;
    }
    // Phases: real once any path in has escaped.
    let rpo: Vec<Block> = cfg.rpo.iter().copied().filter(|b| region.contains(b)).collect();
    let mut real_in: BTreeMap<Block, bool> = BTreeMap::new();
    let mut real_out: BTreeMap<Block, bool> = BTreeMap::new();
    let mut changed = true;
    while changed {
        changed = false;
        for &b in &rpo {
            let rin = b != ok.block
                && bpreds.get(&b).into_iter().flatten().any(|p| region.contains(p) && real_out.get(p).copied().unwrap_or(false));
            let rout = rin || f.blocks[b].insts.iter().any(|i| escapes.contains(i));
            if real_in.get(&b) != Some(&rin) || real_out.get(&b) != Some(&rout) {
                real_in.insert(b, rin);
                real_out.insert(b, rout);
                changed = true;
            }
        }
    }
    // Entries into the region's real part from outside it: none (the
    // region is what the allocation dominates).
    // Field values over the virtual part (as `sroa`'s): the row from the
    // inits, in order.
    let mut row = vec![];
    let rpo_pos: BTreeMap<Block, usize> = cfg.rpo.iter().enumerate().map(|(i, &b)| (b, i)).collect();
    let mut inits: Vec<Inst> = kinds.iter().filter(|(_, k)| **k == UseKind::Init).map(|(&i, _)| i).collect();
    inits.sort_by_key(|i| (rpo_pos[&inst_block[i]], f.blocks[inst_block[i]].insts.iter().position(|x| x == i)));
    for &i in &inits {
        let Opcode::LitInit(name, _) = f.insts[i].op else { unreachable!() };
        if row.contains(&name) {
            return false;
        }
        row.push(name);
    }
    let field_ix = |name| row.iter().position(|&r| r == name);
    let def_of = |f: &Func, i: Inst, s: Option<usize>| -> Option<(usize, Value)> {
        let di = &f.insts[i];
        match (kinds.get(&i), di.op) {
            (Some(UseKind::Init), Opcode::LitInit(name, _)) if s == Some(0) => field_ix(name).map(|x| (x, di.args[1])),
            (Some(UseKind::Store), Opcode::StoreField(name)) if s.is_some_and(|s| s < 2) => {
                field_ix(name).map(|x| (x, di.args[1]))
            }
            (Some(UseKind::Store), Opcode::StoreSlot(name)) if s.is_none() => field_ix(name).map(|x| (x, di.args[1])),
            _ => None,
        }
    };
    let mut fin: BTreeMap<Block, Vec<Field>> = BTreeMap::new();
    fin.insert(ok.block, vec![Field::Absent; row.len()]);
    let mut changed = true;
    while changed {
        changed = false;
        for &b in &rpo {
            if real_in[&b] {
                continue;
            }
            let Some(mut st) = fin.get(&b).cloned() else { continue };
            for &i in &f.blocks[b].insts {
                if escapes.contains(&i) {
                    break;
                }
                if let Some((x, v)) = def_of(f, i, None) {
                    st[x] = Field::Val(v);
                }
                for (s, e) in f.insts[i].succs.iter().enumerate() {
                    if !region.contains(&e.block) || real_in[&e.block] {
                        continue;
                    }
                    let mut s2 = st.clone();
                    if let Some((x, v)) = def_of(f, i, Some(s)) {
                        s2[x] = Field::Val(v);
                    }
                    let merged = match fin.get(&e.block) {
                        None => s2,
                        Some(old) => meet(old, &s2),
                    };
                    if fin.get(&e.block) != Some(&merged) {
                        fin.insert(e.block, merged);
                        changed = true;
                    }
                }
            }
        }
    }
    // Plan the virtual part: each load's value, each exit's fields, and
    // the fields at each materialization (an escape, or an edge into the
    // real part). Every one needs a value on every path.
    let full = |st: &[Field]| -> Option<Vec<Value>> {
        st.iter()
            .map(|s| match *s {
                Field::Val(v) => Some(v),
                _ => None,
            })
            .collect()
    };
    let mut subst: BTreeMap<Value, Value> = BTreeMap::new();
    let mut exits_virtual: Vec<(Inst, Vec<Value>)> = vec![];
    // (block, index of the escape inst in it) -> fields
    let mut mats_at: Vec<(Block, Inst, Vec<Value>)> = vec![];
    // (pred terminator, succ index) -> fields
    let mut mats_edge: Vec<(Inst, usize, Vec<Value>)> = vec![];
    let mut virtual_work = 0usize;
    for &b in &rpo {
        if real_in[&b] {
            continue;
        }
        let Some(st0) = fin.get(&b) else { return false };
        let mut st = st0.clone();
        for &i in &f.blocks[b].insts {
            if escapes.contains(&i) {
                let Some(fv) = full(&st) else { return false };
                mats_at.push((b, i, fv));
                break;
            }
            if let Some((x, v)) = def_of(f, i, None) {
                st[x] = Field::Val(v);
                virtual_work += 1;
            }
            let di = &f.insts[i];
            match kinds.get(&i) {
                Some(UseKind::Load) => {
                    let Opcode::LoadSlot(name) = di.op else { unreachable!() };
                    let Some(Field::Val(v)) = field_ix(name).map(|x| st[x]) else { return false };
                    let r = di.results[0];
                    if !(is_subtype(&f.values[v].ty, &f.values[r].ty) || f.values[v].ty == f.values[r].ty) {
                        return false;
                    }
                    subst.insert(r, v);
                    virtual_work += 1;
                }
                Some(UseKind::Store) if di.op.is_terminator() => virtual_work += 1,
                Some(UseKind::Exit) => {
                    // The fields added so far: a prefix of the row.
                    let fv: Vec<Value> = st
                        .iter()
                        .map_while(|s| match *s {
                            Field::Val(v) => Some(v),
                            _ => None,
                        })
                        .collect();
                    if st[fv.len()..].iter().any(|s| *s != Field::Absent) {
                        return false;
                    }
                    exits_virtual.push((i, fv));
                    virtual_work += 1;
                }
                _ => {}
            }
            for (s, e) in di.succs.iter().enumerate() {
                if region.contains(&e.block) && real_in[&e.block] {
                    let mut s2 = st.clone();
                    if let Some((x, v)) = def_of(f, i, Some(s)) {
                        s2[x] = Field::Val(v);
                    }
                    let Some(fv) = full(&s2) else { return false };
                    mats_edge.push((i, s, fv));
                }
            }
        }
        // A virtual path that ends (a return, an exit without the object)
        // saved the allocation.
        if !real_out[&b] && f.succs(b).iter().all(|s| !region.contains(s)) {
            virtual_work += 1;
        }
    }
    // Nothing virtual to gain: the object escapes right after its inits
    // (as this pass's own materializations do).
    if virtual_work == 0 {
        return false;
    }
    // Real uses of aliases defined in the virtual part are replaced by the
    // materialized object, as a boxed value or its typed view.
    let defined_virtual = |f: &Func, v: Value| -> bool {
        let b = match f.values[v].def {
            ValueDef::Param(b, _) => Some(b),
            ValueDef::Result(i, _) => inst_block.get(&i).copied(),
            ValueDef::Unused => None,
        };
        b.is_some_and(|b| region.contains(&b) && !real_in[&b])
            && match f.values[v].def {
                // An alias defined after its block's escape is real.
                ValueDef::Result(i, _) => {
                    let b = inst_block[&i];
                    let pos = f.blocks[b].insts.iter().position(|&x| x == i).unwrap();
                    !f.blocks[b].insts[..pos].iter().any(|x| escapes.contains(x))
                }
                _ => true,
            }
    };
    let vvals: BTreeSet<Value> = vals.iter().copied().filter(|&v| defined_virtual(f, v)).collect();
    // The typed view the materialization's asserts give: an object, plain,
    // of the literal's layout (TYPES as its stamp has it).
    let val_ty = Type::val(TagSet::OBJECT);
    let claim = LayoutClaim {
        keys: KeyRange::one(key),
        types: word & crate::wasm::bbv::abi::CLASS_WORD_SHALLOW != 0,
        slots: true,
        state: LayoutState::Published,
    };
    let g_unbox = Opcode::GuardUnbox(UnboxKind::Obj);
    let g_kind = Opcode::GuardKind(ObjKind::Plain);
    let g_layout = Opcode::GuardLayout { keys: claim.keys, types: claim.types, slots: true };
    let Ok(o_ty) = signature(&g_unbox, &[val_ty], m).map(|s| s.outputs[0]) else { return false };
    let Ok(p_ty) = signature(&g_kind, &[o_ty], m).map(|s| s.outputs[0]) else { return false };
    let Ok(typed_ty) = signature(&g_layout, &[p_ty], m).map(|s| s.outputs[0]) else { return false };
    // Every real use's type must admit what replaces it.
    for &v in &vvals {
        let ty = f.values[v].ty;
        if !(is_subtype(&val_ty, &ty) || is_subtype(&typed_ty, &ty)) {
            return false;
        }
    }

    // Where the typed view holds: from each materialization until an op
    // or a fence edge kills a component of it (a call the object escaped
    // into may change its layout). Past that the real part carries the
    // view weakened to what no kill touches; a real block any stale path
    // reaches gets that one.
    let weak_ty = typed_ty.weakened(&KillPattern::ALL);
    let starts: Vec<(Block, usize)> = rpo
        .iter()
        .filter_map(|&b| {
            if real_in[&b] {
                return Some((b, 0));
            }
            let (_, i, _) = mats_at.iter().find(|(mb, _, _)| *mb == b)?;
            Some((b, f.blocks[b].insts.iter().position(|x| x == i).unwrap()))
        })
        .collect();
    let mut fresh: BTreeMap<Block, bool> = starts.iter().filter(|(b, _)| real_in[b]).map(|&(b, _)| (b, true)).collect();
    loop {
        let mut changed = false;
        for &(b, start) in &starts {
            let mut fr = fresh.get(&b).copied().unwrap_or(true);
            for &i in &f.blocks[b].insts[start..] {
                let (op_kill, edge_kill) = kills(m, f, i, &typed_ty);
                fr &= !op_kill;
                for (s, e) in f.insts[i].succs.iter().enumerate() {
                    if fresh.get(&e.block) == Some(&true) && !(fr && !edge_kill[s]) {
                        fresh.insert(e.block, false);
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    // Every real use's type must admit the value or the view it gets.
    let admits = |f: &Func, v: Value, fr: bool| -> bool {
        let ty = f.values[v].ty;
        is_subtype(&val_ty, &ty) || is_subtype(if fr { &typed_ty } else { &weak_ty }, &ty)
    };
    for &(b, start) in &starts {
        let mut fr = fresh.get(&b).copied().unwrap_or(true);
        for &i in &f.blocks[b].insts[start..] {
            let d = &f.insts[i];
            if d.args.iter().any(|&a| vvals.contains(&a) && !admits(f, a, fr)) {
                return false;
            }
            let (op_kill, edge_kill) = kills(m, f, i, &typed_ty);
            fr &= !op_kill;
            for (s, e) in d.succs.iter().enumerate() {
                let efr = fr && !edge_kill[s];
                let bad = e.args.iter().any(|a| matches!(a, EdgeArg::Value(v) if vvals.contains(v) && !admits(f, *v, efr)));
                if bad {
                    return false;
                }
            }
        }
    }

    // Blocks outside the region with an edge into its real part: none but
    // unreachable ones (which go).
    let real_set: BTreeSet<Block> = rpo.iter().copied().filter(|b| real_in[b]).collect();
    let strays: Vec<Block> = f
        .layout
        .iter()
        .copied()
        .filter(|&b| !region.contains(&b) && f.succs(b).iter().any(|s| real_set.contains(s)))
        .collect();
    if strays.iter().any(|&b| cfg.reachable(b)) {
        return false;
    }

    // --- Rewrite. ---
    for &b in &strays {
        f.blocks[b].insts.clear();
        f.add_inst(b, Opcode::Unreachable, vec![], &[], vec![]);
    }
    let unreachable = f.add_block();
    f.add_inst(unreachable, Opcode::Unreachable, vec![], &[], vec![]);
    // Materialize at the end of block `b` (which has no terminator yet),
    // with fields `fv`: returns the block to continue in and (value, view).
    // With `typed`, the asserts that give the view follow; without (an
    // exit's rebuild, which needs only the object), it is `sroa`'s own
    // rebuild, which `sroa` then leaves alone.
    let materialize = |f: &mut Func, b: Block, fv: &[Value], frame: u32, typed: bool| -> (Block, Value, Value) {
        let first = f.insts.len();
        let nb = f.add_block();
        let mv = f.add_param(nb, val_ty);
        f.add_inst(b, Opcode::LitNew(nslots), vec![], &[], vec![
            Edge { block: nb, args: vec![EdgeArg::Out(0)] },
            Edge { block: unreachable, args: vec![] },
        ]);
        let mut cur = nb;
        f.add_inst(cur, Opcode::StampFresh(word), vec![mv], &[], vec![]);
        for (x, &v) in fv.iter().enumerate() {
            let next = f.add_block();
            f.add_inst(cur, Opcode::LitInit(row[x], key), vec![mv, v], &[], vec![
                Edge { block: next, args: vec![] },
                Edge { block: unreachable, args: vec![] },
            ]);
            cur = next;
        }
        if !typed {
            for k in first..f.insts.len() {
                f.inst_frame[Inst::from_u32(u32::try_from(k).unwrap())] = frame;
            }
            return (cur, mv, mv);
        }
        let ob = f.add_block();
        let o = f.add_param(ob, o_ty);
        f.add_inst(cur, g_unbox, vec![mv], &[], vec![
            Edge { block: ob, args: vec![EdgeArg::Out(0)] },
            Edge { block: unreachable, args: vec![] },
        ]);
        let pb = f.add_block();
        let po = f.add_param(pb, p_ty);
        f.add_inst(ob, g_kind, vec![o], &[], vec![
            Edge { block: pb, args: vec![EdgeArg::Out(0)] },
            Edge { block: unreachable, args: vec![] },
        ]);
        let tb = f.add_block();
        let mt = f.add_param(tb, typed_ty);
        f.add_inst(pb, g_layout, vec![po], &[], vec![
            Edge { block: tb, args: vec![EdgeArg::Out(0)] },
            Edge { block: unreachable, args: vec![] },
        ]);
        for k in first..f.insts.len() {
            f.inst_frame[Inst::from_u32(u32::try_from(k).unwrap())] = frame;
        }
        (tb, mv, mt)
    };
    // The real part's (value, view) on entry to each of its blocks: params.
    let real_blocks: Vec<Block> = rpo.iter().copied().filter(|b| real_in[b]).collect();
    let mut entry: BTreeMap<Block, (Value, Value)> = BTreeMap::new();
    for &b in &real_blocks {
        let pv = f.add_param(b, val_ty);
        let pt = f.add_param(b, if fresh[&b] { typed_ty } else { weak_ty });
        entry.insert(b, (pv, pt));
    }
    // Escapes in virtual blocks: split the block there, materialize.
    // (the value, and the view each edge of the block's terminator passes)
    let mut cur_out: BTreeMap<Block, (Value, Vec<Value>)> = BTreeMap::new();
    for (b, i, fv) in &mats_at {
        let pos = f.blocks[*b].insts.iter().position(|x| x == i).unwrap();
        let tail: Vec<Inst> = f.blocks[*b].insts.split_off(pos);
        let frame = f.inst_frame[*i];
        let (tb, mv, mt) = materialize(f, *b, fv, frame, true);
        // The rest of the block continues after the materialization.
        f.blocks[tb].insts.extend(tail.iter().copied());
        // Uses in the tail: real.
        let views = rewrite_real(m, f, tb, &vvals, mv, mt, weak_ty);
        for &x in &f.blocks[tb].insts {
            inst_block.insert(x, tb);
        }
        cur_out.insert(tb, (mv, views));
    }
    // Virtual-to-real edges: materialize on the edge.
    for (i, s, fv) in &mats_edge {
        let e = f.insts[*i].succs[*s].clone();
        let nb = f.add_block();
        // The edge's args through params of the target's types, but where
        // the target's param is the object: the real one.
        let mut new_args = vec![];
        let mut fwd: Vec<Option<Value>> = vec![];
        for (k, a) in e.args.iter().enumerate() {
            let tp = f.blocks[e.block].params[k];
            if vals.contains(&tp) {
                fwd.push(None);
                continue;
            }
            let ty = f.values[tp].ty;
            let p = f.add_param(nb, ty);
            new_args.push(*a);
            fwd.push(Some(p));
        }
        let frame = f.inst_frame[*i];
        let (tb, mv, mt) = materialize(f, nb, fv, frame, true);
        let mut args: Vec<EdgeArg> = vec![];
        for (k, p) in fwd.iter().enumerate() {
            match p {
                Some(p) => args.push(EdgeArg::Value(*p)),
                None => {
                    let tp = f.blocks[e.block].params[k];
                    let r = if is_subtype(&typed_ty, &f.values[tp].ty) { mt } else { mv };
                    args.push(EdgeArg::Value(r));
                }
            }
        }
        args.push(EdgeArg::Value(mv));
        args.push(EdgeArg::Value(mt));
        let (j, _) = f.add_inst(tb, Opcode::Jump, vec![], &[], vec![Edge { block: e.block, args }]);
        f.inst_frame[j] = frame;
        f.insts[*i].succs[*s] = Edge { block: nb, args: new_args };
        // An alias passed on that edge (a virtual param's arg) is now
        // real: through `fwd`'s params into an alias param, which the
        // real part rewrites below.
    }
    // Real blocks: their uses, and their edges into real blocks.
    for &b in &real_blocks {
        let (mv, mt) = entry[&b];
        let views = rewrite_real(m, f, b, &vvals, mv, mt, weak_ty);
        for &x in &f.blocks[b].insts {
            inst_block.insert(x, b);
        }
        cur_out.insert(b, (mv, views));
    }
    // Every edge into a real block from inside the region passes the
    // current (value, view); edges from the materialization blocks were
    // made above.
    for b in f.layout.clone() {
        let Some(tt) = f.terminator(b) else { continue };
        let Some((mv, views)) = cur_out.get(&b) else { continue };
        let mv = *mv;
        let views = views.clone();
        for (s, e) in f.insts[tt].succs.iter_mut().enumerate() {
            if entry.contains_key(&e.block) && e.args.len() + 2 == f.blocks[e.block].params.len() {
                e.args.push(EdgeArg::Value(mv));
                e.args.push(EdgeArg::Value(views[s]));
            }
        }
    }
    // The virtual part: exits rebuild (as `sroa`'s), field ops go, guards
    // pass.
    for (e, fv) in exits_virtual {
        let b = inst_block[&e];
        let pos = f.blocks[b].insts.iter().position(|&x| x == e).unwrap();
        let tail: Vec<Inst> = f.blocks[b].insts.split_off(pos);
        let frame = f.inst_frame[e];
        let (tb, mv, _) = materialize(f, b, &fv, frame, false);
        for a in &mut f.insts[e].args {
            if vvals.contains(a) {
                *a = mv;
            }
        }
        f.blocks[tb].insts.extend(tail);
    }
    let virtual_inst = |f: &Func, i: Inst, inst_block: &BTreeMap<Inst, Block>| -> bool {
        inst_block.get(&i).is_some_and(|b| region.contains(b) && !real_in.get(b).copied().unwrap_or(true))
            && !f.blocks[inst_block[&i]].insts.is_empty()
    };
    let mut dead: BTreeSet<Inst> = BTreeSet::new();
    let mut to_jump: Vec<Inst> = vec![t];
    for (&i, &k) in &kinds {
        if escapes.contains(&i) || !virtual_inst(f, i, &inst_block) {
            continue;
        }
        if !f.blocks[inst_block[&i]].insts.contains(&i) {
            continue;
        }
        match k {
            UseKind::Init | UseKind::Guard => to_jump.push(i),
            UseKind::Store if f.insts[i].op.is_terminator() => to_jump.push(i),
            UseKind::Store | UseKind::Stamp | UseKind::Conv | UseKind::Load | UseKind::FrameStore => {
                dead.insert(i);
            }
            UseKind::Enter => {
                // The callee's frame slot: a placeholder (its exits write
                // their own operands).
                let undef = f.add_inst(inst_block[&i], Opcode::ConstVal(crate::mir::ops::ConstVal::Undefined), vec![], &[Type::val(TagSet::prims(crate::opsem::PRIM_UNDEFINED))], vec![]).1[0];
                let b = inst_block[&i];
                f.blocks[b].insts.pop();
                let pos = f.blocks[b].insts.iter().position(|&x| x == i).unwrap();
                let ci = match f.values[undef].def {
                    ValueDef::Result(ci, _) => ci,
                    _ => unreachable!(),
                };
                f.blocks[b].insts.insert(pos, ci);
                for a in &mut f.insts[i].args {
                    if vvals.contains(a) {
                        *a = undef;
                    }
                }
            }
            _ => {}
        }
    }
    for i in to_jump {
        let Some(&b) = inst_block.get(&i) else { continue };
        let Some(pos) = f.blocks[b].insts.iter().position(|&x| x == i) else { continue };
        let e = f.insts[i].succs[0].clone();
        let frame = f.inst_frame[i];
        f.blocks[b].insts.remove(pos);
        let (j, _) = f.add_inst(b, Opcode::Jump, vec![], &[], vec![e]);
        f.inst_frame[j] = frame;
    }
    for b in f.layout.clone() {
        f.blocks[b].insts.retain(|i| !dead.contains(i));
    }
    replace_values(f, &subst);
    // Virtual aliases that are params: dropped (every edge passed one).
    let params: Vec<(Block, Value)> = vvals
        .iter()
        .filter_map(|&v| match f.values[v].def {
            ValueDef::Param(b, _) => Some((b, v)),
            _ => None,
        })
        .collect();
    for (b, v) in params {
        if let Some(k) = f.blocks[b].params.iter().position(|&p| p == v) {
            crate::mir::mem::drop_param(f, b, k);
        }
    }
    for &v in &vvals {
        f.values[v].def = ValueDef::Unused;
    }
    tried.insert(t);
    true
}

/// Replace, in block `b`, uses of the virtual part's aliases by the real
/// object: its view where the use's type admits it, else its value. The
/// view is `vw` until an op or a fence edge kills a component of it; a
/// `weaken` before that op gives what survives. Returns the view each of
/// the terminator's edges passes.
#[allow(clippy::too_many_arguments)]
fn rewrite_real(m: &Module, f: &mut Func, b: Block, vvals: &BTreeSet<Value>, mv: Value, mut vw: Value, weak_ty: Type) -> Vec<Value> {
    let pick = |f: &Func, v: Value, vw: Value| -> Value {
        if is_subtype(&f.values[vw].ty, &f.values[v].ty) {
            vw
        } else {
            mv
        }
    };
    let mut out = vec![];
    let mut k = 0;
    while k < f.blocks[b].insts.len() {
        let i = f.blocks[b].insts[k];
        let args = f.insts[i].args.clone();
        for (x, a) in args.iter().enumerate() {
            if vvals.contains(a) {
                f.insts[i].args[x] = pick(f, *a, vw);
            }
        }
        let vty = f.values[vw].ty;
        let (op_kill, edge_kill) = kills(m, f, i, &vty);
        let mut weak = vw;
        if op_kill || edge_kill.iter().any(|&x| x) {
            let (wi, rs) = f.add_inst(b, Opcode::Weaken, vec![vw], &[weak_ty], vec![]);
            f.blocks[b].insts.pop();
            f.blocks[b].insts.insert(k, wi);
            f.inst_frame[wi] = f.inst_frame[i];
            k += 1;
            weak = rs[0];
        }
        if op_kill {
            vw = weak;
        }
        let succs = f.insts[i].succs.clone();
        for (s, e) in succs.iter().enumerate() {
            let ev = if edge_kill[s] { weak } else { vw };
            for (x, a) in e.args.iter().enumerate() {
                if let EdgeArg::Value(v) = a {
                    if vvals.contains(v) {
                        f.insts[i].succs[s].args[x] = EdgeArg::Value(pick(f, *v, ev));
                    }
                }
            }
            out.push(ev);
        }
        k += 1;
    }
    out
}

/// Whether `i` kills a component of `ty`: at the op (for everything after
/// it), and per edge (a fence: the edge its kill site names, and err).
fn kills(m: &Module, f: &Func, i: Inst, ty: &Type) -> (bool, Vec<bool>) {
    let d = &f.insts[i];
    let tys: Vec<Type> = d.args.iter().map(|&a| f.values[a].ty).collect();
    let fx = effects(&d.op, &tys, m);
    let n = d.succs.len();
    if !fx.kill.matches(ty) {
        return (false, vec![false; n]);
    }
    let fence = match d.op.kill_site(&fx) {
        KillSite::Op => return (true, vec![false; n]),
        KillSite::None => return (false, vec![false; n]),
        KillSite::OkEdge => SuccRole::Ok,
        KillSite::DirtyEdge => SuccRole::OkDirty,
    };
    let roles = d.op.roles();
    let edges = (0..n).map(|s| roles.get(s).is_some_and(|&r| r == fence || r == SuccRole::Err)).collect();
    (false, edges)
}
