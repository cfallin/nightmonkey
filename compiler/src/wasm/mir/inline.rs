//! Inlining by splicing (docs/MIR.md §5.5): a callee's MIR, built on its
//! own, copied into the caller at a call site.
//!
//! The callee keeps a real baseline-format frame (an inline frame), kept
//! current by write-through, so each of its exits becomes an
//! `exit.inline`: finish the callee in its baseline body, then continue
//! the caller. Its throws, which nothing in it catches, go straight to the
//! call's exception edge. Its `return`s become edges to the call's
//! continuation, and its onramp roots are dropped (the copy is entered
//! only at the call).

use std::collections::{BTreeMap, BTreeSet};

use crate::mir;
use crate::mir::entity::{AtomId, Block, FuseId, Inst, Value};
use crate::mir::func::{Edge, EdgeArg, Func, InlineFrame, LoopDecl, RootKind};
use crate::mir::module::{FieldDef, Module};
use crate::mir::ops::Opcode;
use crate::mir::types::{FactKind, StrInfo, Type};

/// A callee built for inlining: its module and function, and its frame's
/// deepest operand stack.
pub(crate) struct Callee {
    pub mm: Module,
    pub f: Func,
    pub max_depth: u32,
    /// Whether some op in it may kill facts and continue (a fence): then
    /// the caller's facts do not survive the splice. Without one, every
    /// kill exits (its dirty edge leaves for baseline, and an exit's
    /// rest, run there, reports whether it demoted anything).
    pub fenced: bool,
}

/// The blocks a kill's dirty edge leads to that exit.
fn dirty_exit_blocks(f: &Func, mm: &Module) -> BTreeSet<Block> {
    use mir::ops::KillSite;
    let mut out = BTreeSet::new();
    for &b in &f.layout {
        for &i in &f.blocks[b].insts {
            let d = &f.insts[i];
            let tys: Vec<Type> = d.args.iter().map(|&v| f.ty(v)).collect();
            let fx = mir::ops::effects(&d.op, &tys, mm);
            if d.op.kill_site(&fx) == KillSite::DirtyEdge {
                out.insert(d.succs[1].block);
            }
        }
    }
    out
}

/// Whether `f` has a fence (`Callee::fenced`).
pub(crate) fn fenced(f: &Func, mm: &Module) -> bool {
    use mir::ops::KillSite;
    let exits = |b: Block| {
        f.blocks[b]
            .insts
            .last()
            .is_some_and(|&i| matches!(f.insts[i].op, Opcode::Exit { .. }))
    };
    f.layout.iter().flat_map(|&b| f.blocks[b].insts.iter()).any(|&i| {
        let d = &f.insts[i];
        let tys: Vec<Type> = d.args.iter().map(|&v| f.ty(v)).collect();
        let fx = mir::ops::effects(&d.op, &tys, mm);
        match d.op.kill_site(&fx) {
            KillSite::OkEdge => true,
            KillSite::DirtyEdge => !exits(d.succs[1].block),
            // A fuse write (a caller's fuse facts); publishing kills only
            // claims on the object under construction.
            KillSite::Op => !matches!(d.op, Opcode::PublishLayout),
            KillSite::None => false,
        }
    })
}

/// How the callee's module entities are named in the caller's.
struct Maps {
    atoms: BTreeMap<AtomId, AtomId>,
    fuses: BTreeMap<FuseId, FuseId>,
    /// Where the callee's restamp descriptors start in the caller's table.
    restamp_base: u32,
}

impl Maps {
    fn atom(&self, a: AtomId) -> AtomId {
        self.atoms[&a]
    }

    fn ty(&self, t: Type) -> Result<Type, String> {
        Ok(match t {
            Type::Str(s) => Type::Str(self.str(s)),
            Type::Val(mut v) => {
                v.str = self.str(v.str);
                Type::Val(v)
            }
            Type::Fact(FactKind::Fuse(f)) => Type::Fact(FactKind::Fuse(self.fuses[&f])),
            Type::Fact(_) => return Err("inline: a binding or native fact".into()),
            t => t,
        })
    }

    fn str(&self, s: StrInfo) -> StrInfo {
        StrInfo {
            atom: s.atom.map(|a| self.atom(a)),
        }
    }

    fn op(&self, op: Opcode) -> Result<Opcode, String> {
        use Opcode::*;
        Ok(match op {
            ConstStr(a) => ConstStr(self.atom(a)),
            JsGetProp(a) => JsGetProp(self.atom(a)),
            JsSetProp(a, s) => JsSetProp(self.atom(a), s),
            JsGetName(a) => JsGetName(self.atom(a)),
            JsBindGName(a) => JsBindGName(self.atom(a)),
            JsSetName(a, s) => JsSetName(self.atom(a), s),
            LoadField(a) => LoadField(self.atom(a)),
            StoreField(a) => StoreField(self.atom(a)),
            InitField(a) => InitField(self.atom(a)),
            CheckFuse(f) => CheckFuse(self.fuses[&f]),
            JsRt(mir::ops::RtOp::DelProp(a, s)) => JsRt(mir::ops::RtOp::DelProp(self.atom(a), s)),
            JsRt(mir::ops::RtOp::InitProp(a, t)) => JsRt(mir::ops::RtOp::InitProp(self.atom(a), t)),
            JsRt(mir::ops::RtOp::InitPropGetSet(a, k)) => {
                JsRt(mir::ops::RtOp::InitPropGetSet(self.atom(a), k))
            }
            JsRt(mir::ops::RtOp::Intrinsic(a)) => JsRt(mir::ops::RtOp::Intrinsic(self.atom(a))),
            Restamp(i) => Restamp(self.restamp_base + i),
            ConstObj(_) | GuardSingleton(_) | CheckBinding(_) | CheckNative(_) | LoadGName(_)
            | StoreGName(_) | CallNative(_) => {
                return Err(format!("inline: {} is not remapped", mir::print::mnemonic(&op)))
            }
            op => op,
        })
    }
}

/// Merge the callee's module tables into the caller's, returning how its
/// entities are renamed. Fails where the two describe a layout slot
/// differently.
fn merge_module(mm: &mut Module, k: &Module) -> Result<Maps, String> {
    let mut maps = Maps {
        atoms: BTreeMap::new(),
        fuses: BTreeMap::new(),
        restamp_base: u32::try_from(mm.restamps.len()).unwrap(),
    };
    mm.restamps.extend(k.restamps.iter().copied());
    for (a, s) in k.atoms.iter() {
        maps.atoms.insert(a, mm.intern_atom(s.chars()));
    }
    for (fid, d) in k.fuses.iter() {
        let found = mm.fuses.iter().find(|(_, x)| x.addr == d.addr).map(|(f, _)| f);
        let id = match found {
            Some(f) => f,
            None => mm.fuses.push(d.clone()),
        };
        maps.fuses.insert(fid, id);
    }
    if !k.snap_objs.is_empty() || !k.bindings.is_empty() || !k.natives.is_empty() {
        return Err("inline: snapshot objects, bindings or natives".into());
    }
    for (&key, lay) in &k.layouts {
        let mine = mm.layouts.entry(key).or_default();
        if lay.elements.is_some() && mine.elements.is_some() && lay.elements != mine.elements {
            return Err("inline: array layouts disagree".into());
        }
        if mine.elements.is_none() {
            mine.elements = lay.elements;
        }
        if mine.fields.len() < lay.fields.len() {
            mine.fields.resize(lay.fields.len(), None);
        }
        for (i, fd) in lay.fields.iter().enumerate() {
            let Some(fd) = fd else { continue };
            let def = FieldDef {
                name: maps.atom(fd.name),
                claim: maps.ty(fd.claim)?,
            };
            match &mine.fields[i] {
                None => mine.fields[i] = Some(def),
                Some(x) if *x == def => {}
                Some(_) => return Err("inline: layouts disagree on a field".into()),
            }
        }
    }
    mm.script_addrs.extend(k.script_addrs.iter().map(|(&s, &a)| (s, a)));
    Ok(maps)
}

/// Splice callee `k` into `f` (of module `mm`) at the end of block
/// `enter`, which is not yet terminated, called from frame `parent` with
/// `operands`: callee (an object of `k`'s script), `this`, and one value
/// per formal. Its returns go to `join` (one `Val` param), its exceptions
/// to `err` (no params).
pub(crate) fn splice(
    mm: &mut Module,
    f: &mut Func,
    k: &Callee,
    parent: u32,
    enter: Block,
    operands: &[Value],
    new_target: Option<Value>,
    join: Block,
    dirty: Option<Edge>,
    err: Block,
) -> Result<(), String> {
    let kf = &k.f;
    // Where an exit continues when the callee's rest (or the kill it
    // exits from) may have demoted a class word: the caller's dirty exit,
    // or, if the caller fences here instead, the join.
    let dirty = dirty.unwrap_or(Edge {
        block: join,
        args: vec![EdgeArg::Out(0)],
    });
    let dirty_exits: BTreeSet<Inst> = dirty_exit_blocks(kf, &k.mm)
        .into_iter()
        .filter_map(|b| kf.blocks[b].insts.last().copied())
        .collect();
    if operands.len() != 2 + kf.frame.formals as usize {
        return Err("inline: operands are not callee, this and the formals".into());
    }
    let maps = merge_module(mm, &k.mm)?;
    // Everything that can fail, before `f` changes: every op and type of
    // the copy must remap.
    for (i, d) in kf.insts.iter() {
        let _ = i;
        match d.op {
            Opcode::Return | Opcode::Exit { .. } | Opcode::ExitThrow { .. } => {}
            op => {
                maps.op(op)?;
            }
        }
    }
    for (_, v) in kf.values.iter() {
        maps.ty(v.ty)?;
    }
    // Frames: the callee's own, then its own inlined callees'.
    let base = u32::try_from(f.inline_frames.len()).unwrap() + 1;
    let frame = |j: u32| if j == 0 { base } else { base + j };
    f.inline_frames.push(InlineFrame {
        script: kf.script,
        shape: kf.frame.clone(),
        parent,
        max_depth: k.max_depth,
    });
    for fr in &kf.inline_frames {
        f.inline_frames.push(InlineFrame {
            parent: frame(fr.parent),
            ..fr.clone()
        });
    }
    // The callee's blocks reachable from its entry.
    let entry = kf
        .roots
        .iter()
        .find(|r| r.kind == RootKind::Entry)
        .ok_or("inline: the callee has no entry")?
        .block;
    let mut reach = BTreeSet::new();
    let mut work = vec![entry];
    while let Some(b) = work.pop() {
        if reach.insert(b) {
            work.extend(kf.succs(b));
        }
    }
    let mut bmap: BTreeMap<Block, Block> = BTreeMap::new();
    let mut vmap: BTreeMap<Value, Value> = BTreeMap::new();
    for &b in &kf.layout {
        if !reach.contains(&b) {
            continue;
        }
        let nb = f.add_block();
        for &p in &kf.blocks[b].params {
            let t = maps.ty(kf.values[p].ty)?;
            vmap.insert(p, f.add_param(nb, t));
        }
        bmap.insert(b, nb);
    }
    // Instructions, first without operands or successors (a value may be
    // used in a block laid out before its definition's).
    let mut imap: Vec<(Inst, Inst)> = vec![];
    for &b in &kf.layout {
        if !reach.contains(&b) {
            continue;
        }
        for &i in &kf.blocks[b].insts {
            let d = &kf.insts[i];
            let op = match d.op {
                Opcode::Return => Opcode::Jump,
                Opcode::Exit { pc, nargs, nlocals } => Opcode::ExitInline {
                    pc,
                    nargs,
                    nlocals,
                    throw: false,
                },
                // No handler of an inline-eligible callee covers any pc
                // (it has only loop notes) and its environment needs no
                // unwinding, so its baseline body would only return the
                // error: the exception propagates to the call site.
                Opcode::ExitThrow { .. } => Opcode::Jump,
                op => maps.op(op)?,
            };
            let tys: Vec<Type> = d
                .results
                .iter()
                .map(|&r| maps.ty(kf.values[r].ty))
                .collect::<Result<_, _>>()?;
            let (ni, rs) = f.add_inst(bmap[&b], op, vec![], &tys, vec![]);
            for (&r, &nr) in d.results.iter().zip(&rs) {
                vmap.insert(r, nr);
            }
            f.inst_frame[ni] = frame(kf.inst_frame[i]);
            f.witnesses[ni] = match op {
                Opcode::Jump if matches!(d.op, Opcode::ExitThrow { .. }) => None,
                // Finishing the callee may do anything.
                Opcode::ExitInline { .. } => Some(mir::func::Witness {
                    may_kill: mir::types::KillPattern::ALL,
                }),
                _ => kf.witnesses[i].clone(),
            };
            imap.push((i, ni));
        }
    }
    let val = |v: Value| -> Result<Value, String> {
        vmap.get(&v)
            .copied()
            .ok_or_else(|| format!("inline: {v} is not defined in the copy"))
    };
    for &(i, ni) in &imap {
        let d = &kf.insts[i];
        let args: Vec<Value> = d.args.iter().map(|&v| val(v)).collect::<Result<_, _>>()?;
        let succs: Vec<Edge> = match d.op {
            Opcode::Return => vec![Edge {
                block: join,
                args: vec![EdgeArg::Value(args[0])],
            }],
            Opcode::ExitThrow { .. } => vec![Edge {
                block: err,
                args: vec![],
            }],
            // A kill's dirty exit already saw the demotion the hub's
            // epoch samples would miss: it continues dirty either way.
            Opcode::Exit { .. } if dirty_exits.contains(&i) => vec![
                dirty.clone(),
                dirty.clone(),
                Edge {
                    block: err,
                    args: vec![],
                },
            ],
            Opcode::Exit { .. } => vec![
                Edge {
                    block: join,
                    args: vec![EdgeArg::Out(0)],
                },
                dirty.clone(),
                Edge {
                    block: err,
                    args: vec![],
                },
            ],
            _ => d
                .succs
                .iter()
                .map(|e| {
                    Ok(Edge {
                        block: *bmap
                            .get(&e.block)
                            .ok_or("inline: an edge leaves the callee's reachable blocks")?,
                        args: e
                            .args
                            .iter()
                            .map(|a| match *a {
                                EdgeArg::Value(v) => val(v).map(EdgeArg::Value),
                                EdgeArg::Out(k) => Ok(EdgeArg::Out(k)),
                            })
                            .collect::<Result<_, String>>()?,
                    })
                })
                .collect::<Result<_, String>>()?,
        };
        let nd = &mut f.insts[ni];
        nd.args = if matches!(d.op, Opcode::Return | Opcode::ExitThrow { .. }) {
            vec![]
        } else {
            args
        };
        nd.succs = succs;
    }
    for l in &kf.loops {
        if let (Some(&h), Some(&p)) = (bmap.get(&l.header), bmap.get(&l.preheader)) {
            f.loops.push(LoopDecl {
                header: h,
                preheader: p,
            });
        }
    }
    // Enter: write the callee's frame, then its entry with the operands.
    // A construct's frame also gets its new.target (`inline.enter`'s last
    // operand); the entry's params are callee, this and the formals.
    let mut enter_ops = operands.to_vec();
    enter_ops.extend(new_target);
    let (enter_inst, _) = f.add_inst(enter, Opcode::InlineEnter, enter_ops, &[], vec![]);
    f.inst_frame[enter_inst] = base;
    let (jump, _) = f.add_inst(
        enter,
        Opcode::Jump,
        vec![],
        &[],
        vec![Edge {
            block: bmap[&entry],
            args: operands.iter().map(|&v| EdgeArg::Value(v)).collect(),
        }],
    );
    f.inst_frame[jump] = parent;
    Ok(())
}
