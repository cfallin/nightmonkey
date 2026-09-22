/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! The per-block execution census (`--block-census`): EXECUTED emitted IR
//! per executed bytecode op, by block role.
//!
//! Every other instrument in this tree counts either emitted IR
//! (`--dump-opsize`, `--dump-redundant`) or executed native per function
//! (`nativeprof.sh`). Neither can say how much of what an op's lowering
//! emitted actually RAN: an op's arm bundle is 80-87% of its emitted IR, and
//! an execution takes one path through it. This closes that gap the way the
//! guard census closes the static-vs-dynamic gap for arms: one runtime tick
//! at the head of every block an op's lowering created (and one at the start
//! of the op's tail of its entry block), joined at analysis time to a static
//! record of what that block holds.
//!
//! The block set is the same one `dump_opsize` and `viz_dump_lowering`
//! attribute to the op -- the entry block's tail plus every block created
//! during the op, minus the continuation version blocks the op minted -- so
//! it inherits their under-attribution (an op that appends into an EARLIER
//! op's block is counted for neither). A block that a LATER op fills (the
//! op's fall-through continuation) is counted by that op's own entry tick:
//! within a block, the ticks delimit each op's span.
//!
//! Roles, decided structurally over the op's block set S:
//!   entry  the tail of the block the op started in (ticked always: its
//!          count is the op's execution count);
//!   side   an arm emitted through `side_arm` (steps the track: the miss /
//!          slow arm leaving Opt);
//!   keep   an arm emitted through `side_arm_keep` (leaves on its own edge,
//!          same track);
//!   num    an arm emitted through `side_arm_num` (inline numeric arm);
//!   merge  two or more in-set predecessors;
//!   exit   the block the op ended in (the fall-through lineage);
//!   leave  a hand-rolled arm: single predecessor, branches out of S;
//!   fast   everything else -- the guard chain on the fall-through path.
//!
//! The records are printed at the end of the body, AFTER LICM, so the
//! instruction counts describe the code that ships rather than the code the
//! lowering appended. Each record also says how many of its instructions
//! are DEAD -- pure values (alu, const, box, unbox, reinterpret) no live
//! value, terminator, store or call ever consumes -- because the backend
//! deletes those and an executed-IR count that includes them overstates the
//! native cost. Loads count as live: a wasm load can trap, so the backend
//! keeps it.
//!
//! The tick is a `CallPure` call like the other census ticks: LICM does not
//! hoist it, `value_count()` does not see it, and the runtime keeps one
//! counter per (kind, id). Kind 70; the id is a module-global sequence
//! number, so the join needs nothing but the two stderr streams.

use super::*;
use std::sync::atomic::{AtomicU32, Ordering};

pub(crate) const BLOCK_CENSUS_KIND: u32 = 70;

static NEXT_ID: AtomicU32 = AtomicU32::new(1);

/// Which `side_arm` family emitted an arm block, recorded per op.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ArmKind {
    Side,
    Keep,
    Num,
}

pub(super) struct BlockRec {
    id: u32,
    pc: Pc,
    lpc: Pc,
    op: crate::bytecode::JSOp,
    track: Track,
    spliced: bool,
    blk: Block,
    role: &'static str,
    form: &'static str,
    choke: &'static str,
    tick: Value,
}

impl<'a> Bbv<'a> {
    pub(super) fn note_arm_block(&mut self, blk: Block, kind: ArmKind) {
        if self.opts.instrument.blocks && self.mode == EmitMode::Code {
            self.op_arm_blocks.push((blk, kind));
        }
    }

    /// One tick, inserted at position `pos` of `blk`'s instruction list.
    /// Returns the call value, which names the tick in the block from then
    /// on.
    fn insert_block_tick(&mut self, blk: Block, pos: usize, id: u32) -> Option<Value> {
        let f = self.helpers.census?;
        let before = self.body.values.len();
        let ty = self.body.single_type_list(Type::I32);
        let k = self.body.add_value(ValueDef::Operator(
            Operator::I32Const {
                value: BLOCK_CENSUS_KIND,
            },
            Default::default(),
            ty,
        ));
        let i = self.body.add_value(ValueDef::Operator(
            Operator::I32Const { value: id },
            Default::default(),
            ty,
        ));
        let arg_list = self.body.arg_pool.from_iter([k, i].into_iter());
        let v = self.body.add_value(ValueDef::Operator(
            Operator::Call { function_index: f },
            arg_list,
            ty,
        ));
        let insts = &mut self.body.blocks[blk].insts;
        let pos = pos.min(insts.len());
        insts.insert(pos, k);
        insts.insert(pos + 1, i);
        insts.insert(pos + 2, v);
        self.effects.insert(v, Eff::CallPure);
        self.instrument_values += self.body.values.len() - before;
        self.blockcen_ticks.insert(k, id);
        self.blockcen_ticks.insert(i, id);
        self.blockcen_ticks.insert(v, id);
        Some(v)
    }

    /// Classify and tick every block of the op just lowered. Same arguments
    /// as `dump_opsize`. The records are printed by `flush_block_census`.
    pub(super) fn block_census(
        &mut self,
        op: crate::bytecode::JSOp,
        pc: Pc,
        lpc: Pc,
        entry: (Block, usize),
        first_new: usize,
        spliced: bool,
    ) {
        if self.helpers.census.is_none() {
            return;
        }
        let mut set: HashSet<Block> = HashSet::default();
        set.insert(entry.0);
        for i in first_new..self.body.blocks.len() {
            let b = Block::new(i);
            if !self.ver_blocks.contains(&b) {
                set.insert(b);
            }
        }
        let mut preds: HashMap<Block, u32> = HashMap::default();
        let mut leaves: HashSet<Block> = HashSet::default();
        for &b in &set {
            let mut out_of_set = false;
            self.body.blocks[b].terminator.visit_successors(|s| {
                if set.contains(&s) {
                    *preds.entry(s).or_default() += 1;
                } else {
                    out_of_set = true;
                }
            });
            if out_of_set {
                leaves.insert(b);
            }
        }
        let arms: HashMap<Block, ArmKind> = self.op_arm_blocks.iter().copied().collect();
        let exit = self.cur;
        let mut blocks: Vec<(Block, usize, &'static str)> = vec![(entry.0, entry.1, "entry")];
        for i in first_new..self.body.blocks.len() {
            let b = Block::new(i);
            if !set.contains(&b) {
                continue;
            }
            let role = match arms.get(&b) {
                Some(ArmKind::Side) => "side",
                Some(ArmKind::Keep) => "keep",
                Some(ArmKind::Num) => "num",
                None if preds.get(&b).copied().unwrap_or(0) >= 2 => "merge",
                None if b == exit => "exit",
                None if leaves.contains(&b) => "leave",
                None => "fast",
            };
            blocks.push((b, 0, role));
        }
        let track = self.cur_track;
        let form = self.op_form.unwrap_or("-");
        let choke = self.op_choke.unwrap_or("-");
        for (b, skip, role) in blocks {
            let n = self.body.blocks[b].insts.len().saturating_sub(skip);
            if n == 0 && role != "entry" {
                continue;
            }
            let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
            let Some(tick) = self.insert_block_tick(b, skip, id) else {
                return;
            };
            self.blockcen_recs.push(BlockRec {
                id,
                pc,
                lpc,
                op,
                track,
                spliced,
                blk: b,
                role,
                form,
                choke,
                tick,
            });
        }
    }

    /// Pure values nothing live consumes: the set the backend deletes.
    fn dead_values(&self) -> HashSet<Value> {
        let is_pure = |v: Value| -> bool {
            match &self.body.values[v] {
                ValueDef::Operator(op, _, _) => {
                    let name = format!("{op:?}");
                    let head = name.split_whitespace().next().unwrap_or("");
                    !(head.starts_with("Call")
                        || head.contains("Store")
                        || head.contains("Load")
                        || head.starts_with("Memory")
                        || head.starts_with("Table")
                        || head.starts_with("Global")
                        || head == "Unreachable")
                }
                ValueDef::PickOutput(..) | ValueDef::Alias(_) => true,
                _ => false,
            }
        };
        let mut live: HashSet<Value> = HashSet::default();
        let mut work: Vec<Value> = Vec::new();
        let push = |v: Value, live: &mut HashSet<Value>, work: &mut Vec<Value>| {
            if live.insert(v) {
                work.push(v);
            }
        };
        for (_, blk) in self.body.blocks.entries() {
            for &v in &blk.insts {
                if !is_pure(v) {
                    push(v, &mut live, &mut work);
                }
            }
            let tgt = |t: &BlockTarget, live: &mut HashSet<Value>, work: &mut Vec<Value>| {
                for &a in &t.args {
                    push(a, live, work);
                }
            };
            match &blk.terminator {
                Terminator::Br { target } => tgt(target, &mut live, &mut work),
                Terminator::CondBr {
                    cond,
                    if_true,
                    if_false,
                } => {
                    push(*cond, &mut live, &mut work);
                    tgt(if_true, &mut live, &mut work);
                    tgt(if_false, &mut live, &mut work);
                }
                Terminator::Select {
                    value,
                    targets,
                    default,
                } => {
                    push(*value, &mut live, &mut work);
                    for t in targets {
                        tgt(t, &mut live, &mut work);
                    }
                    tgt(default, &mut live, &mut work);
                }
                Terminator::Return { values } => {
                    for &v in values {
                        push(v, &mut live, &mut work);
                    }
                }
                _ => {}
            }
        }
        while let Some(v) = work.pop() {
            match &self.body.values[v] {
                ValueDef::Operator(_, args, _) => {
                    for &a in &self.body.arg_pool[*args] {
                        push(a, &mut live, &mut work);
                    }
                }
                ValueDef::PickOutput(o, _, _) | ValueDef::Alias(o) => {
                    push(*o, &mut live, &mut work);
                }
                _ => {}
            }
        }
        let mut dead = HashSet::default();
        for (_, blk) in self.body.blocks.entries() {
            for &v in &blk.insts {
                if is_pure(v) && !live.contains(&v) {
                    dead.insert(v);
                }
            }
        }
        dead
    }

    /// Print every record, post-LICM. Within a block the ticks delimit the
    /// ops' spans; instructions before the first tick (the version-entry
    /// census) belong to no op.
    pub(super) fn flush_block_census(&mut self) {
        if self.blockcen_recs.is_empty() {
            return;
        }
        let dead = self.dead_values();
        let sid = self.root_source_id;
        let recs = std::mem::take(&mut self.blockcen_recs);
        let mut tick_of: HashMap<Value, usize> = HashMap::default();
        for (i, r) in recs.iter().enumerate() {
            tick_of.insert(r.tick, i);
        }
        // Per block: the tick positions, in order, with the record index.
        let mut spans: Vec<Vec<Value>> = vec![Vec::new(); recs.len()];
        for (_, blk) in self.body.blocks.entries() {
            let mut cur: Option<usize> = None;
            for &v in &blk.insts {
                if let Some(&i) = tick_of.get(&v) {
                    cur = Some(i);
                    continue;
                }
                if self.blockcen_ticks.contains_key(&v) {
                    continue;
                }
                if let Some(i) = cur {
                    spans[i].push(v);
                }
            }
        }
        for (i, r) in recs.iter().enumerate() {
            let insts = &spans[i];
            let mut cls = [0u32; 7];
            let mut ndead = 0u32;
            for &v in insts {
                cls[self.opsize_class(v)] += 1;
                if dead.contains(&v) {
                    ndead += 1;
                }
            }
            let blk = &self.body.blocks[r.blk];
            let term = match &blk.terminator {
                Terminator::Br { .. } => "br",
                Terminator::CondBr { .. } => "condbr",
                Terminator::Select { .. } => "select",
                Terminator::Return { .. } => "ret",
                Terminator::None => "none",
                _ => "other",
            };
            crate::diag_line!(
                "night: blockcen id {} sid#{sid} pc {} lpc {} op {:?} track {:?} spliced {} blk b{} \
role {} insts {} alu {} load {} store {} call {} boxing {} const {} other {} term {term} \
dead {ndead} form {} choke {}",
                r.id,
                r.pc,
                r.lpc,
                r.op,
                r.track,
                u8::from(r.spliced),
                r.blk.index(),
                r.role,
                insts.len(),
                cls[0],
                cls[1],
                cls[2],
                cls[3],
                cls[4],
                cls[5],
                cls[6],
                r.form,
                r.choke,
            );
            if self.opts.diagnostics.viz_lower {
                self.blockcen_listing(r.id, r.blk, insts, &dead);
            }
        }
    }

    /// The span's code, one line per instruction, with value ids, the
    /// immediates that make a guard legible (a load's offset, a const's
    /// value) and the effect the emitter recorded. Dead values are marked.
    /// This is the "stare at the code" half: the viz listing drops consts
    /// and folds alu.
    fn blockcen_listing(&self, id: u32, b: Block, insts: &[Value], dead: &HashSet<Value>) {
        let blk = &self.body.blocks[b];
        let params: Vec<String> = blk
            .params
            .iter()
            .map(|(t, v)| format!("{t:?}:v{}", v.index()))
            .collect();
        crate::diag_line!("night: blockcen params id {id} [{}]", params.join(" "));
        for &v in insts {
            let kind = if dead.contains(&v) { "dead" } else { "inst" };
            crate::diag_line!("night: blockcen {kind} id {id} {}", self.blockcen_inst(v));
        }
        let tgt = |t: &BlockTarget| -> String {
            let args: Vec<String> = t.args.iter().map(|a| format!("v{}", a.index())).collect();
            format!("b{}({})", t.block.index(), args.join(","))
        };
        let term = match &blk.terminator {
            Terminator::Br { target } => format!("br {}", tgt(target)),
            Terminator::CondBr {
                cond,
                if_true,
                if_false,
            } => format!(
                "condbr v{} {} {}",
                cond.index(),
                tgt(if_true),
                tgt(if_false)
            ),
            Terminator::Select {
                value,
                targets,
                default,
            } => format!(
                "select v{} [{}] {}",
                value.index(),
                targets.iter().map(tgt).collect::<Vec<_>>().join(" "),
                tgt(default)
            ),
            Terminator::Return { values } => format!(
                "ret ({})",
                values
                    .iter()
                    .map(|a| format!("v{}", a.index()))
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            Terminator::None => "none".to_string(),
            Terminator::Unreachable => "unreachable".to_string(),
        };
        crate::diag_line!("night: blockcen term id {id} {term}");
    }

    fn blockcen_inst(&self, v: Value) -> String {
        match &self.body.values[v] {
            ValueDef::Operator(op, args, _) => {
                let dbg = format!("{op:?}");
                let head = dbg.split_whitespace().next().unwrap_or(&dbg).to_string();
                let mut imm = String::new();
                for key in ["offset: ", "value: ", "function_index: "] {
                    if let Some(i) = dbg.find(key) {
                        let rest = &dbg[i + key.len()..];
                        let end = rest
                            .find(|c: char| !(c.is_ascii_alphanumeric() || c == '-'))
                            .unwrap_or(rest.len());
                        imm = format!("#{}", &rest[..end]);
                        break;
                    }
                }
                let a: Vec<String> = self.body.arg_pool[*args]
                    .iter()
                    .map(|x| format!("v{}", x.index()))
                    .collect();
                let eff = match self.effects.get(&v) {
                    Some(e) => format!("  {e:?}"),
                    None => String::new(),
                };
                format!("v{} = {head}{imm} ({}){eff}", v.index(), a.join(","))
            }
            ValueDef::BlockParam(b, i, ty) => {
                format!("v{} = param b{}.{i} {ty:?}", v.index(), b.index())
            }
            ValueDef::PickOutput(o, i, ty) => {
                format!("v{} = pick v{}.{i} {ty:?}", v.index(), o.index())
            }
            ValueDef::Alias(o) => format!("v{} = alias v{}", v.index(), o.index()),
            other => format!("v{} = {other:?}", v.index()),
        }
    }
}
