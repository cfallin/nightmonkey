/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! The redundant-work census: where the Opt track's own emitted IR does work
//! it did not have to do.
//!
//! Residency says which track the code runs on. It says nothing about what
//! the Opt track spends its instructions on, and the machine counters
//! (`tools/machperf.sh <bench> ion <bin>`) say that is now the question:
//! navier-stokes issues twice Ion's loads per instruction while sitting at
//! 100% OPT.
//!
//! Three shapes, all static, each attributed to the (pc, op, track) whose
//! lowering emitted it so `tools/opclass.py`'s join weights it by execution:
//!
//! - **box round trips.** An unbox of a value a box produced. The pair is a
//!   register shuffle the backend usually folds, so the count is a *witness*
//!   that the two lowerings disagreed about the operand's repr, not a cost
//!   estimate on its own.
//! - **dead boxes.** A box whose every use in the body is an unbox: the
//!   boxed form is never stored, passed or merged, so the box exists only to
//!   be taken apart again. Unlike a round trip this one has no defence --
//!   nothing consumed the boxed value.
//! - **frame round trips.** A load of a frame slot a store in the same block
//!   already wrote, with no call in between. `locals_ssa` exists to prevent
//!   exactly this, so every hit is a gap in its coverage -- and unlike the
//!   first two these are real memory operations that the backend must keep,
//!   because the address is a memory it cannot prove unaliased.
//!
//! What the census deliberately does not claim: that an emitted instruction
//! runs. An op's lowering emits every arm of its diamond and execution takes
//! one, so a count here is IR *carried* by an executed op, not IR executed.
//! That is the same reading `dIR/op` has, and the reason the ranking is worth
//! more than the magnitude.

use super::*;

/// What an op instance's lowering contributed, in the census's terms.
#[derive(Default, Clone, Copy)]
pub(super) struct Redundant {
    box_round: u32,
    dead_box: u32,
    frame_round: u32,
    /// Every load and store of the census's frame base, redundant or not:
    /// the denominator that says whether a frame round-trip count is a
    /// rounding error or the shape of the body.
    frame_load: u32,
    frame_store: u32,
    /// The half of that traffic addressed to a frame's OPERAND area rather
    /// than to a named slot. A named slot is what `locals_ssa` and the
    /// carried block params exist to keep in registers; the operand area is
    /// the spill the frame-based ABI takes at every seam that must leave a
    /// rooted, GC-walkable stack behind. The two have entirely different
    /// answers, so they are counted apart.
    stack_load: u32,
    stack_store: u32,
    /// The frame traffic emitted into the op's ENTRY block -- the one the
    /// lowering was already in when it started, so the one every execution
    /// that reaches the op runs. Everything else is in a block the op
    /// created, which is an arm: emitted at every instance, reached at some.
    /// The pair is the closest a static census gets to executed traffic, and
    /// the gap between them is the arm bundle.
    entry_load: u32,
    entry_store: u32,
    /// Every value the op's lowering appended, and the subset of them in the
    /// entry block. The complement is the arm bundle -- code emitted at every
    /// instance of the op and reached at some of them -- and its size is what
    /// the instruction-fetch volume is made of (richards fetches 29x Ion's
    /// instruction bytes for 2.4x its instructions).
    insts: u32,
    entry_insts: u32,
}

/// One frame's slot layout, in the shape `enter_frame_view` builds it: the
/// root frame at 0 and each spliced segment at its `frame_base`.
struct FrameRegion {
    base: u32,
    operand_base: u32,
}

impl<'a> Bbv<'a> {
    /// `--dump-redundant`, once per body. One line per op instance with a
    /// finding, plus a body total.
    pub(super) fn dump_redundant(&self) {
        let n = self.body.values.len();
        let mut frames: Vec<FrameRegion> = vec![FrameRegion {
            base: 0,
            operand_base: self.root_operand_base,
        }];
        for g in &self.segs {
            let local_base = g.frame_base + 16 + 8 * u32::from(g.nformals);
            frames.push(FrameRegion {
                base: g.frame_base,
                operand_base: local_base + 8 * max_locals(g.script) + 8,
            });
        }
        frames.sort_unstable_by_key(|f| f.base);
        // Uses, and whether every one of them is an unbox. A value used by
        // a terminator or a block param is used by something that is not an
        // unbox, which is what makes `dead_box` an honest question.
        let mut uses = vec![0u32; n];
        let mut nonunbox = vec![0u32; n];
        for (_, blk) in self.body.blocks.entries() {
            for &v in &blk.insts {
                let ValueDef::Operator(op, args, _) = &self.body.values[v] else {
                    continue;
                };
                let un = Self::is_unbox(op);
                for &a in &self.body.arg_pool[*args] {
                    let a = self.body.resolve_alias(a);
                    uses[a.index()] += 1;
                    if !un {
                        nonunbox[a.index()] += 1;
                    }
                }
            }
            blk.terminator.visit_uses(|a| {
                let a = self.body.resolve_alias(a);
                uses[a.index()] += 1;
                nonunbox[a.index()] += 1;
            });
        }

        let mut per = vec![Redundant::default(); n];
        let mut blk_of = vec![u32::MAX; n];
        for (b, blk) in self.body.blocks.entries() {
            for &v in &blk.insts {
                blk_of[self.body.resolve_alias(v).index()] = u32::try_from(b.index()).unwrap();
            }
        }
        for (_, blk) in self.body.blocks.entries() {
            // Frame traffic, in block order. A call may write any slot
            // (a splice's callee frame overlaps this one's operand area),
            // so it clears the store map rather than just the calls' own
            // slots.
            let mut stored: HashMap<u32, ()> = HashMap::default();
            for &v in &blk.insts {
                let ValueDef::Operator(op, args, _) = &self.body.values[v] else {
                    continue;
                };
                let args = &self.body.arg_pool[*args];
                match self.frame_access(op, args) {
                    Some((true, off)) => {
                        per[v.index()].frame_store += 1;
                        per[v.index()].stack_store += u32::from(Self::in_operands(&frames, off));
                        stored.insert(off, ());
                    }
                    Some((false, off)) => {
                        per[v.index()].frame_load += 1;
                        per[v.index()].stack_load += u32::from(Self::in_operands(&frames, off));
                        if stored.contains_key(&off) {
                            per[v.index()].frame_round += 1;
                        }
                    }
                    None => {}
                }
                if matches!(op, Operator::Call { .. } | Operator::CallIndirect { .. }) {
                    stored.clear();
                }
                // A box taken apart again. The def may sit in an earlier
                // block -- a cross-op round trip is the same mistake made
                // one op further away, and hiding it would flatter the
                // per-op numbers.
                if Self::is_unbox(op) && self.boxes_to(args[0], op) {
                    per[v.index()].box_round += 1;
                }
                if Self::is_box(&self.body, op, args)
                    && uses[v.index()] > 0
                    && nonunbox[v.index()] == 0
                {
                    per[v.index()].dead_box += 1;
                }
            }
        }

        // Attribute by value index: the per-op ranges were recorded in
        // emission order and `add_value` appends, so they partition the
        // values every op lowered. Anything outside them was added by a
        // later pass (LICM, block params) and is reported as such.
        let sid = self.root_source_id;
        let mut tot = Redundant::default();
        let mut claimed = 0usize;
        for &(pc, lpc, op, track, entry_blk, lo, hi) in &self.red_ranges {
            let mut r = Redundant::default();
            for (i, p) in per.iter().enumerate().take(hi as usize).skip(lo as usize) {
                r.insts += 1;
                if blk_of[i] == entry_blk {
                    r.entry_insts += 1;
                    r.entry_load += p.frame_load;
                    r.entry_store += p.frame_store;
                }
                r.box_round += p.box_round;
                r.dead_box += p.dead_box;
                r.frame_round += p.frame_round;
                r.frame_load += p.frame_load;
                r.frame_store += p.frame_store;
                r.stack_load += p.stack_load;
                r.stack_store += p.stack_store;
            }
            tot.entry_load += r.entry_load;
            tot.entry_store += r.entry_store;
            tot.insts += r.insts;
            tot.entry_insts += r.entry_insts;
            claimed += (hi - lo) as usize;
            tot.box_round += r.box_round;
            tot.dead_box += r.dead_box;
            tot.frame_round += r.frame_round;
            tot.frame_load += r.frame_load;
            tot.frame_store += r.frame_store;
            tot.stack_load += r.stack_load;
            tot.stack_store += r.stack_store;
            // Every instance, including the ones with nothing to report:
            // the join weights a key by `sum / instances`, so dropping the
            // empty instances would divide by a smaller number and inflate
            // every mean. (Measured: navier's frame loads read 2.51 per
            // executed op that way against a true 1.06.)
            crate::diag_line!(
                "night: redundant sid#{sid} pc {pc} lpc {lpc} op {op:?} track {track:?} \
boxround {} deadbox {} frameround {} frameload {} framestore {} stackload {} stackstore {} entryload {} entrystore {} insts {} entryinsts {}",
                r.box_round,
                r.dead_box,
                r.frame_round,
                r.frame_load,
                r.frame_store,
                r.stack_load,
                r.stack_store,
                r.entry_load,
                r.entry_store,
                r.insts,
                r.entry_insts,
            );
        }
        crate::diag_line!(
            "night: redundant sid#{sid} TOTAL values {n} attributed {claimed} \
boxround {} deadbox {} frameround {} frameload {} framestore {} stackload {} stackstore {} entryload {} entrystore {} insts {} entryinsts {}",
            tot.box_round,
            tot.dead_box,
            tot.frame_round,
            tot.frame_load,
            tot.frame_store,
            tot.stack_load,
            tot.stack_store,
            tot.entry_load,
            tot.entry_store,
            tot.insts,
            tot.entry_insts,
        );
    }

    /// Whether a frame offset lands in the operand area of whichever frame
    /// owns it: the innermost frame whose base it is at or above.
    fn in_operands(frames: &[FrameRegion], off: u32) -> bool {
        let i = frames.partition_point(|f| f.base <= off);
        i > 0 && off >= frames[i - 1].operand_base
    }

    fn is_unbox(op: &Operator) -> bool {
        matches!(op, Operator::I32WrapI64 | Operator::F64ReinterpretI64)
    }

    /// Whether `op(args)` is one of the two boxing forms `to_boxed` emits:
    /// the tag-OR of a widened i32, and the reinterpret of an exact double.
    fn is_box(body: &FunctionBody, op: &Operator, args: &[Value]) -> bool {
        match op {
            Operator::I64ReinterpretF64 => true,
            Operator::I64Or => args.iter().any(|&a| {
                matches!(
                    &body.values[body.resolve_alias(a)],
                    ValueDef::Operator(Operator::I64ExtendI32U | Operator::I64ExtendI32S, _, _)
                )
            }),
            _ => false,
        }
    }

    /// Whether `v` is a box of the kind `unbox` undoes.
    fn boxes_to(&self, v: Value, unbox: &Operator) -> bool {
        let v = self.body.resolve_alias(v);
        let ValueDef::Operator(op, args, _) = &self.body.values[v] else {
            return false;
        };
        let args = &self.body.arg_pool[*args];
        match unbox {
            // `I32WrapI64` undoes the widening, whether or not the tag was
            // OR-ed in on the way -- the wrap discards the tag either way.
            Operator::I32WrapI64 => {
                matches!(op, Operator::I64ExtendI32U | Operator::I64ExtendI32S)
                    || (matches!(op, Operator::I64Or) && Self::is_box(&self.body, op, args))
            }
            Operator::F64ReinterpretI64 => matches!(op, Operator::I64ReinterpretF64),
            _ => false,
        }
    }

    /// `Some((is_store, offset))` for a load or store addressed off the
    /// frame pointer. Heap traffic is a different question and is excluded:
    /// the frame is the memory `locals_ssa` was built to stop touching, and
    /// every frame address in a body -- root or spliced segment -- is a
    /// constant displacement from the one `vp`, so the offset alone names
    /// the slot.
    fn frame_access(&self, op: &Operator, args: &[Value]) -> Option<(bool, u32)> {
        let (store, mem) = match op {
            Operator::I64Load { memory } | Operator::I32Load { memory } => (false, memory),
            Operator::I64Store { memory } | Operator::I32Store { memory } => (true, memory),
            _ => return None,
        };
        (self.body.resolve_alias(args[0]) == self.vp).then_some((store, mem.offset))
    }
}
