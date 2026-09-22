/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Diamond arms: the emitter state an arm borrows, and the arm-scoping
//! primitive every forking lowering builds on.

use super::*;

impl<'a> Bbv<'a> {
    /// Every branch splits context, applied to the arms that leave the
    /// version. A diamond's miss arm continues at its own `dirty_edge_to`
    /// lineage, so the may-GC bookkeeping it does -- the fact kills in
    /// `note_call_eff` -- belongs to that lineage, not to the fall-through,
    /// which never runs the call. `side_arm` saves exactly this state, so an
    /// emitted-but-never-executed miss call cannot kill the lineage's facts.
    ///
    /// With the fact context keyed by the program point, an arm has no fact
    /// context of its own -- only its own SSA values and its own successor
    /// edge. What is saved here is emitter-local bookkeeping plus the fact
    /// vectors the transfer is computed through.
    ///
    /// The elem and compare arms are unconditionally scoped, and that is a
    /// design rule: an array read or write must have a fast path that does
    /// not kill the facts of the code around it, or every loop over an
    /// array pays for a miss it never takes.
    pub(super) fn arm_state(&self) -> ArmState {
        ArmState {
            stack: self.stack.clone(),
            track: self.cur_track,
            post_call: self.post_call,
            cur_flags: self.cur_flags,
            locals_ctx: self.locals_ctx.clone(),
            args_ctx: self.args_ctx.clone(),
            caller_locals_ctx: self.caller_locals_ctx.clone(),
            caller_args_ctx: self.caller_args_ctx.clone(),
            outer_ctx: self.outer_ctx.clone(),
            gcells_ctx: self.gcells_ctx.clone(),
            locals_ssa: self.locals_ssa.clone(),
            args_ssa: self.args_ssa.clone(),
            outer_ssa: self.outer_ssa.clone(),
            frame_stale: self.frame_stale.clone(),
        }
    }

    /// Restore what a leaving arm borrowed. The merge-back form (a slow arm
    /// with no continuation of its own) must not call this: there the
    /// post-call lineage really is the one that continues.
    pub(super) fn arm_restore(&mut self, s: ArmState) {
        self.stack = s.stack;
        self.cur_track = s.track;
        self.post_call = s.post_call;
        self.cur_flags = s.cur_flags;
        self.locals_ctx = s.locals_ctx;
        self.args_ctx = s.args_ctx;
        self.caller_locals_ctx = s.caller_locals_ctx;
        self.caller_args_ctx = s.caller_args_ctx;
        self.outer_ctx = s.outer_ctx;
        self.gcells_ctx = s.gcells_ctx;
        self.locals_ssa = s.locals_ssa;
        self.args_ssa = s.args_ssa;
        self.outer_ssa = s.outer_ssa;
        self.frame_stale = s.frame_stale;
    }

    /// Emit a side arm: build the arm's result in `blk`, then continue at
    /// `succ_pc` under the arm's implication (a per-arm continuation).
    /// Restores the emission point and the borrowed state afterwards.
    /// `side_arm` for an arm that computes a NUMERIC result inline -- no
    /// helper, no effect, both operand tags handled -- and therefore KEEPS
    /// the current track (the numeric-category policy): int32 and double
    /// are one tolerated category on Opt, and the succ join degrades the
    /// result fact (int32 -> numeric) rather than the track. Such an arm
    /// conforms -- it produces a value the successor pc's prediction
    /// admits -- so there is nothing to shunt.
    pub(super) fn side_arm_num(
        &mut self,
        blk: Block,
        succ_pc: Pc,
        emit_arm: impl FnOnce(&mut Self) -> Operand,
    ) {
        let saved_cur = self.cur;
        let saved = self.arm_state();
        self.note_arm_block(blk, blockcen::ArmKind::Num);
        self.post_call = false;
        self.cur = blk;
        let result = emit_arm(self);
        self.stack.push(result);
        debug_assert!(!self.post_call, "numeric arms run no helpers");
        let target = self.edge_to(succ_pc);
        self.body
            .set_terminator(self.cur, Terminator::Br { target });
        self.cur = saved_cur;
        self.arm_restore(saved);
    }

    /// `side_arm` for an arm that KEEPS the current track: an arm whose
    /// body routes its own helper paths off as separate continuations
    /// (the property IC in its `slow_cont` form: hits and clean misses
    /// rejoin, the helper-served miss leaves as its own Dirty lineage), so
    /// the arm's result carries no stepped state and its join at `succ_pc`
    /// degrades at most a fact, never the track.
    pub(super) fn side_arm_keep(
        &mut self,
        blk: Block,
        succ_pc: Pc,
        emit_arm: impl FnOnce(&mut Self) -> Operand,
    ) {
        let saved_cur = self.cur;
        let saved = self.arm_state();
        self.note_arm_block(blk, blockcen::ArmKind::Keep);
        self.post_call = false;
        self.cur = blk;
        let result = emit_arm(self);
        self.stack.push(result);
        let target = if self.post_call {
            self.dirty_edge_to(succ_pc)
        } else {
            self.edge_to(succ_pc)
        };
        self.body
            .set_terminator(self.cur, Terminator::Br { target });
        self.cur = saved_cur;
        self.arm_restore(saved);
    }

    pub(super) fn side_arm(
        &mut self,
        blk: Block,
        succ_pc: Pc,
        emit_arm: impl FnOnce(&mut Self) -> Operand,
    ) {
        if self.opts.diagnostics.viz_lower && self.mode == EmitMode::Code {
            crate::diag_line!(
                "night: viz lowerk sid#{} lpc {} blk b{} succ {} track {:?}",
                self.root_source_id,
                self.viz_lpc,
                blk.index(),
                succ_pc,
                self.cur_track,
            );
        }
        let saved_cur = self.cur;
        let saved = self.arm_state();
        self.note_arm_block(blk, blockcen::ArmKind::Side);
        self.post_call = false;
        // The happy-path designation, and it needs no new analysis: bbv
        // already has exactly one out-edge per forking op that falls
        // through, and every other arm comes through here. So a side arm
        // steps the track down, and the fall-through keeps it -- which is
        // precisely what stops `+`'s bottom-typed slow arm from defining
        // the successor pc for the int lineage that fell through it.
        let stepped_from_opt = self.cur_track == Track::Opt;
        self.cur = blk;
        // Tick BEFORE the step so the census kind carries the bump of the
        // track being LEFT (base 156 = fell off Opt), which is what lets
        // the runtime's root attribution own the arm's downstream.
        if stepped_from_opt {
            self.emit_guard_census(census::DIRTY_ENTER_SIDE_ARM, self.cur_pc);
        }
        self.cur_track = self.cur_track.step(Track::Side);
        let result = emit_arm(self);
        if self.opts.diagnostics.bbv
            && self.mode == EmitMode::Code
            && result.ty.prims == ALL_PRIMS
            && result.ty.outside
        {
            crate::diag_line!(
                "night: bbv bottompush sid#{} pc {} op {:?} (side)",
                self.source_id,
                self.cur_pc,
                self.cur_op
            );
        }
        self.stack.push(result);
        // An arm that ran a may-GC call continues as a DIRTY lineage.
        let target = if self.post_call {
            self.dirty_edge_to(succ_pc)
        } else {
            self.edge_to(succ_pc)
        };
        self.body
            .set_terminator(self.cur, Terminator::Br { target });
        self.cur = saved_cur;
        self.arm_restore(saved);
    }

    pub(super) fn cond_br(&mut self, cond: Value, if_true: Block, if_false: Block) {
        self.body.set_terminator(
            self.cur,
            Terminator::CondBr {
                cond,
                if_true: BlockTarget {
                    block: if_true,
                    args: vec![],
                },
                if_false: BlockTarget {
                    block: if_false,
                    args: vec![],
                },
            },
        );
    }
}
