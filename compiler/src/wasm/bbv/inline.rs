/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! The inline splice machinery: candidate selection, cost accounting, and
//! the call/construct splices that mint synthetic pc segments.

use super::*;
use crate::constants::{MAX_INLINE_POLY_BYTES, MAX_INLINE_SITES, MAX_INLINE_TARGETS};

impl<'a> Bbv<'a> {
    /// Undef-init a spliced child frame: the formals the call site did not
    /// supply (under-application; inline callees use no arguments object),
    /// every local, and the return-value slot.
    fn init_child_frame(
        &mut self,
        child_base: u32,
        argc: u16,
        nformals: u16,
        callee: &Script,
        undef: Value,
    ) {
        let c_nargs = u32::from(callee.nargs);
        for i in u32::from(argc)..c_nargs {
            self.store_i64(self.vp, child_base + FRAME_ARGS_OFFSET + 8 * i, undef);
        }
        let c_local_base = child_base + FRAME_ARGS_OFFSET + 8 * u32::from(nformals);
        let c_nlocals = max_locals(callee);
        for i in 0..c_nlocals {
            self.store_i64(self.vp, c_local_base + 8 * i, undef);
        }
        self.store_i64(self.vp, c_local_base + 8 * c_nlocals, undef);
    }

    /// Store the popped call operands at the child frame base. The actuals
    /// in `args` (indices into `popped`, formal 0 first) with a raw repr get
    /// a placeholder instead of a canonical box: the entering edge hands
    /// them to the callee as raw formal carriers (`carried_out`), and stores
    /// the real value only where the target does not carry one raw
    /// (`cont_at`). Returns the stash `seam_args` takes, indexed by formal.
    fn store_seam_frame(
        &mut self,
        child_base: u32,
        popped: &[Operand],
        args: std::ops::Range<usize>,
        undef: Value,
    ) -> Vec<Option<Operand>> {
        let mut seam = vec![None; args.len()];
        for (i, o) in popped.iter().enumerate() {
            let raw = args.contains(&i) && Self::raw_repr(o.repr);
            let b = if raw { undef } else { self.to_boxed(o) };
            self.store_i64(self.vp, child_base + 8 * u32::try_from(i).unwrap(), b);
            if raw {
                seam[i - args.start] = Some(o.clone());
            }
        }
        seam
    }
    /// Depth-1 inline candidacy: the likely callees that pass the
    /// per-target rules, in evidence order. Mono keeps the tiny-helper cap;
    /// a polymorphic set is the hot-dispatch shape and earns a larger
    /// per-target allowance -- dropping poly splices is a large loss. Caller
    /// must be the root frame with no handlers and no vp rebase. Construct
    /// sites are mono only and reject class ctors (their this/super
    /// protocol ops are off the allowlist anyway; the funcidx guard chain
    /// could never hit them since the classify routes class ctors to the
    /// generic arm).
    pub(super) fn inline_candidates(&self, pc: Pc, construct: bool) -> Option<Vec<ScriptId>> {
        if self.gen_only || self.is_global {
            return None;
        }
        let sids = self
            .ctx
            .facts
            .scripted_targets(Site::new(self.source_id, self.evid_pc(pc)))
            .to_vec();
        self.inline_candidates_for(pc, construct, sids)
    }

    /// `inline_candidates` over a caller-supplied target set (the
    /// apply-forward direct arm's resolved target, which the site's own
    /// call facts do not name).
    pub(super) fn inline_candidates_for(
        &self,
        pc: Pc,
        construct: bool,
        sids: Vec<ScriptId>,
    ) -> Option<Vec<ScriptId>> {
        if self.gen_only || self.is_global {
            return None;
        }
        // Two admission tiers by the transitively-resolved root call site,
        // since the hot-dispatch shape is loop-interior: loop-interior sites
        // earn depth 8 and a mono cap wide enough for a dispatcher body; the
        // rest keep the tight policy. Expanding both tiers costs a large
        // bundle more compile time than it is worth, for wins that
        // concentrate entirely in loops.
        let mut root_site = pc;
        let mut cur = self.cur_seg;
        let mut depth = 0;
        while let Some(i) = cur {
            depth += 1;
            root_site = self.segs[i].call_pc;
            cur = self.seg_of(root_site);
        }
        let root_nest = self
            .loop_intervals
            .iter()
            .filter(|&&(h, e)| root_site >= Pc::new(h) && root_site < Pc::new(e))
            .count();
        let seg_nest = if self.cur_seg.is_some() {
            self.loop_intervals
                .iter()
                .filter(|&&(h, e)| pc >= Pc::new(h) && pc < Pc::new(e))
                .count()
        } else {
            0
        };
        let in_loop_site = root_nest > 0;
        // Total loop-nest depth over the site (enclosing root loops + loops
        // of the enclosing spliced callees): a loop-bearing callee spliced
        // under an already-deep nest multiplies the relooper's tail
        // duplication -- a chain of such splices can lower a five-figure
        // block count to a function tens of megabytes long, past the
        // engine's body-size limit entirely.
        let site_nest = root_nest + seg_nest;
        let max_depth: u32 = if in_loop_site { 8 } else { 4 };
        let mono_cap: usize = if in_loop_site { 200 } else { 150 };
        let kind = if construct { "new" } else { "call" };
        if sids.is_empty() {
            if self.opts.diagnostics.bbv {
                crate::diag_line!(
                    "night: bbv inline-decline {kind} sid#{} pc {}: no likely-call evidence",
                    self.source_id,
                    self.evid_pc(pc),
                );
            }
            return None;
        };
        // Frozen means decided, and the gates below decide two different
        // things. ADMISSION -- may this site splice this target at all --
        // is the per-script site cap, the args-object bar, the depth cap,
        // the target rejects, the handler ranges. Those are answered once,
        // on the walk that created the segments, and are not re-asked: a
        // later walk's budgets are already spent, so re-asking would
        // decline a splice an earlier walk made and emit calls into a pc
        // space the prediction still describes as spliced.
        //
        // The splice FUEL is the other kind: not "may this site splice" but
        // "has this body grown enough to stop expanding it", which is a
        // property of the walk doing the emitting and has to be re-asked.
        // Both lowerings are correct at a spliced site, so a fuel decline
        // costs code quality, not agreement.
        if self.splices_frozen {
            let picked: Vec<ScriptId> = sids
                .iter()
                .copied()
                .filter(|&sid| self.seg_by_call_pc.contains_key(&(pc, sid)))
                .collect();
            if picked.is_empty() || self.splice_fuel_out(&picked) {
                return None;
            }
            return Some(picked);
        }
        if depth >= max_depth {
            if self.opts.diagnostics.bbv {
                crate::diag_line!(
                    "night: bbv inline-decline {kind} sid#{} pc {} ({} targets): depth cap",
                    self.source_id,
                    self.evid_pc(pc),
                    sids.len()
                );
            }
            return None;
        }
        let decline = |why: &str| {
            if self.opts.diagnostics.bbv {
                crate::diag_line!(
                    "night: bbv inline-decline {kind} sid#{} pc {} ({} targets): {why}",
                    self.source_id,
                    self.evid_pc(pc),
                    sids.len()
                );
            }
            None
        };
        if self.needs_args_obj || self.inline_sites >= MAX_INLINE_SITES {
            return decline("args-obj caller or site cap");
        }

        // Splice fuel (the theta mint-fuel discipline): once the body is
        // large, new splices multiply versions on exactly the scripts that
        // will ladder-retry -- they run the generic dispatch instead.
        // Small callees are exempt up to a harder line: the fuel exists to
        // stop version-multiplying big splices, but a tiny straight-line
        // callee left as a call is worse than its size suggests -- the call
        // kills the caller's class facts, and a loop body containing it
        // re-kills them every iteration, so one tiny clamp helper called
        // from a solver loop can hold the whole steady state factless.
        if self.splice_fuel_out(&sids) {
            return decline("splice fuel exhausted");
        }
        // Loop-kind notes are Ion osr bookkeeping -- walk_try_notes ignores
        // them (no handler, no unwind close), so they don't gate splices.
        // A handler/close note whose range covers the call site does: an
        // exception at a synthetic segment pc cannot match the caller's
        // note ranges, so the site must have nothing to match (the error
        // epilogue is then the correct landing).
        let lpc = self.evid_pc(pc);
        if self.script.try_notes.iter().any(|t| {
            !matches!(t.kind, TryNoteKind::Loop) && lpc >= t.start && lpc < t.start + t.length
        }) {
            return decline("call site inside caller handler/close range");
        }
        // Fanout-off rung: seg_site is disabled, so a splice inside a loop
        // would emit tokenless shared segment versions -- two caller-loop
        // lineages entering the shared interior is a second entry into the
        // loop's cycle (irreducible). Loop-interior sites stay generic on
        // this rung (it exists to shed version growth anyway).
        if self.fanout_off && in_loop_site {
            return decline("fanout-off loop-interior site");
        }
        if sids.is_empty() || sids.len() > MAX_INLINE_TARGETS {
            return decline("target count");
        }
        let cap = if sids.len() == 1 {
            mono_cap
        } else {
            MAX_INLINE_POLY_BYTES
        };
        // A loop-bearing callee spliced at a loop-interior site stacks its
        // loop under the site's: the two-level version-loop nest is what
        // the relooper amplifies, and it amplifies it into tens of
        // megabytes. Loop-free sites keep them.
        let allow_callee_loops = site_nest == 0;
        let picked: Vec<ScriptId> = sids
            .iter()
            .copied()
            .filter(|&sid| {
                match self.inline_target_reject(sid.get(), cap, allow_callee_loops, construct) {
                    None => true,
                    Some(why) => {
                        if self.opts.diagnostics.bbv {
                            crate::diag_line!(
                                "night: bbv inline-decline {kind} sid#{} pc {} target#{sid}: {why}",
                                self.source_id,
                                self.evid_pc(pc)
                            );
                        }
                        false
                    }
                }
            })
            .collect();
        if picked.is_empty() {
            return None;
        }
        if construct && picked.len() != 1 {
            return decline("construct poly");
        }
        // Transitive splice budget: every other admission
        // rule prices this splice in isolation. Price instead what it will
        // transitively pull in -- the picked bodies plus, recursively, the
        // bodies their own mono sites resolve to within the remaining depth
        // -- against what this function has left. That is the quantity the
        // isolated rules were all approximating: a small ctor can pass every
        // individual cap -- well under its byte cap, well under the depth
        // cap -- while its closure takes the enclosing body from tens of
        // thousands of values to six figures.
        if construct {
            let room = CONSTRUCT_CLOSURE_CAP;
            let depth_left = max_depth - depth;
            let est: usize = picked
                .iter()
                .map(|&sid| {
                    self.splice_closure_cost(
                        sid,
                        depth_left,
                        room,
                        Some(Site::new(self.source_id, lpc)),
                    )
                })
                .sum();
            if est > room {
                return decline(&format!("transitive closure {est} over cap {room}"));
            }
        }
        Some(picked)
    }

    /// Whether this body has grown past the point where a further splice
    /// pays. Small callees are exempt up to a harder line: the fuel exists
    /// to stop version-multiplying big splices, but a tiny straight-line
    /// callee left as a call is worse than its size suggests -- the call
    /// kills the caller's class facts, and a loop body containing it
    /// re-kills them every iteration, so one tiny clamp helper called from
    /// a solver loop can hold the whole steady state factless.
    fn splice_fuel_out(&self, sids: &[ScriptId]) -> bool {
        if self.value_count() < SPLICE_FUEL_VALUES {
            return false;
        }
        let small = sids.iter().all(|&s| {
            matches!(
                self.source.object(SourceObjectId::new(s.get())),
                SourceObject::Script(c) if c.bytecode.len() <= SMALL_SPLICE_BC
            )
        });
        !small || self.value_count() >= SMALL_SPLICE_FUEL_VALUES
    }

    /// Estimated emitted cost of splicing `sid`: its own body plus,
    /// recursively within `depth_left`, whatever its own call sites bring.
    ///
    /// Bytecode bytes alone are the wrong currency -- a `Call` lowers to a
    /// whole classify diamond (and, inside a segment, once per version of
    /// that segment) while an `Add` lowers to a handful of values. So a call
    /// site costs `CALL_COST` whether it resolves (recurse: the callee's own
    /// cost) or not (stays generic: the classify chain lands in the caller
    /// either way). That is what makes a tiny ctor with two calls out price
    /// above a call-free helper of twice the bytecode, which is the
    /// separation the structural "a ctor that calls out must not splice"
    /// rule was cutting by hand. Poly sites count their full fan-out (one segment each).
    /// Stops climbing once past `room`: the caller only needs the verdict.
    ///
    /// `entry` is the site that would splice `sid` (None when unknown):
    /// an apply-forward site inside `sid` resolves per entry, and where it
    /// does it is not a classify chain but one guard in front of the
    /// target's own closure, which is what it is priced as.
    pub(super) fn splice_closure_cost(
        &self,
        sid: ScriptId,
        depth_left: u32,
        room: usize,
        entry: Option<Site>,
    ) -> usize {
        const CALL_COST: usize = 300;
        const APPLY_FWD_COST: usize = 40;
        const RESOLVED_COST: usize = 60;
        const LOOP_WEIGHT: usize = 3;
        let SourceObject::Script(s) = self.source.object(sid.source()) else {
            return 0;
        };
        // A loop in a spliced callee is the term no size budget can see: its
        // interior is emitted once per version of the segment, and the
        // relooper duplicates tails per skipped-header context on top of
        // that. Measured across the corpus, a loop-bearing closure expands
        // roughly three times the values per unit of un-weighted cost that a
        // loop-free one does, and the loops are the whole difference.
        let nloops = LOOP_WEIGHT * super::translate::scan_loop_intervals(s).len();
        let mut total = s.bytecode.len() * (1 + nloops);
        if total > room {
            return total;
        }
        for (cpc, op) in call_site_pcs(s) {
            if !matches!(op, JSOp::Call | JSOp::CallIgnoresRv | JSOp::New) {
                continue;
            }
            let site = Site::new(sid, Pc::new(cpc));
            let fwd_target = entry
                .and_then(|e| self.ctx.facts.apply_targets_in.get(&(e, site)))
                .or_else(|| self.ctx.facts.apply_targets.get(&site))
                .copied()
                .filter(|_| {
                    op != JSOp::New && self.callee_apply_fwd_pcs(sid, s).contains(&Pc::new(cpc))
                });
            let targets: Vec<ScriptId> = match fwd_target {
                Some(t) => {
                    total += APPLY_FWD_COST;
                    vec![t]
                }
                None => {
                    let ts = self.ctx.facts.scripted_targets(site).to_vec();
                    // A mono-resolved site splices behind one identity
                    // guard (a construct site adds its shape guards and
                    // the inline `this` creation); any other site costs
                    // the classify chain, which a spliced one emits too
                    // (guard + generic miss arm), on top of the callee
                    // body.
                    total += if ts.len() == 1 {
                        RESOLVED_COST
                    } else {
                        CALL_COST
                    };
                    ts
                }
            };
            if depth_left > 0 {
                for t in targets {
                    total += self.splice_closure_cost(
                        t,
                        depth_left - 1,
                        room.saturating_sub(total),
                        Some(site),
                    );
                    if total > room {
                        return total;
                    }
                }
            }
            if total > room {
                return total;
            }
        }
        total
    }

    /// The callee's apply-forward pc set (empty unless it is a wrapper
    /// whose `arguments` provably never materializes).
    pub(super) fn callee_apply_fwd_pcs(&self, sid: ScriptId, callee: &Script) -> HashSet<Pc> {
        super::translate::compute_apply_fwd_pcs(callee, &self.ctx.facts.apply_sites, sid.get())
            .unwrap_or_default()
    }

    /// Formal slots a splice of `callee` at an `argc`-actual site keeps:
    /// an apply-forward wrapper keeps every actual (its payload); any other
    /// callee keeps its declared formals and lets the locals init clobber
    /// the surplus, which it cannot observe.
    pub(super) fn seg_nformals(&self, sid: ScriptId, callee: &Script, argc: u16) -> u16 {
        if self.callee_apply_fwd_pcs(sid, callee).is_empty() {
            callee.nargs
        } else {
            callee.nargs.max(argc)
        }
    }

    /// Per-target inline rules: tiny plain body, argc == nargs, no
    /// env/args/new.target/try/generator, and every callee op on the
    /// emission allowlist (an unsupported op inside a splice would sink
    /// the whole caller). Returns the reject reason (None = inlinable).
    pub(super) fn inline_target_reject(
        &self,
        sid: u32,
        cap: usize,
        allow_callee_loops: bool,
        construct: bool,
    ) -> Option<String> {
        let SourceObject::Script(callee) = self.source.object(SourceObjectId::new(sid)) else {
            return Some("not a script".to_string());
        };
        if callee.bytecode.is_empty() || callee.bytecode.len() > cap {
            return Some(format!("size {} > cap {cap}", callee.bytecode.len()));
        }
        if callee.is_generator_or_async {
            return Some("generator/async".to_string());
        }
        // An apply-forward wrapper (`T.apply(this, arguments)` and nothing
        // else touching `arguments`) mentions its arguments object without
        // ever observing it: the forward reads the actuals off the frame.
        // Its mapped-args flag aliases nothing either -- the proof requires
        // `nargs == 0`, so there is no formal for the object to alias.
        let apply_fwd =
            super::args_object_elided(callee, ScriptId::new(sid), &self.ctx.facts.apply_sites);
        if callee.has_mapped_args && !apply_fwd {
            return Some("mapped-args".to_string());
        }
        if construct && callee.is_class_ctor {
            return Some("class ctor".to_string());
        }
        // Over-application (argc > nargs) is fine, and the root frame has
        // always relied on the same argument: the extra actuals land on the
        // callee's locals region, and the prologue's undef-init clobbers
        // them -- which is sound exactly because a callee that cannot reach
        // `arguments`, a rest parameter or `GetActualArg` cannot observe
        // them. Every one of those is rejected above, so the splice inherits
        // the property. JS semantics need nothing else: surplus actuals are
        // dropped (they are simply never read) and missing ones are the
        // undefined padding the under-application loop already writes. Both
        // entry-ctx builders `resize` to `1 + nargs`, which truncates the
        // surplus facts.
        let mut kinds = callee.try_notes.iter().map(|t| t.kind);
        if kinds.any(|k| !matches!(k, TryNoteKind::Loop)) {
            return Some("callee try notes".to_string());
        }
        if !allow_callee_loops && callee.try_notes.iter().any(|t| t.kind == TryNoteKind::Loop) {
            return Some("loop-bearing callee at deep nest".to_string());
        }
        if uses_env_ops(callee)
            || (uses_arguments(callee) && !apply_fwd)
            || uses_actual_args(callee)
            || uses_new_target(callee)
        {
            return Some("env/arguments/new.target".to_string());
        }
        let mut cp = callee.parser();
        while let Some(op) = cp.next_op() {
            if splice_blocked(op) && !(apply_fwd && op == JSOp::Arguments) {
                return Some(format!("op {op:?} not spliceable"));
            }
            let imm = usize::try_from(op.len()).unwrap() - 1;
            if imm > 0 && cp.advance(imm).is_none() {
                return Some("truncated bytecode".to_string());
            }
        }
        None
    }
}

/// Whether one bytecode op may NOT appear inside a spliced callee body.
///
/// A segment is not a compilation of the callee -- it is the callee's
/// bytecode mapped into the caller's pc space with the frame view swapped
/// (`enter_frame_view`). Every op whose lowering addresses the frame through
/// that view is fine; what is listed here is the set that reaches around it.
///
/// This is a BLOCKLIST, so an op nobody has classified is admitted. That is a
/// deliberate trade -- the exclusions really are the exception, and an
/// allowlist would cost more in maintenance than these escapes cost in risk
/// -- but it means the list has to be maintained as lowerings change, and a
/// mistake here is a miscompile rather than a decline. Fixing each lowering
/// to address the active frame makes the corresponding entry unnecessary.
///
/// Three of these are held ONLY by this list -- no script-level gate covers
/// them, and getting one wrong is a real miscompile, not a missed
/// optimization:
///
/// - `ArgumentsLength` lowers to `self.argc`, the root frame's ABI
///   parameter. `uses_arguments` matches only `JSOp::Arguments` and
///   `uses_actual_args` only `Rest`/`GetActualArg`, so nothing else stops a
///   callee's `arguments.length` returning the *caller's* argc.
/// - `FunWithProto` loads `self.env_slot_off`, and it is not one of the ops
///   `uses_env_ops` scans for.
/// - `Callee` loads `self.sp[0]`, which is the root frame's callee slot; a
///   segment's callee lives at `vp + frame_base`.
/// - Every op that pairs a script-relative index with a *script value*
///   passes `self.script_param` (directly or through `cur_script_value`,
///   which is a stub returning it): `RegExp`, `Object`, `CallSiteObj`,
///   `InitGLexical`, `CheckLexical`, `ThrowSetConst`. In a segment that
///   resolves the callee's gcthing index against the ROOT script's table.
///   `ion/bug1304640.js` catches the `RegExp` case: `f()` returning `/x/`
///   twice compared equal, because both got the same wrong object.
/// - `TableSwitch` reads its case targets as ABSOLUTE pcs out of the
///   script's `resume_offsets` side table and edges straight to them. Every
///   other pc in a segment is `seg.base + local`, so those edges land in the
///   root script's bytecode -- a wild jump (`ion/bug1034400.js`). Relative
///   branches are fine; it is the side table that is not rebased.
fn splice_blocked(op: JSOp) -> bool {
    use JSOp::*;
    matches!(
        op,
        // Reach around the frame view: `argc`, `env_slot_off`,
        // `args_obj_slot_off`, `new_target_slot_off`, `script_param` and
        // `sp`-relative slots are all root-frame absolute.
        ArgumentsLength | Arguments | Rest | GetActualArg | NewTarget | FunWithProto | Callee
        // Script-relative: resolved against `self.script_param`, the root.
        | RegExp | Object | CallSiteObj | InitGLexical | CheckLexical | ThrowSetConst
        | GlobalOrEvalDeclInstantiation
        // Absolute pcs from a script side table, not rebased into the
        // segment's pc space.
        | TableSwitch
        // The environment chain hangs off the root frame's env slot.
        | GetName | BindName | BindUnqualifiedName | BindVar | DelName | GetImport
        | PushLexicalEnv | PopLexicalEnv | FreshenLexicalEnv | RecreateLexicalEnv
        | PushVarEnv | PushClassBodyEnv | EnterWith | LeaveWith | Lambda
        | GetAliasedVar | SetAliasedVar | InitAliasedLexical | CheckAliasedLexical
        // Direct eval needs the calling frame's scope, which the splice has
        // dissolved.
        | Eval | StrictEval | SpreadEval | StrictSpreadEval
        // The derived-constructor this/super protocol is frame-identity
        // bound (`super` resolves through the home object of the *running*
        // frame's callee).
        | SuperCall | SpreadSuperCall | SuperFun | SuperBase | InitHomeObject
        | CheckThisReinit | GetPropSuper | SetPropSuper | StrictSetPropSuper
        | GetElemSuper | SetElemSuper | StrictSetElemSuper
        // The resumable state machine: whole-script rejected already, listed
        // so the two gates cannot drift apart.
        | Generator | InitialYield | Yield | AfterYield | FinalYieldRval | Await
        | AsyncAwait | AsyncResolve | AsyncReject | CanSkipAwait | MaybeExtractAwaitValue
        | ToAsyncIter | Resume | ResumeKind | CheckResumeKind | IsGenClosing
        // Debugger / interpreter escapes: designed out of this tier.
        | Debugger | ForceInterpreter | DebugLeaveLexicalEnv | DebugCheckSelfHosted
        | GetAliasedDebugVar
    )
}

impl<'a> Bbv<'a> {
    /// Emit the guarded mono splice: classify + patched
    /// funcidx compare; the hit arm builds the contiguous child frame and
    /// edges into the callee's pc-space segment; the miss arm is the
    /// generic dispatch continuing at next_pc.
    pub(super) fn emit_inline_call(
        &mut self,
        pc: Pc,
        argc: u16,
        need: usize,
        sids: &[ScriptId],
    ) -> Result<(), String> {
        let next_pc = pc + JSOp::Call.len();
        let len = self.stack.len();
        let callee_op = self.stack[len - need].clone();
        let callee_boxed = self.to_boxed(&callee_op);
        let (funcidx, _script, _native) = self.emit_inline_classify(callee_boxed);
        let chain_blk = self.body.add_block();
        let generic_blk = self.body.add_block();
        self.body.set_terminator(
            self.cur,
            Terminator::Br {
                target: BlockTarget {
                    block: chain_blk,
                    args: vec![],
                },
            },
        );

        // Miss arm: the generic dispatch over the intact operand stack,
        // continuing at next_pc under the weaker ctx (the classify
        // repeats inside -- one dead compare). Its call kills facts on the
        // arm's own continuation only, not on the sibling hit arms -- which
        // demands the full arm state: a hand-rolled save that drops part of
        // it lets the generic helper's kills reach every hit arm emitted
        // after it.
        {
            let saved_cur = self.cur;
            let st = self.arm_state();
            self.cur = generic_blk;
            self.emit_call_generic(pc, argc, need, true)?;
            let target = self.dirty_edge_to(next_pc);
            self.body
                .set_terminator(self.cur, Terminator::Br { target });
            self.cur = saved_cur;
            self.arm_restore(st);
        }

        // Shared frame build (dominates every hit arm; the stores are
        // dead on the generic path, which spills for itself): pop the
        // call operands, root the caller's remaining operands across the
        // callee (the GC tracer updates the slots in place; the return
        // path reloads), and store the popped [callee, this, args...] at
        // the child base -- the frame prefix IS the spilled call operands
        // (argc == nargs for every target).
        self.cur = chain_blk;
        let popped: Vec<Operand> = self.stack.split_off(len - need);
        let n_parent = u32::try_from(self.stack.len()).unwrap();
        for i in 0..n_parent as usize {
            let o = self.stack[i].clone();
            let b = self.to_boxed(&o);
            self.store_i64(self.vp, self.operand_base + 8 * i as u32, b);
        }
        let child_base = self.operand_base + 8 * n_parent;
        let undef = self.boxed_const(TAG_UNDEFINED << 32);
        let seam = self.store_seam_frame(child_base, &popped, 2..2 + usize::from(argc), undef);
        let entry_args: Vec<SlotCtx> = popped[1..].iter().map(Operand::slot).collect();

        // Guard chain: one patched funcidx compare per target (v2 poly;
        // u32::MAX = target not compiled, that guard never matches); each
        // hit arm undef-inits its callee's locals + rval and edges into
        // its pc-space segment with the call-site entry ctx (inline ctx
        // inheritance). The final miss falls to the generic arm.
        let saved_stack = std::mem::take(&mut self.stack);
        for (t, &sid) in sids.iter().enumerate() {
            let SourceObject::Script(callee) = self.source.object(SourceObjectId::new(sid.get()))
            else {
                return Err("inline callee not a script".to_string());
            };
            let expected = self.i32_const(u32::MAX);
            self.likely_patches.push((expected, expected, sid.get()));
            let is_k = self.binop(Operator::I32Eq, funcidx, expected, Type::I32);
            let hit_blk = self.body.add_block();
            let next_blk = if t + 1 == sids.len() {
                generic_blk
            } else {
                self.body.add_block()
            };
            self.cond_br(is_k, hit_blk, next_blk);

            self.cur = hit_blk;
            let c_nlocals = max_locals(callee);
            let nformals = self.seg_nformals(sid, callee, argc);
            self.init_child_frame(child_base, argc, nformals, callee, undef);
            let seg_base =
                self.ensure_seg(pc, sid, callee, next_pc, n_parent, child_base, false, argc);
            if self.opts.diagnostics.bbv {
                crate::diag_line!(
                    "night: bbv inline-splice sid#{} pc {} target#{sid} depth-seg {:?}",
                    self.source_id,
                    self.evid_pc(pc),
                    self.cur_seg
                );
            }
            let mut entry = entry_args.clone();
            entry.resize(
                1 + usize::from(nformals),
                SlotCtx {
                    prims: PRIM_UNDEFINED,
                    outside: false,
                    range: RangeBucket::Top,
                    cls: None,
                    cls_shallow: false,
                    cls_slots: false,
                    ta: None,
                    likely_cls: None,
                    src: None,
                    iv: None,
                    iv_grow: 0,
                    prov: Prov::NONE,
                },
            );
            let saved_locals =
                std::mem::replace(&mut self.locals_ctx, vec![SlotCtx::TOP; c_nlocals as usize]);
            let saved_args = std::mem::replace(&mut self.args_ctx, entry);
            // The caller's frame facts ride the segment ctx (the
            // splice cannot reassign caller slots) and are restored at
            // the return edge.
            let (in_cl, in_ca) = if self.fanout_off {
                (Vec::new(), Vec::new())
            } else {
                (saved_locals.clone(), saved_args.clone())
            };
            // Push the frame this splice is displacing onto the outer chain
            // -- without it a nested splice drops its grandparent's facts
            // and its return edge erases them for the enclosing frame.
            let in_outer = self.push_outer_frame();
            let saved_caller_locals = std::mem::replace(&mut self.caller_locals_ctx, in_cl);
            let saved_caller_args = std::mem::replace(&mut self.caller_args_ctx, in_ca);
            let saved_outer = std::mem::replace(&mut self.outer_ctx, in_outer);
            self.seam_args = seam.clone();
            let target = self.cont(Pc::new(seg_base));
            self.seam_args.clear();
            self.body
                .set_terminator(self.cur, Terminator::Br { target });
            self.locals_ctx = saved_locals;
            self.args_ctx = saved_args;
            self.caller_locals_ctx = saved_caller_locals;
            self.caller_args_ctx = saved_caller_args;
            self.outer_ctx = saved_outer;
            self.cur = next_blk;
        }
        self.stack = saved_stack;
        Ok(())
    }

    /// Ctor-body splice at a `new` site. Mirrors
    /// `emit_inline_call` with the construct deltas: a mono patched
    /// funcidx guard plus ctor-shape + newTarget guards, the hit arm
    /// allocates `this` inline (construct cell / create_this reactor)
    /// into the child frame's this slot, and the segment is marked
    /// is_construct (its returns stamp the ctor-exit class word and
    /// substitute `is_object(ret) ? ret : this`). The miss arm is the
    /// direct-dispatch classify continuing at next_pc. The construct
    /// operand frame is `[callee, this_ph, args..., newTarget]` (argc+3);
    /// the newTarget slot is dead once `this` exists (new.target users
    /// are rejected) and is clobbered by the arg padding / locals init.
    pub(super) fn emit_inline_construct(
        &mut self,
        pc: Pc,
        argc: u16,
        need: usize,
        sid: ScriptId,
    ) -> Result<(), String> {
        let next_pc = pc + JSOp::New.len();
        let len = self.stack.len();
        let callee_op = self.stack[len - need].clone();
        let nt_op = self.stack[len - 1].clone();
        let callee_boxed = self.to_boxed(&callee_op);
        let nt_boxed = self.to_boxed(&nt_op);
        let (funcidx, _script, _native) = self.emit_inline_classify(callee_boxed);
        let chain_blk = self.body.add_block();
        let generic_blk = self.body.add_block();
        self.body.set_terminator(
            self.cur,
            Terminator::Br {
                target: BlockTarget {
                    block: chain_blk,
                    args: vec![],
                },
            },
        );

        // Miss arm: the direct-dispatch classify over the intact operand
        // stack, continuing at next_pc under the weaker ctx (the classify
        // repeats inside -- one dead compare).
        {
            let saved_cur = self.cur;
            let st = self.arm_state();
            self.cur = generic_blk;
            // The classify's merge may arm the return on-ramp; that is this
            // arm's business only (`ArmState` does not carry it).
            let saved_onramp = self.ret_onramp_pc;
            self.emit_construct_classify(pc, argc, need, Some(funcidx))?;
            let target = self.dirty_edge_to(next_pc);
            self.body
                .set_terminator(self.cur, Terminator::Br { target });
            self.ret_onramp_pc = saved_onramp;
            self.cur = saved_cur;
            self.arm_restore(st);
        }

        // Shared frame build (the stores are dead on the generic path,
        // which spills for itself): pop the construct operands, root the
        // caller's remaining operands, and store the popped [callee,
        // this_ph, args..., newTarget] at the child base.
        self.cur = chain_blk;
        let popped: Vec<Operand> = self.stack.split_off(len - need);
        let n_parent = u32::try_from(self.stack.len()).unwrap();
        for i in 0..n_parent as usize {
            let o = self.stack[i].clone();
            let b = self.to_boxed(&o);
            self.store_i64(self.vp, self.operand_base + 8 * i as u32, b);
        }
        let child_base = self.operand_base + 8 * n_parent;
        let undef = self.boxed_const(TAG_UNDEFINED << 32);
        let seam = self.store_seam_frame(child_base, &popped, 2..2 + usize::from(argc), undef);
        let SourceObject::Script(callee) = self.source.object(SourceObjectId::new(sid.get()))
        else {
            return Err("inline ctor callee not a script".to_string());
        };
        let saved_stack = std::mem::take(&mut self.stack);

        // Identity guard (patched funcidx compare; u32::MAX = target not
        // compiled, never matches), then ctor-shape + newTarget guards in
        // the hit arm (loads safe: a funcidx hit proves a script-backed
        // JSFunction; ctor-ness is a JSFunction flag, not the script's,
        // so it needs its own check).
        let expected = self.i32_const(u32::MAX);
        self.likely_patches.push((expected, expected, sid.get()));
        let is_k = self.binop(Operator::I32Eq, funcidx, expected, Type::I32);
        let chk_blk = self.body.add_block();
        self.cond_br(is_k, chk_blk, generic_blk);

        self.cur = chk_blk;
        let ptr = self.unop(Operator::I32WrapI64, callee_boxed, Type::I32);
        let slot0 = self.load_i64(ptr, FUNC_FLAGS_SLOT_OFFSET);
        let raw = self.unop(Operator::I32WrapI64, slot0, Type::I32);
        let ctor_bit = self.i32_const(FUNCTION_FLAGS_CONSTRUCTOR);
        let ctor_raw = self.binop(Operator::I32And, raw, ctor_bit, Type::I32);
        let zero_c = self.i32_const(0);
        let is_ctor = self.binop(Operator::I32Ne, ctor_raw, zero_c, Type::I32);
        let kind_mask = self.i32_const(FUNCTION_KIND_MASK);
        let kind = self.binop(Operator::I32And, raw, kind_mask, Type::I32);
        let is_normal = self.unop(Operator::I32Eqz, kind, Type::I32);
        let nt_eq = self.binop(Operator::I64Eq, callee_boxed, nt_boxed, Type::I32);
        let a = self.binop(Operator::I32And, is_ctor, is_normal, Type::I32);
        let take = self.binop(Operator::I32And, a, nt_eq, Type::I32);
        let hit_blk = self.body.add_block();
        self.cond_br(take, hit_blk, generic_blk);

        // Hit arm: create `this` (caller operands + the popped construct
        // frame are rooted below top_c; the create_this out-slot past the
        // frame is dead space the locals init owns), splice it into the
        // child this slot, pad + init the child frame, and edge into the
        // callee's pc-space segment.
        self.cur = hit_blk;
        let top_off_c = child_base + 8 * u32::try_from(need).unwrap();
        let top_c = self.add_offset(self.vp, top_off_c);
        let (ok_ct, _delta) = self.emit_construct_this(
            pc,
            top_c,
            top_off_c,
            callee_boxed,
            nt_boxed,
            Some(funcidx),
            false,
        );
        self.branch_on_err(ok_ct);
        let this_val = self.load_i64(self.vp, top_off_c);
        self.store_i64(self.vp, child_base + 8, this_val);
        let c_nlocals = max_locals(callee);
        let nformals = self.seg_nformals(sid, callee, argc);
        self.init_child_frame(child_base, argc, nformals, callee, undef);
        let seg_base = self.ensure_seg(pc, sid, callee, next_pc, n_parent, child_base, true, argc);
        if self.opts.diagnostics.bbv {
            crate::diag_line!(
                "night: bbv inline-splice sid#{} pc {} target#{sid} construct depth-seg {:?}",
                self.source_id,
                self.evid_pc(pc),
                self.cur_seg
            );
        }
        // Entry ctx: `this` is the freshly-created object (a positive
        // object claim); the args carry the call-site facts minus class
        // facts (create_this may GC, which kills every durable cls fact
        // -- the snapshot below predates the call).
        let this_ctx = SlotCtx {
            prims: Prims::EMPTY,
            outside: true,
            range: RangeBucket::Top,
            cls: None,
            cls_shallow: false,
            cls_slots: false,
            ta: None,
            likely_cls: None,
            src: None,
            iv: None,
            iv_grow: 0,
            prov: Prov::NONE,
        };
        let mut entry: Vec<SlotCtx> = std::iter::once(this_ctx)
            .chain(popped[2..2 + usize::from(argc)].iter().map(|o| {
                let mut s = o.slot_cell();
                s.cls = None;
                s.cls_shallow = false;
                s.cls_slots = false;
                s
            }))
            .collect();
        entry.resize(
            1 + usize::from(nformals),
            SlotCtx {
                prims: PRIM_UNDEFINED,
                outside: false,
                range: RangeBucket::Top,
                cls: None,
                cls_shallow: false,
                cls_slots: false,
                ta: None,
                likely_cls: None,
                src: None,
                iv: None,
                iv_grow: 0,
                prov: Prov::NONE,
            },
        );
        let saved_locals =
            std::mem::replace(&mut self.locals_ctx, vec![SlotCtx::TOP; c_nlocals as usize]);
        let saved_args = std::mem::replace(&mut self.args_ctx, entry);
        let (in_cl, in_ca) = if self.fanout_off {
            (Vec::new(), Vec::new())
        } else {
            (saved_locals.clone(), saved_args.clone())
        };
        // Push the frame this splice is displacing onto the outer chain
        // -- without it a nested splice drops its grandparent's facts
        // and its return edge erases them for the enclosing frame.
        let in_outer = self.push_outer_frame();
        let saved_caller_locals = std::mem::replace(&mut self.caller_locals_ctx, in_cl);
        let saved_caller_args = std::mem::replace(&mut self.caller_args_ctx, in_ca);
        let saved_outer = std::mem::replace(&mut self.outer_ctx, in_outer);
        self.seam_args = seam;
        let target = self.cont(Pc::new(seg_base));
        self.seam_args.clear();
        self.body
            .set_terminator(self.cur, Terminator::Br { target });
        self.locals_ctx = saved_locals;
        self.args_ctx = saved_args;
        self.caller_locals_ctx = saved_caller_locals;
        self.caller_args_ctx = saved_caller_args;
        self.outer_ctx = saved_outer;
        self.stack = saved_stack;
        Ok(())
    }

    /// The outer chain a splice entered from here should carry: the frame
    /// `caller_*` currently describes, pushed in front of the frames above
    /// it. Innermost first, so index 0 is always the immediate caller of
    /// the frame `caller_*` names.
    fn push_outer_frame(&self) -> Vec<CallerFrame> {
        let mut v = Vec::with_capacity(self.outer_ctx.len() + 1);
        v.push(CallerFrame {
            locals: self.caller_locals_ctx.clone(),
            args: self.caller_args_ctx.clone(),
        });
        v.extend(self.outer_ctx.iter().cloned());
        v
    }

    /// Register (or reuse) the pc-space segment for the call site at
    /// synthetic pc `call_pc`; appends the callee's loop intervals offset
    /// by the base (token machinery sees callee loops natively).
    pub(super) fn ensure_seg(
        &mut self,
        call_pc: Pc,
        sid: ScriptId,
        callee: &'a Script,
        ret_pc: Pc,
        caller_depth: u32,
        frame_base: u32,
        is_construct: bool,
        argc: u16,
    ) -> u32 {
        if let Some(&i) = self.seg_by_call_pc.get(&(call_pc, sid)) {
            return self.segs[i].base;
        }
        debug_assert!(
            !self.splices_frozen,
            "a frozen splice set must not grow: pc space would renumber"
        );
        if self.seg_alloc == 0 {
            self.seg_alloc = u32::try_from(self.root_script.bytecode.len()).unwrap() + 8;
        }
        let base = self.seg_alloc;
        let end = base + u32::try_from(callee.bytecode.len()).unwrap();
        assert!(end <= MAX_PC, "inline pc space overflow");
        self.seg_alloc = end + 8;
        let callee_loops = super::translate::scan_loop_intervals(callee);
        let hot = hot_locals(callee);
        for (h, e) in callee_loops {
            self.loop_intervals.push((base + h, base + e));
        }
        self.segs.push(InlineSeg {
            base,
            end,
            sid,
            script: callee,
            call_pc,
            ret_pc,
            caller_depth,
            frame_base,
            parent: self.cur_seg,
            caller_operand_base: self.operand_base,
            hot,
            is_construct,
            argc,
            nformals: self.seg_nformals(sid, callee, argc),
            apply_fwd_pcs: self.callee_apply_fwd_pcs(sid, callee),
            this_alias_locals: compute_this_alias_locals(callee),
            live: {
                let source = self.source;
                let names = &self.atoms.names;
                let syn_gnames = self.ctx.syn_gnames;
                let bid_of = |idx: u32| -> Option<u32> {
                    let gc = *callee.gcthings.get(usize::try_from(idx).ok()?)?;
                    let SourceObject::String(st) = source.object(gc) else {
                        return None;
                    };
                    syn_gnames.get(&names.lookup(st)?).copied()
                };
                live::ScriptLive::shared(&mut self.live_cache, sid, callee, &bid_of)
            },
        });
        if self.gname_bids_scanned.insert(sid) {
            let (bids, methods) = super::translate::compute_gname_call_bids(
                self.source,
                callee,
                &self.atoms.names,
                self.ctx.syn_gnames,
            );
            for (cpc, bid) in bids {
                self.gname_call_bids.insert(Site::new(sid, cpc), bid);
            }
            for cpc in methods {
                self.gname_method_pcs.insert(Site::new(sid, cpc));
            }
        }
        self.seg_by_call_pc
            .insert((call_pc, sid), self.segs.len() - 1);
        self.spliced_cost += self.splice_closure_cost(sid, 0, usize::MAX - 1, None);
        self.inline_sites += 1;
        base
    }
}
