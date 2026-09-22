/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! The prediction: **one fact context per program point**, and the block
//! parameter contract that goes with it.
//!
//! This is the compiler's only fact store for emitted code. Every Opt block
//! at a pc reads the same prediction and therefore emits the same body; a
//! GEN block reads nothing, because a non-conforming execution carries no
//! facts. Token class and operand depth name a *block* -- they are what
//! makes the CFG reducible (DESIGN 4.9) -- and they do not name a
//! prediction: two blocks that differ only in those dimensions are
//! duplicates of one another, and would collapse into a single block on an
//! ISA that admitted irreducible control flow, with no dynamic path's code
//! changing.
//!
//! The type is split down the middle on purpose:
//!
//! - the **consult** half (`at`, `carried`) is what codegen may
//!   use. Codegen reads a prediction and emits code that enforces it; any
//!   execution that would diverge is shunted to GEN. It never mints a fact
//!   and never moves one.
//! - the **prediction** half (`join_arrival`, `set`, `widen_all`) belongs to
//!   the pass that computes the fixpoint. `theta` gates every call to it on
//!   `EmitMode::ContextOnly`, and debug-asserts the consultation contract in
//!   `Code`: every Opt arrival implies its program point's prediction.
//!
//! The pass is the emitter walked with its IR primitives suppressed
//! (`EmitMode::ContextOnly`), so the abstract transfer and the lowering are
//! one body of code; its result is this table, and emission is a function
//! of it.

use super::*;
use crate::constants::{CTXONLY_MAX_ROUNDS, STRIP_MAX_ROUNDS};

/// The fact context at each program point, plus the location contract.
#[derive(Default)]
pub(super) struct Predictions {
    /// The prediction, keyed by program point and nothing else. Absent
    /// means no Opt lineage reaches that pc.
    at: HashMap<Pc, Ctx>,
    /// The operand depth each prediction was minted at. Depth is a function
    /// of the pc on every ordinary edge; the one exception is an exceptional
    /// landing, which enters at the try note's unwound depth -- and those go
    /// to GEN, where there are no facts to misalign. A disagreement is a
    /// bug, and widening is how it stays sound.
    depth: HashMap<Pc, u16>,
    /// Which locals arrive as block params at a (pc, track). Keyed like the
    /// prediction, so every block there has one param layout. First arrival
    /// decides: this is a location, not a fact, and `cont_at` reconciles a
    /// mismatch with one frame load.
    carried: HashMap<(Pc, Track), Vec<u32>>,
    /// `--dump-peel` only: per loop header, the join of the arrivals from
    /// inside the loop (its back edges), kept apart from `at` so the peel
    /// census can compare the two.
    back_at: HashMap<Pc, Ctx>,
}

impl Predictions {
    // --- consult ---------------------------------------------------------

    /// The facts an Opt block at `pc` may assume. `None` where no Opt
    /// lineage reaches the point.
    pub(super) fn at(&self, pc: Pc) -> Option<&Ctx> {
        self.at.get(&pc)
    }

    pub(super) fn carried(&self, pc: Pc, track: Track) -> Option<&Vec<u32>> {
        self.carried.get(&(pc, track))
    }

    pub(super) fn back_at(&self, pc: Pc) -> Option<&Ctx> {
        self.back_at.get(&pc)
    }

    /// `--dump-peel` only: join a back-edge arrival at a loop header.
    pub(super) fn join_back(&mut self, pc: Pc, arrival: Ctx) {
        match self.back_at.get_mut(&pc) {
            None => {
                self.back_at.insert(pc, arrival);
            }
            Some(cur) => {
                if !arrival.implies(cur) {
                    *cur = arrival.join(cur);
                }
            }
        }
    }

    // --- the prediction pass ---------------------------------------------

    /// Join one Opt arrival into a program point's prediction. Returns
    /// whether the prediction moved, which is the pass's re-arm signal.
    pub(super) fn join_arrival(&mut self, pc: Pc, depth: u16, arrival: Ctx) -> bool {
        match self.depth.get(&pc) {
            None => {
                self.depth.insert(pc, depth);
            }
            Some(&d) if d != depth => {
                // Two Opt depths at one pc. LOUD: on the ordinary rungs
                // this should be unreachable, and it wipes a whole program
                // point's prediction, so a firing is worth chasing.
                log::warn!("night: predict: two Opt depths at pc {pc}: {d} and {depth}");
                // Two Opt depths at one pc. On the ordinary rungs this
                // cannot happen -- bytecode depth is a function of the pc,
                // and the one exception, an exceptional landing, goes to
                // GEN. On the `gen_only` rung it can: `gen_collapsed` maps
                // every track onto Opt, so the landing's stripped state
                // arrives here too. Either way the answer is the same and
                // it is sound: widen the whole prediction away.
                let moved = self.at.get(&pc).is_some_and(|c| {
                    !c.locals.is_empty()
                        || !c.stack.is_empty()
                        || !c.args.is_empty()
                        || !c.caller_locals.is_empty()
                        || !c.caller_args.is_empty()
                        || !c.gcells.is_empty()
                });
                self.at.insert(pc, Ctx::default());
                return moved;
            }
            Some(_) => {}
        }
        match self.at.get_mut(&pc) {
            None => {
                self.at.insert(pc, arrival);
                true
            }
            Some(cur) => {
                if arrival.implies(cur) {
                    return false;
                }
                // An arrival disagreeing only on intervals weakens them in
                // place (`join_iv_only`); an arrival disagreeing on
                // anything else takes the full join.
                let j = if arrival.implies_sans_iv(cur) {
                    cur.join_iv_only(&arrival)
                } else {
                    arrival.join(cur)
                };
                if j == *cur {
                    return false;
                }
                *cur = j;
                true
            }
        }
    }

    /// Overwrite a prediction outright. The on-ramp's funnel uses it to
    /// widen a header's stored intervals to what the recovering tail can
    /// deliver; nothing else may.
    pub(super) fn set(&mut self, pc: Pc, facts: Ctx) {
        self.at.insert(pc, facts);
    }

    /// The settled table, one line per program point (`--dump-ctxedge`).
    /// The mint and rejoin records say how a prediction got where it is;
    /// this says where it ended, which is what every Opt block at that pc
    /// actually reads. Needed because a version's ctx is a VIEW of this,
    /// and telling "the prediction is weak" from "this version's ctx
    /// diverged from it" is otherwise guesswork.
    pub(super) fn dump(&self, sid: ScriptId) {
        self.dump_tagged(sid, "");
    }

    pub(super) fn dump_tagged(&self, sid: ScriptId, tag: &str) {
        let mut pcs: Vec<&Pc> = self.at.keys().collect();
        pcs.sort();
        for pc in pcs {
            let c = &self.at[pc];
            let mut f: Vec<String> = Vec::new();
            for (i, s) in c.args.iter().enumerate() {
                if Bbv::viz_slot_interesting(s) {
                    let nm = if i == 0 {
                        "a_this".to_string()
                    } else {
                        format!("a{}", i - 1)
                    };
                    f.push(format!("{nm}={}", Bbv::viz_slot_str(s)));
                }
            }
            for (i, s) in c.locals.iter().enumerate() {
                if Bbv::viz_slot_interesting(s) {
                    f.push(format!("l{i}={}", Bbv::viz_slot_str(s)));
                }
            }
            for (i, s) in c.stack.iter().enumerate() {
                if Bbv::viz_slot_interesting(s) {
                    f.push(format!("s{i}={}", Bbv::viz_slot_str(s)));
                }
            }
            for (bid, s) in &c.gcells {
                f.push(format!("g{bid}={}", Bbv::viz_slot_str(s)));
            }
            crate::diag_line!(
                "night: ctxpred{tag} sid#{sid} pc {pc} facts [{}]",
                f.join(" ")
            );
        }
    }

    /// Record the first arrival's carried set for a (pc, track), and return
    /// the set. A location, not a fact: an arrival that lacks one of these
    /// locals supplies it with a frame load at the edge
    /// (`local_operand_for_edge`), so a mismatch costs one load and never
    /// correctness.
    ///
    /// First arrival wins. Taking the union of arrivals' proposals instead
    /// looks principled -- `kill_carriers` empties `locals_ssa` at every
    /// may-GC call, so a post-call edge proposes almost nothing, and since
    /// a call does not step the track that proposal reaches the same key
    /// as the strong one -- but it would add block params paid on every
    /// edge while the reload they save is paid only where the local is
    /// read, the same asymmetry that decides `carried_out`'s filter.
    pub(super) fn carried_join(&mut self, pc: Pc, track: Track, arr: &[u32]) -> (Vec<u32>, bool) {
        let e = self
            .carried
            .entry((pc, track))
            .or_insert_with(|| arr.to_vec());
        (e.clone(), false)
    }

    /// Widen every prediction to its facts-free form: the pass's
    /// compile-time escape hatch, sound in one direction only, and this is
    /// that direction -- every lineage implies the facts-free context.
    pub(super) fn widen_all(&mut self) {
        for c in self.at.values_mut() {
            *c = c.facts_free();
        }
    }

    /// Provenance rides the same joins but is invisible to `Eq` and
    /// `implies`, so an implied arrival would never deliver its bits. Census
    /// builds only; the prediction itself is already closed, so this changes
    /// no codegen.
    pub(super) fn or_prov(&mut self, pc: Pc, arrival: &Ctx) -> bool {
        let Some(cur) = self.at.get_mut(&pc) else {
            return false;
        };
        let mut changed = false;
        let mut or_into = |cur: &mut [SlotCtx], arr: &[SlotCtx]| {
            for (c, a) in cur.iter_mut().zip(arr.iter()) {
                let m = c.prov.or(a.prov);
                if !m.same_bits(c.prov) {
                    c.prov = m;
                    changed = true;
                }
            }
        };
        or_into(&mut cur.locals, &arrival.locals);
        or_into(&mut cur.stack, &arrival.stack);
        or_into(&mut cur.args, &arrival.args);
        or_into(&mut cur.caller_locals, &arrival.caller_locals);
        or_into(&mut cur.caller_args, &arrival.caller_args);
        changed
    }
}

/// Run the prediction to a fixpoint.
///
/// The pass walks the program with the emitter's IR primitives suppressed
/// (`EmitMode::ContextOnly`), so the abstract transfer function and the
/// lowering are one body of code and cannot drift apart -- the property the
/// whole design rests on. What it produces is this module's `Predictions`,
/// carried in `VerTable`, and emission is then a pure consumer of it.
///
/// Inside one walk the fixpoint is a **worklist over program points**: a
/// moved prediction re-arms exactly the blocks at that pc
/// (`Bbv::rearm_pc`). The outer rounds remain because a walk can still
/// discover blocks the previous walk never reached, and because the splice
/// set is only frozen after the first one.
pub(super) fn run(
    m: &mut Module,
    sig: waffle::Signature,
    ctx: &TranslateCtx,
    atoms: &mut AtomTable,
    source_id: ScriptId,
    script: &Script,
    rung: Rung,
    st: &mut State<'_>,
) -> Result<(), String> {
    loop {
        let mut t = Bbv::new(
            FunctionBody::new(m, sig),
            ctx,
            &mut *atoms,
            source_id,
            script,
        );
        t.is_global = rung.is_global;
        t.bigint_free = ctx.bigint_free;
        t.gen_only = rung.gen_only;
        t.fanout_off = rung.fanout_off;
        t.mode = EmitMode::ContextOnly;
        t.stripping = *st.stripping;
        t.vers = std::mem::take(st.vers);
        t.tok_classes = std::mem::take(st.tok_classes);
        if let Some(sp) = st.splices.take() {
            t.adopt_splices(sp);
        }
        // An unsupported op is a skip, not an error: the fixpoint walks
        // the same program the Code pass would, so it hits the same
        // refusals, and they have to reach the same handler.
        t.emit()?;
        let changed = t.map_changed;
        *st.vers = std::mem::take(&mut t.vers);
        *st.tok_classes = std::mem::take(&mut t.tok_classes);
        *st.splices = Some(t.take_splices());
        if ctx.opts.diagnostics.bbv {
            crate::diag_line!(
                "night: bbv script#{source_id} predict round {} discover {} join {} versions {}",
                *st.rounds,
                t.changed_discover,
                t.changed_join,
                st.vers.len()
            );
        }
        if ctx.opts.diagnostics.ctxedge {
            st.vers
                .pred
                .dump_tagged(source_id, &format!("-r{}", *st.rounds));
        }
        if !changed {
            // Provenance-only extension rounds (census/dump builds
            // only): the ctx map is closed, so codegen is settled,
            // but implied arrivals deliver their provenance bits
            // one hop per walk. Bounded (the bits are finite and
            // only accumulate); never counts toward the strip cap.
            if (ctx.opts.instrument.guards || ctx.opts.diagnostics.ctxedge)
                && t.prov_changed
                && *st.prov_rounds < 32
            {
                *st.prov_rounds += 1;
                continue;
            }
            break;
        }
        *st.rounds += 1;
        // The strip path must keep iterating, never break straight
        // into `Code`: widening every ctx changes which arms the walk
        // takes, so the stripped program has versions the pre-strip
        // rounds never minted, and `Code` must not be the pass that
        // discovers them -- that is exactly what the closure
        // invariant forbids. Two more rounds settle it and no more:
        // once every ctx is stripped, a version's ctx is determined
        // by its own identity, so no arrival can move one, so the
        // round after the first stripped walk finds nothing new.
        // The cap scales with the version population (rounds needed
        // are bounded by lattice height x the version-dependency
        // chain); the floor covers small scripts. Convergence is
        // guaranteed (finite height, joins only descend), so any
        // firing is a bug to chase, and the strip is a loud safety
        // net, never policy.
        let cap = CTXONLY_MAX_ROUNDS.max(u32::try_from(st.vers.len()).unwrap_or(u32::MAX) / 4);
        if *st.rounds >= cap && !*st.stripping {
            log::warn!(
                "night: bbv script#{source_id} widened at round {} cap {cap} ({} versions)",
                *st.rounds,
                st.vers.len()
            );
            st.vers.strip_all();
            *st.stripping = true;
        } else if *st.rounds >= cap + STRIP_MAX_ROUNDS {
            // Unreachable by the argument above; the closure check
            // below is what keeps it sound if the argument is wrong.
            break;
        }
    }
    if ctx.opts.diagnostics.bbv {
        crate::diag_line!(
            "night: bbv script#{source_id} predict rounds {} versions {}",
            *st.rounds,
            st.vers.len()
        );
    }
    if ctx.opts.diagnostics.ctxedge {
        st.vers.pred.dump(source_id);
    }
    Ok(())
}

/// Which rung of the compile ladder this walk is on (section 4.12).
#[derive(Clone, Copy)]
pub(super) struct Rung {
    pub(super) is_global: bool,
    pub(super) gen_only: bool,
    pub(super) fanout_off: bool,
}

/// The state carried between walks: everything whose identity must name the
/// same thing in walk N+1 that it named in walk N.
pub(super) struct State<'s> {
    pub(super) vers: &'s mut VerTable,
    pub(super) tok_classes: &'s mut HashMap<Vec<(u32, u64)>, u32>,
    pub(super) splices: &'s mut Option<Splices>,
    pub(super) stripping: &'s mut bool,
    pub(super) rounds: &'s mut u32,
    pub(super) prov_rounds: &'s mut u32,
}
