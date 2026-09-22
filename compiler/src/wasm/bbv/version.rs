/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Version identity and the driver: `Ver`/`VerTable`, the token vectors,
//! carriers, `theta`, the continuation seam, and the workqueue drain.

use super::predict::Predictions;
use super::*;

/// A version identity: the pc, the enclosing-loop token class, and the
/// track. The point of the whole design is that this is structural -- it
/// does not mention the ctx -- so the ctx becomes derived data (the join of
/// everything that reaches the identity, computed by the `ContextOnly`
/// fixpoint) instead of "whichever lineage arrived first". Two consequences
/// fall out: tokens naming a version stay stable across fixpoint rounds, and
/// version count is bounded by construction at three per (pc, token class),
/// which is what retires every mint budget.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(super) struct Ver {
    pub(super) pc: Pc,
    pub(super) class: u32,
    pub(super) track: Track,
    /// The operand-stack depth the version is entered with. For ordinary
    /// edges this is a function of the pc (bytecode depth is deterministic)
    /// and so costs nothing; it is in the identity because an exceptional
    /// landing enters a pc with the try note's unwound depth, which is a
    /// second, equally legitimate depth for the same pc.
    pub(super) depth: u16,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(super) struct VerId(pub(super) u32);

/// Interned block identities, plus the prediction they read.
///
/// The two halves are different kinds of thing and are now stored as such.
/// `vers` is STRUCTURAL identity -- pc, token class, track, depth -- and it
/// names a *block*: the token machinery duplicates blocks to keep every
/// cycle single-entry (DESIGN 4.9), which is reducibility and is not a fact
/// question. `pred` is the FACT context, keyed by program point alone
/// (`predict.rs`). Both persist across prediction rounds and into the `Code`
/// pass.
#[derive(Default)]
pub(super) struct VerTable {
    pub(super) ids: HashMap<Ver, VerId>,
    pub(super) vers: Vec<Ver>,
    /// Per-identity emission context: the prediction at its pc (or nothing,
    /// on GEN) plus that identity's own tokens, carried set and track. Pure
    /// derived data -- `pred` is the only thing the fixpoint moves.
    pub(super) ctx: Vec<Option<Ctx>>,
    /// THE PREDICTION, and the only fact store emitted code reads: one
    /// context per program point, on the Opt track (`predict.rs`).
    pub(super) pred: Predictions,
    /// The identities at each program point: the prediction's dependents.
    /// A moved prediction re-arms exactly these, which is what makes the
    /// pass a worklist over program points instead of a sequence of
    /// whole-program re-walks.
    pub(super) at_pc: HashMap<Pc, Vec<VerId>>,
}

impl VerTable {
    pub(super) fn intern(&mut self, v: Ver) -> VerId {
        if let Some(&id) = self.ids.get(&v) {
            return id;
        }
        let id = VerId(u32::try_from(self.vers.len()).unwrap());
        self.vers.push(v);
        self.ctx.push(None);
        self.ids.insert(v, id);
        self.at_pc.entry(v.pc).or_default().push(id);
        id
    }

    pub(super) fn ver(&self, id: VerId) -> Ver {
        self.vers[id.0 as usize]
    }

    pub(super) fn ctx(&self, id: VerId) -> &Ctx {
        self.ctx[id.0 as usize]
            .as_ref()
            .expect("version ctx not computed")
    }

    pub(super) fn len(&self) -> usize {
        self.vers.len()
    }

    /// Widen every version straight to its all-TOP ctx: the fixpoint's
    /// compile-time escape hatch. Sound in one direction only, and this is
    /// that direction -- every lineage implies the stripped ctx.
    ///
    /// The caller must set `Bbv::stripping` and keep iterating after this.
    /// Stripping is not just a widening of the existing map: it changes which
    /// arms the walk takes, so it brings versions into existence that the
    /// pre-strip rounds never minted, and those have to be discovered by
    /// `ContextOnly` rather than by `Code`.
    pub(super) fn strip_all(&mut self) {
        for ctx in self.ctx.iter_mut().flatten() {
            *ctx = ctx.stripped();
        }
        self.pred.widen_all();
    }
}

impl<'a> Bbv<'a> {
    /// Locals-into-SSA: the locals a version at `(tgt_seg, ctx)` carries as
    /// block params -- every local the frame's script touches. Derivable
    /// from (pc, ctx) alone, so edge builders and `run_version` always agree
    /// on the param layout; GEN versions carry nothing.
    ///
    /// Every local, not just the ones with a proven fact: a value needs a
    /// carrier because it is live, not because its type is known. Gating on
    /// facts makes a TOP-fact local re-read from the frame at every use, and
    /// un-carried reads are where the frame traffic actually is -- several
    /// times the loads at near-identical store counts. An unwritten local is
    /// `undefined` (the prologue stores it) and its carrier costs one
    /// const-folded param.
    pub(super) fn carried_for(&self, _tgt_seg: Option<usize>, ctx: &Ctx) -> Vec<u32> {
        ctx.carried.clone()
    }

    /// The ctx slot a carried key names: a local, or (`STALE_ARG` set) a
    /// formal.
    pub(super) fn carried_slot(ctx: &Ctx, key: u32) -> SlotCtx {
        if key & STALE_ARG != 0 {
            ctx.arg(1 + (key & !STALE_ARG) as usize)
        } else if key & OUTER_LOCAL != 0 {
            ctx.caller_locals
                .get((key & !OUTER_LOCAL) as usize)
                .copied()
                .unwrap_or(SlotCtx::TOP)
        } else {
            ctx.local(key as usize)
        }
    }

    /// Whether an edge from the active frame into `tgt_seg` ENTERS a splice
    /// of it (the target segment's parent is the active frame).
    pub(super) fn edge_enters_child(&self, tgt_seg: Option<usize>) -> bool {
        tgt_seg != self.ssa_seg && tgt_seg.is_some_and(|i| self.segs[i].parent == self.ssa_seg)
    }

    /// Whether an edge from the active frame into `tgt_seg` RETURNS from a
    /// splice (the target is the active segment's parent).
    pub(super) fn edge_returns(&self, tgt_seg: Option<usize>) -> bool {
        self.ssa_seg.is_some_and(|i| self.segs[i].parent == tgt_seg)
    }

    /// The segment the active frame's `outer_ssa` belongs to.
    fn outer_seg(&self) -> Option<usize> {
        self.ssa_seg.and_then(|i| self.segs[i].parent)
    }

    pub(super) fn raw_repr(r: Repr) -> bool {
        matches!(r, Repr::I32 | Repr::F64 | Repr::Bool | Repr::I64)
    }

    /// Whether the frame slot carried key `key` names (a local or a
    /// `STALE_ARG` formal of the frame owning `seg`) may be read at `pc`
    /// before it is written. `pc` is in the unified space; `seg` is its
    /// segment.
    pub(super) fn key_live_at(&self, seg: Option<usize>, pc: Pc, key: u32) -> bool {
        let (live, base) = match seg {
            Some(i) => (&self.segs[i].live, self.segs[i].base),
            None => (&self.live_root, 0),
        };
        let local_pc = pc.get() - base;
        if key & STALE_ARG != 0 {
            live.arg_live(local_pc, key & !STALE_ARG)
        } else {
            live.local_live(local_pc, key)
        }
    }

    /// Whether a value fact for binding `bid` can still be consumed from
    /// `pc` (unified space, in segment `seg`): a later `GetGName` of it in
    /// the segment's script, or -- the fact rides through a splice -- in
    /// the parent after the segment returns, recursively.
    pub(super) fn gcell_live_at(&self, seg: Option<usize>, pc: Pc, bid: u32) -> bool {
        let (live, base) = match seg {
            Some(i) => (&self.segs[i].live, self.segs[i].base),
            None => (&self.live_root, 0),
        };
        if live.gcell_live(pc.get() - base, bid) {
            return true;
        }
        match seg {
            Some(i) => self.gcell_live_at(self.segs[i].parent, self.segs[i].ret_pc, bid),
            None => false,
        }
    }

    /// Whether the parent frame's local `l` (an `OUTER_LOCAL` carrier of
    /// segment `seg`) may be read after the splice returns: liveness at the
    /// segment's return pc in the parent's space.
    pub(super) fn outer_live_after(&self, seg: Option<usize>, l: u32) -> bool {
        let Some(i) = seg else {
            return true;
        };
        self.key_live_at(self.segs[i].parent, self.segs[i].ret_pc, l)
    }

    /// Write the parent frame's raw carriers an edge does not carry onward
    /// back to their slots: every one of them is conservatively stale (the
    /// seam that brought them in did not flush them).
    pub(super) fn flush_outer_dropped(&mut self, tgt_seg: Option<usize>, ctx: &Ctx) {
        if self.outer_ssa.iter().all(Option::is_none) {
            return;
        }
        let same = tgt_seg == self.ssa_seg;
        let returning = self.edge_returns(tgt_seg);
        let base = self.frame_local_base_of(self.outer_seg());
        for l in 0..self.outer_ssa.len() {
            let Some((val, repr)) = self.outer_ssa[l] else {
                continue;
            };
            let l32 = u32::try_from(l).unwrap();
            // Riding means riding RAW at the target: a param the target's
            // fact would box is a carrier a later kill sweeps with the slot
            // still stale, so it is written back here instead.
            let key = if same {
                OUTER_LOCAL | l32
            } else if returning {
                l32
            } else {
                continue_flush(self, base, l32, val, repr);
                continue;
            };
            let rides = ctx.carried.contains(&key)
                && Self::raw_repr(Self::slot_repr(&Self::carried_slot(ctx, key)));
            if rides || !self.outer_live_after(self.ssa_seg, l32) {
                continue;
            }
            continue_flush(self, base, l32, val, repr);
        }
        fn continue_flush(s: &mut Bbv<'_>, base: u32, l32: u32, val: Value, repr: Repr) {
            let slot = s
                .caller_locals_ctx
                .get(l32 as usize)
                .copied()
                .unwrap_or(SlotCtx::TOP);
            let mut o = Operand::from_slot(val, slot, SlotRef::Local(l32));
            o.repr = repr;
            let boxed = s.to_boxed(&o);
            s.store_i64(s.vp, base + 8 * l32, boxed);
        }
    }

    /// The edge value for carried key `key` (see `carried_slot`).
    pub(super) fn carried_operand_for_edge(&mut self, tgt_seg: Option<usize>, key: u32) -> Operand {
        if key & STALE_ARG != 0 {
            self.arg_operand_for_edge(tgt_seg, u16::try_from(key & !STALE_ARG).unwrap())
        } else if key & OUTER_LOCAL != 0 {
            self.outer_operand_for_edge(tgt_seg, key & !OUTER_LOCAL)
        } else {
            self.local_operand_for_edge(tgt_seg, key)
        }
    }

    /// The edge value for the parent frame's local `l` riding into
    /// `tgt_seg` as an outer carrier: the parent's own carrier when the edge
    /// enters the splice, the riding value when it stays inside it, else a
    /// boxed load of the parent's slot.
    fn outer_operand_for_edge(&mut self, tgt_seg: Option<usize>, l: u32) -> Operand {
        let fact = self
            .caller_locals_ctx
            .get(l as usize)
            .copied()
            .unwrap_or(SlotCtx::TOP);
        // The key names a local of the TARGET segment's parent. Entering
        // the target, that parent is the active frame and the value is its
        // live carrier; inside it, the riding value; on a return into it
        // (its own outer carriers, the grandparent's locals), nothing is
        // held here and the slot -- flushed when this segment was entered
        // -- is the truth.
        let owner = tgt_seg.and_then(|i| self.segs[i].parent);
        let held = if self.edge_enters_child(tgt_seg) {
            self.locals_ssa.get(l as usize).copied().flatten()
        } else if tgt_seg == self.ssa_seg {
            self.outer_ssa.get(l as usize).copied().flatten()
        } else {
            None
        };
        let (val, repr) = match held {
            Some(c) => c,
            None => {
                let base = self.frame_local_base_of(owner);
                (self.load_i64(self.vp, base + 8 * l), Repr::Boxed)
            }
        };
        Operand {
            val,
            repr,
            ty: fact.to_ty(),
            range: fact.range,
            cls: fact.cls,
            cls_shallow: fact.cls_shallow,
            cls_slots: fact.cls_slots,
            ta: fact.ta,
            likely_cls: fact.likely_cls,
            src: None,
            iv: fact.iv.map(|r| (r.lo, r.hi, false)),
            fresh: false,
            prov: fact.prov,
        }
    }

    /// The carried set an edge into `tgt_seg` proposes: the locals we hold a
    /// live SSA value for. Cross-frame seams carry nothing -- the callee's
    /// locals are freshly undef-stored, and after a return the caller's
    /// carriers are stale (the callee may have GC'd), so the frame is the
    /// truth on both.
    ///
    /// The filter is liveness and nothing wider. Proposing every local the
    /// script touches -- so that a may-GC sweep could never erode the set --
    /// loses across the corpus, and so does the narrow form of the same idea
    /// (re-offering only what a may-GC call swept). An edge load is paid on
    /// Every edge, and at this many versions per pc that costs more than the
    /// lazy frame read it replaces, which is paid only where the local is
    /// actually read.
    pub(super) fn carried_out(&self, tgt_seg: Option<usize>, succ_pc: Pc) -> Vec<u32> {
        if tgt_seg != self.ssa_seg {
            // The two seams of a splice carry the PARENT's raw locals
            // through it (`OUTER_LOCAL`): the values are GC-immune by repr
            // and the callee cannot see the slots, so the seam has no
            // reason to box them into the frame and the return no reason
            // to load them back. Only raw ones -- a boxed carrier does not
            // survive the callee's GCs -- and only where the target's fact
            // for the slot keeps the repr raw, or the param would be boxed.
            let mut out: Vec<u32> = if self.edge_enters_child(tgt_seg) {
                let mut out: Vec<u32> = (0..self.locals_ssa.len())
                    .filter(|&l| {
                        self.locals_ssa[l].is_some_and(|(_, r)| Self::raw_repr(r))
                            && Self::raw_repr(Self::slot_repr(
                                &self
                                    .caller_locals_ctx
                                    .get(l)
                                    .copied()
                                    .unwrap_or(SlotCtx::TOP),
                            ))
                    })
                    .map(|l| OUTER_LOCAL | u32::try_from(l).unwrap())
                    .filter(|&k| self.outer_live_after(tgt_seg, k & !OUTER_LOCAL))
                    .collect();
                // The seam's raw actuals ride in as the callee's formal
                // carriers where the entry fact keeps them raw
                // (`args_ctx` is the callee's entry vector here).
                out.extend(
                    self.seam_raw_formals(tgt_seg)
                        .map(|a| STALE_ARG | a)
                        .filter(|&k| self.key_live_at(tgt_seg, succ_pc, k)),
                );
                out
            } else if self.edge_returns(tgt_seg) {
                (0..self.outer_ssa.len())
                    .filter(|&l| {
                        self.outer_ssa[l].is_some_and(|(_, r)| Self::raw_repr(r))
                            && Self::raw_repr(Self::slot_repr(
                                &self.locals_ctx.get(l).copied().unwrap_or(SlotCtx::TOP),
                            ))
                    })
                    .map(|l| u32::try_from(l).unwrap())
                    .filter(|&k| self.key_live_at(tgt_seg, succ_pc, k))
                    .collect()
            } else {
                Vec::new()
            };
            out.sort_unstable();
            return out;
        }
        let hot = match tgt_seg {
            Some(i) => &self.segs[i].hot,
            None => &self.hot_root,
        };
        let mapped_args = match tgt_seg {
            Some(i) => self.segs[i].script.has_mapped_args,
            None => self.root_script.has_mapped_args,
        };
        // A formal is proposed whether or not it has a live carrier: its
        // frame slot holds a value from the activation's first instruction,
        // so an edge without the carrier supplies the param with one load
        // (`arg_operand_for_edge`), and a loop header entered once from
        // above then carries every formal RAW around the loop -- a narrower
        // liveness filter would carry only the formals read before the
        // loop, leaving every deferred SetArg's store to land on the back
        // edge with each read reloading the frame.
        // A slot the target cannot read before writing needs no carrier:
        // the write mints one.
        let mut out: Vec<u32> = hot
            .iter()
            .copied()
            .filter(|&l| {
                if l & STALE_ARG != 0 {
                    !mapped_args
                } else {
                    self.locals_ssa.get(l as usize).copied().flatten().is_some()
                }
            })
            .filter(|&l| self.key_live_at(tgt_seg, succ_pc, l))
            .collect();
        // The parent's carriers riding through this segment stay on every
        // edge inside it whose target keeps them raw.
        out.extend((0..self.outer_ssa.len()).filter_map(|l| {
            let raw = self.outer_ssa[l].is_some_and(|(_, r)| Self::raw_repr(r))
                && Self::raw_repr(Self::slot_repr(
                    &self
                        .caller_locals_ctx
                        .get(l)
                        .copied()
                        .unwrap_or(SlotCtx::TOP),
                ))
                && self.outer_live_after(tgt_seg, u32::try_from(l).unwrap());
            raw.then(|| OUTER_LOCAL | u32::try_from(l).unwrap())
        }));
        out.sort_unstable();
        out
    }

    /// The formals the seam stash can hand `tgt_seg` raw: a raw actual
    /// whose entry fact keeps the slot raw, on a callee whose formals are
    /// not aliased by an arguments object.
    fn seam_raw_formals(&self, tgt_seg: Option<usize>) -> impl Iterator<Item = u32> + '_ {
        let seg = tgt_seg.map(|i| &self.segs[i]);
        let ok = seg.is_some_and(|s| !s.script.has_mapped_args);
        let nformals = seg.map_or(0, |s| usize::from(s.nformals));
        self.seam_args
            .iter()
            .enumerate()
            .take(if ok { nformals } else { 0 })
            .filter_map(move |(a, o)| {
                let o = o.as_ref()?;
                let fact = self.args_ctx.get(1 + a).copied().unwrap_or(SlotCtx::TOP);
                (Self::raw_repr(o.repr) && Self::raw_repr(Self::slot_repr(&fact)))
                    .then(|| u32::try_from(a).unwrap())
            })
    }

    /// The edge value for carried formal `a` of the frame owning `tgt_seg`:
    /// the live carrier when the edge stays in the carriers' frame, else a
    /// load from the target frame's arg slot (the `local_operand_for_edge`
    /// rule -- a version's `carried_args` was proposed by a same-frame
    /// arrival, but a cross-frame edge into it, e.g. a splice return, must
    /// still supply the params, and the current view's addressing would
    /// read the wrong frame).
    pub(super) fn arg_operand_for_edge(&mut self, tgt_seg: Option<usize>, argno: u16) -> Operand {
        let held = if tgt_seg == self.ssa_seg {
            self.args_ssa.get(usize::from(argno)).copied().flatten()
        } else if self.edge_enters_child(tgt_seg) {
            self.seam_args
                .get(usize::from(argno))
                .and_then(|o| o.as_ref().map(|o| (o.val, o.repr)))
        } else {
            None
        };
        let fact = if held.is_some() || tgt_seg == self.ssa_seg {
            self.args_ctx
                .get(1 + usize::from(argno))
                .copied()
                .unwrap_or(SlotCtx::TOP)
        } else {
            SlotCtx::TOP
        };
        let (val, repr) = match held {
            Some(c) => c,
            None => {
                let v = match tgt_seg {
                    Some(i) => {
                        let base = self.segs[i].frame_base;
                        self.load_i64(self.vp, base + 16 + 8 * u32::from(argno))
                    }
                    None => self.load_i64(self.sp, 16 + 8 * u32::from(argno)),
                };
                (v, Repr::Boxed)
            }
        };
        Operand {
            val,
            repr,
            ty: fact.to_ty(),
            range: fact.range,
            cls: fact.cls,
            cls_shallow: fact.cls_shallow,
            cls_slots: fact.cls_slots,
            ta: fact.ta,
            likely_cls: fact.likely_cls,
            src: None,
            iv: fact.iv.map(|r| (r.lo, r.hi, false)),
            fresh: false,
            prov: fact.prov,
        }
    }

    /// The local-region byte offset from vp of the frame owning `seg`.
    pub(super) fn frame_local_base_of(&self, seg: Option<usize>) -> u32 {
        match seg {
            Some(i) => self.segs[i].frame_base + 16 + 8 * u32::from(self.segs[i].nformals),
            None => self.root_local_base,
        }
    }

    /// The edge value for carried local `l` of the frame owning `tgt_seg`:
    /// the live carrier when the edge stays in the carriers' frame, else a
    /// boxed load of the target frame's slot (cross-splice edges; the frame
    /// is the rooted truth). The attached fact is the edge's tracked fact
    /// for the slot (`locals_ctx` is already the target frame's vector at
    /// the splice entry/return seams), which implies the target ctx's fact
    /// and so licenses the target-repr conversion.
    pub(super) fn local_operand_for_edge(&mut self, tgt_seg: Option<usize>, l: u32) -> Operand {
        let fact = self
            .locals_ctx
            .get(l as usize)
            .copied()
            .unwrap_or(SlotCtx::TOP);
        let (val, repr) = match if tgt_seg == self.ssa_seg {
            self.locals_ssa.get(l as usize).copied().flatten()
        } else if self.edge_returns(tgt_seg) {
            self.outer_ssa.get(l as usize).copied().flatten()
        } else {
            None
        } {
            Some(c) => c,
            None => {
                let base = self.frame_local_base_of(tgt_seg);
                (self.load_i64(self.vp, base + 8 * l), Repr::Boxed)
            }
        };
        Operand {
            val,
            repr,
            ty: fact.to_ty(),
            range: fact.range,
            cls: fact.cls,
            cls_shallow: fact.cls_shallow,
            cls_slots: fact.cls_slots,
            ta: fact.ta,
            likely_cls: fact.likely_cls,
            src: None,
            iv: fact.iv.map(|r| (r.lo, r.hi, false)),
            fresh: false,
            prov: fact.prov,
        }
    }

    /// Locals-into-SSA CallGc sweep: a moving GC relocates GC things, so a
    /// carrier whose value may be one dies at the call (the frame slot, which
    /// the GC updates in place, is the truth). Raw-number reprs and boxed
    /// values whose fact excludes GC things survive.
    ///
    /// Reloading the swept carriers here, so the call cannot demote the
    /// region behind it, does not typecheck as SSA: a may-GC call is often
    /// emitted inside a diamond arm, so a value defined at the sweep point
    /// does not dominate the merge that follows. Offering them on the
    /// out-edge instead (the place that dominates by construction) does
    /// build, and it is a measured loss -- see `carried_out`.
    pub(super) fn kill_carriers(&mut self) {
        for i in 0..self.locals_ssa.len() {
            let Some((_, r)) = self.locals_ssa[i] else {
                continue;
            };
            let immune = match r {
                Repr::I32 | Repr::Bool | Repr::F64 | Repr::I64 => true,
                Repr::StrPtr | Repr::ObjPtr => false,
                Repr::Boxed => {
                    let f = self.locals_ctx.get(i).copied().unwrap_or(SlotCtx::TOP);
                    !f.outside
                        && f.prims.subset_of(
                            PRIM_INT32 | PRIM_DOUBLE | PRIM_BOOLEAN | PRIM_UNDEFINED | PRIM_NULL,
                        )
                }
            };
            if !immune {
                self.locals_ssa[i] = None;
            }
        }
        // The formals' carriers: raw reprs survive (an I32/F64 in SSA is
        // not a GC thing, and its deferred frame store is the only copy --
        // dropping it here reads the stale slot back: frame-deferred-arg.js
        // hangs); a boxed carrier does not, the frame slot being the copy
        // the GC updates.
        for a in &mut self.args_ssa {
            if !matches!(
                *a,
                Some((_, Repr::I32 | Repr::Bool | Repr::F64 | Repr::I64))
            ) {
                *a = None;
            }
        }
        for o in &mut self.outer_ssa {
            if !matches!(
                *o,
                Some((_, Repr::I32 | Repr::Bool | Repr::F64 | Repr::I64))
            ) {
                *o = None;
            }
        }
    }

    // --- theta + the continuation seam ----------------------------------

    /// Intern a token vector as a small class id (theta budgets are
    /// per-(pc, class)).
    pub(super) fn tok_class(&mut self, toks: &[(u32, u64)]) -> u32 {
        if let Some(&c) = self.tok_classes.get(toks) {
            return c;
        }
        let c = u32::try_from(self.tok_classes.len()).unwrap();
        self.tok_classes.insert(toks.to_vec(), c);
        c
    }

    /// Every enclosing call site of `pc`, innermost first (each in its own
    /// pc space), for loop-membership tests: spliced code is loop-interior
    /// code of its caller, so a synthetic segment pc is tested through the
    /// caller-space call site it came from. Without that mapping a splice
    /// tail reads as a TOK_SIDE entry and its back edges erode to GEN.
    ///
    /// Membership must try every level, not just the root-space site: a
    /// segment's loop intervals live in the pc space of the frame that owns
    /// them, so for a nested splice only the site at the matching level can
    /// fall inside a given interval. Collapsing to the root site makes a
    /// nested splice inside a callee loop read as a SIDE entry, whose return
    /// edge then gives that loop's cycle a second entry -- irreducible.
    /// Hoisted out of the per-interval loops: `seg_of` is a linear scan.
    pub(super) fn seg_sites(&self, pc: Pc) -> Vec<u32> {
        let mut out = Vec::new();
        if self.fanout_off {
            return out;
        }
        let mut cur = self.seg_of(pc);
        while let Some(i) = cur {
            let site = self.segs[i].call_pc;
            out.push(site.get());
            cur = self.seg_of(site);
        }
        out
    }

    /// The per-loop header tokens an edge from the current emission point
    /// to `succ_pc` carries: for each loop whose body strictly contains
    /// `succ_pc` -- an edge to
    /// the header drops that loop's token (the target IS a new top); an
    /// in-loop edge keeps the current token (or hands out the current
    /// version's own key when it IS that header); an edge from outside the
    /// loop that bypasses the header is a SIDE entry. A post-call flow
    /// ORs TOK_DIRTY into every carried token; the explicit header check
    /// precedes the ctx lookup because twin headers carry an own-loop
    /// marker entry that must not leak to their bodies (each twin hands
    /// out its own key).
    pub(super) fn out_tokens_for(&self, succ_pc: Pc) -> Vec<(u32, u64)> {
        if self.gen_only {
            // GEN-only is one version per pc, so it is reducible without
            // any token dimension at all.
            return Vec::new();
        }
        let cur_tokens = &self.cur_tokens;
        let succ_site = self.seg_sites(succ_pc);
        let cur_site = self.seg_sites(self.cur_pc);
        let in_loop = |pc: Pc, sites: &[u32], h: u32, e: u32| {
            (pc >= Pc::new(h) && pc < Pc::new(e)) || sites.iter().any(|&s| s >= h && s < e)
        };
        // The shared peel, marker form: a non-Opt lineage's marker for an
        // enclosing loop is peel unless it is the loop's dirty-cycle
        // membership (cycle, handed at non-Opt headers); an Opt lineage's
        // marker is OPT from that loop's Opt header, or peel on a side entry
        // (entered the body without passing a header -- load-bearing for
        // reducibility).
        // This collapses the acyclic per-(fork-point x outer-history)
        // chains to one funnel per loop while every cycle stays entered
        // at its header only.
        let peel = self.cur_track != Track::Opt;
        let mut out = Vec::new();
        for (idx, &(h, e)) in self.loop_intervals.iter().enumerate() {
            let idx = u32::try_from(idx).unwrap();
            if !in_loop(succ_pc, &succ_site, h + 1, e) {
                // The twin-header own-loop marker: a recovery-twin
                // lineage's Opt back edge to its own header KEEPS the
                // marker, so the edge re-targets the twin -- dropping it
                // like a steady token would aim the back edge at the
                // steady header, whose preheader entry two-heads the
                // composite cycle.
                if succ_pc == Pc::new(h)
                    && self.cur_track == Track::Opt
                    && in_loop(self.cur_pc, &cur_site, h, e)
                    && cur_tokens
                        .iter()
                        .any(|&(i, t)| i == idx && t == TOK_RECOVER)
                {
                    out.push((idx, TOK_RECOVER));
                }
                continue;
            }
            let tok = if !in_loop(self.cur_pc, &cur_site, h, e) {
                TOK_PEEL
            } else if self.cur_pc == Pc::new(h) {
                if self.vers.ver(self.cur_ver).track != Track::Opt {
                    TOK_CYCLE
                } else if cur_tokens
                    .iter()
                    .any(|&(i, t)| i == idx && t == TOK_RECOVER)
                {
                    // The recovery twin hands its body its own marker.
                    TOK_RECOVER
                } else {
                    TOK_OPT
                }
            } else if let Some(&(_, t)) = cur_tokens.iter().find(|&&(i, _)| i == idx) {
                if peel && (t == TOK_RECOVER || t == TOK_RECOVER_PEEL) {
                    // A twin excursion funnels into the twin's OWN peel
                    // class, never the shared one (see TOK_RECOVER_PEEL).
                    TOK_RECOVER_PEEL
                } else if peel && !self.cycle_tok(t) {
                    TOK_PEEL
                } else {
                    t
                }
            } else if peel {
                TOK_PEEL
            } else {
                TOK_OPT
            };
            out.push((idx, tok));
        }
        out
    }

    /// Whether a carried token is the dirty-cycle membership the peel
    /// keeps: TOK_CYCLE alone. Opt-header keys (a lineage that track-stepped
    /// mid-body still carries the Opt header's token) and the other
    /// sentinels are not.
    pub(super) fn cycle_tok(&self, t: u64) -> bool {
        t == TOK_CYCLE
    }

    /// The merge point, and it holds no policy at all: an edge's version is
    /// its structural identity (pc, token class, track) and its ctx is
    /// whatever the `ContextOnly` fixpoint joined for that identity. Which
    /// lineage defines a pc, how many versions a pc may have, and when to
    /// widen are all answered by construction rather than decided here.
    ///
    /// The discriminator is structural, never the ctx pair. Deciding from
    /// the pair -- absorb into an existing version when its ctx is weaker,
    /// or mint before absorbing -- silently discards the incoming lineage's
    /// facts whenever the weaker version wins, and in a numeric kernel the
    /// weak version is typically the one a slow arm produced (`+` pushes
    /// `bottom_ty()` because it may concat), so a whole int lineage lands on
    /// a fully generic site. The track split is what fixes that at the
    /// source: such a slow arm is a `side_arm`, so it sits on `Side` and can
    /// no longer define the pc for the int lineage that fell through.
    /// The operand depth a version identity names. A stack deeper than
    /// `u16::MAX` cannot be keyed; clamp and let the drain refuse the
    /// script rather than aborting the process.
    fn key_depth(&mut self) -> u16 {
        u16::try_from(self.stack.len()).unwrap_or_else(|_| {
            self.depth_overflow = true;
            u16::MAX
        })
    }

    pub(super) fn theta(&mut self, pc: Pc, ctx_in: Ctx) -> VerId {
        // GEN-only (the ladder's bottom rung) is one facts-empty version per
        // pc: no tokens, no tracks, exactly the generic lane.
        let ctx_in = if self.gen_only {
            ctx_in.gen_collapsed()
        } else if self.stripping {
            ctx_in.stripped()
        } else {
            ctx_in
        };
        // Side folds into Dirty at the version key. Two tracks matter --
        // the optimized lane and the generic one -- and Side was only a
        // third way of saying "not Opt". Keeping it separate bought one
        // thing, a side arm's ctx not meeting a post-call ctx at the same
        // pc, which is not worth a duplicate version chain for Side's
        // small share of dynamic entries.
        //
        // `cur_track` still steps to Side during an arm's own emission, so
        // the arm-local reads (the fork gates) see it; only the successor
        // version is folded. The enum keeps three values for that reason.
        let ctx_in = if ctx_in.track == Track::Side {
            Ctx {
                track: Track::Dirty,
                ..ctx_in
            }
        } else {
            ctx_in
        };
        // GEN carries no facts. Out-of-lining made every GEN op body a
        // generic helper call, so no fact reaches a lowering decision
        // there, and a typed carrier only buys an edge conversion the
        // callee immediately reboxes. `carried` survives: which locals
        // ride the edge is a location, not a fact.
        let ctx_in = if ctx_in.track == Track::Dirty {
            ctx_in.facts_free()
        } else {
            ctx_in
        };
        let class = self.tok_class(&ctx_in.tokens);
        let depth = self.key_depth();
        let ver = self.vers.intern(Ver {
            pc,
            class,
            track: ctx_in.track,
            depth,
        });
        // THE PREDICTION STEP. The fact context is keyed by the program
        // point and by nothing else: token class and depth are structural
        // identity, and GEN carries no facts. Every Opt arrival joins into
        // that one prediction, so every Opt block at a pc reads identical
        // facts and emits identical code -- which is what would let the
        // side-entry copies vanish on an ISA that admits irreducible
        // control flow, with no dynamic path's code changing.
        let mut rejoin_report: Option<(Ctx, Ctx)> = None;
        if ctx_in.track == Track::Opt && self.mode == EmitMode::ContextOnly {
            let before = self
                .opts
                .diagnostics
                .ctxedge
                .then(|| self.vers.pred.at(pc).cloned().unwrap_or_default());
            let had = self.vers.pred.at(pc).is_some();
            if self.opts.diagnostics.peel {
                let src = self.cur_pc;
                let back = self
                    .loop_intervals
                    .iter()
                    .any(|&(h, e)| pc == Pc::new(h) && src >= Pc::new(h) && src < Pc::new(e));
                if back {
                    self.vers.pred.join_back(pc, ctx_in.facts_only());
                }
            }
            if self.vers.pred.join_arrival(pc, depth, ctx_in.facts_only()) {
                self.map_changed = true;
                if had {
                    self.changed_join += 1;
                } else {
                    // THE MINT. `join_arrival` only ever weakens, so the
                    // first arrival at a pc decides what every later one can
                    // at best preserve -- and a mint logs nothing in the
                    // rejoin audit (its `pre` is all-TOP, so every slot is
                    // skipped). Without this record a prediction that was
                    // born weak is indistinguishable from one that was
                    // eroded, and the two have completely different fixes.
                    self.changed_discover += 1;
                    if self.opts.diagnostics.ctxedge {
                        self.dump_ctx_mint(pc, &ctx_in);
                    }
                }
                if let (Some(pre), Some(post)) = (before, self.vers.pred.at(pc)) {
                    rejoin_report = Some((pre, post.clone()));
                }
                self.rearm_pc(pc);
            }
        }
        // The identity's emission context is derived, never stored facts of
        // its own: the pc's prediction, plus this identity's tokens, track
        // and carried set. `carried` follows the first arrival -- it is a
        // location, and `cont_at` reconciles a mismatch with one frame load.
        {
            let facts = if ctx_in.track == Track::Opt {
                self.vers.pred.at(pc).cloned().unwrap_or_default()
            } else {
                Ctx::default()
            };
            let (carried, grew) = self
                .vers
                .pred
                .carried_join(pc, ctx_in.track, &ctx_in.carried);
            if grew {
                self.map_changed = true;
                self.rearm_pc(pc);
            }
            let want = Ctx {
                tokens: ctx_in.tokens.clone(),
                carried,
                track: ctx_in.track,
                ..facts
            }
            .canon();
            let slot = &mut self.vers.ctx[ver.0 as usize];
            if slot.as_ref() != Some(&want) {
                // CONSULT-ONLY: in `Code` the prediction is closed and this
                // is pure lookup. Reaching here means the emitter walked a
                // program the prediction pass did not, and the edge
                // conversions below would convert a value to a repr nothing
                // proved it has -- so the closure check re-runs the pass
                // and, failing that, declines the body.
                debug_assert!(
                    self.mode == EmitMode::ContextOnly,
                    "Code mode moved the prediction at pc {pc}"
                );
                *slot = Some(want);
                self.map_changed = true;
                self.rearm(ver);
            } else if self.mode == EmitMode::Code && ctx_in.track == Track::Opt {
                // The consultation contract, checked: every Opt arrival must
                // imply its program point's prediction, or the edge would
                // hand a value across in a repr it was never proven to have.
                debug_assert!(
                    self.vers
                        .pred
                        .at(pc)
                        .is_some_and(|p| ctx_in.facts_only().implies(p)),
                    "Code arrival at pc {pc} does not imply the prediction"
                );
            }
        }
        // The rejoin audit: an Opt arrival whose join stripped a fact from
        // the version is an arm that rejoins with weaker facts -- the join
        // law's violator census, keyed to the op that emitted the edge.
        // Claim-backed losses are the rule's violations; test-backed ones
        // are part-(i) gaps (the bits ride the record, filtered downstream).
        if let Some((pre, post)) = rejoin_report {
            self.dump_rejoin_loss(pc, &pre, &post, &ctx_in);
            self.dump_ctx_join(pc, &pre, &post, &ctx_in.facts_only());
        }
        // Provenance flows along the same joins but is invisible to Eq and
        // `implies`, so an implied arrival would never deliver its bits:
        // OR them in unconditionally. `prov_changed` re-arms fixpoint
        // rounds only under the census instruments (mod.rs); the ctx map
        // itself is already closed, so the extra rounds change no codegen.
        if (self.opts.instrument.guards || self.opts.diagnostics.ctxedge)
            && ctx_in.track == Track::Opt
        {
            self.prov_changed |= self.vers.pred.or_prov(pc, &ctx_in);
        }
        if self.opts.diagnostics.bbv {
            crate::diag_line!(
                "night: bbv theta sid#{} pc {pc} track {:?} class {class}",
                self.source_id,
                self.vers.ctx(ver).track,
            );
        }
        ver
    }

    /// Put an identity back on the worklist: its input prediction moved, so
    /// whatever it derived last time may now be wrong. Only in the
    /// prediction pass -- in `Code` the prediction is closed and re-running
    /// a version would emit its body twice.
    pub(super) fn rearm(&mut self, ver: VerId) {
        if self.mode == EmitMode::ContextOnly
            && self.blocks.contains_key(&ver)
            && self.processed.remove(&ver)
        {
            self.workqueue.push(ver);
        }
    }

    /// A program point's prediction moved: refresh every identity there
    /// from it and put them back on the worklist. The refresh is the half
    /// that matters -- an identity's emission context is a view of its pc's
    /// prediction, and a stale view would have the walk deriving successors
    /// from facts the prediction no longer claims.
    pub(super) fn rearm_pc(&mut self, pc: Pc) {
        if self.mode != EmitMode::ContextOnly {
            return;
        }
        let Some(vs) = self.vers.at_pc.get(&pc).cloned() else {
            return;
        };
        let facts = self.vers.pred.at(pc).cloned().unwrap_or_default();
        for v in vs {
            let Some(cur) = self.vers.ctx[v.0 as usize].as_ref() else {
                continue;
            };
            // Only Opt blocks read the prediction; a GEN block's facts are
            // empty and cannot have moved.
            if cur.track != Track::Opt {
                continue;
            }
            let want = Ctx {
                tokens: cur.tokens.clone(),
                carried: cur.carried.clone(),
                track: cur.track,
                ..facts.clone()
            }
            .canon();
            if *cur != want {
                self.vers.ctx[v.0 as usize] = Some(want);
            }
            self.rearm(v);
        }
    }

    /// The unboxed repr a ctx slot's facts license for a block param:
    /// values flow between versions in their proven repr, never reboxed
    /// (exactly-Int32 -> i32; boolean -> i32; exact-integer numeric (the
    /// I32/I53 buckets, never -0 by the domain) -> i64; numeric -> f64;
    /// anything else boxed).
    pub(super) fn slot_repr(slot: &SlotCtx) -> Repr {
        if slot.prims == PRIM_INT32 && !slot.outside {
            Repr::I32
        } else if slot.prims == PRIM_BOOLEAN && !slot.outside {
            Repr::Bool
        } else if slot.is_numeric() && slot.range != RangeBucket::Top {
            Repr::I64
        } else if slot.is_numeric() {
            Repr::F64
        } else if slot.prims == PRIM_STRING && !slot.outside {
            Repr::StrPtr
        } else if slot.prims.is_empty() && slot.outside {
            Repr::ObjPtr
        } else {
            Repr::Boxed
        }
    }

    pub(super) fn repr_type(r: Repr) -> Type {
        match r {
            Repr::Boxed | Repr::I64 => Type::I64,
            Repr::F64 => Type::F64,
            Repr::I32 | Repr::Bool | Repr::StrPtr | Repr::ObjPtr => Type::I32,
        }
    }

    /// The version-table edge to `(succ_pc, id)` (theta's choice). Block
    /// params are typed by the target ctx's slot reprs; edge args convert
    /// each live operand to its target repr.
    /// Materialize a version's block and typed params (and queue it for
    /// emission) if it does not exist yet. Params are [stack(depth),
    /// carried locals], each typed by the ctx slot's repr -- the layout
    /// `run_version` reads back.
    pub(super) fn ensure_version_block(&mut self, ver: VerId, tgt_seg: Option<usize>) {
        if self.blocks.contains_key(&ver) {
            return;
        }
        let ctx = self.vers.ctx(ver).clone();
        let carried = self.carried_for(tgt_seg, &ctx);
        let depth = usize::from(self.vers.ver(ver).depth);
        let block = self.body.add_block();
        let mut params = Vec::with_capacity(depth + carried.len());
        for i in 0..depth {
            let r = Self::slot_repr(&ctx.stack_slot(i));
            params.push(self.body.add_blockparam(block, Self::repr_type(r)));
        }
        for &l in &carried {
            let r = Self::slot_repr(&Self::carried_slot(&ctx, l));
            params.push(self.body.add_blockparam(block, Self::repr_type(r)));
        }
        // Trailing accumulator param (threaded bodies only): every version
        // receives the lineage's flags word; edges materialize the
        // tri-state (Zero/All become constants at the edge).
        if self.flags_threading() {
            params.push(self.body.add_blockparam(block, Type::I32));
        }
        self.blocks.insert(ver, block);
        self.ver_blocks.insert(block);
        self.block_params.insert(ver, params);
        self.workqueue.push(ver);
    }

    pub(super) fn cont_at(&mut self, succ_pc: Pc, ver: VerId) -> BlockTarget {
        let key = ver;
        let tgt_seg = self.seg_of(succ_pc);
        self.ensure_version_block(ver, tgt_seg);
        let ctx = self.vers.ctx(ver).clone();
        let carried = self.carried_for(tgt_seg, &ctx);
        let mut exit_flush: Option<Vec<u32>> = None;
        // The frame is the truth for every local the target reads from it.
        // A stale local may stay unflushed only where the target carries it
        // RAW: the entry re-marks carried raw locals stale, and nothing
        // else. Carried BOXED, the raw value is converted for the param and
        // the entry takes the slot as fresh, so a later carrier kill must
        // not reload the frame there, or it would read a stale value.
        if tgt_seg == self.ssa_seg {
            let mut keep: Vec<u32> = carried
                .iter()
                .copied()
                .filter(|&l| {
                    matches!(
                        Self::slot_repr(&Self::carried_slot(&ctx, l)),
                        Repr::I32 | Repr::F64 | Repr::Bool | Repr::I64
                    )
                })
                .collect();
            // A stale slot the target cannot read before writing stays
            // stale: the frame keeps an older value the tracer can walk.
            // Except across a loop exit, where the dead raw values are
            // stored anyway -- on the edge, in a block of their own -- so
            // the loop's values have a use past it.
            let dead: Vec<u32> = self
                .frame_stale
                .iter()
                .copied()
                .filter(|&l| !keep.contains(&l) && !self.key_live_at(tgt_seg, succ_pc, l))
                .collect();
            keep.extend(dead.iter().copied());
            self.flush_stale_locals(&keep);
            // The CFG exists only over a frozen pc space; the walks before
            // the freeze emit into a body that is discarded, so their edges
            // need no trampoline.
            let cfg_ready = self.splices_frozen || self.segs.is_empty();
            if !dead.is_empty() && cfg_ready && self.cfg().leaves_loop(self.cur_pc, succ_pc) {
                exit_flush = Some(dead);
            }
        } else if self.edge_enters_child(tgt_seg) {
            // A raw local riding into the splice as an outer carrier keeps
            // its store deferred: the return edge hands it back raw and the
            // continuation's entry re-marks it stale.
            let mut keep: Vec<u32> = carried
                .iter()
                .filter(|&&k| {
                    k & OUTER_LOCAL != 0
                        && Self::raw_repr(Self::slot_repr(&Self::carried_slot(&ctx, k)))
                })
                .map(|&k| k & !OUTER_LOCAL)
                .collect();
            // The caller's next read of its own slots is past the return.
            let ret_pc = self.segs[tgt_seg.unwrap()].ret_pc;
            keep.extend(
                self.frame_stale
                    .iter()
                    .copied()
                    .filter(|&l| !self.key_live_at(self.ssa_seg, ret_pc, l)),
            );
            self.flush_stale_locals(&keep);
            // A seam actual the target does not carry raw gets its real
            // value stored over the placeholder now: the callee reads the
            // slot (or a boxed carrier of it) as fresh.
            let base = self.segs[tgt_seg.unwrap()].frame_base + 16;
            for a in 0..self.seam_args.len() {
                let Some(o) = self.seam_args[a].clone() else {
                    continue;
                };
                let key = STALE_ARG | u32::try_from(a).unwrap();
                let rides = carried.contains(&key)
                    && Self::raw_repr(Self::slot_repr(&Self::carried_slot(&ctx, key)));
                if !rides {
                    let b = self.to_boxed(&o);
                    self.store_i64(self.vp, base + 8 * u32::try_from(a).unwrap(), b);
                }
            }
        } else if self.edge_returns(tgt_seg) {
            // The frame being left is dead past this edge: nothing reads
            // its slots again, so its deferred stores are dropped, not
            // paid.
            self.frame_stale.clear();
        } else {
            self.flush_stale_locals(&[]);
        }
        self.flush_outer_dropped(tgt_seg, &ctx);
        let mut args: Vec<Value> = (0..self.stack.len())
            .map(|i| {
                let o = self.stack[i].clone();
                let r = Self::slot_repr(&ctx.stack_slot(i));
                self.convert_to_repr(&o, r)
            })
            .collect();
        for &l in &carried {
            let r = Self::slot_repr(&Self::carried_slot(&ctx, l));
            let o = self.carried_operand_for_edge(tgt_seg, l);
            args.push(self.convert_to_repr(&o, r));
        }
        if let Some(f) = self.flags_edge_arg() {
            args.push(f);
        }
        // Every edge to a key must agree with its creator on stack depth
        // (bytecode depth is deterministic per pc): the carried-local
        // params sit after the stack params, so a depth mismatch would
        // silently shift them into the wrong slots.
        // Every edge to a version must agree with its creator on the param
        // layout. `Ver.depth` puts the stack half in the identity, and the
        // carried half comes from the version ctx -- which is frozen by the
        // time Code runs, but still moving during the fixpoint rounds, so
        // only Code asserts.
        if self.mode == EmitMode::Code {
            assert_eq!(
                self.block_params[&key].len(),
                args.len(),
                "block arg/param count mismatch at pc {succ_pc} ver {:?}",
                self.vers.ver(ver),
            );
        }
        if let Some(dead) = exit_flush {
            let tramp = self.body.add_block();
            let save = self.cur;
            self.cur = tramp;
            self.flush_dead_raw(&dead);
            self.body.set_terminator(
                tramp,
                Terminator::Br {
                    target: BlockTarget {
                        block: self.blocks[&key],
                        args,
                    },
                },
            );
            self.cur = save;
            return BlockTarget {
                block: tramp,
                args: Vec::new(),
            };
        }
        BlockTarget {
            block: self.blocks[&key],
            args,
        }
    }

    /// The continuation seam: every successor edge an op lowering produces
    /// routes through here -- tracked facts + edge tokens + track -> theta
    /// -> the version table.
    ///
    /// Reducibility is by construction, so there is no back-edge special
    /// case at all. `out_tokens_for` drops
    /// a loop's own token at its header pc, so every edge to header `h`
    /// -- entry or back -- targets `(h, outer class, track)`; and every pc
    /// in that header version's body carries a token naming that identity,
    /// so a body version's only predecessors are that header and its own
    /// body. Each cycle therefore has exactly one entry, at the header.
    /// Tracks only ever descend (Opt -> Side -> Dirty), so a body version
    /// on a lower track back-edges to the lower track's header -- which is
    /// again an entry AT a header, never into the middle of a cycle.
    pub(super) fn cont(&mut self, succ_pc: Pc) -> BlockTarget {
        // The recovery on-ramp. Its bail is the ordinary continuation,
        // computed first and unconditionally, so the theta call sequence
        // (and every join) is identical whether or not the on-ramp fires.
        // The failure arm mints nothing by construction.
        let normal = self.cont_normal(succ_pc);
        if let Some(t) = self.try_onramp(succ_pc, &normal) {
            return t;
        }
        if let Some(t) = self.try_call_return_onramp(succ_pc, &normal) {
            return t;
        }
        normal
    }

    /// The just-in-time on-ramp: rejoin Opt at a call's return, on the spot.
    ///
    /// A call site with a keep fork leaves its merge on GEN
    /// (`keep_fork_merge_stepped_track`) because every arm reaching it
    /// failed the callee's runtime intactness proof. That proof is
    /// all-or-nothing -- it asks whether the callee wrote ANY heap -- and
    /// the answer is usually about some other object entirely. So instead
    /// of dwelling on GEN until the next loop header, re-prove the
    /// successor's own prediction here, fact by fact, and take the Opt
    /// version if the guards pass.
    ///
    /// Three properties make this a much better bet than the loop-header
    /// conform on an Opt edge, which pays its guards on every iteration
    /// whether or not the population needs them:
    ///
    /// - It is reached only after the cheap proof has already failed, so
    ///   the guards run on the population that needs them, not on every
    ///   iteration of a loop that was fine.
    /// - Its target is the version this lineage was continuing into
    ///   anyway, so nothing about the CFG changes: same pc, same token
    ///   class, same depth. The token vector is computed as if the track
    ///   had not been stepped, which is exactly what it was before the
    ///   step.
    /// - Failing is free. The bail is `normal`, the GEN continuation that
    ///   already exists, and the proof mints no facts anywhere.
    fn try_call_return_onramp(&mut self, succ_pc: Pc, bail: &BlockTarget) -> Option<BlockTarget> {
        if self.gen_only || self.ret_onramp_pc != Some(succ_pc) {
            return None;
        }
        debug_assert_eq!(self.cur_track, Track::Dirty);
        // The identity this lineage would have continued into had the merge
        // not stepped the track. `out_tokens_for` and `edge_track` both read
        // `cur_track`, so it is put back for the question and restored
        // after: an Opt lineage's membership label for an enclosing loop is
        // OPT, and that is the class of the version the call's own version
        // falls through to. Nothing is emitted under the restored track.
        let saved = self.cur_track;
        self.cur_track = self.vers.ver(self.cur_ver).track;
        let toks = self.out_tokens_for(succ_pc);
        let track = self.edge_track(succ_pc);
        self.cur_track = saved;
        if track != Track::Opt {
            return None;
        }
        let depth = u16::try_from(self.stack.len()).ok()?;
        // Same-frame only, like the loop on-ramp: caller-frame claims are
        // compile-time carried state no runtime guard can re-prove.
        let tgt_seg = self.seg_of(succ_pc);
        if tgt_seg != self.ssa_seg {
            return None;
        }
        // The facts to prove are the successor pc's prediction. If no Opt
        // lineage reaches it there is nothing to rejoin -- and nothing to
        // mint, because minting one would be a loss for the same reason
        // header minting is: a pc no Opt lineage reaches is one whose code
        // steps off Opt anyway.
        let facts = self.vers.pred.at(succ_pc)?.clone();
        let hcarried = self.vers.pred.carried(succ_pc, Track::Opt)?.clone();
        let opt_ctx = Ctx {
            tokens: toks,
            carried: hcarried,
            track: Track::Opt,
            ..facts
        }
        .canon();
        if opt_ctx.caller_locals.iter().any(|s| !s.is_top_sans_iv())
            || opt_ctx.caller_args.iter().any(|s| !s.is_top_sans_iv())
        {
            return None;
        }
        let key = Ver {
            pc: succ_pc,
            class: self.tok_class(&opt_ctx.tokens),
            track: Track::Opt,
            depth,
        };
        let opt = self.vers.intern(key);
        if self.vers.ctx[opt.0 as usize].as_ref() != Some(&opt_ctx) {
            if self.mode == EmitMode::Code {
                // Consult-only: the prediction pass never walked this
                // version, so emitting into it would emit against an open
                // map.
                return None;
            }
            self.vers.ctx[opt.0 as usize] = Some(opt_ctx.clone());
            self.map_changed = true;
            self.changed_discover += 1;
        }
        // Intervals are proven, never joined: this edge must not move the
        // successor's prediction, which every other lineage through that pc
        // reads. `proof_gaps` with `iv_guards` either proves containment
        // with a bounds check or declines the slot.
        let plan = self.proof_gaps(&opt_ctx, succ_pc, depth, true).ok()?;
        if !self.ret_onramp_admits(succ_pc, &plan.gaps) {
            return None;
        }
        if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
            crate::diag_line!(
                "night: ret-onramp sid#{} pc {} to {succ_pc} guards {}",
                self.source_id,
                self.cur_pc,
                plan.gaps.len(),
            );
        }
        Some(self.emit_proof(
            opt,
            &opt_ctx,
            tgt_seg,
            depth,
            &plan.gaps,
            bail,
            census::RET_ONRAMP_TRY,
            census::RET_ONRAMP_OK,
        ))
    }

    /// The track an edge to `succ_pc` runs on.
    ///
    /// B(c) cascade boundary: an Opt lineage whose membership label for
    /// the target header's own loop is TOK_CYCLE is a proof copy's
    /// tail arriving back at the dirty cycle it was recovered out of
    /// (only non-Opt headers hand out TOK_CYCLE, so no other Opt lineage
    /// can carry one). It must not re-enter the steady Opt cycle: that
    /// cycle is also entered from its preheader, and the copy is
    /// reachable from dirty entry paths that never pass the Opt header,
    /// so the rejoin edge would be a second entry into the composite
    /// cycle -- the irreducibility reducify pays for exponentially.
    /// Rejoining the DIRTY cycle header instead keeps every cycle
    /// single-entry: the copy's own loop cycles alone, and the next
    /// outer iteration re-conforms at the same entry edge.
    fn edge_track(&self, succ_pc: Pc) -> Track {
        if self.cur_track != Track::Opt {
            return self.cur_track;
        }
        let Some(li) = self
            .loop_intervals
            .iter()
            .position(|&(lh, _)| lh == succ_pc.get())
        else {
            return Track::Opt;
        };
        let li = u32::try_from(li).unwrap();
        if self
            .cur_tokens
            .iter()
            .any(|&(i, t)| i == li && t == TOK_CYCLE)
        {
            Track::Dirty
        } else {
            Track::Opt
        }
    }

    /// The context this edge delivers: the live fact vectors, the operand
    /// stack projected slot-wise, the outgoing token vector and the carrier
    /// set.
    fn arrival_ctx(&self, succ_pc: Pc, track: Track) -> Ctx {
        Ctx {
            locals: self.locals_ctx.clone(),
            stack: self.stack.iter().map(Operand::slot).collect(),
            args: self.args_ctx.clone(),
            caller_locals: self.caller_locals_ctx.clone(),
            caller_args: self.caller_args_ctx.clone(),
            outer: self.outer_ctx.clone(),
            tokens: self.out_tokens_for(succ_pc),
            carried: self.carried_out(self.seg_of(succ_pc), succ_pc),
            // A binding fact no later read can consume is dropped here: a
            // carried fact costs every keep site between here and its use
            // a re-proof, and one that fails there sends the lineage to
            // GEN for nothing.
            gcells: {
                let seg = self.seg_of(succ_pc);
                self.gcells_ctx
                    .iter()
                    .filter(|(b, _)| self.gcell_live_at(seg, succ_pc, *b))
                    .cloned()
                    .collect()
            },
            track,
        }
        .canon()
    }

    pub(super) fn cont_normal(&mut self, succ_pc: Pc) -> BlockTarget {
        let track = self.edge_track(succ_pc);
        let ctx = self.arrival_ctx(succ_pc, track);
        // A loop header'S entry and its steady state are one version here,
        // and that is a measured choice. Splitting them -- a structural
        // `steady` bit set iff the arriving edge is a back edge, so the
        // steady-state version joins only back edges and the weak loop entry
        // cannot poison it -- was built and measured repeatedly. It does
        // what it is designed to do on a loop whose entry really is weaker
        // than its steady state, and loses more than that everywhere else,
        // because peeling every loop's entry costs a second copy of every
        // loop body.
        if self.opts.diagnostics.ctxedge && self.mode == EmitMode::Code {
            self.dump_ctx_edge(succ_pc, &ctx);
        }
        let id = self.theta(succ_pc, ctx);
        self.cont_at(succ_pc, id)
    }

    /// The version an edge to `succ_pc` from the current emitter state
    /// lands on, WITHOUT building the edge. Pure bookkeeping: the resume
    /// dispatcher needs the landing version interned at the suspend point,
    /// but supplies its block args from the restored frame much later
    /// (generator.rs).
    pub(super) fn succ_version(&mut self, succ_pc: Pc) -> VerId {
        let ctx = self.arrival_ctx(succ_pc, self.cur_track);
        self.theta(succ_pc, ctx)
    }

    /// What one proof gap needs: None = not re-provable by the proof's
    /// guard vocabulary; Some(None) = the arriving fact already implies
    /// the target's, no guard owed; Some(Some(k)) = guardable by guard
    /// kind k (a tag test on a boxed source, or an exactness compare on an
    /// I64 carrier).
    ///
    /// Interval-blind on purpose: the guard vocabulary can prove at most
    /// the int32 range, never a tighter interval, so the proof edge is a
    /// proof edge for everything except the interval component -- for that
    /// it is an ordinary arrival, and `try_onramp` joins what the edge
    /// delivers into the target header's stored iv (rung-widened).
    /// The refusal detail for a proof gap: which slot, in what
    /// representation, could not re-prove which claim. A bare
    /// "decline local-gap" says a loop cannot be recovered and nothing
    /// about what would fix it.
    fn gap_why(what: &str, loc: &str, src: &SlotCtx, repr: Repr, tgt: &SlotCtx) -> String {
        format!(
            "decline {what} {loc} repr {repr:?} src {} tgt {}",
            Self::viz_slot_str(src),
            Self::viz_slot_str(tgt)
        )
    }

    pub(super) fn proof_gap(
        src: &SlotCtx,
        src_repr: Repr,
        tgt: &SlotCtx,
    ) -> Option<Option<ProofGuard>> {
        if src.implies_sans_iv(tgt) {
            return Some(None);
        }
        match src_repr {
            Repr::Boxed => {
                let obj_only = tgt.prims.is_empty() && tgt.outside;
                // An identity claim is discharged in phase 2, which reads the
                // receiver's class word -- and that read is only licensed
                // behind phase 1's object proof. A union target admits
                // non-object tags, so the read could land on a payload that
                // is not a pointer; those stay refused.
                if (tgt.cls.is_some() || tgt.cls_shallow || tgt.cls_slots) && !obj_only {
                    return None;
                }
                // A range claim rides on the int32 tag and nothing else.
                if tgt.range != RangeBucket::Top && (tgt.prims != PRIM_INT32 || tgt.outside) {
                    return None;
                }
                // An unsatisfiable slot (no primitive, no object) has no tag
                // to prove; a dead path is not something to conform into.
                if tgt.prims.is_empty() && !tgt.outside {
                    return None;
                }
                // Everything else is a disjunction of tag tests, which
                // `proof_tag_cond` now builds for any set.
                Some(Some(ProofGuard::Tag))
            }
            // An exact-integer carrier re-proving exact int32 (the dirty
            // path widened a counter): one wrap/extend compare. Exact by
            // construction, so no -0 hazard.
            Repr::I64
                if tgt.prims == PRIM_INT32
                    && !tgt.outside
                    && tgt.cls.is_none()
                    && !tgt.cls_shallow
                    && !tgt.cls_slots =>
            {
                Some(Some(ProofGuard::ExactI64))
            }
            // The f64 carrier's twin, and the commonest single refusal in
            // the corpus: a loop counter that the dirty path widened to a
            // double, arriving at a header whose slot is exact int32. The
            // check is the same round-trip plus a -0 rejection, because an
            // f64 can hold a negative zero and an int32 cannot.
            Repr::F64
                if tgt.prims == PRIM_INT32
                    && !tgt.outside
                    && tgt.cls.is_none()
                    && !tgt.cls_shallow
                    && !tgt.cls_slots =>
            {
                Some(Some(ProofGuard::ExactF64))
            }
            _ => None,
        }
    }

    /// The interval the proof edge delivers into a slot: the source's
    /// claim narrowed by the guard's proven range (an int32-tag or
    /// exact-i64 guard admits only int32-range values; every other guard
    /// proves no bound).
    pub(super) fn proof_delivered_iv(
        src: &SlotCtx,
        guard: Option<ProofGuard>,
        tgt: &SlotCtx,
    ) -> Option<ValueRange> {
        const I32: ValueRange = ValueRange::new(i32::MIN as i64, i32::MAX as i64);
        let g_iv = match guard {
            Some(ProofGuard::ExactI64 | ProofGuard::ExactF64) => Some(I32),
            Some(ProofGuard::Tag) if tgt.prims == PRIM_INT32 && !tgt.outside => Some(I32),
            _ => None,
        };
        match (src.iv, g_iv) {
            (Some(s), Some(g)) => {
                let (lo, hi) = (s.lo.max(g.lo), s.hi.min(g.hi));
                if lo <= hi {
                    Some(ValueRange::new(lo, hi))
                } else {
                    // Contradictory: the guard can never pass at runtime;
                    // the guard-proven range is the sound claim either way.
                    Some(g)
                }
            }
            (s, None) => s,
            (None, g) => g,
        }
    }

    /// Entry-form iv gap, guardable: the delivered interval would change
    /// the stored slot (tolerance included -- an entry edge declines on
    /// ANY iv movement), and the arriving value's int32-ness is certain,
    /// so a bounds check against the stored interval proves containment
    /// exactly and the slot delivers the stored interval unchanged.
    /// Certain means an unboxed i32 arrival, or a boxed arrival whose
    /// int32-only tag is proven by this slot's own phase-1 Tag guard --
    /// the conditions AND, so the low-bits compare can never pass on a
    /// non-int payload.
    fn iv_gap_guardable(
        delivered: Option<ValueRange>,
        src: &SlotCtx,
        tgt: &SlotCtx,
        repr: Repr,
        g: Option<ProofGuard>,
    ) -> bool {
        // These edges are admitted unconditionally: a program point has one
        // prediction, the join of its own arrivals, and a proof edge
        // PROVES that prediction rather than joining into it, so an
        // admission cannot reshape the map.
        // Only runtime-proven int-ness admits: an unboxed i32 IS one, a
        // boxed value behind this slot's own int32-only Tag guard, an f64
        // carrier behind its ExactF64 proof (bounds exact in f64, NaN
        // fails the compares, -0 fails ExactF64). A compile-time mask
        // claim alone does NOT qualify: the stored interval licenses
        // overflow-check elision, and one unproven admission cascades
        // garbage numbers through the loop.
        let _ = src;
        let int_arrival = repr == Repr::I32
            || (repr == Repr::Boxed
                && matches!(g, Some(ProofGuard::Tag))
                && tgt.prims == crate::opsem::PRIM_INT32
                && !tgt.outside)
            || (repr == Repr::F64 && matches!(g, Some(ProofGuard::ExactF64)));
        if !int_arrival || tgt.iv.is_none() {
            return false;
        }
        let (niv, ngrow) = crate::opsem::iv_join_tolerant(delivered, tgt.iv, tgt.iv_grow);
        (niv, ngrow) != (tgt.iv, tgt.iv_grow)
    }

    /// The phase-1 condition proving `tgt`'s tag claim on a boxed value.
    /// The tag condition proving membership in `tgt`'s admissible tag set:
    /// one compare per tag, OR-ed, with the number pair collapsed to the
    /// single `is_number_tag` range test wherever both members are present.
    ///
    /// A target with a union claim like `int32 | object` needs several
    /// compares, and those unions are exactly what a dirty loop carries.
    /// Several compares are the right price: the
    /// alternative to a successful on-ramp is running the whole remainder of
    /// the loop off the Opt track, and the alternative to a failed one is
    /// the dirty continuation that already existed.
    pub(super) fn proof_tag_cond(&mut self, boxed: Value, tgt: &SlotCtx) -> Value {
        // Single-test shapes stay exactly the code they were.
        if tgt.prims.is_empty() && tgt.outside {
            let is_obj = self.tag_eq(boxed, TAG_OBJECT as u32);
            let Some(kind) = tgt.ta else {
                return is_obj;
            };
            // A typed-array fact: the clasp test behind the tag test, as a
            // diamond (the clasp loads dereference the payload).
            let merge = self.body.add_block();
            let ok = self.body.add_blockparam(merge, Type::I32);
            let obj_blk = self.body.add_block();
            let zero = self.i32_const(0);
            self.body.set_terminator(
                self.cur,
                Terminator::CondBr {
                    cond: is_obj,
                    if_true: BlockTarget {
                        block: obj_blk,
                        args: vec![],
                    },
                    if_false: BlockTarget {
                        block: merge,
                        args: vec![zero],
                    },
                },
            );
            self.cur = obj_blk;
            let objptr = self.unop(Operator::I32WrapI64, boxed, Type::I32);
            let is_ta = self.ta_clasp_eq(objptr, kind);
            self.body.set_terminator(
                self.cur,
                Terminator::Br {
                    target: BlockTarget {
                        block: merge,
                        args: vec![is_ta],
                    },
                },
            );
            self.cur = merge;
            return ok;
        }
        if !tgt.outside {
            if tgt.prims == PRIM_INT32 {
                return self.tag_eq(boxed, TAG_INT32 as u32);
            }
            if tgt.prims == PRIM_BOOLEAN {
                return self.tag_eq(boxed, TAG_BOOLEAN as u32);
            }
            if tgt.prims == PRIM_STRING {
                return self.tag_eq(boxed, TAG_STRING as u32);
            }
            if tgt.prims == PRIM_DOUBLE {
                return self.is_double_tag(boxed);
            }
            if tgt.is_numeric() {
                return self.is_number_tag(boxed);
            }
        }
        let mut parts: Vec<Value> = Vec::new();
        match (
            tgt.prims.intersects(PRIM_INT32),
            tgt.prims.intersects(PRIM_DOUBLE),
        ) {
            (true, true) => parts.push(self.is_number_tag(boxed)),
            (true, false) => parts.push(self.tag_eq(boxed, TAG_INT32 as u32)),
            (false, true) => parts.push(self.is_double_tag(boxed)),
            (false, false) => {}
        }
        for (bit, tag) in [
            (PRIM_BOOLEAN, TAG_BOOLEAN as u32),
            (PRIM_STRING, TAG_STRING as u32),
            (PRIM_UNDEFINED, TAG_UNDEFINED as u32),
            (PRIM_NULL, TAG_NULL as u32),
            (PRIM_BIGINT, TAG_BIGINT_HI),
            (PRIM_SYMBOL, TAG_SYMBOL as u32),
        ] {
            if tgt.prims.intersects(bit) {
                let c = self.tag_eq(boxed, tag);
                parts.push(c);
            }
        }
        if tgt.outside {
            let c = self.tag_eq(boxed, TAG_OBJECT as u32);
            parts.push(c);
        }
        // `proof_gap` refuses an empty tag set, so there is always one.
        let mut it = parts.into_iter();
        let first = it.next().expect("proof_gap admitted an empty tag set");
        it.fold(first, |acc, c| {
            self.binop(Operator::I32Or, acc, c, Type::I32)
        })
    }

    /// The onramp conform sequence, funnel back edge only.
    /// On a non-Opt edge to a loop's header
    /// from inside that loop's funnel, emit an edge-owned guard chain that
    /// re-proves every fact the existing Opt header's ctx claims and
    /// re-unboxes its carried reprs: success brs the Opt header (whose ctx
    /// is not joined -- the proof edge proves it, the design's one
    /// load-bearing asymmetry), failure brs `bail`, the dirty continuation
    /// that already exists. Emission is confined to fresh blocks
    /// (straight-line, pure reads only -- the merge-back law) and touches
    /// no lineage state, so the fall-through arm of the branching op is
    /// unaffected.
    pub(super) fn try_onramp(&mut self, succ_pc: Pc, bail: &BlockTarget) -> Option<BlockTarget> {
        // The header lookup first: it is a pure query, and hoisting it lets
        // every return below name a header: a silent decline here leaves
        // no way to diagnose why a cycle got no on-ramp attempt.
        let &(h, e) = self
            .loop_intervals
            .iter()
            .find(|&&(lh, _)| lh == succ_pc.get())?;
        let onramp_log = |slf: &Self, what: &str| {
            if self.opts.diagnostics.bbv && slf.mode == EmitMode::Code {
                crate::diag_line!(
                    "night: onramp {what} sid#{} hdr {h} from pc {}",
                    slf.source_id,
                    slf.cur_pc
                );
            }
            if self.opts.diagnostics.viz && slf.mode == EmitMode::Code {
                crate::diag_line!(
                    "night: viz onramp {what} sid#{} hdr {h} pc {} site {} guards []",
                    slf.root_source_id,
                    slf.cur_pc,
                    slf.viz_site(slf.cur_pc),
                );
            }
        };
        if self.gen_only {
            onramp_log(self, "decline gen-only");
            return None;
        }
        // With the fact context keyed by the program point, an Opt edge
        // whose arrival is weaker than its target's prediction does not
        // land in a version of its own -- it degrades the one prediction
        // every lineage through that point reads. Having such an edge
        // PROVE the prediction here instead (same target block, a guard
        // chain in front, a bail to the pc's GEN version) loses, because
        // the edge runs every iteration of a loop that mostly does not
        // need it and a proof that can fail there will. It is the same
        // population lesson as the dirty cycle's own back edge two
        // paragraphs down -- an edge that reaches here every iteration
        // pays every iteration, and a proof that can fail will.
        if self.cur_track == Track::Opt {
            onramp_log(self, "decline opt-source");
            return None;
        }
        let in_loop = |pc: Pc, sites: &[u32], h: u32, e: u32| {
            (pc >= Pc::new(h) && pc < Pc::new(e)) || sites.iter().any(|&s| s >= h && s < e)
        };
        // Two conforming edge shapes. Mode 1, the funnel back edge: current
        // version strictly inside the loop holding the funnel's TOK_PEEL
        // membership (first-excursion recovery). Mode 2 adds the dirty entry
        // edge (from outside the loop): once per invocation, before the
        // first iteration -- the shape where a dirty caller context enters
        // the loop and would otherwise cycle dirty forever. Both are legal
        // at any header depth: the proof's target is a COPY of the header
        // keyed by the arriving outer labels (see `tgt_key` below), not the
        // steady Opt version, so an inner level recovers on its own cycle.
        // The dirty cycle's own back edge deliberately does not conform: a
        // population whose facts are genuinely false (an unstamped receiver)
        // would pay the guards every iteration and fail them every time --
        // when tried, the proof failed on nine attempts in ten.
        if self.cur_pc == Pc::new(h) {
            onramp_log(self, "decline self-edge");
            return None;
        }
        let sites_cur = self.seg_sites(self.cur_pc);
        let funnel = in_loop(self.cur_pc, &sites_cur, h, e);
        let Some(lidx) = self
            .loop_intervals
            .iter()
            .position(|&iv| iv == (h, e))
            .map(|i| u32::try_from(i).unwrap())
        else {
            onramp_log(self, "decline no-loop-index");
            return None;
        };
        // Which conform this is decides the target. TOK_PEEL (the shared
        // funnel's first-excursion recovery) targets the steady header /
        // outer-labeled copy, as ever. The dirty cycle's own back edge
        // (TOK_CYCLE) and the recovery twin's excursion funnel
        // (TOK_RECOVER_PEEL) target the RECOVERY TWIN instead -- the Opt
        // header copy keyed with an own-loop TOK_RECOVER marker, entered
        // only by these proof edges. Targeting the STEADY header from
        // the dirty cycle would make the composite region a two-headed,
        // irreducible SCC; the twin has no preheader entry, so the
        // composite region stays a natural loop headed at the dirty
        // header.
        // Twin admission is off: the dirty cycle's own back edge is not an
        // unproven population but a false one (its facts are typically
        // wrong, e.g. an unstamped receiver), so the guards fail on
        // essentially every attempt and no admission rule built on
        // frequency or guard count can change that. Re-enabling it needs a
        // mechanism that makes the guards pass, not another gate.
        //
        // To re-admit, make `twin` true for `TOK_CYCLE` / `TOK_RECOVER_PEEL`
        // below.
        let twin = false;
        if funnel {
            let cur_tok = self
                .cur_tokens
                .iter()
                .find(|&&(i, _)| i == lidx)
                .map(|&(_, t)| t);
            match cur_tok {
                Some(t) if t == TOK_PEEL => {}
                _ => {
                    onramp_log(self, "decline funnel-token");
                    return None;
                }
            }
        }
        let Ok(depth) = u16::try_from(self.stack.len()) else {
            onramp_log(self, "decline stack-depth");
            return None;
        };
        // The proof target: the Opt version keyed by the arriving
        // lineage's own outer labels with this loop's token dropped
        // (out_tokens_for's header rule). For an outermost header that
        // class is empty and the target IS the existing steady Opt header.
        // For a non-outermost header the target is a new copy of the inner
        // loop: conforming into the existing inner Opt header (whose class
        // carries the outer OPT label) would enter the outer Opt cycle
        // off-header, but the copy cycles alone -- its own back edge keeps
        // the outer labels and re-targets it, and its outer back edge
        // drops the outer token at the outer header and so re-enters the
        // outer Opt cycle at its header: one loop level recovered per
        // iteration, reducibility by construction.
        let toks_out = self.out_tokens_for(Pc::new(h));
        // Every outer label must be the dirty-cycle membership: the copy's
        // tail re-crosses each enclosing header carrying these labels, and
        // only TOK_CYCLE routes it back into the dirty cycle there (the
        // cont_normal cascade-boundary rule). A peel-labeled tail would
        // rejoin the steady Opt header off its dominance region -- the
        // irreducible shape. First-entry (peel) dirt becomes cycle after
        // one pass of the enclosing dirty cycle and conforms from the
        // second outer iteration on.
        //
        // Admitting TOK_PEEL here is unsound: the shared funnel erases
        // outer-cycle provenance (a steady excursion under outer-OPT and a
        // copy's excursion both collapse to outer-PEEL), so a proof out of
        // the funnel to any one inner Opt cycle couples the steady cycle
        // and the copy through the shared funnel segment -- a multi-headed,
        // irreducible SCC. Un-sharing the funnel per outer-history is the
        // version explosion the funnel exists to prevent.
        // Outer TOK_PEEL is declined for BOTH modes. For the peel-funnel
        // conform the reason is the original one (its tail re-enters the
        // enclosing steady cycle off-header). For the TWIN it is one step
        // subtler: the twin itself is sound under an outer peel
        // (conform-only entries, an acyclic exit tail reaching the
        // enclosing header AT the header), but a two-deep nest under
        // both-PEEL labels re-couples a shared funnel. Admitting
        // outer-PEEL twins needs one more grammar rule for that interior
        // funnel.
        if !toks_out.iter().all(|&(_, t)| t == TOK_CYCLE) {
            onramp_log(self, "decline entry-peel-label");
            return None;
        }
        let toks_out = if twin {
            // The twin's identity: the arriving outer labels plus the
            // own-loop recovery marker, inserted in loop-index order.
            let mut t = toks_out;
            let at = t.partition_point(|&(i, _)| i < lidx);
            t.insert(at, (lidx, TOK_RECOVER));
            t
        } else {
            toks_out
        };
        let class_out = self.tok_class(&toks_out);
        let tgt_key = Ver {
            pc: Pc::new(h),
            class: class_out,
            track: Track::Opt,
            depth,
        };
        // The facts to prove are the header pc's PREDICTION. There is one
        // per program point, so the steady Opt cycle and every proof copy
        // of this header read the same one -- there is no per-copy context
        // to seed, and no "unseeded" case to decline. If no Opt lineage
        // ever reached this header there is no prediction, and nothing to
        // rejoin.
        //
        // Minting a prediction for a header no Opt lineage reaches (instead
        // of declining) is a loss however the seed is chosen: such a
        // header's body steps off Opt every iteration, so the minted copy
        // runs Opt header -> departure -> Dirty tail -> funnel-back-edge
        // conform -> Opt header, and pays the proof's reloads every
        // iteration where the Dirty cycle carried its values in SSA.
        // Interior re-entry has to happen where the lineage falls off
        // (post-call re-entry), not at the header.
        let hpc = Pc::new(h);
        let (Some(facts), Some(hcarried)) = (
            self.vers.pred.at(hpc).cloned(),
            self.vers.pred.carried(hpc, Track::Opt).cloned(),
        ) else {
            onramp_log(self, "decline no-opt-header");
            return None;
        };
        let opt = self.vers.intern(tgt_key);
        let opt_ctx = Ctx {
            tokens: toks_out,
            carried: hcarried,
            track: Track::Opt,
            ..facts
        }
        .canon();
        if self.vers.ctx[opt.0 as usize].as_ref() != Some(&opt_ctx) {
            if self.mode == EmitMode::Code {
                // Consult-only: the prediction pass never walked this copy,
                // so emitting into it would emit against an open map.
                onramp_log(self, "decline unseeded");
                return None;
            }
            self.vers.ctx[opt.0 as usize] = Some(opt_ctx.clone());
            self.map_changed = true;
            self.changed_discover += 1;
        }
        // Caller-frame claims (splice ctx) are compile-time carried state
        // the proof cannot re-prove; same-frame edges only. An iv-only
        // caller claim does not decline: the interval is arrival-joined
        // below like every other slot's, never guard-proven.
        let tgt_seg = self.seg_of(Pc::new(h));
        if tgt_seg != self.ssa_seg {
            onramp_log(self, "decline cross-seg");
            return None;
        }
        // The proof's target must live in the frame whose locals are in SSA
        // here; a cross-frame edge is not something the guard chain can
        // rebuild. The CALLER's frame is a different matter: a splice
        // carries the caller's frame facts into the segment ctx by
        // construction, so a header inside a segment claims them, and those
        // claims are discharged by `ProofSrc::CallerLocal` / `CallerArgSlot`
        // below like any other slot. Refusing them outright would leave a
        // loop that degrades on a handful of caller-frame slots cycling on
        // GEN indefinitely instead of recovering once those slots are
        // re-proven.
        let tgt_seg = self.seg_of(Pc::new(h));
        if tgt_seg != self.ssa_seg {
            onramp_log(self, "decline cross-seg");
            return None;
        }
        // Feasibility over every slot the Opt ctx claims: stack, all
        // locals and args (a fact on a frame-resident slot is trusted at
        // its next read, so it owes a guard even when nothing is carried).
        let ProofPlan {
            gaps,
            iv_stack,
            iv_locals,
            iv_args,
            //
            // `iv_guards` is true on the funnel too: passing false would
            // widen the header's stored intervals to what a Tag guard
            // delivers (the full int32 range) through `pred.set`, silently
            // erasing a loop-invariant constant, and because `set` bypasses
            // `join_arrival` no mint, rejoin or ctxjoin record would show
            // it.
            //
            // The guards this admits cannot fail: `iv_gap_guardable` fires only
            // where the delivery would MOVE the stored interval, which on a
            // funnel edge is exactly the loop-INVARIANT slots (a slot the
            // ordinary back edge already widened has a stored interval the
            // Tag delivery does not move, so it asks for nothing). A genuine
            // loop counter is therefore untouched, and the constant costs one
            // i32 compare that is true by construction.
        } = match self.proof_gaps(&opt_ctx, succ_pc, depth, true) {
            Ok(p) => p,
            Err(why) => {
                onramp_log(self, &why);
                return None;
            }
        };
        // An entry edge may owe a guard: owing one does not by itself
        // decline. The guard chain this admits has a code-layout cost even
        // where it never executes -- cold chains placed at hot loop
        // entries -- but the Opt reach it buys elsewhere is worth it: Opt
        // reach is the direction, and that cost is a code-layout cost in a
        // tier whose bulk is a standing, separately tracked problem.
        // Paying it now and out-lining the cold tier later is the chosen
        // order; refusing reach to protect a layout that is itself slated
        // for rework would be the short-sighted trade.
        //
        // The honest caveat, so the next reader does not have to
        // rediscover it: this reach does NOT by itself make the executed
        // code denser -- the ladder arm a site takes is set by its
        // `prop_sites` row and by whether a durable fact is live, not by
        // the track. Reach is a precondition for compaction, not
        // compaction.
        // The twin owes whatever the proof owes, and pays it. No cost gate
        // restricts admission to a free conform: if the arriving context
        // matches the header's prediction it is almost certainly better to
        // run OPT, and a guard-count heuristic at this seam would hide the
        // benefit it is meant to price. Feasibility still decides (an
        // unprovable gap is an `Err` from `proof_gaps` above, not a cost);
        // the count is only reported, so the population stays countable.
        if twin {
            onramp_log(self, &format!("twin ({} gaps)", gaps.len()));
        }
        let _ = &gaps;
        // The proof edge discharges the guardable facts; for the
        // interval component (proof_gap is interval-blind) the funnel
        // form joins what each slot delivers into the header's stored iv,
        // exactly as theta's iv-only step would. The entry form is
        // iv-conservative instead: if the delivery would widen any stored iv
        // of the target header, decline rather than join. Joining on an
        // entry edge erodes the steady header's rungs for every other
        // lineage, which costs more than the proof recovers. Declining
        // mutates nothing, so the map stays closed and the decision is
        // stable within a round. Skipped once ivs are stripped
        // (stripping): there are no ivs to erode or join.
        if !self.stripping {
            let ivslot = |iv: &Option<ValueRange>| SlotCtx {
                iv: *iv,
                ..SlotCtx::TOP
            };
            let arr = Ctx {
                locals: iv_locals.iter().map(ivslot).collect(),
                stack: iv_stack.iter().map(ivslot).collect(),
                args: iv_args.iter().map(ivslot).collect(),
                // Caller slots deliver the current lineage's caller claims
                // unguarded (the proof never touches the caller frame).
                caller_locals: self
                    .caller_locals_ctx
                    .iter()
                    .map(|s| ivslot(&s.iv))
                    .collect(),
                caller_args: self.caller_args_ctx.iter().map(|s| ivslot(&s.iv)).collect(),
                outer: self
                    .outer_ctx
                    .iter()
                    .map(|f| CallerFrame {
                        locals: f.locals.iter().map(|s| ivslot(&s.iv)).collect(),
                        args: f.args.iter().map(|s| ivslot(&s.iv)).collect(),
                    })
                    .collect(),
                tokens: opt_ctx.tokens.clone(),
                carried: Vec::new(),
                gcells: Vec::new(),
                track: Track::Opt,
            };
            let cur = self.vers.ctx[opt.0 as usize]
                .as_ref()
                .expect("opt header ctx exists");
            let j = cur.join_iv_only(&arr);
            let widened_slots = |cur: &Ctx, j: &Ctx| {
                let mut widened: Vec<String> = Vec::new();
                let mut diff = |tag: &str, a: &[SlotCtx], b: &[SlotCtx]| {
                    for (i, (x, y)) in a.iter().zip(b.iter()).enumerate() {
                        if x.iv != y.iv || x.iv_grow != y.iv_grow {
                            widened.push(format!("{tag}{i} {:?}->{:?}", x.iv, y.iv));
                        }
                    }
                };
                diff("loc", &cur.locals, &j.locals);
                diff("stk", &cur.stack, &j.stack);
                diff("arg", &cur.args, &j.args);
                diff("cloc", &cur.caller_locals, &j.caller_locals);
                diff("carg", &cur.caller_args, &j.caller_args);
                widened.join(" ")
            };
            if j != *cur {
                if !funnel {
                    if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
                        onramp_log(
                            self,
                            &format!("decline iv-widening [{}]", widened_slots(cur, &j)),
                        );
                    } else {
                        onramp_log(self, "decline iv-widening");
                    }
                    return None;
                }
                if self.mode == EmitMode::Code {
                    // Consult-only: widening the header's prediction now
                    // would move a closed map under emitted code.
                    onramp_log(self, "decline iv-widening (closed)");
                    return None;
                }
                // The funnel DOES join, so name what it erodes.
                //
                // NOT `onramp_log`: `onramp_log`'s silence here is not
                // evidence of inactivity -- this event happens only in
                // `ContextOnly` (the branch above returns in `Code`), and
                // `onramp_log` prints only in `Code`. It bypasses
                // `join_arrival`, so no mint, rejoin or ctxjoin record
                // shows it either.
                if self.opts.diagnostics.bbv || self.opts.diagnostics.ctxedge {
                    crate::diag_line!(
                        "night: funnel-iv-widen sid#{} hdr {h} from pc {} [{}]",
                        self.source_id,
                        self.cur_pc,
                        widened_slots(cur, &j)
                    );
                }
                self.vers.pred.set(hpc, j.facts_only());
                self.map_changed = true;
                self.changed_join += 1;
                self.rearm_pc(hpc);
            }
        }
        let (k_try, k_ok) = if twin {
            (census::CYC_ONRAMP_TRY, census::CYC_ONRAMP_OK)
        } else {
            (census::ONRAMP_TRY, census::ONRAMP_OK)
        };
        let target = self.emit_proof(opt, &opt_ctx, tgt_seg, depth, &gaps, bail, k_try, k_ok);
        if (self.opts.diagnostics.bbv || self.opts.diagnostics.viz) && self.mode == EmitMode::Code {
            let desc: Vec<String> = gaps
                .iter()
                .map(|(s, t, _)| {
                    let loc = match s {
                        ProofSrc::Stack(i) => format!("stk{i}"),
                        ProofSrc::Local(l) => format!("loc{l}"),
                        ProofSrc::ArgSlot(0) => "this".to_string(),
                        ProofSrc::ArgSlot(i) => format!("arg{}", i - 1),
                        ProofSrc::CallerLocal(l) => format!("cloc{l}"),
                        ProofSrc::CallerArgSlot(0) => "cthis".to_string(),
                        ProofSrc::CallerArgSlot(i) => format!("carg{}", i - 1),
                        ProofSrc::GCell(b) => format!("g{b}"),
                    };
                    format!(
                        "{loc}:m{:x}o{}r{:?}c{:?}s{}",
                        t.prims.bits(),
                        u8::from(t.outside),
                        t.range,
                        t.cls,
                        u8::from(t.cls_shallow)
                    )
                })
                .collect();
            if self.opts.diagnostics.bbv {
                crate::diag_line!(
                    "night: onramp emit sid#{} hdr {h} from pc {} guards [{}]",
                    self.source_id,
                    self.cur_pc,
                    desc.join(" ")
                );
            }
            if self.opts.diagnostics.viz {
                let gdesc: Vec<String> = gaps
                    .iter()
                    .map(|(s, t, _)| {
                        let loc = match s {
                            ProofSrc::Stack(i) => format!("s{i}"),
                            ProofSrc::Local(l) => format!("l{l}"),
                            ProofSrc::ArgSlot(0) => "this".to_string(),
                            ProofSrc::ArgSlot(i) => format!("a{}", i - 1),
                            ProofSrc::CallerLocal(l) => format!("cl{l}"),
                            ProofSrc::CallerArgSlot(0) => "cthis".to_string(),
                            ProofSrc::CallerArgSlot(i) => format!("ca{}", i - 1),
                            ProofSrc::GCell(b) => format!("g{b}"),
                        };
                        format!("{loc}={}", Self::viz_slot_str(t))
                    })
                    .collect();
                crate::diag_line!(
                    "night: viz onramp emit sid#{} hdr {h} pc {} site {} guards [{}]",
                    self.root_source_id,
                    self.cur_pc,
                    self.viz_site(self.cur_pc),
                    gdesc.join(" ")
                );
            }
        }
        Some(target)
    }

    /// Whether a call-return proof is worth its guards.
    ///
    /// Two static inputs decide whether a call-return proof is worth its
    /// guards:
    ///
    /// - **What the proof costs**: the guard chain's length. A proof
    ///   owing nothing at all is free and always admitted -- it is a
    ///   branch on a constant that waffle folds away.
    /// - **How often the edge runs, against what it recovers**: this edge
    ///   runs once per execution of its call site, and what it buys is
    ///   every program point from the successor to the end of the
    ///   innermost loop containing it (past that, the loop's own header
    ///   on-ramp is the recovery mechanism, and outside a loop, the rest
    ///   of the body). Recovering a long tail is worth more guards than
    ///   recovering three ops, so the budget is proportional to the span.
    ///
    /// The ratio is a byte count rather than an op count because the span
    /// is bytecode, and the constant is one guard per `RET_ONRAMP_BYTES_PER_GUARD`
    /// bytes of recovered code.
    fn ret_onramp_admits(&self, succ_pc: Pc, gaps: &[(ProofSrc, SlotCtx, ProofGuard)]) -> bool {
        if gaps.is_empty() {
            return true;
        }
        let seg_end = match self.seg_of(succ_pc) {
            Some(i) => self.segs[i].end,
            None => u32::try_from(self.script.bytecode.len()).unwrap(),
        };
        // The innermost enclosing loop's end, else the body's.
        let end = self
            .loop_intervals
            .iter()
            .filter(|&&(h, e)| succ_pc >= Pc::new(h) && succ_pc < Pc::new(e))
            .map(|&(_, e)| e)
            .min()
            .unwrap_or(seg_end);
        let span = end.saturating_sub(succ_pc.get());
        usize::try_from(span / RET_ONRAMP_BYTES_PER_GUARD).unwrap() >= gaps.len()
    }

    /// The proof plan for one target fact context: which slots owe a
    /// guard, and what interval each one would deliver.
    ///
    /// `Err` is a decline -- some slot's fact is outside the guard
    /// vocabulary, so no proof edge to this target is possible from here
    /// -- and carries the reason, for the diagnostic. Pure: it reads the
    /// lineage and mints nothing.
    ///
    /// `iv_guards` admits the interval bounds check as a guard. The funnel
    /// back edge passes false and arrival-joins its intervals into the
    /// target header instead; an edge that must not move the target's
    /// prediction (an entry edge, a call return) passes true and proves
    /// them.
    fn proof_gaps(
        &self,
        opt_ctx: &Ctx,
        succ_pc: Pc,
        depth: u16,
        iv_guards: bool,
    ) -> Result<ProofPlan, String> {
        let mut gaps: Vec<(ProofSrc, SlotCtx, ProofGuard)> = Vec::new();
        // A slot the target cannot read before writing owes no guard: its
        // frame value may be a stale deferred store (the liveness rule that
        // skipped the flush), and the fact is never consumed.
        let tgt_seg = self.seg_of(succ_pc);
        let mut iv_stack: Vec<Option<ValueRange>> = Vec::new();
        let mut iv_locals: Vec<Option<ValueRange>> = Vec::new();
        let mut iv_args: Vec<Option<ValueRange>> = Vec::new();
        for i in 0..usize::from(depth) {
            let tgt = opt_ctx.stack_slot(i);
            let o = &self.stack[i];
            let g = match Self::proof_gap(&o.slot(), o.repr, &tgt) {
                Some(Some(g)) => {
                    gaps.push((ProofSrc::Stack(i), tgt, g));
                    Some(g)
                }
                Some(None) => None,
                None => {
                    return Err(Self::gap_why(
                        "stack-gap",
                        &format!("stk{i}"),
                        &o.slot(),
                        o.repr,
                        &tgt,
                    ))
                }
            };
            let mut delivered = Self::proof_delivered_iv(&o.slot(), g, &tgt);
            if iv_guards && Self::iv_gap_guardable(delivered, &o.slot(), &tgt, o.repr, g) {
                gaps.push((ProofSrc::Stack(i), tgt, ProofGuard::IvRange));
                delivered = tgt.iv;
            }
            iv_stack.push(delivered);
        }
        for l in 0..self.nlocals {
            let tgt = opt_ctx.local(l as usize);
            if tgt.is_top() || !self.key_live_at(tgt_seg, succ_pc, l) {
                iv_locals.push(None);
                continue;
            }
            let src = self
                .locals_ctx
                .get(l as usize)
                .copied()
                .unwrap_or(SlotCtx::TOP);
            let repr = self
                .locals_ssa
                .get(l as usize)
                .copied()
                .flatten()
                .map_or(Repr::Boxed, |(_, r)| r);
            let g = match Self::proof_gap(&src, repr, &tgt) {
                Some(Some(g)) => {
                    gaps.push((ProofSrc::Local(l), tgt, g));
                    Some(g)
                }
                Some(None) => None,
                None => {
                    return Err(Self::gap_why(
                        "local-gap",
                        &format!("loc{l}"),
                        &src,
                        repr,
                        &tgt,
                    ))
                }
            };
            let mut delivered = Self::proof_delivered_iv(&src, g, &tgt);
            if iv_guards && Self::iv_gap_guardable(delivered, &src, &tgt, repr, g) {
                gaps.push((ProofSrc::Local(l), tgt, ProofGuard::IvRange));
                delivered = tgt.iv;
            } else if iv_guards
                && self.opts.diagnostics.bbv
                && self.mode == EmitMode::Code
                && tgt.iv.is_some()
            {
                let (niv, ngrow) = crate::opsem::iv_join_tolerant(delivered, tgt.iv, tgt.iv_grow);
                if (niv, ngrow) != (tgt.iv, tgt.iv_grow) {
                    crate::diag_line!(
                        "night: ivgap-hard sid#{} loc{l} repr {:?} srcm {:?} o{} g {:?}",
                        self.source_id,
                        repr,
                        src.prims,
                        u8::from(src.outside),
                        g
                    );
                }
            }
            iv_locals.push(delivered);
        }
        for i in 0..1 + usize::from(self.nformals) {
            let tgt = opt_ctx.arg(i);
            let dead = i > 0
                && !self.key_live_at(tgt_seg, succ_pc, STALE_ARG | u32::try_from(i - 1).unwrap());
            if tgt.is_top() || dead {
                iv_args.push(None);
                continue;
            }
            let src = self.args_ctx.get(i).copied().unwrap_or(SlotCtx::TOP);
            if i == 0 {
                // `this` is never SSA-cached: always a boxed frame load.
                let g = match Self::proof_gap(&src, Repr::Boxed, &tgt) {
                    Some(Some(g)) => {
                        gaps.push((ProofSrc::ArgSlot(0), tgt, g));
                        Some(g)
                    }
                    Some(None) => None,
                    None => return Err(Self::gap_why("this-gap", "this", &src, Repr::Boxed, &tgt)),
                };
                iv_args.push(Self::proof_delivered_iv(&src, g, &tgt));
                continue;
            }
            let repr = self
                .args_ssa
                .get(i - 1)
                .copied()
                .flatten()
                .map_or(Repr::Boxed, |(_, r)| r);
            let g = match Self::proof_gap(&src, repr, &tgt) {
                Some(Some(g)) => {
                    gaps.push((ProofSrc::ArgSlot(i), tgt, g));
                    Some(g)
                }
                Some(None) => None,
                None => {
                    return Err(Self::gap_why(
                        "arg-gap",
                        &format!("arg{}", i - 1),
                        &src,
                        repr,
                        &tgt,
                    ))
                }
            };
            let mut delivered = Self::proof_delivered_iv(&src, g, &tgt);
            if iv_guards && Self::iv_gap_guardable(delivered, &src, &tgt, repr, g) {
                gaps.push((ProofSrc::ArgSlot(i), tgt, ProofGuard::IvRange));
                delivered = tgt.iv;
            }
            iv_args.push(delivered);
        }
        // The caller's frame, when the target header is inside a spliced
        // segment. The arriving lineage knows nothing about these slots --
        // GEN carries no facts, and every on-ramp source is a GEN lineage --
        // which is not an obstacle but the premise: the proof edge exists to
        // re-establish facts by testing for them. So the source is TOP and
        // the guard is whatever the claim needs. The slot is a boxed frame
        // load from the parent segment's view; nothing in the segment can
        // have written it, because a splice cannot assign the caller's
        // frame.
        // The caller's slots the caller cannot read after the return owe no
        // guard either: the seam left them stale for the same reason.
        let parent_ret = tgt_seg.map(|i| (self.segs[i].parent, self.segs[i].ret_pc));
        for (l, tgt) in opt_ctx.caller_locals.iter().enumerate() {
            if tgt.is_top_sans_iv() {
                continue;
            }
            let l = u32::try_from(l).unwrap();
            if !self.outer_live_after(tgt_seg, l) {
                continue;
            }
            match Self::proof_gap(&SlotCtx::TOP, Repr::Boxed, tgt) {
                Some(Some(g)) => gaps.push((ProofSrc::CallerLocal(l), *tgt, g)),
                Some(None) => {}
                None => {
                    return Err(Self::gap_why(
                        "caller-local-gap",
                        &format!("cloc{l}"),
                        &SlotCtx::TOP,
                        Repr::Boxed,
                        tgt,
                    ))
                }
            }
        }
        for (i, tgt) in opt_ctx.caller_args.iter().enumerate() {
            if tgt.is_top_sans_iv() {
                continue;
            }
            let dead = i > 0
                && parent_ret.is_some_and(|(pseg, rpc)| {
                    !self.key_live_at(pseg, rpc, STALE_ARG | u32::try_from(i - 1).unwrap())
                });
            if dead {
                continue;
            }
            match Self::proof_gap(&SlotCtx::TOP, Repr::Boxed, tgt) {
                Some(Some(g)) => gaps.push((ProofSrc::CallerArgSlot(i), *tgt, g)),
                Some(None) => {}
                None => {
                    return Err(Self::gap_why(
                        "caller-arg-gap",
                        &format!("carg{i}"),
                        &SlotCtx::TOP,
                        Repr::Boxed,
                        tgt,
                    ))
                }
            }
        }
        // The binding value facts: the arriving lineage's own fact for the
        // binding (TOP on a GEN arrival) against the target's, discharged
        // like a boxed frame slot -- the operand is the binding's current
        // value (`gcell_current_value`), and the guard is the tag test.
        for (bid, tgt) in &opt_ctx.gcells {
            let src = self
                .gcells_ctx
                .iter()
                .find(|(x, _)| x == bid)
                .map_or(SlotCtx::TOP, |(_, s)| *s);
            match Self::proof_gap(&src, Repr::Boxed, tgt) {
                Some(Some(g)) => gaps.push((ProofSrc::GCell(*bid), *tgt, g)),
                Some(None) => {}
                None => {
                    return Err(Self::gap_why(
                        "gcell-gap",
                        &format!("g{bid}"),
                        &src,
                        Repr::Boxed,
                        tgt,
                    ))
                }
            }
        }
        Ok(ProofPlan {
            gaps,
            iv_stack,
            iv_locals,
            iv_args,
        })
    }

    /// A slot of the caller's frame, as a boxed load through the parent
    /// segment's frame view. `seg` is the frame the proof's target lives in;
    /// its parent is the caller (`None` = the root frame).
    fn caller_operand_for_edge(&mut self, seg: Option<usize>, slot: CallerSlot) -> Operand {
        let parent = seg.and_then(|i| self.segs[i].parent);
        let base = match parent {
            Some(p) => self.segs[p].frame_base,
            None => 0,
        };
        let v = match slot {
            CallerSlot::Local(l) => {
                let lb = self.frame_local_base_of(parent);
                self.load_i64(self.vp, lb + 8 * l)
            }
            CallerSlot::Arg(0) => match parent {
                Some(_) => self.load_i64(self.vp, base + 8),
                None => self.load_i64(self.sp, 8),
            },
            CallerSlot::Arg(i) => {
                let a = u32::try_from(i - 1).unwrap();
                match parent {
                    Some(_) => self.load_i64(self.vp, base + 16 + 8 * a),
                    None => self.load_i64(self.sp, 16 + 8 * a),
                }
            }
        };
        Operand::plain(v, Repr::Boxed, bottom_ty())
    }

    /// Emit one proof edge: an edge-owned guard chain proving `opt_ctx`,
    /// branching to version `opt` on success and to `bail` on any failure.
    /// Returns the chain's entry block, for the caller to branch at.
    ///
    /// This is the mechanism, and it is deliberately policy-free -- which
    /// target, which edges may attempt one, and what an unprovable interval
    /// means all stay with the caller. Two callers: the loop-header on-ramp
    /// (`try_onramp`) and the call-return on-ramp
    /// (`try_call_return_onramp`).
    ///
    /// Nothing here mutates lineage state. The operand-for-edge fetchers
    /// read caches or emit fresh frame loads into the proof's own blocks,
    /// so the caller's fall-through is unaffected.
    #[allow(clippy::too_many_arguments)]
    fn emit_proof(
        &mut self,
        opt: VerId,
        opt_ctx: &Ctx,
        tgt_seg: Option<usize>,
        depth: u16,
        gaps: &[(ProofSrc, SlotCtx, ProofGuard)],
        bail: &BlockTarget,
        k_try: u32,
        k_ok: u32,
    ) -> BlockTarget {
        // Emit: an edge-owned block chain. Nothing below mutates lineage
        // state (the operand-for-edge fetchers read caches or emit fresh
        // frame loads into the current -- conform -- block).
        let saved_cur = self.cur;
        let entry = self.body.add_block();
        self.cur = entry;
        self.emit_guard_census(k_try, self.cur_pc);
        let carried = self.carried_for(tgt_seg, opt_ctx);
        let mut phase1: Option<Value> = None;
        let mut cls_checks: Vec<(Value, SlotCtx)> = Vec::new();
        for (ord, (src, tgt, guard)) in gaps.iter().enumerate() {
            let mut gcell_have: Option<Value> = None;
            let o = match src {
                ProofSrc::Stack(i) => self.stack[*i].clone(),
                ProofSrc::Local(l) => self.local_operand_for_edge(tgt_seg, *l),
                ProofSrc::ArgSlot(0) => {
                    let v = match tgt_seg {
                        Some(i) => {
                            let base = self.segs[i].frame_base;
                            self.load_i64(self.vp, base + 8)
                        }
                        None => self.load_i64(self.sp, 8),
                    };
                    Operand::plain(v, Repr::Boxed, bottom_ty())
                }
                ProofSrc::ArgSlot(i) => {
                    let argno = u16::try_from(*i - 1).unwrap();
                    self.arg_operand_for_edge(tgt_seg, argno)
                }
                ProofSrc::CallerLocal(l) => {
                    self.caller_operand_for_edge(tgt_seg, CallerSlot::Local(*l))
                }
                ProofSrc::CallerArgSlot(i) => {
                    self.caller_operand_for_edge(tgt_seg, CallerSlot::Arg(*i))
                }
                ProofSrc::GCell(bid) => {
                    let (v, have) = self.gcell_current_value(self.cur_pc, *bid);
                    gcell_have = Some(have);
                    Operand::plain(v, Repr::Boxed, bottom_ty())
                }
            };
            let c = match guard {
                ProofGuard::Tag => {
                    debug_assert!(o.repr == Repr::Boxed);
                    self.proof_tag_cond(o.val, tgt)
                }
                ProofGuard::ExactI64 => {
                    debug_assert!(o.repr == Repr::I64);
                    let w = self.unop(Operator::I32WrapI64, o.val, Type::I32);
                    let x = self.unop(Operator::I64ExtendI32S, w, Type::I64);
                    self.binop(Operator::I64Eq, o.val, x, Type::I32)
                }
                ProofGuard::IvRange => {
                    // Bounds check against the stored interval. A boxed
                    // arrival's low bits are compared unconditionally: its
                    // int32-only tag condition is in the same phase-1
                    // conjunction, so a non-int payload fails the edge via
                    // that condition regardless. A repr the gap builder did
                    // not promise fails closed (bail = stay Dirty).
                    let iv = tgt.iv.expect("IvRange gap carries a stored interval");
                    let mut c: Option<Value> = None;
                    let and_in = |slf: &mut Self, c: &mut Option<Value>, x: Value| {
                        *c = Some(match *c {
                            Some(p) => slf.binop(Operator::I32And, p, x, Type::I32),
                            None => x,
                        });
                    };
                    match o.repr {
                        Repr::F64 => {
                            if iv.lo > i64::from(i32::MIN) {
                                let lo = self.f64_const(iv.lo as f64);
                                let ge = self.binop(Operator::F64Ge, o.val, lo, Type::I32);
                                and_in(self, &mut c, ge);
                            }
                            if iv.hi < i64::from(i32::MAX) {
                                let hi = self.f64_const(iv.hi as f64);
                                let le = self.binop(Operator::F64Le, o.val, hi, Type::I32);
                                and_in(self, &mut c, le);
                            }
                        }
                        Repr::I32 | Repr::Boxed => {
                            let v = if o.repr == Repr::I32 {
                                o.val
                            } else {
                                self.unop(Operator::I32WrapI64, o.val, Type::I32)
                            };
                            if iv.lo > i64::from(i32::MIN) {
                                let lo = self.i32_const(iv.lo as i32 as u32);
                                let ge = self.binop(Operator::I32GeS, v, lo, Type::I32);
                                and_in(self, &mut c, ge);
                            }
                            if iv.hi < i64::from(i32::MAX) {
                                let hi = self.i32_const(iv.hi as i32 as u32);
                                let le = self.binop(Operator::I32LeS, v, hi, Type::I32);
                                and_in(self, &mut c, le);
                            }
                        }
                        _ => {
                            debug_assert!(false, "IvRange gap on unsupported repr");
                            let z = self.i32_const(0);
                            and_in(self, &mut c, z);
                        }
                    }
                    c.unwrap_or_else(|| self.i32_const(1))
                }
                ProofGuard::ExactF64 => {
                    debug_assert!(o.repr == Repr::F64);
                    // Saturating trunc so NaN and out-of-range values fail
                    // the compare instead of trapping; the round-trip then
                    // holds exactly for the int32-valued doubles.
                    let i = self.unop(Operator::I32TruncSatF64S, o.val, Type::I32);
                    let back = self.unop(Operator::F64ConvertI32S, i, Type::F64);
                    let eq = self.binop(Operator::F64Eq, o.val, back, Type::I32);
                    // -0 round-trips through 0 and `f64.eq` calls it equal,
                    // so the bit pattern has to be excluded outright: the
                    // target claims int32, and boxing -0 as 0 is a real
                    // change of value.
                    let bits = self.unop(Operator::I64ReinterpretF64, o.val, Type::I64);
                    let negz = self.boxed_const(0x8000_0000_0000_0000);
                    let not_negz = self.binop(Operator::I64Ne, bits, negz, Type::I32);
                    self.binop(Operator::I32And, eq, not_negz, Type::I32)
                }
            };
            // A binding fact's value comes from the cell or the guarded
            // slot; a name neither can serve fails the edge.
            let c = match gcell_have {
                Some(have) => self.binop(Operator::I32And, have, c, Type::I32),
                None => c,
            };
            phase1 = Some(match phase1 {
                Some(p) => self.binop(Operator::I32And, p, c, Type::I32),
                None => c,
            });
            // Instrument-only per-guard verdict: kind 1000 + 2*ordinal +
            // pass, ordinal in `gaps` order (matching the emit log's guard
            // list), so a persistently failing conform names its dead slot.
            if self.guard_census_on() {
                let ord = u32::try_from(ord).unwrap();
                let kf = self.i32_const(1000 + 2 * ord);
                let kp = self.i32_const(1000 + 2 * ord + 1);
                let kv = self.select(Type::I32, kp, kf, c);
                self.emit_guard_census_dyn(kv, self.cur_pc);
                // On a failing boxed tag guard, the operand's nunbox tag
                // rides as the id of kind 1800+ordinal: what the slot
                // actually HELD (a stale frame copy reads differently
                // from a genuinely retyped variable).
                if matches!(guard, ProofGuard::Tag) {
                    let sh = self.boxed_const(32);
                    let hi64 = self.binop(Operator::I64ShrU, o.val, sh, Type::I64);
                    let tag = self.unop(Operator::I32WrapI64, hi64, Type::I32);
                    let z = self.i32_const(0);
                    let tid = self.select(Type::I32, z, tag, c);
                    let kt = self.i32_const(1800 + ord);
                    self.emit_guard_census_dyn_id(kt, tid);
                }
            }
            if tgt.cls.is_some() || tgt.cls_shallow || tgt.cls_slots {
                cls_checks.push((o.val, *tgt));
            }
        }
        let succ_blk = self.body.add_block();
        let p2_blk = if cls_checks.is_empty() {
            None
        } else {
            Some(self.body.add_block())
        };
        let after_p1 = p2_blk.unwrap_or(succ_blk);
        match phase1 {
            Some(c) => self.body.set_terminator(
                self.cur,
                Terminator::CondBr {
                    cond: c,
                    if_true: BlockTarget {
                        block: after_p1,
                        args: vec![],
                    },
                    if_false: bail.clone(),
                },
            ),
            None => self.body.set_terminator(
                self.cur,
                Terminator::Br {
                    target: BlockTarget {
                        block: after_p1,
                        args: vec![],
                    },
                },
            ),
        }
        if let Some(p2) = p2_blk {
            // Class-word reads only run behind the phase-1 object proofs:
            // a wild in-bounds read of a non-object payload could
            // spuriously match.
            self.cur = p2;
            let mut cond: Option<Value> = None;
            let and_into = |slf: &mut Self, cur: Option<Value>, c: Value| match cur {
                Some(p) => Some(slf.binop(Operator::I32And, p, c, Type::I32)),
                None => Some(c),
            };
            for (j, (boxed, tgt)) in cls_checks.iter().enumerate() {
                let ptr = self.unop(Operator::I32WrapI64, *boxed, Type::I32);
                if let Some((lo, hi)) = tgt.cls {
                    let idx = self.load16_u(ptr, OBJ_CLASS_IDX_OFFSET);
                    self.eff(idx, Eff::ReadBits(HeapKind::ClassWord));
                    let c = if lo == hi {
                        let k = self.i32_const(u32::from(lo));
                        self.binop(Operator::I32Eq, idx, k, Type::I32)
                    } else {
                        let klo = self.i32_const(u32::from(lo));
                        let khi = self.i32_const(u32::from(hi));
                        let ge = self.binop(Operator::I32GeU, idx, klo, Type::I32);
                        let le = self.binop(Operator::I32LeU, idx, khi, Type::I32);
                        self.binop(Operator::I32And, ge, le, Type::I32)
                    };
                    // Instrument-only twin of the phase-1 verdicts: kind
                    // 1500 + 2*ordinal + pass for the class-idx checks
                    // (kind 1600 band for the flag-bit checks below), and
                    // the receiver's whole class word keyed by kind 1700 +
                    // ordinal on a failing idx check, naming what the
                    // receivers actually carry.
                    if self.guard_census_on() {
                        let jj = u32::try_from(j).unwrap();
                        let kf = self.i32_const(1500 + 2 * jj);
                        let kp = self.i32_const(1500 + 2 * jj + 1);
                        let kv = self.select(Type::I32, kp, kf, c);
                        self.emit_guard_census_dyn(kv, self.cur_pc);
                        let w = self.load_i32(ptr, OBJ_CLASS_IDX_OFFSET);
                        self.eff(w, Eff::ReadBits(HeapKind::ClassWord));
                        let kw = self.i32_const(1700 + jj);
                        let z = self.i32_const(0);
                        let wid = self.select(Type::I32, z, w, c);
                        self.emit_guard_census_dyn_id(kw, wid);
                    }
                    cond = and_into(self, cond, c);
                }
                if tgt.cls_shallow || tgt.cls_slots {
                    let w = self.load_i32(ptr, OBJ_CLASS_IDX_OFFSET);
                    self.eff(w, Eff::ReadBits(HeapKind::ClassWord));
                    let mut m_bits = 0;
                    if tgt.cls_shallow {
                        m_bits |= CLASS_WORD_SHALLOW;
                    }
                    if tgt.cls_slots {
                        m_bits |= CLASS_WORD_SLOTS;
                    }
                    let m = self.i32_const(m_bits);
                    let t = self.binop(Operator::I32And, w, m, Type::I32);
                    let c = self.binop(Operator::I32Eq, t, m, Type::I32);
                    if self.guard_census_on() {
                        let jj = u32::try_from(j).unwrap();
                        let kf = self.i32_const(1600 + 2 * jj);
                        let kp = self.i32_const(1600 + 2 * jj + 1);
                        let kv = self.select(Type::I32, kp, kf, c);
                        self.emit_guard_census_dyn(kv, self.cur_pc);
                    }
                    cond = and_into(self, cond, c);
                }
            }
            let c = cond.expect("cls_checks nonempty");
            self.body.set_terminator(
                p2,
                Terminator::CondBr {
                    cond: c,
                    if_true: BlockTarget {
                        block: succ_blk,
                        args: vec![],
                    },
                    if_false: bail.clone(),
                },
            );
        }
        // Success: build the Opt header's params in its layout (stack,
        // carried locals), post-guard conversions licensed.
        self.cur = succ_blk;
        self.emit_guard_census(k_ok, self.cur_pc);
        let mut args: Vec<Value> = Vec::with_capacity(usize::from(depth) + carried.len());
        for i in 0..usize::from(depth) {
            let o = self.stack[i].clone();
            let r = Self::slot_repr(&opt_ctx.stack_slot(i));
            args.push(self.convert_to_repr(&o, r));
        }
        for &l in &carried {
            let r = Self::slot_repr(&Self::carried_slot(opt_ctx, l));
            let o = self.carried_operand_for_edge(tgt_seg, l);
            args.push(self.convert_to_repr(&o, r));
        }
        // The proof edge keeps the invocation's accumulated flags (a
        // recovery is not a cleanse -- recorded effects stay recorded).
        if let Some(f) = self.flags_edge_arg() {
            args.push(f);
        }
        self.ensure_version_block(opt, tgt_seg);
        if self.mode == EmitMode::Code {
            assert_eq!(
                self.block_params[&opt].len(),
                args.len(),
                "conform arg/param mismatch at pc {}",
                self.vers.ver(opt).pc
            );
        }
        let opt_blk = self.blocks[&opt];
        self.body.set_terminator(
            succ_blk,
            Terminator::Br {
                target: BlockTarget {
                    block: opt_blk,
                    args,
                },
            },
        );
        self.cur = saved_cur;
        BlockTarget {
            block: entry,
            args: vec![],
        }
    }

    /// A continuation whose facts are stripped and whose track is forced --
    /// the exception/finally landings, which are off every happy path by
    /// definition, and a slow path carries no facts. Routing them through the
    /// same seam as everything else is what keeps their landing block's
    /// param layout in step with `run_version`: the version they enter is
    /// joined with an all-TOP arrival, so it holds no facts and every param
    /// is boxed.
    pub(super) fn cont_stripped(&mut self, succ_pc: Pc, depth: usize) -> BlockTarget {
        let boxed: Vec<Operand> = (0..depth)
            .map(|i| {
                let o = self.stack[i].clone();
                let b = self.to_boxed(&o);
                Operand::plain(b, Repr::Boxed, bottom_ty())
            })
            .collect();
        self.flush_stale_locals(&[]);
        // Every slot is written now, and the carriers are dropped below:
        // a key left in the set would meet no SSA value at the landing's
        // own seam.
        self.frame_stale.clear();
        let empty = Ctx::default();
        self.flush_outer_dropped(None, &empty);
        let saved_stack = std::mem::replace(&mut self.stack, boxed);
        let saved_locals = std::mem::take(&mut self.locals_ctx);
        let saved_args = std::mem::take(&mut self.args_ctx);
        let saved_cl = std::mem::take(&mut self.caller_locals_ctx);
        let saved_ca = std::mem::take(&mut self.caller_args_ctx);
        let saved_outer = std::mem::take(&mut self.outer_ctx);
        let saved_ssa = std::mem::replace(&mut self.locals_ssa, vec![None; self.nlocals as usize]);
        let saved_track = self.cur_track;
        self.cur_track = Track::Dirty;
        let t = self.cont(succ_pc);
        self.cur_track = saved_track;
        self.stack = saved_stack;
        self.locals_ctx = saved_locals;
        self.args_ctx = saved_args;
        self.caller_locals_ctx = saved_cl;
        self.caller_args_ctx = saved_ca;
        self.outer_ctx = saved_outer;
        self.locals_ssa = saved_ssa;
        t
    }

    /// The copied lowerings call this where translate.rs called `edge_to`.
    pub(super) fn edge_to(&mut self, pc: Pc) -> BlockTarget {
        self.cont(pc)
    }

    /// A DIRTY-arm continuation edge: an IC-miss or slow-helper arm that ran
    /// a may-GC call and is handing the successor pc a claim-free result.
    ///
    /// It steps the track itself, because a call does not, and this edge
    /// must: it delivers an untyped value, and with one prediction per
    /// program point one untyped Opt arrival would degrade every lineage
    /// through that point. A non-conforming execution belongs on GEN, and
    /// this is one.
    ///
    /// The step is scoped to the edge: several callers emit this arm and
    /// then carry on with the main line, which never ran the call.
    pub(super) fn dirty_edge_to(&mut self, pc: Pc) -> BlockTarget {
        let saved = self.cur_track;
        self.cur_track = Track::Dirty;
        let t = self.cont(pc);
        self.cur_track = saved;
        t
    }

    // --- driver ----------------------------------------------------------

    /// The entry claims this body hoists: (arg ctx slot, pass-arm shape)
    /// for `this` (slot 0) and every formal (slot 1 + i) with a guardable
    /// likelier claim. The this claim is validated on the RAW frame slot,
    /// pre-FunctionThis-boxing: the analysis's This cell is fed by call
    /// sites' receivers, so a script whose claim is Obj sees object
    /// receivers arrive raw (a bare non-strict call's undefined would have
    /// widened the cell and killed the claim). Mapped-args frames alias
    /// the FORMAL slots through the arguments object, so those carry no
    /// claims -- but `this` is not aliased by it and its claim stands
    /// (raytrace's hottest bodies open with `Arguments`). The gen ladder
    /// carries no facts at all.
    pub(super) fn entry_claims(&self) -> Vec<(u32, ClaimShape)> {
        if self.gen_only || self.is_global {
            return Vec::new();
        }
        let mut out = Vec::new();
        if let Some(&m) = self
            .ctx
            .facts
            .arg_types
            .get(&(self.source_id, ArgIndex::THIS))
        {
            if let Some(s) = claim_shape(m) {
                out.push((0, s));
            }
        }
        if self.script.has_mapped_args {
            return out;
        }
        for i in 0..u32::from(self.script.nargs) {
            if let Some(&m) = self
                .ctx
                .facts
                .arg_types
                .get(&(self.source_id, ArgIndex::formal(i)))
            {
                if let Some(s) = claim_shape(m) {
                    out.push((1 + i, s));
                }
            }
        }
        // Piggyback rule: in an unmapped frame the this claim rides an
        // EXISTING validation (formal claims present) for one marginal tag
        // test; a this-only claim set would mint a brand-new three-way
        // entry whose per-invocation validation cost is not repaid by
        // facts on tiny, very hot bodies with many generic-caller calls (a
        // variant that seeded no facts at all regresses identically, so it
        // is pure validation tax there). Mapped frames keep their
        // this-only claims: they
        // have no formal claims to ride ever, their SEL proof covers the
        // resolved sites (raytrace recovered on exactly that), and their
        // bodies are not the tiny-call population.
        if out.len() == 1 && out[0].0 == 0 && !self.script.has_mapped_args {
            out.clear();
        }
        out
    }

    /// Whether this call site's argument operands statically imply every
    /// entry claim of resolved callee `sid` -- the typed-entry proof. The
    /// callee seeds `claim_slot_ctx`, i.e. the guard's pass-arm fact, so
    /// implication is checked against that, not the raw claim mask: a
    /// proven double under an int32-bearing claim must not pass. Double
    /// claims are never statically provable at all -- canonical boxing
    /// re-tags integral doubles as int32 in the frame, so only the
    /// callee's own tag test can prove the double TAG the interior's bare
    /// reinterpret relies on. Type is the authority (not repr): `to_boxed`
    /// of an exact-int32-typed or object-only-typed operand always yields
    /// that tag.
    pub(super) fn callee_entry_proven(&self, sid: u32, argc: u16, need: usize) -> bool {
        if self.gen_only {
            return false;
        }
        let SourceObject::Script(callee) = self.source.object(SourceObjectId::new(sid)) else {
            return false;
        };
        let len = self.stack.len();
        let mut any = false;
        let prove = |o: &Operand, shape: ClaimShape| match shape {
            ClaimShape::Obj => is_object_only(&o.ty),
            ClaimShape::Int32 => o.ty.prims == PRIM_INT32 && !o.ty.outside,
            ClaimShape::Double => false,
            // Any proven-numeric actual implies the number tag: an
            // exact int32 is number-tagged, and a proven double boxes
            // to a number tag either way (canonical re-tagging keeps
            // it in the admitted pair).
            ClaimShape::Number => is_numeric(&o.ty),
            ClaimShape::Str => is_string_only(&o.ty),
            ClaimShape::Bool => is_exact_bool(&o.ty),
            ClaimShape::Sym => is_symbol_only(&o.ty),
            ClaimShape::Ta(k) => is_object_only(&o.ty) && o.ta == Some(k),
        };
        let this_claim = self
            .ctx
            .facts
            .arg_types
            .get(&(ScriptId::new(sid), ArgIndex::THIS))
            .copied()
            .and_then(claim_shape);
        // Mirror `entry_claims`' piggyback rule: an unmapped callee whose
        // only guardable claim is `this` claims nothing, so there is
        // nothing to prove and no SEL to earn.
        if let Some(shape) = this_claim {
            let has_formal_claim = callee.has_mapped_args
                || (0..u32::from(callee.nargs)).any(|i| {
                    self.ctx
                        .facts
                        .arg_types
                        .get(&(ScriptId::new(sid), ArgIndex::formal(i)))
                        .copied()
                        .and_then(claim_shape)
                        .is_some()
                });
            if has_formal_claim {
                if need < 2 || !prove(&self.stack[len - need + 1], shape) {
                    return false;
                }
                any = true;
            }
        }
        // Mirror `entry_claims` exactly: a mapped-args callee claims only
        // `this`, so the proof set stops here (its arg_types formal rows
        // exist but are not validated by the body -- proving them would
        // mean skipping a validation the body never runs, which is fine,
        // but requiring them would drop the SEL bit the this proof earns).
        if callee.has_mapped_args {
            return any;
        }
        for i in 0..u32::from(callee.nargs) {
            let Some(&m) = self
                .ctx
                .facts
                .arg_types
                .get(&(ScriptId::new(sid), ArgIndex::formal(i)))
            else {
                continue;
            };
            let Some(shape) = claim_shape(m) else {
                continue;
            };
            if i >= u32::from(argc) {
                return false;
            }
            let o = &self.stack[len - need + 2 + i as usize];
            if !prove(o, shape) {
                return false;
            }
            any = true;
        }
        any
    }

    pub(super) fn emit(&mut self) -> Result<(), String> {
        let entry = self.body.entry;
        self.cur = entry;
        // The typed-entry selector rides the argc param's top bit; every
        // body strips it before argc is used (a body without entry claims
        // just ignores it, which keeps a stale caller-side proof safe).
        let raw_argc = self.argc;
        let sel_c = self.i32_const(ARGC_SEL_BIT);
        let sel = self.binop(Operator::I32And, raw_argc, sel_c, Type::I32);
        let mask_c = self.i32_const(!ARGC_SEL_BIT);
        self.argc = self.binop(Operator::I32And, raw_argc, mask_c, Type::I32);
        // vp rebase for a `uses_arguments` body.
        if self.needs_args_obj {
            let eight = self.i32_const(8);
            let argc_bytes = self.binop(Operator::I32Mul, self.argc, eight, Type::I32);
            let nargs_bytes = self.i32_const(8 * u32::from(self.script.nargs));
            let diff = self.binop(Operator::I32Sub, argc_bytes, nargs_bytes, Type::I32);
            let over = self.binop(Operator::I32GtU, argc_bytes, nargs_bytes, Type::I32);
            let zero = self.i32_const(0);
            let extra = self.select(Type::I32, diff, zero, over);
            self.vp = self.binop(Operator::I32Add, self.sp, extra, Type::I32);
        }
        // The prologue lives in a synthetic entry block outside the version
        // table (so a branch back to pc 0 can never re-run it), then edges
        // to the (0, GEN) version.
        self.cur_pc = Pc::new(0);
        self.cur_tokens = Vec::new();
        self.cur_track = Track::Opt;
        // A generator's physical entry forks fresh-vs-resume before the
        // prologue, which a resume must not run (generator.rs).
        if self.is_generator {
            self.emit_gen_entry_fork();
        }
        self.emit_frame_prologue();
        // Stamping-ctor activation guard: clear a foreign stamped `this`'s
        // conform flags up front (licenses ctor_init_claim's Some(0) arm).
        self.emit_stamp_ctor_foreign_this_guard();
        // Typed entry: the per-formal
        // claim guards are hoisted from GetArg sites into one entry
        // validation, so the Opt interior's derived ctx holds every claim
        // as proven and no GetArg on the Opt track re-guards. Three edges
        // into pc 0: sel != 0 (a resolved caller proved the claims
        // statically -- no tests at all), validation pass (generic caller,
        // one tag test per claimed formal), validation fail (the whole
        // invocation rides the Side lineage, as a per-read guard miss
        // did). Both proving edges seed the same pass-arm facts, so the
        // entry version's join keeps them.
        // Advisory per-formal value class (the lazy tier): rides the
        // entry ctx UNGUARDED on every entry edge; the first use that
        // needs the identity emits the guard (`layout_site_for`'s
        // advisory tier). Mapped-args frames skip formals, mirroring
        // `entry_claims`.
        if !self.gen_only && !self.script.has_mapped_args {
            for i in 1..self.args_ctx.len() {
                let key = (
                    self.source_id,
                    crate::ids::ArgIndex::new(u32::try_from(i).unwrap()),
                );
                if let Some(&(lo, hi)) = self.ctx.facts.arg_cls.get(&key) {
                    if let (Ok(lo), Ok(hi)) = (u16::try_from(lo.get()), u16::try_from(hi.get())) {
                        let c = &mut self.args_ctx[i];
                        if c.cls.is_none() && c.likely_cls.is_none() {
                            c.likely_cls = Some((lo, hi));
                        }
                    }
                }
            }
        }
        let claims = if self.cur_track == Track::Opt {
            self.entry_claims()
        } else {
            Vec::new()
        };
        if claims.is_empty() {
            let target = self.cont(Pc::new(0));
            self.body
                .set_terminator(self.cur, Terminator::Br { target });
        } else {
            if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
                let desc: Vec<String> = claims
                    .iter()
                    .map(|&(k, s)| {
                        if k == 0 {
                            format!("this:{s:?}")
                        } else {
                            format!("arg{}:{:?}", k - 1, s)
                        }
                    })
                    .collect();
                crate::diag_line!(
                    "night: bbv typed-entry sid#{} claims {} [{}]",
                    self.source_id,
                    claims.len(),
                    desc.join(" ")
                );
            }
            let typed_blk = self.body.add_block();
            let val_blk = self.body.add_block();
            let zero = self.i32_const(0);
            let has_sel = self.binop(Operator::I32Ne, sel, zero, Type::I32);
            self.cond_br(has_sel, typed_blk, val_blk);
            let saved_args = self.args_ctx.clone();
            self.cur = typed_blk;
            for &(k, s) in &claims {
                self.args_ctx[k as usize] = claim_slot_ctx(s).with_prov(Prov::C_ENTRY);
            }
            let target = self.cont(Pc::new(0));
            self.body
                .set_terminator(self.cur, Terminator::Br { target });
            self.args_ctx = saved_args.clone();
            self.cur = val_blk;
            let fail_blk = self.body.add_block();
            for &(k, s) in &claims {
                let v = self.load_i64(self.sp, 8 + 8 * k);
                let ok = match s {
                    ClaimShape::Obj => self.tag_eq(v, TAG_OBJECT as u32),
                    ClaimShape::Int32 => self.tag_eq(v, TAG_INT32 as u32),
                    ClaimShape::Double => self.is_double_tag(v),
                    ClaimShape::Number => self.is_number_tag(v),
                    ClaimShape::Str => self.tag_eq(v, TAG_STRING as u32),
                    ClaimShape::Bool => self.tag_eq(v, TAG_BOOLEAN as u32),
                    ClaimShape::Sym => self.tag_eq(v, TAG_SYMBOL as u32),
                    ClaimShape::Ta(kind) => {
                        // The clasp loads dereference the payload, so the
                        // tag test branches first.
                        let is_obj = self.tag_eq(v, TAG_OBJECT as u32);
                        let obj_blk = self.body.add_block();
                        self.cond_br(is_obj, obj_blk, fail_blk);
                        self.cur = obj_blk;
                        let objptr = self.unop(Operator::I32WrapI64, v, Type::I32);
                        self.ta_clasp_eq(objptr, kind)
                    }
                };
                let next = self.body.add_block();
                self.cond_br(ok, next, fail_blk);
                self.cur = next;
            }
            for &(k, s) in &claims {
                self.args_ctx[k as usize] = claim_slot_ctx(s).with_prov(Prov::C_ENTRY);
            }
            let target = self.cont(Pc::new(0));
            self.body
                .set_terminator(self.cur, Terminator::Br { target });
            self.args_ctx = saved_args;
            self.cur = fail_blk;
            // Validation-fail census (kind 47, DIRTYTRACE-selected script
            // only): one ping per claimed formal carrying (formal << 4 |
            // arriving tag class: 1 int32, 2 double, 3 object, 0 other) --
            // the whichformal-which-tag histogram the Side-entry diagnosis
            // needs (a claim whose arriving class differs from its shape is
            // the guard that fails).
            let saved_track = self.cur_track;
            self.cur_track = self.cur_track.step(Track::Side);
            let target = self.cont(Pc::new(0));
            self.body
                .set_terminator(self.cur, Terminator::Br { target });
            self.cur_track = saved_track;
        }
        while let Some(key) = self.workqueue.pop() {
            if !self.processed.insert(key) {
                continue;
            }
            // Overflow early-abort: past the cap this pass is doomed to a
            // ladder retry -- stop emitting instead of running the queue
            // dry (the caller's values-len check routes the retry).
            if self.value_count() > MAX_BODY_VALUES {
                return Ok(());
            }
            self.run_version(key)?;
            if self.depth_overflow {
                return Err("bbv: operand stack too deep to key a version".to_string());
            }
        }
        // Every landing version exists now, so the dispatcher can be built.
        self.finalize_gen_dispatch();
        Ok(())
    }

    /// Emit one version: One op for one (pc, ctx) -- the pure BBV
    /// discipline. Every successor (the fall-through included) routes
    /// through the memo table, so all tails are shared and code is bounded
    /// by O(|ops| x |ctxs-per-pc|). The operand stack and locals facts seed
    /// from the version's ctx in their ctx-typed reprs.
    pub(super) fn run_version(&mut self, key: VerId) -> Result<(), String> {
        let vv_base = if self.mode == EmitMode::ContextOnly {
            let prev = self.ver_values.get(&key).copied().unwrap_or(0);
            self.virtual_values -= prev;
            Some(self.virtual_values)
        } else {
            None
        };
        let r = self.run_version_inner(key);
        if let Some(base) = vv_base {
            let spent = self.virtual_values - base;
            self.ver_values.insert(key, spent);
        }
        r
    }

    fn run_version_inner(&mut self, key: VerId) -> Result<(), String> {
        let pc = self.vers.ver(key).pc;
        self.cur_ver = key;
        self.cur = self.blocks[&key];
        if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
            crate::diag_line!(
                "night: RUNV sid#{} v{} pc {} track {:?}",
                self.source_id,
                key.0,
                pc,
                self.vers.ctx(key).track
            );
        }
        // Census kinds 1/2/3: a version entry executed, by track. This is
        // the dynamic answer to "how much execution is on Opt", which the
        // static per-pc counts cannot give.
        {
            let kind = match self.vers.ctx(key).track {
                Track::Opt => 1,
                Track::Side => 2,
                Track::Dirty => 3,
            };
            let sid = self.root_source_id;
            self.emit_census(kind, sid, pc);
        }
        let seg = self.seg_of(pc);
        self.enter_frame_view(seg);
        let ctx = self.vers.ctx(key).clone();
        self.cur_tokens = ctx.tokens.clone();
        self.cur_track = ctx.track;
        self.locals_ctx = (0..self.nlocals as usize).map(|i| ctx.local(i)).collect();
        self.args_ctx = (0..1 + self.nformals as usize)
            .map(|i| ctx.arg(i))
            .collect();
        self.caller_locals_ctx = ctx.caller_locals.clone();
        self.caller_args_ctx = ctx.caller_args.clone();
        self.outer_ctx = ctx.outer.clone();
        self.gcells_ctx = ctx.gcells.clone();
        // Formal-arg types at the root entry, Opt track (the likely lane):
        // this is slot 0, arg i is slot 1 + i.
        if self.opts.diagnostics.viz
            && self.mode == EmitMode::Code
            && ctx.track == Track::Opt
            && pc == Pc::new(0)
            && seg.is_none()
        {
            for (i, a) in self.args_ctx.iter().enumerate() {
                if Self::viz_slot_interesting(a) {
                    crate::diag_line!(
                        "night: viz argty sid#{} i {} ty {}",
                        self.root_source_id,
                        i,
                        Self::viz_slot_str(a),
                    );
                }
            }
        }
        // The track carries prior dirtiness across versions; these cover
        // this version's emission only.
        self.post_call = false;
        self.ret_onramp_pc = None;
        if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
            let carried_here = self.carried_for(seg, &ctx);
            let non_top = (0..self.nlocals as usize)
                .filter(|&i| ctx.local(i) != SlotCtx::TOP)
                .count();
            let depth = usize::from(self.vers.ver(key).depth);
            let stk_non_top = (0..depth)
                .filter(|&i| ctx.stack_slot(i) != SlotCtx::TOP)
                .count();
            let arg_non_top = (0..1 + usize::from(self.nformals))
                .filter(|&i| ctx.arg(i) != SlotCtx::TOP)
                .count();
            crate::diag_line!(
                "night: bbv version sid#{} pc {pc} track {:?} carried {} non-top {}/{} stk {}/{} arg {}/{} depth {}",
                self.source_id,
                ctx.track,
                carried_here.len(),
                non_top,
                self.nlocals,
                stk_non_top,
                depth,
                arg_non_top,
                1 + usize::from(self.nformals),
                depth,
            );
            // The carried KEYS, so two builds can be diffed by key: `l<n>`
            // a local, `a<n>` a formal (`STALE_ARG`), `o<n>` the parent's
            // local riding through a splice (`OUTER_LOCAL`).
            let keys: Vec<String> = carried_here
                .iter()
                .map(|&k| {
                    if k & OUTER_LOCAL != 0 {
                        format!("o{}", k & !OUTER_LOCAL)
                    } else if k & STALE_ARG != 0 {
                        format!("a{}", k & !STALE_ARG)
                    } else {
                        format!("l{k}")
                    }
                })
                .collect();
            crate::diag_line!(
                "night: bbv carried sid#{} pc {pc} track {:?} keys {}",
                self.source_id,
                ctx.track,
                keys.join(","),
            );
        }
        // Locals-into-SSA: the param vector is [stack..., carried locals...]
        // with the carried set derived from the version's own ctx.
        self.ssa_seg = seg;
        self.locals_ssa = vec![None; self.nlocals as usize];
        self.args_ssa = vec![None; 1 + usize::from(self.nformals)];
        let carried = self.carried_for(seg, &ctx);
        let depth = usize::from(self.vers.ver(key).depth);
        let params = self.block_params.get(&key).cloned().unwrap_or_default();
        let flags_params = usize::from(self.flags_threading());
        debug_assert!(
            self.mode == EmitMode::ContextOnly
                || params.len() == depth + carried.len() + flags_params,
            "param layout disagrees with the version identity"
        );
        self.cur_flags = if self.flags_threading() {
            params
                .last()
                .copied()
                .map_or(FlagsAcc::Const(0), |v| FlagsAcc::Dyn(v, 0))
        } else {
            FlagsAcc::Const(0)
        };
        // DIRTYTRACE companion (kind 43): the arriving accumulator word per
        // version entry, id = pc<<2 | (word & 3) -- the per-pc word
        // bisector for a saturating acc chain.
        self.stack = (0..depth)
            .map(|i| {
                let val = params.get(i).copied().unwrap_or_else(Value::invalid);
                let slot = ctx.stack_slot(i);
                let r = Self::slot_repr(&slot);
                // The class fact rides the edge (`Operand::slot` writes it
                // into the ctx, and it is part of the version key), so it
                // must be read back here. Dropping it made every stack
                // operand's proven class die at the next op -- which in
                // per-op BBV is immediately -- so the fact was being paid
                // for in ctx cardinality and never consumed.
                Operand {
                    cls: slot.cls,
                    cls_shallow: slot.cls_shallow,
                    cls_slots: slot.cls_slots,
                    ta: slot.ta,
                    // The provenance rides the edge too: without it every
                    // guard in this version would have nothing to attribute
                    // its proof to (see `SlotCtx::src`).
                    src: slot.src,
                    // The interval fact rides the edge like `cls` does.
                    iv: slot.iv.map(|r| (r.lo, r.hi, false)),
                    prov: slot.prov,
                    ..Operand::ranged(val, r, slot.to_ty(), slot.range)
                }
            })
            .collect();
        self.frame_stale.clear();
        let parent_nlocals = match seg.and_then(|i| self.segs[i].parent) {
            Some(p) => max_locals(self.segs[p].script) as usize,
            None if seg.is_some() => self.root_nlocals as usize,
            None => 0,
        };
        self.outer_ssa = vec![None; parent_nlocals];
        for (j, &l) in carried.iter().enumerate() {
            let slot = Self::carried_slot(&ctx, l);
            let val = params
                .get(depth + j)
                .copied()
                .unwrap_or_else(Value::invalid);
            let r = Self::slot_repr(&slot);
            if l & STALE_ARG != 0 {
                if let Some(c) = self.args_ssa.get_mut((l & !STALE_ARG) as usize) {
                    *c = Some((val, r));
                }
            } else if l & OUTER_LOCAL != 0 {
                if let Some(c) = self.outer_ssa.get_mut((l & !OUTER_LOCAL) as usize) {
                    *c = Self::raw_repr(r).then_some((val, r));
                }
                continue;
            } else {
                self.locals_ssa[l as usize] = Some((val, r));
            }
            // Freshness is not in the version identity: a carried raw
            // local (or formal) may have arrived with its frame slot behind.
            if !self.gen_only && matches!(r, Repr::I32 | Repr::F64 | Repr::Bool | Repr::I64) {
                self.frame_stale.insert(l);
            }
        }
        let seg_base = seg.map(|i| self.segs[i].base).unwrap_or(0);
        let local_pc = pc - seg_base;
        let mut p = self.script.parser();
        if local_pc > Pc::new(0) {
            p.advance(usize::try_from(local_pc.get()).unwrap());
        }
        let before = p.remaining();
        let Some(op) = p.next_op() else {
            self.emit_ret_rval();
            return Ok(());
        };
        self.cur_pc = pc;
        if self.opts.diagnostics.viz && self.mode == EmitMode::Code {
            let v = self.vers.ver(key);
            let mut facts: Vec<String> = Vec::new();
            for i in 0..1 + usize::from(self.nformals) {
                let s = ctx.arg(i);
                if Self::viz_slot_interesting(&s) {
                    let nm = if i == 0 {
                        "this".to_string()
                    } else {
                        format!("a{}", i - 1)
                    };
                    facts.push(format!("{nm}={}", Self::viz_slot_str(&s)));
                }
            }
            for i in 0..self.nlocals as usize {
                let s = ctx.local(i);
                if Self::viz_slot_interesting(&s) {
                    facts.push(format!("l{i}={}", Self::viz_slot_str(&s)));
                }
            }
            for i in 0..usize::from(v.depth) {
                let s = ctx.stack_slot(i);
                if Self::viz_slot_interesting(&s) {
                    facts.push(format!("s{i}={}", Self::viz_slot_str(&s)));
                }
            }
            let carried_here = self.carried_for(seg, &ctx);
            let cs: Vec<String> = carried_here
                .iter()
                .map(|&l| format!("l{l}={:?}", Self::slot_repr(&ctx.local(l as usize))))
                .collect();
            let inline = if seg.is_some() {
                self.source_id.to_string()
            } else {
                "-".to_string()
            };
            crate::diag_line!(
                "night: viz ver sid#{} pc {pc} lpc {local_pc} inline {inline} site {} path {} op {op:?} args [{}] track {:?} class {} depth {} facts [{}] carried [{}]",
                self.root_source_id,
                self.viz_site(pc),
                self.viz_path(pc),
                viz_op_args(self.source, self.script, local_pc, op),
                ctx.track,
                v.class,
                v.depth,
                facts.join(" "),
                cs.join(" "),
            );
        }
        let blocks_before = self.body.blocks.len();
        let values_before = self.body.values.len();
        let lower_entry = (self.cur, self.body.blocks[self.cur].insts.len());
        let facts_before = (self.opts.diagnostics.ctxedge && self.mode == EmitMode::Code)
            .then(|| self.slot_fact_snapshot());
        self.viz_lpc = pc - seg_base;
        self.op_arm_blocks.clear();
        self.op_form = None;
        self.op_choke = None;
        self.emit_op(&mut p, pc, op)
            .map_err(|e| format!("{e} (at pc {pc}, op {op:?})"))?;
        self.emit_class_idx_local_restamp(pc);
        if self.opts.diagnostics.viz_lower && self.mode == EmitMode::Code {
            self.viz_dump_lowering(pc - seg_base, lower_entry, blocks_before);
        }
        if let Some(before) = facts_before {
            self.dump_ctx_delta(op, pc, &before);
        }
        if self.opts.diagnostics.redundant && self.mode == EmitMode::Code {
            self.red_ranges.push((
                pc,
                pc - seg_base,
                op,
                self.cur_track,
                u32::try_from(lower_entry.0.index()).unwrap(),
                u32::try_from(values_before).unwrap(),
                u32::try_from(self.body.values.len()).unwrap(),
            ));
        }
        if self.opts.diagnostics.opsize && self.mode == EmitMode::Code {
            self.dump_opsize(
                op,
                pc,
                pc - seg_base,
                lower_entry,
                blocks_before,
                seg.is_some(),
            );
        }
        if self.opts.instrument.blocks && self.mode == EmitMode::Code {
            self.block_census(
                op,
                pc,
                pc - seg_base,
                lower_entry,
                blocks_before,
                seg.is_some(),
            );
        }
        // Per-op result type on the Opt track (the likely-executed lane):
        // the def the op just pushed, as the ctx sees it. One line per Opt
        // version reaching the op; the viz joins distinct claims.
        if self.opts.diagnostics.viz
            && self.mode == EmitMode::Code
            && self.cur_track == Track::Opt
            && op.ndefs() > 0
        {
            if let Some(top) = self.stack.last() {
                crate::diag_line!(
                    "night: viz def sid#{} lpc {} path {} ty {}",
                    self.root_source_id,
                    pc - seg_base,
                    self.viz_path(pc),
                    Self::viz_slot_str(&top.slot()),
                );
            }
        }
        if self.body.blocks[self.cur].terminator == Terminator::None {
            let next_pc = pc + u32::try_from(before - p.remaining()).unwrap();
            let limit = seg
                .map(|i| self.segs[i].end)
                .unwrap_or(u32::try_from(self.script.bytecode.len()).unwrap());
            if next_pc < Pc::new(limit) {
                let target = self.cont(next_pc);
                self.body
                    .set_terminator(self.cur, Terminator::Br { target });
            } else {
                self.emit_ret_rval();
            }
        }
        Ok(())
    }
}
