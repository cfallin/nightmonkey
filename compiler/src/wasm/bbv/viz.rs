/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Diagnostic dumps: version, lowering and script views behind the
//! `NIGHT_VIZ` diagnostics.

use super::*;
use crate::source::ObjectData;

impl<'a> Bbv<'a> {
    /// Whether a slot claims anything worth showing (provenance alone is
    /// not a fact).
    pub(super) fn viz_slot_interesting(s: &SlotCtx) -> bool {
        s.prims != ALL_PRIMS
            || !s.outside
            || s.range != RangeBucket::Top
            || s.cls.is_some()
            || s.iv.is_some()
    }

    /// Compact viz description of one ctx slot fact.
    pub(super) fn viz_slot_str(s: &SlotCtx) -> String {
        let mut parts: Vec<&str> = s.prims.viz_parts();
        if s.outside {
            parts.push("obj");
        }
        let mut out = if parts.is_empty() {
            "none".to_string()
        } else {
            parts.join("|")
        };
        if s.range != RangeBucket::Top {
            out.push_str(&format!(":{:?}", s.range));
        }
        if let Some(k) = s.ta {
            out.push_str(&format!(":ta{:?}", k));
        }
        if let Some((lo, hi)) = s.cls {
            if lo == hi {
                out.push_str(&format!(":cls{lo}"));
            } else {
                out.push_str(&format!(":cls{lo}-{hi}"));
            }
            if s.cls_shallow {
                out.push('!');
            }
        }
        if let Some(r) = s.iv {
            out.push_str(&format!(":iv[{},{}]", r.lo, r.hi));
        }
        out
    }

    /// `viz_slot_str` plus the fact's provenance bits (`~p<hex>`), for the
    /// ctxedge/ctxdelta dumps only -- the version viz stays provenance-free.
    pub(super) fn viz_slot_prov_str(s: &SlotCtx) -> String {
        let mut out = Self::viz_slot_str(s);
        if s.prov.0 != 0 {
            out.push_str(&format!("~p{:x}", s.prov.0));
        }
        out
    }

    /// The root-pc call site a (possibly synthetic) pc belongs to, or "-".
    pub(super) fn viz_site(&self, pc: Pc) -> String {
        self.seg_sites(pc)
            .last()
            .map_or_else(|| "-".to_string(), |s| s.to_string())
    }

    /// Root-first splice path of a synthetic pc: each element is the call
    /// op's local pc within its owning frame (root pc first, then the call
    /// pc inside each successive callee). "-" outside any segment.
    pub(super) fn viz_path(&self, pc: Pc) -> String {
        let sites = self.seg_sites(pc);
        if sites.is_empty() {
            return "-".to_string();
        }
        sites
            .iter()
            .rev()
            .map(|&s| match self.seg_of(Pc::new(s)) {
                None => s.to_string(),
                Some(j) => (s - self.segs[j].base).to_string(),
            })
            .collect::<Vec<_>>()
            .join("/")
    }

    /// One instruction's role in a lowering, for the viz. The categories
    /// are the ones a reader of a lowering actually asks about: where the
    /// guards are, where values get boxed or unboxed, what memory is
    /// touched (by heap kind, which is the alias story), and which helper
    /// runs. Everything else is arithmetic and is only counted.
    pub(super) fn viz_inst(&self, v: Value) -> Option<(&'static str, String)> {
        let ValueDef::Operator(op, _, _) = &self.body.values[v] else {
            return None;
        };
        let eff = self.effects.get(&v);
        let kind_of_eff = || match eff {
            Some(Eff::Read(k)) => format!("{k:?}"),
            Some(Eff::ReadBits(k)) => format!("{k:?}/bits"),
            Some(Eff::Write(k)) => format!("{k:?}"),
            _ => "-".to_string(),
        };
        let name = format!("{op:?}");
        let head = name.split_whitespace().next().unwrap_or(&name).to_string();
        let cat = if head.starts_with("Call") {
            return Some(("call", name));
        } else if head.contains("Store") {
            return Some(("store", format!("{head} {}", kind_of_eff())));
        } else if head.contains("Load") {
            return Some(("load", format!("{head} {}", kind_of_eff())));
        } else if head == "I32WrapI64" {
            "unbox"
        } else if head == "I64ExtendI32U" || head == "I64ExtendI32S" {
            "box"
        } else if head == "F64ReinterpretI64" || head == "I64ReinterpretF64" {
            "reinterp"
        } else if head.starts_with("F64Convert") || head.starts_with("I32Trunc") {
            "cvt"
        } else if head.ends_with("Const") {
            return None;
        } else {
            "alu"
        };
        Some((cat, head))
    }

    /// A branch condition, described the way a reader wants it: the
    /// comparison and, when it is against an immediate, that immediate --
    /// which is what makes a guard legible (a tag word, a stamp word, a
    /// class idx) rather than an anonymous compare.
    pub(super) fn viz_cond(&self, v: Value) -> String {
        let ValueDef::Operator(op, args, _) = &self.body.values[v] else {
            // A block param: the arms agreed on the condition upstream.
            return "param".to_string();
        };
        let head = format!("{op:?}");
        let head = head.split_whitespace().next().unwrap_or("?").to_string();
        // Only a comparison's immediate is meaningful as a guard label --
        // it is the tag word, stamp word or class idx being tested. A
        // constant that happens to feed a call is not.
        let is_cmp = [
            "Eq", "Ne", "LtS", "LtU", "GtS", "GtU", "LeS", "LeU", "GeS", "GeU", "Lt", "Gt", "Le",
            "Ge", "Eqz",
        ]
        .iter()
        .any(|sfx| head.ends_with(sfx));
        if !is_cmp {
            return head;
        }
        let mut imm: Option<i64> = None;
        for &a in &self.body.arg_pool[*args] {
            if let ValueDef::Operator(o, _, _) = &self.body.values[a] {
                match o {
                    Operator::I32Const { value } => imm = Some(i64::from(*value as i32)),
                    Operator::I64Const { value } => imm = Some(*value as i64),
                    _ => {}
                }
            }
        }
        match imm {
            Some(i) => format!("{head}#{i}"),
            None => head,
        }
    }

    /// The instruction class of one lowered value, for the opsize census:
    /// 0 alu, 1 load, 2 store, 3 call, 4 box/unbox/reinterpret, 5 const,
    /// 6 anything that is not an operator.
    pub(super) fn opsize_class(&self, v: Value) -> usize {
        let ValueDef::Operator(op, _, _) = &self.body.values[v] else {
            return 6;
        };
        let name = format!("{op:?}");
        let head = name.split_whitespace().next().unwrap_or("");
        if head.starts_with("Call") {
            3
        } else if head.contains("Store") {
            2
        } else if head.contains("Load") {
            1
        } else if head.ends_with("Const") {
            5
        } else if matches!(
            head,
            "I32WrapI64"
                | "I64ExtendI32U"
                | "I64ExtendI32S"
                | "F64ReinterpretI64"
                | "I64ReinterpretF64"
        ) {
            4
        } else {
            0
        }
    }

    /// The durable-slot fact summary (args then locals), for the per-op kill
    /// delta. The operand stack is deliberately excluded: an op reshapes it
    /// by construction, so a stack slot that "lost" a fact is usually just a
    /// different value, not an invalidation.
    /// `--dump-peel`: per root loop header, the slots the body reads whose
    /// single-version join (`pred.at`) is strictly weaker than the join of
    /// the back edges alone (`pred.back_at`): what a peel version would
    /// keep in the steady state. Segment loops are skipped (their liveness
    /// is the callee's).
    pub(super) fn dump_peel(&self, source_id: ScriptId) {
        let root_len = u32::try_from(self.script.bytecode.len()).unwrap();
        let mut loops = self.loop_intervals.clone();
        loops.sort_unstable();
        loops.dedup();
        for (h, e) in loops {
            if h >= root_len {
                continue;
            }
            let hp = Pc::new(h);
            let (Some(j), Some(b)) = (self.vers.pred.at(hp), self.vers.pred.back_at(hp)) else {
                crate::diag_line!(
                    "night: peel sid#{source_id} header {h} end {e}: no Opt back edge"
                );
                continue;
            };
            let mut weaker: Vec<String> = Vec::new();
            let mut non_iv = 0u32;
            let mut read = 0u32;
            for (i, bs) in b.locals.iter().enumerate() {
                let i32i = u32::try_from(i).unwrap();
                if !self.live_root.local_live(h, i32i) {
                    continue;
                }
                read += 1;
                let js = j.locals.get(i).cloned().unwrap_or(SlotCtx::TOP);
                if !js.implies(bs) {
                    let iv_only = js.implies_sans_iv(bs);
                    if !iv_only {
                        non_iv += 1;
                    }
                    weaker.push(format!(
                        "l{i}{}: join {} back {}",
                        if iv_only { " [iv]" } else { "" },
                        Self::viz_slot_prov_str(&js),
                        Self::viz_slot_prov_str(bs)
                    ));
                }
            }
            for (i, bs) in b.args.iter().enumerate() {
                if i > 0 && !self.live_root.arg_live(h, u32::try_from(i - 1).unwrap()) {
                    continue;
                }
                read += 1;
                let js = j.args.get(i).cloned().unwrap_or(SlotCtx::TOP);
                if !js.implies(bs) {
                    let iv_only = js.implies_sans_iv(bs);
                    if !iv_only {
                        non_iv += 1;
                    }
                    let nm = if i == 0 {
                        "this".to_string()
                    } else {
                        format!("a{}", i - 1)
                    };
                    weaker.push(format!(
                        "{nm}{}: join {} back {}",
                        if iv_only { " [iv]" } else { "" },
                        Self::viz_slot_prov_str(&js),
                        Self::viz_slot_prov_str(bs)
                    ));
                }
            }
            for (i, bs) in b.stack.iter().enumerate() {
                read += 1;
                let js = j.stack.get(i).cloned().unwrap_or(SlotCtx::TOP);
                if !js.implies(bs) {
                    let iv_only = js.implies_sans_iv(bs);
                    if !iv_only {
                        non_iv += 1;
                    }
                    weaker.push(format!(
                        "s{i}{}: join {} back {}",
                        if iv_only { " [iv]" } else { "" },
                        Self::viz_slot_prov_str(&js),
                        Self::viz_slot_prov_str(bs)
                    ));
                }
            }
            crate::diag_line!(
                "night: peel sid#{source_id} header {h} end {e}: {} of {read} read slots weaker ({non_iv} beyond intervals){}{}",
                weaker.len(),
                if weaker.is_empty() { "" } else { " -- " },
                weaker.join("; ")
            );
        }
    }

    pub(super) fn slot_fact_snapshot(&self) -> Vec<(String, String)> {
        let mut out = Vec::new();
        for (i, s) in self.args_ctx.iter().enumerate() {
            if Self::viz_slot_interesting(s) {
                let nm = if i == 0 {
                    "a_this".to_string()
                } else {
                    format!("a{}", i - 1)
                };
                out.push((nm, Self::viz_slot_prov_str(s)));
            }
        }
        for (i, s) in self.locals_ctx.iter().enumerate() {
            if Self::viz_slot_interesting(s) {
                out.push((format!("l{i}"), Self::viz_slot_prov_str(s)));
            }
        }
        out
    }

    /// Per-op durable-slot fact delta (`--dump-ctxedge`): which durable
    /// slots this op's lowering changed, and to what.
    ///
    /// The record is a raw before/after delta in both directions -- an op
    /// that *proves* a class (`l2:obj->obj:cls6`) shows up next to one that
    /// kills it (`a0:obj:cls5->obj`) -- because deciding which direction is
    /// a loss needs a fact-strength order, and that belongs in
    /// `tools/ctxdiff.py` where it can be argued with rather than baked into
    /// the emitter.
    ///
    /// This is the origin instrument. The edge census says an arrival is
    /// weaker than its sibling, but by then the fact has usually been dead
    /// for many pcs -- 82.6% of edge-census losses are at pcs that emitted
    /// no call at all, i.e. they are carrying a loss, not causing it. This
    /// record fires only at the op that actually did the weakening, which is
    /// what a fix has to target.
    pub(super) fn dump_ctx_delta(
        &self,
        op: crate::bytecode::JSOp,
        pc: Pc,
        before: &[(String, String)],
    ) {
        let after = self.slot_fact_snapshot();
        let now: HashMap<&str, &str> = after
            .iter()
            .map(|(k, v)| (k.as_str(), v.as_str()))
            .collect();
        let mut delta: Vec<String> = Vec::new();
        for (k, was) in before {
            match now.get(k.as_str()) {
                None => delta.push(format!("{k}:{was}->gone")),
                Some(&is) if is != was.as_str() => delta.push(format!("{k}:{was}->{is}")),
                _ => {}
            }
        }
        // Slots that had no fact before and gained one are pure wins; they
        // are not in `before`, so they are not reported.
        if delta.is_empty() {
            return;
        }
        crate::diag_line!(
            "night: ctxdelta sid#{} pc {pc} op {op:?} track {:?} n {} delta [{}]",
            self.root_source_id,
            self.cur_track,
            delta.len(),
            delta.join(" "),
        );
    }

    /// Continuation-edge fact census (`--dump-ctxedge`). One record per
    /// continuation edge, naming the ctx it hands to `succ_pc`: which slots
    /// still carry a fact, and what the fact is.
    ///
    /// This is the instrument for the question the `dmerge` audit cannot
    /// answer -- `dmerge` sees a may-GC call merging back, but an arm that
    /// drops a `likelier` claim and rejoins without calling anything is
    /// invisible to it. Here every arrival at a pc is recorded, so the
    /// cross-arm diff (`tools/ctxdiff.py`) can say which slot lost which
    /// fact on which arm, and attribute it to the op that emitted the edge.
    ///
    /// Slots are named `a<n>` (args, `a0` = this), `l<n>` (locals) and
    /// `s<n>` (operand stack); only slots carrying something worth showing
    /// appear, by the same rule the version view uses. A record with no
    /// slots is an all-bottom arrival.
    pub(super) fn dump_ctx_edge(&self, succ_pc: Pc, ctx: &Ctx) {
        let mut facts: Vec<String> = Vec::new();
        for (i, s) in ctx.args.iter().enumerate() {
            if Self::viz_slot_interesting(s) {
                let nm = if i == 0 {
                    "a_this".to_string()
                } else {
                    format!("a{}", i - 1)
                };
                facts.push(format!("{nm}={}", Self::viz_slot_prov_str(s)));
            }
        }
        for (i, s) in ctx.locals.iter().enumerate() {
            if Self::viz_slot_interesting(s) {
                facts.push(format!("l{i}={}", Self::viz_slot_prov_str(s)));
            }
        }
        for (i, s) in ctx.stack.iter().enumerate() {
            if Self::viz_slot_interesting(s) {
                facts.push(format!("s{i}={}", Self::viz_slot_prov_str(s)));
            }
        }
        for (i, s) in ctx.caller_locals.iter().enumerate() {
            if Self::viz_slot_interesting(s) {
                facts.push(format!("cl{i}={}", Self::viz_slot_prov_str(s)));
            }
        }
        for (i, s) in ctx.caller_args.iter().enumerate() {
            if Self::viz_slot_interesting(s) {
                facts.push(format!("ca{i}={}", Self::viz_slot_prov_str(s)));
            }
        }
        crate::diag_line!(
            "night: ctxedge sid#{} pc {} op {} to {succ_pc} track {:?} \
nslots {} nfacts {} carried {} facts [{}]",
            self.root_source_id,
            self.cur_pc,
            self.cur_op
                .map_or_else(|| "-".to_string(), |o| format!("{o:?}")),
            ctx.track,
            ctx.args.len() + ctx.locals.len() + ctx.stack.len(),
            facts.len(),
            ctx.carried.len(),
            facts.join(" "),
        );
    }

    /// The MINT record (`--dump-ctxedge`): the arrival that FIRST reached a
    /// program point, and therefore set the ceiling for every later one --
    /// `Predictions::join_arrival` only ever weakens. A prediction that is
    /// weak because it was born weak needs a different fix from one that was
    /// eroded, and the rejoin audit cannot tell them apart (a mint's `pre`
    /// is all-TOP, so `dump_rejoin_loss` skips every slot).
    pub(super) fn dump_ctx_mint(&self, pc: Pc, ctx: &Ctx) {
        let mut facts: Vec<String> = Vec::new();
        for (i, s) in ctx.args.iter().enumerate() {
            if Self::viz_slot_interesting(s) {
                let nm = if i == 0 {
                    "a_this".to_string()
                } else {
                    format!("a{}", i - 1)
                };
                facts.push(format!("{nm}={}", Self::viz_slot_str(s)));
            }
        }
        for (i, s) in ctx.locals.iter().enumerate() {
            if Self::viz_slot_interesting(s) {
                facts.push(format!("l{i}={}", Self::viz_slot_str(s)));
            }
        }
        for (i, s) in ctx.stack.iter().enumerate() {
            if Self::viz_slot_interesting(s) {
                facts.push(format!("s{i}={}", Self::viz_slot_str(s)));
            }
        }
        crate::diag_line!(
            "night: ctxmint sid#{} at {pc} from pc {} op {} facts [{}]",
            self.source_id,
            self.cur_pc,
            self.cur_op
                .map_or_else(|| "-".to_string(), |o| format!("{o:?}")),
            facts.join(" "),
        );
    }

    /// Every prediction MOVE, with the slots that changed
    /// (`--dump-ctxedge`). `dump_rejoin_loss` reports only the moves that
    /// look like a loss under `SlotCtx::implies`, and its filter skips a
    /// pre-slot that is TOP; `ctxmint` reports only the first arrival. This
    /// is the unfiltered middle, so the life of a program point's
    /// prediction -- minted, moved N times, settled -- can be read end to
    /// end. Without it a prediction that ends weaker than every recorded
    /// step is untraceable.
    pub(super) fn dump_ctx_join(&self, pc: Pc, pre: &Ctx, post: &Ctx, arr: &Ctx) {
        let mut moved: Vec<String> = Vec::new();
        let mut diff = |tag: &str, a: &[SlotCtx], b: &[SlotCtx], c: &[SlotCtx]| {
            for i in 0..a.len().max(b.len()) {
                let (x, y) = (
                    a.get(i).copied().unwrap_or(SlotCtx::TOP),
                    b.get(i).copied().unwrap_or(SlotCtx::TOP),
                );
                if x == y {
                    continue;
                }
                let z = c.get(i).copied().unwrap_or(SlotCtx::TOP);
                moved.push(format!(
                    "{tag}{i}:{}->{} arr {}",
                    Self::viz_slot_str(&x),
                    Self::viz_slot_str(&y),
                    Self::viz_slot_str(&z)
                ));
            }
        };
        diff("a", &pre.args, &post.args, &arr.args);
        diff("l", &pre.locals, &post.locals, &arr.locals);
        diff("s", &pre.stack, &post.stack, &arr.stack);
        if moved.is_empty() {
            return;
        }
        crate::diag_line!(
            "night: ctxjoin sid#{} at {pc} from pc {} op {} moved [{}]",
            self.source_id,
            self.cur_pc,
            self.cur_op
                .map_or_else(|| "-".to_string(), |o| format!("{o:?}")),
            moved.join(" "),
        );
    }

    /// Rejoin audit record (`--dump-ctxedge`): one line per slot whose
    /// fact the joining arrival weakened in an Opt version's ctx, naming
    /// the pre-join fact and its provenance, the joined (weakened) fact,
    /// and the arrival's own fact for the slot. Emitted from theta's join
    /// step, so the op/pc are the edge that carried the weaker arrival --
    /// the arm the join law indicts. `tools/rejoin.py` filters to the
    /// claim-backed losses.
    pub(super) fn dump_rejoin_loss(&self, pc: Pc, pre: &Ctx, post: &Ctx, arr: &Ctx) {
        let name = |sect: u8, i: usize| match sect {
            0 => {
                if i == 0 {
                    "a_this".to_string()
                } else {
                    format!("a{}", i - 1)
                }
            }
            1 => format!("l{i}"),
            _ => format!("s{i}"),
        };
        let sects: [(u8, &[SlotCtx], &[SlotCtx], &[SlotCtx]); 3] = [
            (0, &pre.args, &post.args, &arr.args),
            (1, &pre.locals, &post.locals, &arr.locals),
            (2, &pre.stack, &post.stack, &arr.stack),
        ];
        for (sect, pres, posts, arrs) in sects {
            for (i, p) in pres.iter().enumerate() {
                let q = posts.get(i).copied().unwrap_or(SlotCtx::TOP);
                if p.is_top() || *p == q {
                    continue;
                }
                if !q.implies(p) {
                    let a = arrs.get(i).copied().unwrap_or(SlotCtx::TOP);
                    crate::diag_line!(
                        "night: rejoinloss sid#{} pc {} op {} at {pc} slot {} pre {} post {} arr {} prov {:x}",
                        self.source_id,
                        self.evid_pc(self.cur_pc),
                        self.cur_op
                            .map_or_else(|| "-".to_string(), |o| format!("{o:?}")),
                        name(sect, i),
                        Self::viz_slot_str(p),
                        Self::viz_slot_str(&q),
                        Self::viz_slot_str(&a),
                        p.prov.0,
                    );
                }
            }
        }
    }

    /// Dirty-merge audit (`--dump-opsize`): does this op's mini-CFG let a
    /// path that ran a may-GC helper rejoin the *same* continuation the
    /// clean path takes?
    ///
    /// The discipline being checked: inside one op, a path that dirties --
    /// a `CallGc` helper, which kills facts and saturates the flags word --
    /// should leave as its own lineage (`side_arm` /
    /// `edge_to`), not merge back. Only cheap validations should rejoin.
    /// An op where *every* path to the exit runs the call is an ordinary
    /// may-GC op, not a violation: the whole lineage is honestly dirty and
    /// the call-site flag fork is what recovers it.
    ///
    /// So the reported condition is a merge with both a dirtied and an
    /// undirtied predecessor path, computed over the blocks this op created
    /// (`entry` tail plus everything from `first_new`), with the op's exit
    /// being `self.cur`. Paths that leave the block set -- a version edge,
    /// a continuation -- cannot reach the exit and so are not merges.
    ///
    /// Blind spot worth stating: this sees calls, not fact invalidation. An
    /// arm that violates a likelier-types claim without calling anything
    /// rejoins invisibly here.
    pub(super) fn dirty_merge_kind(&self, entry: (Block, usize), first_new: usize) -> &'static str {
        let exit = self.cur;
        let mut set: HashSet<Block> = HashSet::default();
        set.insert(entry.0);
        for i in first_new..self.body.blocks.len() {
            set.insert(Block::new(i));
        }
        if !set.contains(&exit) {
            return "leaves";
        }
        // Does block `b` dirty, counting only the op's own instructions?
        let dirties = |b: Block| -> bool {
            let skip = if b == entry.0 { entry.1 } else { 0 };
            self.body.blocks[b]
                .insts
                .iter()
                .skip(skip)
                .any(|v| matches!(self.effects.get(v), Some(Eff::CallGc)))
        };
        // Forward fixpoint over the op's blocks: can the block be reached
        // clean, dirty, or both?
        let mut clean: HashSet<Block> = HashSet::default();
        let mut dirty: HashSet<Block> = HashSet::default();
        clean.insert(entry.0);
        let mut changed = true;
        while changed {
            changed = false;
            for &b in &set {
                let in_clean = clean.contains(&b);
                let in_dirty = dirty.contains(&b);
                if !in_clean && !in_dirty {
                    continue;
                }
                let d = dirties(b);
                let out_clean = in_clean && !d;
                let out_dirty = in_dirty || d;
                self.body.blocks[b].terminator.visit_successors(|succ| {
                    if !set.contains(&succ) {
                        return;
                    }
                    if out_clean && clean.insert(succ) {
                        changed = true;
                    }
                    if out_dirty && dirty.insert(succ) {
                        changed = true;
                    }
                });
            }
        }
        match (clean.contains(&exit), dirty.contains(&exit)) {
            (true, true) => "merge",
            (false, true) => "alldirty",
            _ => "clean",
        }
    }

    /// Per-op emitted-IR census (`--dump-opsize`). One record per emitted
    /// op instance, counting the waffle blocks and instructions the op's
    /// lowering added, split by instruction class. The accounting is the
    /// same as `viz_dump_lowering`: the entry block's tail plus every block
    /// created during the op.
    pub(super) fn dump_opsize(
        &self,
        op: crate::bytecode::JSOp,
        pc: Pc,
        lpc: Pc,
        entry: (Block, usize),
        first_new: usize,
        spliced: bool,
    ) {
        let mut blocks: Vec<(Block, usize)> = vec![(entry.0, entry.1)];
        for i in first_new..self.body.blocks.len() {
            blocks.push((Block::new(i), 0));
        }
        let mut cls = [0u32; 7];
        let mut nblocks = 0u32;
        let mut ninsts = 0u32;
        let mut nparams = 0u32;
        for (b, skip) in blocks {
            if self.body.blocks.get(b).is_none() {
                continue;
            }
            nblocks += 1;
            let blk = &self.body.blocks[b];
            if skip == 0 {
                nparams += u32::try_from(blk.params.len()).unwrap_or(0);
            }
            for &v in blk.insts.iter().skip(skip) {
                ninsts += 1;
                cls[self.opsize_class(v)] += 1;
            }
        }
        crate::diag_line!(
            "night: opsize sid#{} pc {pc} lpc {lpc} op {op:?} track {:?} spliced {} \
dmerge {} rung {} blocks {nblocks} params {nparams} insts {ninsts} alu {} load {} store {} \
call {} boxing {} const {} other {}",
            self.root_source_id,
            self.cur_track,
            u8::from(spliced),
            self.dirty_merge_kind(entry, first_new),
            if self.gen_only {
                "gen"
            } else if self.fanout_off {
                "nofan"
            } else {
                "full"
            },
            cls[0],
            cls[1],
            cls[2],
            cls[3],
            cls[4],
            cls[5],
            cls[6],
        );
    }

    /// Per-op lowering dump (viz-lower). `entry` is the block the op
    /// started in and how many instructions it already held, so the op's
    /// own contribution to a shared block is separable from what came
    /// before it.
    pub(super) fn viz_dump_lowering(&self, lpc: Pc, entry: (Block, usize), first_new: usize) {
        let sid = self.root_source_id;
        let mut blocks: Vec<(Block, usize)> = vec![(entry.0, entry.1)];
        for i in first_new..self.body.blocks.len() {
            blocks.push((Block::new(i), 0));
        }
        crate::diag_line!(
            "night: viz lower sid#{sid} lpc {lpc} entry b{} blocks {}",
            entry.0.index(),
            blocks.len()
        );
        for (b, skip) in blocks {
            if self.body.blocks.get(b).is_none() {
                continue;
            }
            let blk = &self.body.blocks[b];
            let params: Vec<String> = blk.params.iter().map(|(t, _)| format!("{t:?}")).collect();
            let term = match &blk.terminator {
                Terminator::Br { target } => format!("br b{}", target.block.index()),
                Terminator::CondBr {
                    cond,
                    if_true,
                    if_false,
                } => format!(
                    "condbr {} b{} b{}",
                    self.viz_cond(*cond),
                    if_true.block.index(),
                    if_false.block.index()
                ),
                Terminator::Select { .. } => "select".to_string(),
                Terminator::Return { .. } => "ret".to_string(),
                Terminator::None => "-".to_string(),
                other => format!("{other:?}")
                    .split_whitespace()
                    .next()
                    .unwrap()
                    .into(),
            };
            let insts = &blk.insts;
            crate::diag_line!(
                "night: viz lowerb sid#{sid} lpc {lpc} blk b{} skip {skip} params [{}] \
                 insts {} term {term}",
                b.index(),
                params.join(","),
                insts.len().saturating_sub(skip),
            );
            let mut n_alu = 0u32;
            for (i, &v) in insts.iter().enumerate().skip(skip) {
                let Some((k, d)) = self.viz_inst(v) else {
                    continue;
                };
                if k == "alu" {
                    n_alu += 1;
                    continue;
                }
                if i - skip >= crate::constants::VIZ_BLOCK_INST_CAP {
                    continue;
                }
                crate::diag_line!(
                    "night: viz loweri sid#{sid} lpc {lpc} blk b{} k {k} d {d}",
                    b.index()
                );
            }
            if n_alu > 0 {
                crate::diag_line!(
                    "night: viz loweri sid#{sid} lpc {lpc} blk b{} k alu d {n_alu}",
                    b.index()
                );
            }
        }
    }
}

/// A display name for a script: the function object's explicit name, the
/// selfhosted path, or the key of any object property holding the function.
pub(crate) fn viz_script_name(source: &Source, source_id: u32) -> Option<String> {
    let as_str = |n: SourceObjectId| {
        if n.is_other() {
            return None;
        }
        match source.object(n) {
            SourceObject::String(st) => Some(String::from_utf16_lossy(st.chars())),
            _ => None,
        }
    };
    for (_, o) in source.objects() {
        if let SourceObject::Object(ObjectData {
            script: Some(s),
            name: Some(n),
            ..
        }) = o
        {
            if s.id() == source_id {
                if let Some(nm) = as_str(*n) {
                    return Some(nm);
                }
            }
        }
    }
    for (sid, path) in &source.selfhosted {
        if sid.id() == source_id {
            return Some(path.clone());
        }
    }
    let holds_script = |v: SourceObjectId| {
        !v.is_other()
            && matches!(source.object(v),
                SourceObject::Object(ObjectData { script: Some(s), .. }) if s.id() == source_id)
    };
    // (owner, key) of the first property holding `target`.
    let key_of = |target: SourceObjectId| {
        source.objects().find_map(|(oid, o)| match o {
            SourceObject::Object(ObjectData { properties, .. }) => properties
                .iter()
                .find(|(_, v)| *v == target)
                .and_then(|(k, _)| as_str(*k).map(|nm| (oid, nm))),
            _ => None,
        })
    };
    for (oid, o) in source.objects() {
        if let SourceObject::Object(ObjectData { properties, .. }) = o {
            for (k, v) in properties {
                if holds_script(*v) {
                    let Some(nm) = as_str(*k) else { continue };
                    // Qualify a method with its constructor's name:
                    // owner reached as someone's `prototype` property.
                    if Some(oid) != source.global_object {
                        if let Some((ctor, key2)) = key_of(oid) {
                            if key2 == "prototype" {
                                if let Some((_, ctor_nm)) = key_of(ctor) {
                                    return Some(format!("{ctor_nm}.{nm}"));
                                }
                            } else if Some(ctor) == source.global_object {
                                return Some(format!("{key2}.{nm}"));
                            }
                        }
                    }
                    return Some(nm);
                }
            }
        }
    }
    None
}

pub(crate) fn viz_sanitize(s: &str) -> String {
    let mut out: String = s
        .chars()
        .map(|c| {
            if c.is_ascii_graphic() && c != '[' && c != ']' {
                c
            } else {
                '_'
            }
        })
        .collect();
    out.truncate(24);
    out
}

/// PRIM_* mask in the viz fact notation ("0" for no claim).
pub(crate) fn viz_prims_str(m: Prims) -> String {
    if m == Prims::EMPTY {
        return "0".to_string();
    }
    m.viz_parts().join("|")
}

/// One likely claim, for the diagnostic views.
pub(crate) fn viz_claim_str(c: Claim) -> String {
    if c.is_object() {
        return "obj".to_string();
    }
    let mut s = viz_prims_str(c.prims());
    if c.double_first() {
        s.push_str("|dbl1st");
    }
    s
}

/// cls range in the +1-biased stamped-id space (what SlotCtx cls facts and
/// the layout panel show).
pub(super) fn viz_cls_range(lo: u32, hi: u32) -> String {
    if lo == hi {
        format!("cls[{}]", lo + 1)
    } else {
        format!("cls[{}-{}]", lo + 1, hi + 1)
    }
}

pub(super) fn viz_gc_name(source: &Source, script: &Script, idx: u32) -> Option<String> {
    let id = *script.gcthings.get(idx as usize)?;
    if id.is_other() {
        return None;
    }
    match source.object(id) {
        SourceObject::String(st) => Some(viz_sanitize(&String::from_utf16_lossy(st.chars()))),
        _ => None,
    }
}

/// Operand rendering for the viz op/version lines (display only;
/// operand widths mirror the bytecode.rs dispatch).
pub(super) fn viz_op_args(source: &Source, script: &Script, pc: Pc, op: JSOp) -> String {
    use JSOp as J;
    let base = (pc.get() as usize + 1).min(script.bytecode.len());
    let b = &script.bytecode[base..];
    let rd = |o: usize, n: usize| -> Option<u64> {
        let mut v = 0u64;
        for i in 0..n {
            v |= u64::from(*b.get(o + i)?) << (8 * i);
        }
        Some(v)
    };
    let num = |v: Option<u64>| v.map_or_else(String::new, |v| v.to_string());
    let name = |v: Option<u64>| {
        v.and_then(|i| viz_gc_name(source, script, u32::try_from(i).unwrap()))
            .unwrap_or_default()
    };
    match op {
        J::GetLocal | J::SetLocal => num(rd(0, 3)),
        J::GetArg | J::SetArg | J::GetFrameArg => num(rd(0, 2)),
        J::GetProp
        | J::SetProp
        | J::StrictSetProp
        | J::InitProp
        | J::InitHiddenProp
        | J::InitLockedProp
        | J::InitPropGetter
        | J::InitHiddenPropGetter
        | J::InitPropSetter
        | J::InitHiddenPropSetter
        | J::DelProp
        | J::StrictDelProp
        | J::GetPropSuper
        | J::SetPropSuper
        | J::StrictSetPropSuper
        | J::ThrowSetConst
        | J::InitGLexical
        | J::BindUnqualifiedGName
        | J::BindUnqualifiedName
        | J::BindName
        | J::GetName
        | J::GetGName
        | J::GetImport
        | J::GetBoundName
        | J::GetIntrinsic
        | J::SetName
        | J::StrictSetName
        | J::SetGName
        | J::StrictSetGName
        | J::SetIntrinsic
        | J::DelName
        | J::NewPrivateName => name(rd(0, 4)),
        J::String => format!("\"{}\"", name(rd(0, 4))),
        J::Int8 => rd(0, 1).map_or_else(String::new, |v| (v as u8 as i8).to_string()),
        J::Int32 => rd(0, 4).map_or_else(String::new, |v| (v as u32 as i32).to_string()),
        J::Uint16 => num(rd(0, 2)),
        J::Uint24 => num(rd(0, 3)),
        J::Double => rd(0, 8).map_or_else(String::new, |v| format!("{}", f64::from_bits(v))),
        J::Goto
        | J::JumpIfTrue
        | J::JumpIfFalse
        | J::And
        | J::Or
        | J::Coalesce
        | J::Case
        | J::Default => rd(0, 4).map_or_else(String::new, |v| {
            format!("->{}", i64::from(pc.get()) + i64::from(v as u32 as i32))
        }),
        J::Call
        | J::CallIgnoresRv
        | J::CallIter
        | J::CallContent
        | J::CallContentIter
        | J::New
        | J::NewContent
        | J::SuperCall
        | J::Eval
        | J::StrictEval => format!("argc={}", num(rd(0, 2))),
        J::GetAliasedVar | J::SetAliasedVar => {
            format!("hops={} slot={}", num(rd(0, 2)), num(rd(2, 3)))
        }
        _ => String::new(),
    }
}
