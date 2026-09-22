/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! The control-flow graph, dominator tree and loop nest over the **unified
//! pc space**: the root script's bytecode plus every frozen splice segment.
//!
//! Nothing else in the compiler has one. `likelier/` has no blocks at all,
//! and the emitter's own graph is waffle's -- one node per emitted *version*,
//! which is a different space (a pc has many versions, and the versions of a
//! pc that a walk minted are a property of the walk). This is the graph over
//! program points, which is what the prediction is keyed by, so it is the
//! graph a fact question is asked in.
//!
//! Three consumers, in the order they arrive:
//!
//! - **"check here, trust below" is a dominance query.** The transfer
//!   function's guard-derived family (`refine_src` and the arm-local facts)
//!   knows something because a guard just ran at a point that is not a block
//!   boundary; stating that as a prediction needs to know which points the
//!   guard covers.
//! - **A redundant guard is a guard whose condition a dominating guard
//!   already proved.** That is the static half of the OPT-path efficiency
//!   question and it cannot be asked without this.
//! - **The loop nest** is already computed twice in weaker forms:
//!   `scan_loop_intervals` gives extents but no nesting and no body set, and
//!   the token machinery derives lineage from the extents. Both are checked
//!   against this one (`audit`) rather than replaced, because the extents
//!   key interned token classes and renumbering them would renumber every
//!   version.
//!
//! Soundness is by over-approximation in one direction: **more edges means
//! weaker dominance**, and every consumer wants dominance to be conservative.
//! So a spliced call site keeps its generic fall-through edge beside the edge
//! into the segment (a walk that declined the splice really does take it),
//! and an exception handler is given the entry block as a predecessor rather
//! than an edge from each covered pc -- the handler ends up dominated by the
//! entry alone, which is the weakest true answer.

use super::*;

/// No block / no header.
const NONE: u32 = u32::MAX;

/// What the op at a pc does to control flow. Everything not named here
/// falls through, which is the overwhelming majority.
enum Flow {
    /// An unconditional branch.
    Br(u32),
    /// A conditional branch: the named target, plus the fall-through.
    CondBr(u32),
    /// `TableSwitch`: the case targets and the default.
    Switch(Vec<u32>),
    /// `Return` / `RetRval`. Leaves the frame: inside a segment that is an
    /// edge to the segment's return pc, at the root it is a graph exit.
    Ret,
    /// A throw. Its successors are handler edges, which are modelled on the
    /// handler rather than here.
    Halt,
}

/// One basic block: a contiguous pc range within one script instance.
///
/// Contiguity is what makes an intra-block dominance query a pc comparison,
/// and it holds because a block is cut at every leader -- so no branch
/// target, and no pc after a branch, is interior to one.
struct CfgBlock {
    start: u32,
    /// One past the last pc of the block's last op.
    end: u32,
    succs: Vec<u32>,
    preds: Vec<u32>,
}

pub(super) struct Cfg {
    blocks: Vec<CfgBlock>,
    /// `(start, end, block)` sorted by start: the pc -> block index.
    span: Vec<(u32, u32, u32)>,
    /// Immediate dominator per block; the entry's is itself, and an
    /// unreachable block's is `NONE`.
    idom: Vec<u32>,
    /// Depth in the dominator tree, so `dominates` is a walk up the shorter
    /// side rather than a set.
    dom_depth: Vec<u32>,
    /// The innermost natural loop's header block per block, or `NONE`.
    loop_hdr: Vec<u32>,
    /// Loop-nest depth per block.
    loop_depth: Vec<u16>,
    /// Natural loop headers, in block order.
    headers: Vec<u32>,
    /// `(header, block)` for every block in every natural loop's body.
    loop_members: HashSet<(u32, u32)>,
}

impl Cfg {
    // --- queries ---------------------------------------------------------

    /// Whether the edge `src -> dst` leaves the innermost natural loop
    /// containing `src`: `dst` is outside that loop's body.
    pub(super) fn leaves_loop(&self, src: Pc, dst: Pc) -> bool {
        let Some(bs) = self.block_of(src) else {
            return false;
        };
        let h = self.loop_hdr[bs as usize];
        if h == NONE {
            return false;
        }
        match self.block_of(dst) {
            Some(bd) => !self.loop_members.contains(&(h, bd)),
            None => true,
        }
    }

    fn block_of(&self, pc: Pc) -> Option<u32> {
        let pc = pc.get();
        let i = self.span.partition_point(|&(s, _, _)| s <= pc);
        let (_, e, b) = *self.span.get(i.checked_sub(1)?)?;
        (pc < e).then_some(b)
    }

    fn block_dominates(&self, a: u32, b: u32) -> bool {
        let mut b = b;
        while self.dom_depth[b as usize] > self.dom_depth[a as usize] {
            b = self.idom[b as usize];
        }
        a == b
    }

    // --- construction ----------------------------------------------------

    /// Build the graph for a body: its root script plus the frozen splice
    /// segments, in the pc space `ensure_seg` laid out.
    pub(super) fn build(root: &Script, segs: &[InlineSeg<'_>]) -> Cfg {
        // 1. The per-op flow of every script instance, rebased.
        let mut ops: Vec<(u32, u32)> = Vec::new(); // (pc, len), ascending
        let mut flow: HashMap<u32, Flow> = HashMap::default();
        let mut leaders: HashSet<u32> = HashSet::default();
        // Which instance a pc belongs to: `None` = the root, `Some(i)` = a
        // segment, which is what a `Ret` needs in order to name its edge.
        let mut instance: Vec<(u32, u32, Option<usize>)> = Vec::new();

        let mut scan = |script: &Script, base: u32, seg: Option<usize>| {
            let s = script.parser().visit(FlowScan {
                base,
                pc: 0,
                ops: Vec::new(),
                flow: HashMap::default(),
                handlers: Vec::new(),
            });
            let end = base + u32::try_from(script.bytecode.len()).unwrap();
            instance.push((base, end, seg));
            leaders.insert(base);
            for &h in &s.handlers {
                leaders.insert(h);
            }
            for (pc, len) in &s.ops {
                match s.flow.get(pc) {
                    None => {}
                    Some(Flow::Br(t)) => {
                        leaders.insert(*t);
                        leaders.insert(pc + len);
                    }
                    Some(Flow::CondBr(t)) => {
                        leaders.insert(*t);
                        leaders.insert(pc + len);
                    }
                    Some(Flow::Switch(ts)) => {
                        for t in ts {
                            leaders.insert(*t);
                        }
                        leaders.insert(pc + len);
                    }
                    Some(Flow::Ret | Flow::Halt) => {
                        leaders.insert(pc + len);
                    }
                }
            }
            ops.extend(s.ops);
            flow.extend(s.flow);
            s.handlers
        };

        let mut handlers: Vec<u32> = scan(root, 0, None);
        for (i, g) in segs.iter().enumerate() {
            handlers.extend(scan(g.script, g.base, Some(i)));
        }
        // A splice cuts its call site: the segment entry and the generic
        // fall-through are both successors of it.
        for g in segs {
            leaders.insert(g.base);
            leaders.insert(g.ret_pc.get());
        }
        ops.sort_unstable();
        // A call site splices one segment PER CALLEE, so this is a list:
        // richards' four-target dispatch owns four segments at one pc, and
        // keying by the pc alone would leave three of them with no edge in
        // and their loops with no back edge (the audit catches exactly that).
        let mut by_call: HashMap<u32, Vec<u32>> = HashMap::default();
        for g in segs {
            by_call.entry(g.call_pc.get()).or_default().push(g.base);
        }

        // 2. Cut the blocks. A block runs from a leader to the next leader
        //    in the same instance, so every pc in it is interior by
        //    construction and the last op is its terminator.
        let mut blocks: Vec<CfgBlock> = Vec::new();
        let mut span: Vec<(u32, u32, u32)> = Vec::new();
        // The last op of each block, for the successor pass.
        let mut last_op: Vec<(u32, u32)> = Vec::new();
        let mut blk_seg: Vec<Option<usize>> = Vec::new();
        for &(base, end, seg) in &instance {
            let lo = ops.partition_point(|&(p, _)| p < base);
            let hi = ops.partition_point(|&(p, _)| p < end);
            let mut i = lo;
            while i < hi {
                let start = ops[i].0;
                let mut j = i;
                while j + 1 < hi && !leaders.contains(&ops[j + 1].0) {
                    j += 1;
                }
                let b = u32::try_from(blocks.len()).unwrap();
                blocks.push(CfgBlock {
                    start,
                    end: ops[j].0 + ops[j].1,
                    succs: Vec::new(),
                    preds: Vec::new(),
                });
                span.push((start, ops[j].0 + ops[j].1, b));
                last_op.push(ops[j]);
                blk_seg.push(seg);
                i = j + 1;
            }
        }
        span.sort_unstable();
        let of = |pc: u32| -> Option<u32> {
            let i = span.partition_point(|&(s, _, _)| s <= pc);
            let (_, e, b) = *span.get(i.checked_sub(1)?)?;
            (pc < e).then_some(b)
        };

        // 3. The successor relation.
        for b in 0..blocks.len() {
            let (pc, len) = last_op[b];
            let mut succs: Vec<u32> = Vec::new();
            let mut push = |t: Option<u32>| {
                if let Some(t) = t {
                    succs.push(t);
                }
            };
            match flow.get(&pc) {
                None => push(of(pc + len)),
                Some(Flow::Br(t)) => push(of(*t)),
                Some(Flow::CondBr(t)) => {
                    push(of(*t));
                    push(of(pc + len));
                }
                Some(Flow::Switch(ts)) => {
                    for t in ts {
                        push(of(*t));
                    }
                }
                Some(Flow::Ret) => {
                    if let Some(si) = blk_seg[b] {
                        push(of(segs[si].ret_pc.get()));
                    }
                }
                Some(Flow::Halt) => {}
            }
            // The splice's own edge, beside the generic fall-through the
            // `None` arm above already pushed.
            if let Some(bases) = by_call.get(&pc) {
                for &seg_base in bases {
                    push(of(seg_base));
                }
            }
            succs.sort_unstable();
            succs.dedup();
            blocks[b].succs = succs;
        }
        // An exception landing is reachable from every covered pc. Rather
        // than cut every one of those blocks in two, make it a successor of
        // the entry: it is then dominated by the entry alone, which is the
        // weakest true answer and the one every consumer wants.
        for h in handlers {
            if let Some(b) = of(h) {
                if b != 0 {
                    blocks[0].succs.push(b);
                }
            }
        }
        blocks[0].succs.sort_unstable();
        blocks[0].succs.dedup();
        for b in 0..blocks.len() {
            for i in 0..blocks[b].succs.len() {
                let s = blocks[b].succs[i] as usize;
                blocks[s].preds.push(u32::try_from(b).unwrap());
            }
        }

        let mut cfg = Cfg {
            blocks,
            span,
            idom: Vec::new(),
            dom_depth: Vec::new(),
            loop_hdr: Vec::new(),
            loop_depth: Vec::new(),
            headers: Vec::new(),
            loop_members: HashSet::default(),
        };
        cfg.dominators();
        cfg.loops();
        cfg
    }

    /// Reverse postorder from the entry, then Cooper-Harvey-Kennedy.
    fn dominators(&mut self) {
        let n = self.blocks.len();
        let mut post: Vec<u32> = Vec::with_capacity(n);
        let mut seen = vec![false; n];
        // Iterative DFS: bodies nest deep enough that recursion is a risk.
        let mut stack: Vec<(u32, usize)> = vec![(0, 0)];
        seen[0] = true;
        while let Some(&mut (b, ref mut i)) = stack.last_mut() {
            if *i < self.blocks[b as usize].succs.len() {
                let s = self.blocks[b as usize].succs[*i];
                *i += 1;
                if !seen[s as usize] {
                    seen[s as usize] = true;
                    stack.push((s, 0));
                }
            } else {
                post.push(b);
                stack.pop();
            }
        }
        let rpo: Vec<u32> = post.iter().rev().copied().collect();
        let mut rpo_num = vec![NONE; n];
        for (i, &b) in rpo.iter().enumerate() {
            rpo_num[b as usize] = u32::try_from(i).unwrap();
        }
        let mut idom = vec![NONE; n];
        idom[0] = 0;
        loop {
            let mut changed = false;
            for &b in rpo.iter().skip(1) {
                let mut new = NONE;
                for i in 0..self.blocks[b as usize].preds.len() {
                    let p = self.blocks[b as usize].preds[i];
                    if idom[p as usize] == NONE {
                        continue;
                    }
                    new = if new == NONE {
                        p
                    } else {
                        // Walk both up to their common ancestor.
                        let (mut x, mut y) = (p, new);
                        while x != y {
                            while rpo_num[x as usize] > rpo_num[y as usize] {
                                x = idom[x as usize];
                            }
                            while rpo_num[y as usize] > rpo_num[x as usize] {
                                y = idom[y as usize];
                            }
                        }
                        x
                    };
                }
                if new != NONE && idom[b as usize] != new {
                    idom[b as usize] = new;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        let mut depth = vec![0u32; n];
        for &b in rpo.iter().skip(1) {
            if idom[b as usize] != NONE {
                depth[b as usize] = depth[idom[b as usize] as usize] + 1;
            }
        }
        self.idom = idom;
        self.dom_depth = depth;
    }

    /// The natural loops: a back edge is an edge to a block that dominates
    /// it, and the loop is the header plus everything that reaches the back
    /// edge's source without leaving through the header.
    ///
    /// The nest is read off the containment lists rather than built as a
    /// tree, which is sound because the graph is reducible by construction
    /// (DESIGN 4.9) -- so the loops containing a block form a chain, and the
    /// innermost is simply the deepest.
    fn loops(&mut self) {
        let n = self.blocks.len();
        let mut bodies: HashMap<u32, Vec<u32>> = HashMap::default();
        for b in 0..n {
            let b32 = u32::try_from(b).unwrap();
            if self.idom[b] == NONE {
                continue;
            }
            for i in 0..self.blocks[b].succs.len() {
                let h = self.blocks[b].succs[i];
                if !self.block_dominates(h, b32) {
                    continue;
                }
                let body = bodies.entry(h).or_insert_with(|| vec![h]);
                let mut stack = vec![b32];
                let mut inbody: HashSet<u32> = body.iter().copied().collect();
                while let Some(x) = stack.pop() {
                    if !inbody.insert(x) {
                        continue;
                    }
                    body.push(x);
                    for j in 0..self.blocks[x as usize].preds.len() {
                        stack.push(self.blocks[x as usize].preds[j]);
                    }
                }
            }
        }
        let mut headers: Vec<u32> = bodies.keys().copied().collect();
        headers.sort_unstable();
        let mut depth = vec![0u16; n];
        for h in &headers {
            for &b in &bodies[h] {
                depth[b as usize] += 1;
            }
        }
        let mut hdr = vec![NONE; n];
        for h in &headers {
            for &b in &bodies[h] {
                let cur = hdr[b as usize];
                // The deepest containing header is the innermost one, and a
                // header does not name itself unless it is nested in a loop
                // of its own.
                if cur == NONE || depth[*h as usize] > depth[cur as usize] {
                    hdr[b as usize] = *h;
                }
            }
        }
        // A header's own innermost loop is the one it heads only for the
        // blocks under it; for the header itself the useful answer is the
        // same, and `loop_depth` already counts it.
        self.loop_members = bodies
            .iter()
            .flat_map(|(h, body)| body.iter().map(move |&b| (*h, b)))
            .collect();
        self.loop_hdr = hdr;
        self.loop_depth = depth;
        self.headers = headers;
    }

    // --- diagnostics -----------------------------------------------------

    /// `--dump-cfg`: the shape, the loop nest, and the audit against the
    /// extents `scan_loop_intervals` produced.
    ///
    /// The audit is the point. The extent scan and this graph derive loop
    /// headers by completely different routes -- a `LoopHead` marker with a
    /// backwards branch to it, against a back edge to a dominating block --
    /// and the token machinery keys interned classes on the extents, so a
    /// disagreement is either a bug here or a body whose lineage labelling
    /// is not what it looks like. Neither is something to find later.
    pub(super) fn dump(&self, sid: ScriptId, intervals: &[(u32, u32)]) {
        let reach = self.idom.iter().filter(|&&d| d != NONE).count();
        crate::diag_line!(
            "night: cfg sid#{sid} blocks {} reachable {reach} loops {} maxdepth {}",
            self.blocks.len(),
            self.headers.len(),
            self.loop_depth.iter().copied().max().unwrap_or(0),
        );
        for (i, b) in self.blocks.iter().enumerate() {
            let succs: Vec<u32> = b
                .succs
                .iter()
                .map(|&s| self.blocks[s as usize].start)
                .collect();
            crate::diag_line!(
                "night: cfg sid#{sid} blk {}..{} idom {} depth {} succs {succs:?}",
                b.start,
                b.end,
                match self.idom[i] {
                    NONE => -1,
                    d => i64::from(self.blocks[d as usize].start),
                },
                self.loop_depth[i],
            );
        }
        for &h in &self.headers {
            let b = &self.blocks[h as usize];
            // Blocks whose INNERMOST loop is this one, so a nest's counts
            // partition rather than overlap.
            let own = self.loop_hdr.iter().filter(|&&x| x == h).count();
            crate::diag_line!(
                "night: cfg sid#{sid} loop hdr {} depth {} own {own} idom {}",
                b.start,
                self.loop_depth[h as usize],
                self.blocks[self.idom[h as usize] as usize].start,
            );
        }
        let mine: HashSet<u32> = self
            .headers
            .iter()
            .map(|&h| self.blocks[h as usize].start)
            .collect();
        for &(h, e) in intervals {
            if mine.contains(&h) {
                continue;
            }
            // The extent scan is syntactic: a `LoopHead` with a backwards
            // branch to it is a loop whether or not anything reaches the
            // branch. A back edge from an unreachable block is therefore an
            // agreement, not a disagreement, and saying so is the difference
            // between an audit and a nuisance.
            let dead = self.blocks.iter().enumerate().any(|(i, b)| {
                self.idom[i] == NONE && b.succs.iter().any(|&t| self.blocks[t as usize].start == h)
            });
            let why = if dead {
                "unreachable back edge"
            } else {
                "no back edge"
            };
            crate::diag_line!("night: cfg sid#{sid} AUDIT extent {h}..{e} {why}");
        }
        for h in &mine {
            if !intervals.iter().any(|&(ih, _)| ih == *h) {
                crate::diag_line!("night: cfg sid#{sid} AUDIT header {h} has no extent");
            }
        }
    }
}

/// The one bytecode walk the graph needs: every op's pc and length, and the
/// control-flow shape of the ones that are not a fall-through.
struct FlowScan {
    base: u32,
    pc: u32,
    ops: Vec<(u32, u32)>,
    flow: HashMap<u32, Flow>,
    handlers: Vec<u32>,
}

impl FlowScan {
    fn set(&mut self, f: Flow) {
        self.flow.insert(self.pc, f);
    }

    fn target(&self, off: i32) -> u32 {
        Pc::new(self.pc).branch(off).get()
    }
}

impl OpcodeVisitor for FlowScan {
    fn before_op(&mut self, pc: Pc, op: JSOp, _u: usize, _d: usize) {
        self.pc = self.base + pc.get();
        self.ops.push((self.pc, op.len()));
    }

    fn try_note(&mut self, _pc: Pc, note: &crate::bytecode::TryNote) {
        // The landing pad of a catch or a finally is one past the covered
        // range, exactly as `walk_try_notes` reads it. The other kinds close
        // an iterator or a for-in on the way past and land nowhere.
        if matches!(note.kind, TryNoteKind::Catch | TryNoteKind::Finally) {
            self.handlers
                .push(self.base + note.start.get() + note.length);
        }
    }

    fn goto_(&mut self, off: i32) {
        let t = self.target(off);
        self.set(Flow::Br(t));
    }
    fn default_(&mut self, off: i32) {
        let t = self.target(off);
        self.set(Flow::Br(t));
    }
    fn jump_if_false(&mut self, off: i32) {
        let t = self.target(off);
        self.set(Flow::CondBr(t));
    }
    fn jump_if_true(&mut self, off: i32) {
        let t = self.target(off);
        self.set(Flow::CondBr(t));
    }
    fn and_(&mut self, off: i32) {
        let t = self.target(off);
        self.set(Flow::CondBr(t));
    }
    fn or_(&mut self, off: i32) {
        let t = self.target(off);
        self.set(Flow::CondBr(t));
    }
    fn coalesce(&mut self, off: i32) {
        let t = self.target(off);
        self.set(Flow::CondBr(t));
    }
    fn case_(&mut self, off: i32) {
        let t = self.target(off);
        self.set(Flow::CondBr(t));
    }
    fn table_switch(&mut self, default_off: i32, _low: i32, _high: i32, offsets: &[Pc]) {
        // The resume offsets are absolute pcs in the callee's own space; the
        // default is relative, like every other branch.
        let mut ts: Vec<u32> = offsets.iter().map(|p| self.base + p.get()).collect();
        ts.push(self.target(default_off));
        self.set(Flow::Switch(ts));
    }
    fn return_(&mut self) {
        self.set(Flow::Ret);
    }
    fn ret_rval(&mut self) {
        self.set(Flow::Ret);
    }
    fn throw_(&mut self) {
        self.set(Flow::Halt);
    }
    fn throw_with_stack(&mut self) {
        self.set(Flow::Halt);
    }
    fn throw_msg(&mut self, _n: u8) {
        self.set(Flow::Halt);
    }
    fn throw_set_const(&mut self, _n: u32) {
        self.set(Flow::Halt);
    }
}
