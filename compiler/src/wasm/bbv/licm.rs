/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Post-emission passes over the waffle IR: the reducibility assert and
//! loop-invariant code motion.

use super::*;

// --- the reducibility assert + LICM on the emitted waffle IR --------------

/// The emitted version graph is reducible by construction
/// (loop-header-version tokens); a retreating edge to a non-dominating
/// target means the token discipline broke. Reported as a skip (the script
/// falls to the interpreter and the coverage meters flag it) rather than a
/// silent reducify dispatcher.
pub(super) fn assert_reducible(body: &FunctionBody) -> Result<CFGInfo, (Block, Block)> {
    let cfg = CFGInfo::new(body);
    for (rpo, &block) in cfg.rpo.entries() {
        for &succ in &body.blocks[block].succs {
            if let Some(succ_rpo) = cfg.rpo_pos[succ] {
                if succ_rpo.index() <= rpo.index() && !cfg.dominates(succ, block) {
                    return Err((block, succ));
                }
            }
        }
    }
    Ok(cfg)
}

/// Whether `addr` is frame traffic: the address expression roots at the
/// frame pointers (sp/vp), following constant-offset adds. Frame reads
/// never hoist and frame writes never block heap hoisting.
fn is_frame_addr(body: &FunctionBody, mut addr: Value, roots: &[Value]) -> bool {
    loop {
        if roots.contains(&addr) {
            return true;
        }
        let ValueDef::Operator(op, args, _) = &body.values[addr] else {
            return false;
        };
        if !matches!(op, Operator::I32Add) {
            return false;
        }
        let args = &body.arg_pool[*args];
        let (a, b) = (args[0], args[1]);
        let is_const = |v: Value| {
            matches!(
                body.values[v],
                ValueDef::Operator(Operator::I32Const { .. }, _, _)
            )
        };
        if is_const(a) {
            addr = b;
        } else if is_const(b) {
            addr = a;
        } else {
            return false;
        }
    }
}

/// May a read of kind `k` be hoisted out of a loop with write-kind summary
/// `writes` (direct stores union leaf-call write summaries, from
/// `helper_leaf_writes`)? An
/// untagged (Unknown) write may alias anything, so it blocks every kind.
/// EngineTable is deliberately not exempt from the kind-conflict rule
/// despite its stale-tolerant value contract: an in-loop row write marks
/// a self-warming loop (call-cell fill, gname cold resolve), and hoisting
/// the row read above its own fill pins the guard to the cold value --
/// the consumer then misses every iteration and the warmup never pays.
/// `Fresh` writes are never a read kind, so they block only untagged loads
/// (via the blanket writes-empty rule at the call sites).
fn licm_kind_ok(k: HeapKind, writes: &HashSet<HeapKind>) -> bool {
    if writes.contains(&HeapKind::Unknown) {
        return false;
    }
    if k == HeapKind::Unknown {
        return writes.is_empty();
    }
    !writes.contains(&k)
}

/// Address expression made entirely of constants (const + const-adds):
/// relocation-immune, so a load from it stays addressable across a GC.
fn const_rooted_addr(body: &FunctionBody, mut addr: Value) -> bool {
    loop {
        match &body.values[addr] {
            ValueDef::Operator(Operator::I32Const { .. }, _, _) => return true,
            ValueDef::Operator(Operator::I32Add, args, _) => {
                let args = &body.arg_pool[*args];
                let (a, b) = (args[0], args[1]);
                let is_const = |v: Value| {
                    matches!(
                        body.values[v],
                        ValueDef::Operator(Operator::I32Const { .. }, _, _)
                    )
                };
                if is_const(a) {
                    addr = b;
                } else if is_const(b) {
                    addr = a;
                } else {
                    return false;
                }
            }
            _ => return false,
        }
    }
}

/// LICM (`night/docs/DESIGN.md` section 4.11): per
/// natural loop (reducible by the token discipline), hoist invariant pure
/// ops and effect-cleared loads from blocks that dominate every latch
/// into a preheader split off the loop's single outside entry edge. The
/// loop write summary folds direct store tags and leaf-call write
/// summaries (helper_leaf_writes); redundant-phi header params (provably
/// equal to their entry value every iteration) are admitted as invariant,
/// with hoisted users substituting the preheader's blockparam. A loop
/// containing a may-GC call still hoists only const-addressed EngineTable
/// rows (a moving GC relocates objects, so cached derived pointers/words
/// would be stale). Returns the number of hoisted values.
pub(super) fn licm(
    body: &mut FunctionBody,
    cfg: &CFGInfo,
    effects: &HashMap<Value, Eff>,
    frame_roots: &[Value],
    sid: u32,
    load_pcs: &HashMap<Value, String>,
) -> u32 {
    // Early out: no retreating edge, no loops (the common straight-line
    // script pays two rpo scans and nothing else).
    let mut any_back = false;
    'scan: for (rpo, &b) in cfg.rpo.entries() {
        for &succ in &body.blocks[b].succs {
            if let Some(srpo) = cfg.rpo_pos[succ] {
                if srpo.index() <= rpo.index() {
                    any_back = true;
                    break 'scan;
                }
            }
        }
    }
    if !any_back {
        return 0;
    }
    // Value -> defining block, index-keyed (the epoch-array discipline:
    // never hash per-value).
    let mut def_block: Vec<u32> = vec![u32::MAX; body.values.len()];
    let mut rpo_blocks: Vec<Block> = Vec::new();
    for (_, &b) in cfg.rpo.entries() {
        rpo_blocks.push(b);
        for &(_, p) in &body.blocks[b].params {
            def_block[p.index()] = b.index() as u32;
        }
        for &v in &body.blocks[b].insts {
            def_block[v.index()] = b.index() as u32;
        }
    }
    // Natural loops: one per header (back edges whose target dominates the
    // source; assert_reducible already rejected the rest).
    let mut latches: HashMap<Block, Vec<Block>> = HashMap::default();
    for (rpo, &b) in cfg.rpo.entries() {
        for &succ in &body.blocks[b].succs {
            if let Some(srpo) = cfg.rpo_pos[succ] {
                if srpo.index() <= rpo.index() && cfg.dominates(succ, b) {
                    latches.entry(succ).or_default().push(b);
                }
            }
        }
    }
    struct LoopInfo {
        header: Block,
        set: HashSet<Block>,
        latches: Vec<Block>,
    }
    let mut loops: Vec<LoopInfo> = Vec::new();
    for (&h, ls) in &latches {
        let mut set: HashSet<Block> = HashSet::default();
        set.insert(h);
        let mut work: Vec<Block> = ls.clone();
        while let Some(b) = work.pop() {
            if set.insert(b) {
                for &p in &body.blocks[b].preds {
                    work.push(p);
                }
            }
        }
        loops.push(LoopInfo {
            header: h,
            set,
            latches: ls.clone(),
        });
    }
    // Innermost first so inner-hoisted values can cascade outward on the
    // containing loop's pass (their def moves to the inner preheader,
    // which is added to every containing loop's set below).
    loops.sort_by_key(|l| l.set.len());

    let mut hoisted_total = 0u32;
    for li in 0..loops.len() {
        // Effect summary of the loop body: direct stores unioned with
        // leaf-call write summaries.
        let mut writes: HashSet<HeapKind> = HashSet::default();
        let mut has_gc = false;
        let mut has_leaf = false;
        for &b in &loops[li].set {
            for &v in &body.blocks[b].insts {
                match effects.get(&v) {
                    Some(Eff::Write(k)) => {
                        writes.insert(*k);
                    }
                    Some(Eff::CallGc) => {
                        has_gc = true;
                    }
                    Some(Eff::CallGcQuiet) => {
                        has_gc = true;
                        // The helper bumps the same nursery the inline
                        // paths use and fills fresh memory.
                        writes.insert(HeapKind::AllocCursor);
                        writes.insert(HeapKind::Fresh);
                    }
                    Some(Eff::CallLeaf(mask)) => {
                        has_leaf = true;
                        for k in HeapKind::ALL {
                            if mask & k.bit() != 0 {
                                writes.insert(k);
                            }
                        }
                    }
                    Some(Eff::CallPure) | Some(Eff::Read(_)) | Some(Eff::ReadBits(_)) => {}
                    None => {
                        if let ValueDef::Operator(op, args, _) = &body.values[v] {
                            let se = op.effects();
                            if se.contains(&waffle::SideEffect::WriteMem) {
                                let a = body.arg_pool[*args][0];
                                if !is_frame_addr(body, a, frame_roots) {
                                    writes.insert(HeapKind::Unknown);
                                }
                            }
                            if matches!(op, Operator::Call { .. } | Operator::CallIndirect { .. }) {
                                has_gc = true;
                            }
                        }
                    }
                }
            }
        }
        let all_writes = writes;
        // A may-GC call in the loop restricts hoisting to const-addressed
        // guarded row reads (see HeapKind::EngineTable); everything else
        // needs a call-free body (a moving GC relocates objects).
        // Preheader: split the single outside entry edge, or merge
        // several outside entry edges
        // (conform/onramp entries) into one shared preheader carrying the
        // header's param signature. These are IR blocks, not versions;
        // theta/tokens are untouched.
        let header = loops[li].header;
        let outside: Vec<usize> = body.blocks[header]
            .preds
            .iter()
            .enumerate()
            .filter(|(_, p)| !loops[li].set.contains(p))
            .map(|(i, _)| i)
            .collect();
        if outside.is_empty() {
            continue;
        }
        // entry_args: the single outside edge's args when there is one
        // (lets the phi rule match latch args against the entry value);
        // the preheader's own params in the merged case (no single entry
        // value exists -- only self-carried params can be stable).
        let (pre, entry_args) = if outside.len() == 1 {
            let pred_idx = outside[0];
            let opred = body.blocks[header].preds[pred_idx];
            let succ_idx = body.blocks[header].pos_in_pred_succ[pred_idx];
            let pre = body.split_edge(opred, header, succ_idx);
            let mut entry_args: Vec<Value> = Vec::new();
            body.blocks[opred].terminator.visit_targets(|t| {
                if t.block == pre {
                    entry_args = t.args.clone();
                }
            });
            (pre, entry_args)
        } else {
            let pre = body.add_block();
            let tys: Vec<Type> = body.blocks[header].params.iter().map(|&(t, _)| t).collect();
            let params: Vec<Value> = tys.iter().map(|&t| body.add_blockparam(pre, t)).collect();
            body.blocks[pre].terminator = Terminator::Br {
                target: BlockTarget {
                    block: header,
                    args: params.clone(),
                },
            };
            let opreds: Vec<Block> = outside
                .iter()
                .map(|&i| body.blocks[header].preds[i])
                .collect();
            for p in opreds {
                body.blocks[p].terminator.update_targets(|t| {
                    if t.block == header {
                        t.block = pre;
                    }
                });
            }
            // Terminator-level surgery: rebuild the succ/pred caches.
            body.recompute_edges();
            let params = body.blocks[pre]
                .params
                .iter()
                .map(|&(_, v)| v)
                .collect::<Vec<Value>>();
            (pre, params)
        };
        // The preheader lies inside every loop that strictly contains this
        // one (reducibility: a containing loop holding our header also
        // holds our entry edge).
        for l in loops.iter_mut().skip(li + 1) {
            if l.set.contains(&header) && l.header != header {
                l.set.insert(pre);
            }
        }
        // split_edge minted new values (the preheader's blockparams);
        // give them def_block entries so a containing loop's later pass
        // sees them as defined in `pre` (which is inside that loop).
        def_block.resize(body.values.len(), u32::MAX);
        for &(_, p) in &body.blocks[pre].params {
            def_block[p.index()] = pre.index() as u32;
        }
        // Redundant-phi invariance: the version graph carries locals as
        // header blockparams, so
        // invariant bases look loop-variant. A header param is invariant
        // iff every latch edge passes the param itself, another already-
        // stable param with the same entry arg, or the entry arg's own
        // SSA value -- i.e. the param provably equals its entry value on
        // every iteration. (The looser "any outside-defined latch arg"
        // rule the census used is wrong for real hoisting: such a param
        // changes value once after iteration 1.) The phi is never
        // rewritten (edges/params are the version ABI); hoisted
        // instructions substitute the preheader's corresponding
        // blockparam, which carries exactly the entry value.
        let header_params: Vec<Value> =
            body.blocks[header].params.iter().map(|&(_, v)| v).collect();
        let pre_params: Vec<Value> = body.blocks[pre].params.iter().map(|&(_, v)| v).collect();
        let param_index: HashMap<Value, usize> = header_params
            .iter()
            .enumerate()
            .map(|(i, &p)| (p, i))
            .collect();
        let mut stable = vec![false; header_params.len()];
        if entry_args.len() == header_params.len() {
            loop {
                let mut changed = false;
                'params: for i in 0..header_params.len() {
                    if stable[i] {
                        continue;
                    }
                    for &l in &loops[li].latches {
                        // Collect every latch->header target's arg at
                        // position i (a conditional latch can target the
                        // header on both arms with different args).
                        let mut args_at: Vec<Option<Value>> = Vec::new();
                        body.blocks[l].terminator.visit_targets(|t| {
                            if t.block == header {
                                args_at.push(t.args.get(i).copied());
                            }
                        });
                        if args_at.is_empty() {
                            continue 'params;
                        }
                        for aa in args_at {
                            let ok = match aa {
                                Some(a) => {
                                    a == header_params[i]
                                        || a == entry_args[i]
                                        || param_index.get(&a).is_some_and(|&j| {
                                            stable[j] && entry_args[j] == entry_args[i]
                                        })
                                }
                                None => false,
                            };
                            if !ok {
                                continue 'params;
                            }
                        }
                    }
                    stable[i] = true;
                    changed = true;
                }
                if !changed {
                    break;
                }
            }
        }
        // Hoist from loop blocks that dominate every latch, in rpo (defs
        // before uses).
        for &b in &rpo_blocks {
            if !loops[li].set.contains(&b) {
                continue;
            }
            if !loops[li].latches.iter().all(|&l| cfg.dominates(b, l)) {
                continue;
            }
            let insts = std::mem::take(&mut body.blocks[b].insts);
            let mut keep: Vec<Value> = Vec::with_capacity(insts.len());
            for v in insts {
                // None = not hoistable; Some(subs) = hoistable after
                // substituting each (arg index -> preheader blockparam)
                // pair for the stable header params it uses.
                let hoistable = (|| -> Option<Vec<(usize, Value)>> {
                    let ValueDef::Operator(op, args, _) = &body.values[v] else {
                        return None;
                    };
                    let mut subs: Vec<(usize, Value)> = Vec::new();
                    for (ai, &a) in body.arg_pool[*args].iter().enumerate() {
                        let db = def_block[a.index()];
                        if db != u32::MAX && loops[li].set.contains(&Block::new(db as usize)) {
                            match param_index.get(&a) {
                                Some(&j) if stable[j] => subs.push((ai, pre_params[j])),
                                _ => return None,
                            }
                        }
                    }
                    let se = op.effects();
                    if se.is_empty() {
                        return Some(subs);
                    }
                    let is_load = se.contains(&waffle::SideEffect::ReadMem)
                        && se.iter().all(|e| {
                            matches!(e, waffle::SideEffect::ReadMem | waffle::SideEffect::Trap)
                        });
                    if !is_load {
                        return None;
                    }
                    match effects.get(&v) {
                        Some(Eff::Read(k)) | Some(Eff::ReadBits(k)) => {
                            if !licm_kind_ok(*k, &all_writes) {
                                return None;
                            }
                            if !has_gc {
                                return Some(subs);
                            }
                            (*k == HeapKind::EngineTable && {
                                let a = body.arg_pool[*args][0];
                                const_rooted_addr(body, a)
                            })
                            .then_some(subs)
                        }
                        _ => {
                            if has_gc {
                                return None;
                            }
                            let a = body.arg_pool[*args][0];
                            (!is_frame_addr(body, a, frame_roots)
                                && all_writes.is_empty()
                                && !has_leaf)
                                .then_some(subs)
                        }
                    }
                })();
                if let Some(subs) = hoistable {
                    if !subs.is_empty() {
                        if let ValueDef::Operator(_, args, _) = &body.values[v] {
                            let args = *args;
                            for &(ai, nv) in &subs {
                                body.arg_pool[args][ai] = nv;
                            }
                        }
                    }
                    body.blocks[pre].insts.push(v);
                    def_block[v.index()] = pre.index() as u32;
                    hoisted_total += 1;
                    if let Some(sfx) = load_pcs.get(&v) {
                        crate::diag_line!("night: viz licm sid#{} {} kind clean", sid, sfx);
                    }
                } else {
                    keep.push(v);
                }
            }
            body.blocks[b].insts = keep;
        }
    }
    hoisted_total
}
