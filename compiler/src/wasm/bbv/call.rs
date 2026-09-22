/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Call and construct dispatch: the per-site callee cell, the classify
//! chain, and the generic arms.

use super::*;

/// In-module generic callee classify: `night_call_classify(calleeBoxed,
/// cellAddr, trashAddr) -> (funcidx, script, isNative)`, funcidx 0 = not a
/// dispatchable AOT function.
///
/// The chain below -- function-clasp validation through shape and baseShape,
/// the BaseScript flag, the class-constructor kind test, the nightFuncIndex
/// load and the cell fill -- is byte-for-byte the same work at every call
/// site; only the cell address varies, and that is a parameter. So it is
/// emitted once and called. What stays inline at the site is the per-site
/// cell probe (`emit_inline_classify`), which is the steady state at nearly
/// every site and the reason the cell exists at all.
///
/// `cellAddr` 0 means the site declined a cell: the probe is skipped and
/// nothing is filled.
///
/// A Leaf that writes engine bookkeeping only (the cell row) -- no GC, no
/// user code, no user-visible heap. It lives here rather than in `translate`
/// so it sits next to the inline probe it has to agree with, and reads the
/// same layout constants.
pub fn build_call_classify_helper(m: &mut Module, mem: waffle::Memory, fn_class_slot: u32) -> Func {
    use crate::wasm::translate::RawEmit;
    use waffle::{FuncDecl, SignatureData};
    let sig = m.signatures.push(SignatureData {
        params: vec![Type::I64, Type::I32, Type::I32],
        returns: vec![Type::I32, Type::I32, Type::I32],
    });
    let mut e = RawEmit::new(m, sig, mem);
    let callee_boxed = e.param(0);
    let cell_addr = e.param(1);
    let trash = e.param(2);

    let fail = e.body.add_block();
    let native = e.body.add_block();
    let c1 = e.body.add_block();

    let shift = e.i64c(32);
    let hi64 = e.bin(Operator::I64ShrU, callee_boxed, shift, Type::I64);
    let hi = e.un(Operator::I32WrapI64, hi64, Type::I32);
    let objtag = e.i32c(TAG_OBJECT as u32);
    let is_obj = e.bin(Operator::I32Eq, hi, objtag, Type::I32);
    e.condbr(is_obj, c1, fail);

    // Each arm materializes its own constants: a const is an instruction in
    // the block that made it, and these blocks do not dominate each other.
    e.cur = fail;
    let fz = e.i32c(0);
    e.ret(vec![fz, fz, fz]);
    e.cur = native;
    let nz = e.i32c(0);
    let no = e.i32c(1);
    e.ret(vec![nz, nz, no]);

    e.cur = c1;
    let ptr = e.un(Operator::I32WrapI64, callee_boxed, Type::I32);
    let shape = e.ld32(ptr, SHAPE_OFFSET);
    let base = e.ld32(shape, SHAPE_BASESHAPE_OFFSET);
    let clasp = e.ld32(base, BASESHAPE_CLASP_OFFSET);
    let slot = e.i32c(fn_class_slot);
    let fn_class = e.ld32(slot, 0);
    let ext_class = e.ld32(slot, 4);
    let is_fn = e.bin(Operator::I32Eq, clasp, fn_class, Type::I32);
    let is_ext = e.bin(Operator::I32Eq, clasp, ext_class, Type::I32);
    let is_function = e.bin(Operator::I32Or, is_fn, is_ext, Type::I32);
    let c2 = e.body.add_block();
    e.condbr(is_function, c2, fail);

    e.cur = c2;
    let memarg = e.marg(3, 0);
    let flags_addr = {
        let k = e.i32c(FUNC_FLAGS_SLOT_OFFSET);
        e.bin(Operator::I32Add, ptr, k, Type::I32)
    };
    let slot0 = e.load(Operator::I64Load { memory: memarg }, flags_addr, Type::I64);
    let raw = e.un(Operator::I32WrapI64, slot0, Type::I32);
    let bs_bit = e.i32c(FUNCTION_FLAGS_BASESCRIPT);
    let has_bs = e.bin(Operator::I32And, raw, bs_bit, Type::I32);
    let bs_blk = e.body.add_block();
    e.condbr(has_bs, bs_blk, native);

    e.cur = bs_blk;
    let kind_mask = e.i32c(FUNCTION_KIND_MASK);
    let kind = e.bin(Operator::I32And, raw, kind_mask, Type::I32);
    let class_k = e.i32c(FUNCTION_KIND_CLASS_CTOR);
    let is_class = e.bin(Operator::I32Eq, kind, class_k, Type::I32);
    let c3 = e.body.add_block();
    e.condbr(is_class, fail, c3);

    e.cur = c3;
    let script = e.ld32(ptr, FUNC_SCRIPT_SLOT_OFFSET);
    let idx = e.ld32(script, BASESCRIPT_NIGHTFUNCINDEX_OFFSET);

    // Cell fill, same state machine as the inline version: an empty row
    // learns this callee, a populated row that missed is poisoned with the
    // sentinel so a polymorphic site stops paying the write-back churn. A
    // nursery callee's store is diverted to the shared trash row rather than
    // branched around.
    let has_cell = e.body.add_block();
    let done = e.body.add_block();
    e.condbr(cell_addr, has_cell, done);
    e.cur = has_cell;
    let cached = e.load(Operator::I64Load { memory: memarg }, cell_addr, Type::I64);
    let zero64 = e.i64c(0);
    let was_empty = e.bin(Operator::I64Eq, cached, zero64, Type::I32);
    let fill_blk = e.body.add_block();
    let sent_blk = e.body.add_block();
    e.condbr(was_empty, fill_blk, sent_blk);

    e.cur = fill_blk;
    let mask = e.i32c(NOT_CHUNK_MASK);
    let chunk = e.bin(Operator::I32And, ptr, mask, Type::I32);
    let sb = e.ld32(chunk, CHUNK_STORE_BUFFER_OFFSET);
    let dst = e.sel(Type::I32, trash, cell_addr, sb);
    e.store(Operator::I64Store { memory: memarg }, dst, callee_boxed);
    let fa = {
        let k = e.i32c(CALL_CELL_FUNCIDX);
        e.bin(Operator::I32Add, dst, k, Type::I32)
    };
    let st32 = e.marg(2, 0);
    e.store(Operator::I32Store { memory: st32 }, fa, idx);
    let sa = {
        let k = e.i32c(CALL_CELL_SCRIPT);
        e.bin(Operator::I32Add, dst, k, Type::I32)
    };
    e.store(Operator::I32Store { memory: st32 }, sa, script);
    let z0 = e.i32c(0);
    e.ret(vec![idx, script, z0]);

    e.cur = sent_blk;
    let one64 = e.i64c(1);
    e.store(Operator::I64Store { memory: memarg }, cell_addr, one64);
    let z1 = e.i32c(0);
    e.ret(vec![idx, script, z1]);

    e.cur = done;
    let z2 = e.i32c(0);
    e.ret(vec![idx, script, z2]);

    m.funcs.push(FuncDecl::Body(
        sig,
        "night_call_classify".to_string(),
        e.body,
    ))
}

// --- call dispatch -------------------------------------------------------

impl<'a> Bbv<'a> {
    /// AOT-stack overflow guard for arms that enter an AOT body directly.
    pub(super) fn emit_stack_fits(&mut self, top: Value, argc: u16) -> Value {
        const NIGHT_STACK_HEADROOM: u32 = 64 * 1024;
        let limit = match self.stack_limit_ssa {
            Some(l) => l,
            None => {
                let slot = self.i32_const(self.helpers.night_stack_limit_base);
                self.load_i32(slot, 0)
            }
        };
        let frame_hi = self.add_offset(top, 8 * (2 + u32::from(argc)) + NIGHT_STACK_HEADROOM);
        self.binop(Operator::I32LeU, frame_hi, limit, Type::I32)
    }

    /// Leaf callee classify: returns (funcidx, script, callee_is_native),
    /// funcidx 0 = not a dispatchable AOT function.
    ///
    /// Inline here: the per-site callee value cell probe. The steady state at
    /// nearly every site is one callee repeating, so comparing the boxed
    /// callee against the site's cached `[callee_bits, funcidx, script]` row
    /// is the whole classify on a hit -- without it a call-heavy body spends
    /// several percent of its cycles re-deriving callees through a three-deep
    /// dependent load chain.
    ///
    /// Sound because value identity is object identity: the fill path caches
    /// tenured functions only (a nursery address can be reused by the next
    /// minor GC) and the major-GC callback zeroes the region. A zero row never
    /// false-hits: raw bits 0 is the double +0.0, whose cached funcidx 0
    /// routes the caller to its generic arm anyway.
    ///
    /// Behind the miss: `night_call_classify`, one direct call. The chain it
    /// holds -- clasp validation, the BaseScript flag, the kind test, the
    /// nightFuncIndex load and the cell fill -- is identical at every site and
    /// runs only when the cell missed.
    pub(super) fn emit_inline_classify(&mut self, callee_boxed: Value) -> (Value, Value, Value) {
        let cell = self.call_cell_addr();
        let zero = self.i32_const(0);
        let Some(cell_addr) = cell else {
            // No cell for this site (ContextOnly, or a body over the size
            // gate): the classify is the whole lowering.
            return self.call_i32x3(self.helpers.call_classify, &[callee_boxed, zero, zero]);
        };
        let trash = self.i32_const(CALL_CELL_ADDR_PLACEHOLDER);
        self.call_cell_patches.push((trash, 0));

        let done = self.body.add_block();
        let funcidx_p = self.body.add_blockparam(done, Type::I32);
        let script_p = self.body.add_blockparam(done, Type::I32);
        let native_p = self.body.add_blockparam(done, Type::I32);

        // All three row loads before the branch (always-safe region reads),
        // so a hit needs no block of its own.
        let cached = self.load_i64(cell_addr, 0);
        let f = self.load_i32(cell_addr, CALL_CELL_FUNCIDX);
        let sc = self.load_i32(cell_addr, CALL_CELL_SCRIPT);
        let hit = self.binop(Operator::I64Eq, callee_boxed, cached, Type::I32);
        let miss_blk = self.body.add_block();
        self.body.set_terminator(
            self.cur,
            Terminator::CondBr {
                cond: hit,
                if_true: BlockTarget {
                    block: done,
                    args: vec![f, sc, zero],
                },
                if_false: BlockTarget {
                    block: miss_blk,
                    args: vec![],
                },
            },
        );

        self.cur = miss_blk;
        let (fi, script, native) = self.call_i32x3(
            self.helpers.call_classify,
            &[callee_boxed, cell_addr, trash],
        );
        self.body.set_terminator(
            self.cur,
            Terminator::Br {
                target: BlockTarget {
                    block: done,
                    args: vec![fi, script, native],
                },
            },
        );

        self.cur = done;
        (funcidx_p, script_p, native_p)
    }

    /// The placeholder address const for this call site's value cell, or
    /// None when the site declines one. Interned per `(source_id, evid_pc)`
    /// so the versions of a site share one row; the ContextOnly pass appends
    /// no IR and so claims no cell.
    pub(super) fn call_cell_addr(&mut self) -> Option<Value> {
        if self.mode != EmitMode::Code {
            return None;
        }
        // Size gate: waffle's localify cost is superlinear
        // in blocks/values, and the giant generated bodies this excludes are
        // native-call dominated, where a cell never populates anyway.
        if self.root_script.bytecode.len() > CALL_CELL_SCRIPT_MAX_BYTECODE {
            return None;
        }
        let key = Site::new(self.source_id, Pc::new(self.evid_pc(self.cur_pc).get()));
        let idx = match self.call_cells.get(&key) {
            Some(&i) => i,
            None => {
                let i = self.atoms.next_call_cell();
                self.call_cells.insert(key, i);
                i
            }
        };
        let addr = self.i32_const(CALL_CELL_ADDR_PLACEHOLDER);
        self.call_cell_patches.push((addr, idx + 1));
        Some(addr)
    }

    /// Call/construct dispatch. Non-construct: the lean classify --
    /// `call_indirect` into a compiled AOT callee (keeps AOT->AOT calls off
    /// the EnterNight bounce), generic `night_runtime_call` otherwise. Construct:
    /// the generic `night_runtime_construct` over the same frame (EnterNight
    /// this-substitution).
    pub(super) fn emit_call_op(
        &mut self,
        p: &mut BytecodeParser,
        pc: Pc,
        construct: bool,
        super_call: bool,
    ) -> Result<(), String> {
        let argc = p.next_uint16().unwrap();
        let extra = if construct { 3 } else { 2 };
        let need = usize::from(argc) + extra;
        if self.stack.len() < need {
            return Err(format!("call at pc {pc}: stack underflow"));
        }
        if construct {
            // SuperCall's newTarget is the frame's, not the callee: the
            // splice's nt == callee guard could never pass, so the site
            // goes straight to the classify (whose slow arm handles it).
            if !super_call {
                if let Some(sids) = self.inline_candidates(pc, true) {
                    return self.emit_inline_construct(pc, argc, need, sids[0]);
                }
            }
            // JOF_ARGC: op byte + uint16. The guard is emitted only where
            // the merge stayed on Opt -- where it stepped, its hit arm's
            // refined fact dies at the next edge and the arms that DID
            // stay carry the result value without it.
            if !self.emit_construct_classify(pc, argc, need, None)? {
                self.emit_construct_class_guard(pc, pc + 3);
            }
            return Ok(());
        }
        // Apply-forward: a proven `T.apply(this, arguments)` forward site
        // (the per-script flow check validated this root-space pc; the elided
        // placeholder is the top operand). Forward the caller's own actuals
        // instead of materializing an arguments object.
        if argc == 2 && self.is_hasown_call_site(pc) {
            return self.emit_hasown_call(pc, need);
        }
        if argc == 2 && self.is_apply_fwd_site(pc) {
            if self.opts.diagnostics.bbv {
                crate::diag_line!(
                    "night: bbv apply-fwd sid#{} pc {}",
                    self.source_id,
                    self.evid_pc(pc)
                );
            }
            return self.emit_apply_forward(pc, need);
        }
        if let Some(sids) = self.inline_candidates(pc, false) {
            return self.emit_inline_call(pc, argc, need, &sids);
        }
        self.emit_call_generic(pc, argc, need, true)
    }

    /// The single likely callee script for the call at `pc`, when the site
    /// resolved mono to a compiled script (the frame view un-blinds
    /// segment-interior sites). Class ctors are excluded: their body has no
    /// `[[Call]]`, so entering it from a call site would run it instead of
    /// throwing (`emit_inline_classify` reports funcidx 0 for them).
    pub(super) fn likely_call_target(&self, pc: Pc) -> Option<u32> {
        if self.gen_only {
            return None;
        }
        let sid = self.likely_mono(pc)?;
        let SourceObject::Script(s) = self.source.object(SourceObjectId::new(sid.get())) else {
            return None;
        };
        (!s.is_class_ctor && !s.is_generator_or_async).then_some(sid.get())
    }

    /// The site's single resolved callee, memoized for the current site.
    /// `construct_nslots`, `construct_alloc_word` and both static-target
    /// arms all resolve the same key while emitting one op, and this sits in
    /// the per-version emission path of every call, so the repeated lookups
    /// are measurable compile time on a large bundle.
    pub(super) fn likely_mono(&self, pc: Pc) -> Option<ScriptId> {
        let key = Site::new(self.source_id, self.evid_pc(pc));
        if let Some((k, v)) = self.mono_memo.get() {
            if k == key {
                return v;
            }
        }
        let v = match self.ctx.facts.scripted_targets(key) {
            [sid] => Some(*sid),
            _ => None,
        };
        self.mono_memo.set(Some((key, v)));
        v
    }

    /// The likely callee's effect-summary label, for the fork-site
    /// population diagnostics.
    fn callee_summary_label(&self, likely_sid: Option<u32>) -> String {
        likely_sid
            .and_then(|s| self.ctx.facts.script_effects.get(&ScriptId::new(s)))
            .map_or_else(|| "none".to_string(), crate::facts::EffectSummary::label)
    }

    /// Whether every key in `lo..=hi` provably carries `name` in its
    /// layout row, so a write of `name` to such a receiver is a slot
    /// overwrite -- it can demote no stamp. Missing tables refuse.
    fn name_in_rows(&self, lo: u16, hi: u16, name: crate::ids::NameId) -> bool {
        let facts = &self.ctx.facts;
        if lo == hi {
            if let Some(c) = facts
                .classes
                .get(&crate::ids::LayoutKey::new(u32::from(lo)))
            {
                return c.fields.iter().any(|f| f.name == name);
            }
        }
        facts
            .group_tables
            .get(&crate::ids::LayoutKey::new(u32::from(lo)))
            .is_some_and(|(names, _)| names.contains(&name))
    }

    /// The summary-keep admission: the identity-guarded likely callee's
    /// transitive effect summary cannot demote anything this continuation
    /// carries. Carried state is class identity + SLOTS bits (what
    /// `kill_cls_facts` would kill -- everything else the restore keeps is
    /// frame-resident SSA or re-validated per access: aliased slots are
    /// re-read, gname uses test their fuse, no element state is carried).
    /// Value stores never clear SLOTS, so only add-capable field writes
    /// conflict -- a write of a name outside (or not provably inside) an
    /// overlapping carried class's row. Elems/env/gname writes therefore
    /// pass; a saturated summary refuses.
    fn summary_conflict_free(&self, likely_sid: Option<u32>) -> bool {
        let Some(sid) = likely_sid else {
            return false;
        };
        let Some(e) = self.ctx.facts.script_effects.get(&ScriptId::new(sid)) else {
            return false;
        };
        if e.top {
            return false;
        }
        if e.field_writes.is_empty() {
            return true;
        }
        let mut carried: Vec<(u16, u16)> = Vec::new();
        for c in self
            .locals_ctx
            .iter()
            .chain(self.args_ctx.iter())
            .chain(self.caller_locals_ctx.iter())
            .chain(self.caller_args_ctx.iter())
            .chain(
                self.outer_ctx
                    .iter()
                    .flat_map(|f| f.locals.iter().chain(f.args.iter())),
            )
        {
            if let Some(r) = c.cls {
                if !carried.contains(&r) {
                    carried.push(r);
                }
            }
        }
        for o in &self.stack {
            if let Some(r) = o.cls {
                if !carried.contains(&r) {
                    carried.push(r);
                }
            }
        }
        for &(wr, name) in &e.field_writes {
            for &(lo, hi) in &carried {
                let overlap = wr
                    .is_none_or(|(wl, wh)| wl.get() <= u32::from(hi) && wh.get() >= u32::from(lo));
                if overlap && !self.name_in_rows(lo, hi, name) {
                    return false;
                }
            }
        }
        true
    }

    pub(super) fn emit_call_generic(
        &mut self,
        pc: Pc,
        argc: u16,
        need: usize,
        allow_flag_fork: bool,
    ) -> Result<(), String> {
        self.emit_call_generic_to(pc, argc, need, allow_flag_fork, None, false)
    }

    /// `emit_call_generic` with the likely callee supplied by the caller
    /// rather than read from the site's own call facts.
    ///
    /// The apply-forward fast arm needs this: at `T.apply(this, arguments)`
    /// the site's callee is `apply` itself (a native, so `likely_call_target`
    /// resolves nothing), while the body that actually runs is `T` -- which
    /// the analysis resolves separately into `apply_targets`. Handing it in
    /// lets the whole generic path -- typed entry, the likely-direct arm and
    /// its patch, the effect-flag fork -- apply to a forwarded call
    /// unchanged.
    pub(super) fn emit_call_generic_to(
        &mut self,
        pc: Pc,
        argc: u16,
        need: usize,
        allow_flag_fork: bool,
        likely_override: Option<u32>,
        set_result: bool,
    ) -> Result<(), String> {
        // The generic engine call, or its `CallIter` form: a primitive
        // callee there is "not iterable", not "not a function".
        let call_helper = if matches!(self.op_at(pc), Some(JSOp::CallIter | JSOp::CallContentIter))
        {
            self.helpers.call_iter
        } else {
            self.helpers.call
        };
        // Arm-free outlined form: no fuse/classify/direct/native arms,
        // one call into the engine dispatch. Dirty sites never fork
        // (flag_site is cur_track-gated below), so no admission is lost.
        //
        //
        // A site with no callee fact must not simply take this generic
        // outlined form on either track: a CLASSIFY IS NOT AN ARM. The arm
        // policy targets arms that TEST for a type the prediction did not
        // name; where a prediction names nothing, such arms are dead
        // weight. The call site's inline classify is not that -- it
        // RESOLVES the callee at run time and calls a compiled body
        // directly, succeeding even at unresolved sites where the generic
        // form pays full engine dispatch. Unpredicted is not the same as
        // unproductive.
        if self.outline_generic() && !self.gen_only {
            let n = self.spill_all();
            let frame_off = self.operand_base + 8 * (n - need as u32);
            let frame_base = self.add_offset(self.vp, frame_off);
            let top_off = self.operand_base + 8 * n;
            let top = self.add_offset(self.vp, top_off);
            let argc_v = self.i32_const(u32::from(argc));
            let ok = self.call_i32(call_helper, &[self.cx, top, frame_base, argc_v]);
            self.reload(n);
            let result = self.load_i64(self.vp, top_off);
            self.branch_on_err(ok);
            if set_result {
                let v = self
                    .stack
                    .last()
                    .cloned()
                    .expect("setter call carries a value operand");
                for _ in 0..need {
                    self.stack.pop();
                }
                self.stack.push(v);
                return Ok(());
            }
            for _ in 0..need {
                self.stack.pop();
            }
            if !self.outline_generic() {
                if let (Some(&claim), Some(op)) = (
                    self.ctx
                        .facts
                        .call_types
                        .get(&Site::new(self.source_id, Pc::new(self.evid_pc(pc).get()))),
                    self.cur_op,
                ) {
                    self.push_load_typed(result, claim, pc + op.len(), Prov::C_CALLRET);
                    return Ok(());
                }
            }
            self.push_boxed(result, self.def_type(pc, 0));
            return Ok(());
        }
        let len = self.stack.len();
        let callee_op = self.stack[len - need].clone();
        let callee_boxed = self.to_boxed(&callee_op);
        // The call receiver's classified bit (this / fresh /
        // other) -- decides the fold of returned callee words, the
        // this-only arm's contribution, and the mutating builtin arms
        // (push/pop).
        let recv_bit = if need >= 2 {
            self.store_recv_bit(&self.stack[len - need + 1])
        } else {
            FLAG_MUT_OTHER
        };
        // The typed-entry proof reads the argument operands' facts, so it
        // runs before the spill. Only the two static-target arms may use
        // it -- the `call_indirect` fallback dispatches on a runtime
        // funcidx and must pass a plain argc.
        let likely_sid = likely_override.or_else(|| self.likely_call_target(pc));
        let sel_argc = match likely_sid {
            Some(sid) if self.callee_entry_proven(sid, argc, need) => {
                if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
                    crate::diag_line!(
                        "night: bbv typed-call sid#{} pc {} callee {sid}",
                        self.source_id,
                        self.evid_pc(pc)
                    );
                }
                u32::from(argc) | ARGC_SEL_BIT
            }
            _ => u32::from(argc),
        };

        let n = self.spill_all();
        let frame_off = self.operand_base + 8 * (n - need as u32);
        let frame_base = self.add_offset(self.vp, frame_off);
        let top_off = self.operand_base + 8 * n;
        let top = self.add_offset(self.vp, top_off);
        let fits = self.emit_stack_fits(top, argc);

        // Flag-site gate (call-round part 2): only when the resolved
        // callee's bytecode passes the heap-readonly scan can a clean
        // (err = 0, eff = 1) return ever come back, so only such sites pay
        // the fork. The saved pre-call state (post-spill: the frame is
        // truth, dirty marks clear) is what the clean lineage resumes.
        let next_pc = self.cur_op.map(|op| pc + op.len());
        // A Dirty-lineage site has nothing to save: the restored state
        // would be the same dead facts, so the fork is pure overhead there
        // -- and in a call-heavy loop that is every site in the loop.
        let callee_scan = likely_sid.and_then(|sid| {
            let src = self.source;
            match src.object(SourceObjectId::new(sid)) {
                SourceObject::Script(cs) => Some(self.ret_clean_for(ScriptId::new(sid), cs)),
                _ => None,
            }
        });
        // ReadOnly callees only: the population the fork actually lands
        // clean on.
        //
        // Spliced code forks too. Whether a lineage may stay clean does not
        // depend on which frame the emitter is spliced into: `emit_clean_cont`
        // addresses every slot through the active frame view, and
        // `fold_callee_flags` is identity on a zero word, so the clean test
        // reads the same in a segment as at the root. The one thing that
        // genuinely is root-only is receiver classification, and
        // `store_recv_bit` already refuses MUT_THIS inside a segment.
        // Any callee whose word can come back stamps-clean forks:
        // ReadOnly (the clean arm's population), StoreOnly (the keep-facts
        // arm's population), and UNRESOLVED callees too, now that the arm
        // needs no callee knowledge at all -- the runtime word decides,
        // and an interpreted or unscanned target simply returns a
        // saturated word and takes the dirty arm. Known-scan-failed
        // callees fork too: their word always saturates (the clean arm is
        // dead), but the EPOCH comparison still admits the keep-facts arm
        // -- a scan failure says the analysis gave up, not that stamps
        // die.
        let flag_site = allow_flag_fork
            && !self.gen_only
            && self.cur_track != Track::Dirty
            && next_pc.is_some();
        // Which gate turned a call site down, so the population limiter is
        // a number rather than a guess. The clean arm restores the whole
        // pre-call state, so every site that does NOT fork is a site whose
        // continuation is Dirty for the rest of the body.
        if self.opts.diagnostics.bbv && self.mode == EmitMode::Code && !flag_site {
            let why = if !allow_flag_fork {
                "noallow"
            } else if self.gen_only {
                "gen"
            } else if self.cur_track == Track::Dirty {
                "dirty"
            } else if next_pc.is_none() {
                "nonext"
            } else {
                match callee_scan {
                    None => "nolikely",
                    Some(ScanClass::StoreOnly) => "scan-storeonly",
                    Some(ScanClass::Fail) => "scan-fail",
                    Some(ScanClass::ReadOnly) => "unreachable",
                }
            };
            crate::diag_line!(
                "night: bbv flagsite-miss sid#{} pc {} why {why} track {:?} summary {}",
                self.source_id,
                self.evid_pc(pc),
                self.cur_track,
                self.callee_summary_label(likely_sid),
            );
        }
        // Summary-keep admission for the identity-guarded scripted arms
        // (fuse and likely-direct; the indirect arm has no callee and
        // keeps the runtime word/epoch admission). Mapped-args frames
        // refuse, mirroring the word==0-only rule: a callee holding
        // `arguments` can write this frame's formals without moving a stamp.
        let summary_keep =
            flag_site && !self.mapped_args_reachable() && self.summary_conflict_free(likely_sid);
        let pre_call = if flag_site {
            if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
                crate::diag_line!(
                    "night: bbv flag-site sid#{} pc {} callee {} arms {} recv {} summary {} sumkeep {}",
                    self.source_id,
                    self.evid_pc(pc),
                    likely_sid.unwrap_or(u32::MAX),
                    2,
                    recv_bit,
                    self.callee_summary_label(likely_sid),
                    u8::from(summary_keep),
                );
            }
            Some(self.arm_state())
        } else {
            None
        };
        // The fork-site epoch sample: taken on the op's main line so it
        // dominates every arm, compared in the fork's keep-facts test. It
        // is the runtime ground truth that rescues callees whose WORD is
        // saturated by helper calls (a helper that ran but demoted nothing
        // keeps the epoch still) -- the per-helper accumulator bridge is
        // impossible (minted words escape merge-back arms, section-Z).
        let pre_epoch = pre_call.is_some().then(|| self.emit_epoch_read());
        let pre_bind = pre_call.as_ref().and_then(|_| self.sample_bind_epoch());
        // Builtin-arm clean fork: an unresolved site whose call-free numeric
        // builtin arms (Math/clz32/imul/parseInt) can hit executes no helper
        // and touches no heap on the hit path, so the arm's success exit is
        // a proven-clean continuation -- no flag test needed, the arm
        // selection is the proof. Same population gates as the flag fork
        // (non-Dirty lineage, spliced code included); without this, the arm's
        // exit joins the generic merge and the whole continuation inherits
        // the helper arm's Dirty join -- one coercion builtin called at a
        // function's top is then enough to keep every loop header below it
        // Dirty.
        let native_site = self
            .ctx
            .facts
            .is_native_call(Site::new(self.source_id, self.evid_pc(pc)));
        // The dense push arm's admission (`script_names_push`) also arms
        // the state: its success exit is a keep continuation (the arm ran
        // helper-free; the append wrote elements only) rather than the
        // generic merge's Dirty join.
        let push_site = argc == 1 && likely_sid.is_none() && self.script_names_push();
        let pre_builtin = if allow_flag_fork
            && !self.gen_only
            && self.cur_track != Track::Dirty
            && next_pc.is_some()
            && likely_sid.is_none()
            && argc <= 2
            && (native_site || push_site)
        {
            if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
                crate::diag_line!(
                    "night: bbv builtin-flag-site sid#{} pc {}",
                    self.source_id,
                    self.evid_pc(pc),
                );
            }
            Some(self.arm_state())
        } else {
            None
        };
        // The native route's keep-facts state: an unresolved `.call`/`.apply`
        // -shaped site whose callee classifies native at run time (e.g. a
        // `hasOwnProperty.call(props, name)` loop) gets the epoch-proven
        // keep continuation the scripted fork has, with no static callee
        // knowledge: the epoch is the proof. Population: the syntactic
        // apply/call sites plus the builtin-armed ones -- arming every
        // unresolved site costs code and guard overhead at sites that
        // never classify native, so the population is restricted to the
        // shapes likely to hit. Refused under a mapped arguments object,
        // where a native reached through `fun_call` could rewrite this
        // frame's formals without moving a stamp.
        let call_shaped = self
            .ctx
            .facts
            .apply_sites
            .contains_key(&Site::new(self.source_id, self.evid_pc(pc)))
            || self
                .gname_method_pcs
                .contains(&Site::new(self.source_id, self.evid_pc(pc)));
        let pre_native = if allow_flag_fork
            && !self.gen_only
            && self.cur_track != Track::Dirty
            && next_pc.is_some()
            && likely_sid.is_none()
            && !self.mapped_args_reachable()
            && (call_shaped || pre_builtin.is_some())
        {
            pre_builtin.clone().or_else(|| Some(self.arm_state()))
        } else {
            None
        };

        // The native route and the generic call take the keep arm under
        // EITHER pre-state: a flag site's (a resolved callee that is not
        // compiled, or classified away at run time -- react's closure
        // callbacks, the self-hosted `callFunction` sites) as well as
        // `pre_native`'s. The epoch is the proof either way.
        let pre_keep = pre_native.clone().or_else(|| pre_call.clone());
        if self.opts.diagnostics.bbv && self.mode == EmitMode::Code && pre_keep.is_some() {
            crate::diag_line!(
                "night: bbv keep-site sid#{} pc {} form call{}",
                self.source_id,
                self.evid_pc(pc),
                if pre_native.is_some() { "-native" } else { "" }
            );
        }

        let merge = self.body.add_block();
        let ok_param = self.body.add_blockparam(merge, Type::I32);
        let merge_flags_param = self
            .flags_threading()
            .then(|| self.body.add_blockparam(merge, Type::I32));

        // Fuse-guarded direct call. When the callee was read from
        // GetGName of binding B and B's value fuse is armed with these very
        // bits, arm-time validation already proved the value's AOT target is
        // the predicted body: two loads and two compares replace the whole
        // classify (five validating loads plus its branch chain), and the
        // `call` target is static so wasmtime can inline it. The cell also
        // caches the callee's JSScript* (word 3) for the compiled-body ABI. A blown or
        // differently-valued binding just falls through to the classify.
        // Resolved once (above, for the typed-entry proof): both
        // static-target arms key on it, and this sits in the per-version
        // emission path of every call site, so repeating the lookup is
        // measurable compile time on a large bundle.
        if let (Some(&bid), Some(sid)) = (
            likely_sid.and_then(|_| {
                self.gname_call_bids
                    .get(&Site::new(self.source_id, self.evid_pc(pc)))
            }),
            likely_sid,
        ) {
            let vals_addr = self.helpers.global_vals_base + 16 * bid;
            let vals = self.i32_const(vals_addr);
            let fw = self.load_i32(vals, 8);
            let one = self.i32_const(1);
            let armed = self.binop(Operator::I32Eq, fw, one, Type::I32);
            let bits = self.load_i64(vals, 0);
            let same = self.binop(Operator::I64Eq, callee_boxed, bits, Type::I32);
            let enabled = self.i32_const(0);
            let hs = self.binop(Operator::I32And, armed, same, Type::I32);
            let hs_fits = self.binop(Operator::I32And, hs, fits, Type::I32);
            let hit = self.binop(Operator::I32And, hs_fits, enabled, Type::I32);
            let fuse_blk = self.body.add_block();
            let classify_blk = self.body.add_block();
            self.cond_br(hit, fuse_blk, classify_blk);
            self.cur = fuse_blk;
            let script_c = self.load_i32(vals, 12);
            let argc_v = self.i32_const(sel_argc);
            let undef_nt = self.boxed_const(TAG_UNDEFINED << 32);
            let fargs = [self.cx, frame_base, argc_v, top, script_c, undef_nt];
            let (callv, err, eff) = self.call_abi2(self.helpers.direct_call_stub2, &fargs);
            self.fuse_call_patches.push(FuseCallPatch {
                enabled,
                call: callv,
                binding: bid,
                callee: ScriptId::new(sid),
            });
            let ok_fuse = self.unop(Operator::I32Eqz, err, Type::I32);
            if let Some(pre) = pre_call.as_ref() {
                let pre = pre.clone();
                self.emit_flag_fork(
                    ok_fuse,
                    eff,
                    recv_bit,
                    &pre,
                    need,
                    top_off,
                    next_pc.expect("flag_site implies next_pc"),
                    merge,
                    pre_epoch,
                    pre_bind,
                    set_result,
                    summary_keep,
                );
            } else {
                let saved = self.cur_flags;
                let efff = self.fold_callee_flags(eff, recv_bit);
                self.or_flags_word(efff);
                let margs = self.merge_args(ok_fuse);
                self.cur_flags = saved;
                self.body.set_terminator(
                    self.cur,
                    Terminator::Br {
                        target: BlockTarget {
                            block: merge,
                            args: margs,
                        },
                    },
                );
            }
            self.cur = classify_blk;
        }

        // Likely-callee direct arm, for every site the fuse channel does not
        // cover (no global binding behind the callee, or its fuse blown):
        // compare the classified funcidx against the callee's table index (a
        // patched const; `u32::MAX` = callee uncompiled -> arm dead) and
        // `call` the body statically on match. A wrong likely just misses
        // into the `call_indirect` below.
        let expected = likely_sid.map(|_| self.i32_const(u32::MAX));

        let (funcidx, script, callee_native) = self.emit_inline_classify(callee_boxed);
        let direct_blk = self.body.add_block();
        let fallback_blk = self.body.add_block();
        let zero_g = self.i32_const(0);
        let dispatchable = self.binop(Operator::I32Ne, funcidx, zero_g, Type::I32);
        let take_fast = self.binop(Operator::I32And, dispatchable, fits, Type::I32);
        self.body.set_terminator(
            self.cur,
            Terminator::CondBr {
                cond: take_fast,
                if_true: BlockTarget {
                    block: direct_blk,
                    args: vec![],
                },
                if_false: BlockTarget {
                    block: fallback_blk,
                    args: vec![],
                },
            },
        );

        self.cur = direct_blk;
        let argc_v = self.i32_const(u32::from(argc));
        let undef_nt = self.boxed_const(TAG_UNDEFINED << 32);
        let args = [self.cx, frame_base, argc_v, top, script, undef_nt];
        if let (Some(sid), Some(expected)) = (likely_sid, expected) {
            let sel_argc_v = self.i32_const(sel_argc);
            let sel_args = [self.cx, frame_base, sel_argc_v, top, script, undef_nt];
            let likely_blk = self.body.add_block();
            let indirect_blk = self.body.add_block();
            let is_likely = self.binop(Operator::I32Eq, funcidx, expected, Type::I32);
            self.cond_br(is_likely, likely_blk, indirect_blk);
            self.cur = likely_blk;
            let (callv, err, eff) = self.call_abi2(self.helpers.direct_call_stub2, &sel_args);
            self.likely_patches.push((expected, callv, sid));
            let ok_likely = self.unop(Operator::I32Eqz, err, Type::I32);
            if let Some(pre) = pre_call.as_ref() {
                let pre = pre.clone();
                self.emit_flag_fork(
                    ok_likely,
                    eff,
                    recv_bit,
                    &pre,
                    need,
                    top_off,
                    next_pc.expect("flag_site implies next_pc"),
                    merge,
                    pre_epoch,
                    pre_bind,
                    set_result,
                    summary_keep,
                );
            } else {
                let saved = self.cur_flags;
                let efff = self.fold_callee_flags(eff, recv_bit);
                self.or_flags_word(efff);
                let margs = self.merge_args(ok_likely);
                self.cur_flags = saved;
                self.body.set_terminator(
                    self.cur,
                    Terminator::Br {
                        target: BlockTarget {
                            block: merge,
                            args: margs,
                        },
                    },
                );
            }
            self.cur = indirect_blk;
        }
        let (_iv, err, eff) = self.call_indirect_abi2(&args, funcidx);
        let ok_direct = self.unop(Operator::I32Eqz, err, Type::I32);
        if let Some(pre) = pre_call.as_ref() {
            let pre = pre.clone();
            self.emit_flag_fork(
                ok_direct,
                eff,
                recv_bit,
                &pre,
                need,
                top_off,
                next_pc.expect("flag_site implies next_pc"),
                merge,
                pre_epoch,
                pre_bind,
                set_result,
                false,
            );
        } else {
            let saved = self.cur_flags;
            let efff = self.fold_callee_flags(eff, recv_bit);
            self.or_flags_word(efff);
            let margs = self.merge_args(ok_direct);
            self.cur_flags = saved;
            self.body.set_terminator(
                self.cur,
                Terminator::Br {
                    target: BlockTarget {
                        block: merge,
                        args: margs,
                    },
                },
            );
        }

        self.cur = fallback_blk;
        // Math builtin arms. These match the callee by native pointer
        // against the pristine `math_natives_base` slot, not by value
        // identity: self-hosted code calls the std_Math_* intrinsic clones
        // (distinct JSFunction objects wrapping the same JSNative). A
        // monkeypatched Math.sqrt is a different JSNative, so the compare
        // self-misses and the site falls to the helper -- no fuse hooks
        // needed. `native_fn` is the callee's JSNative behind the
        // `callee_native` proof (an unguarded load off a non-object Value
        // could trap), else the sentinel 1, which is never a slot value.
        // Only where a native callee is plausible: a site whose profile
        // predicts a scripted callee would just carry dead diamonds.
        let builtin_arms = likely_sid.is_none();
        let native_fn = if builtin_arms {
            let nf_blk = self.body.add_block();
            let join = self.body.add_block();
            let nf_p = self.body.add_blockparam(join, Type::I32);
            let sentinel = self.i32_const(1);
            self.body.set_terminator(
                self.cur,
                Terminator::CondBr {
                    cond: callee_native,
                    if_true: BlockTarget {
                        block: nf_blk,
                        args: vec![],
                    },
                    if_false: BlockTarget {
                        block: join,
                        args: vec![sentinel],
                    },
                },
            );
            self.cur = nf_blk;
            let cp = self.unop(Operator::I32WrapI64, callee_boxed, Type::I32);
            let nf = self.load_i32(cp, FUNC_ENV_SLOT_OFFSET);
            self.body.set_terminator(
                self.cur,
                Terminator::Br {
                    target: BlockTarget {
                        block: join,
                        args: vec![nf],
                    },
                },
            );
            self.cur = join;
            Some(nf_p)
        } else {
            None
        };
        let mn_is = |s: &mut Self, nf: Value, idx: u32| {
            let c = s.i32_const(s.helpers.math_natives_base + 4 * idx);
            let slot = s.load_i32(c, 0);
            s.binop(Operator::I32Eq, nf, slot, Type::I32)
        };
        // The cell arms match the callee by value identity against a cached
        // pristine builtin, so a monkeypatched `push`/`charCodeAt` hands the
        // site a different callee value and the compare self-misses -- no
        // fuse hooks needed.
        let bc_is = |s: &mut Self, idx: u32| {
            let c = s.i32_const(s.helpers.builtin_cells_base + 8 * idx);
            let bits = s.load_i64(c, 0);
            s.binop(Operator::I64Eq, callee_boxed, bits, Type::I32)
        };
        // Array.prototype.push dense append, call-free. Legacy's arm needs
        // the `no_extra_indexed` call, and the standing law is that a call
        // in a hot diamond costs several percent even when it never
        // executes. The proto check rides the append-cache row instead, exactly
        // as `emit_elem_append_arm`: a row hit pins the receiver shape, the
        // row's cached proto pointers are checked against their live shape
        // words (an indexed prop appearing on a proto forces a proto shape
        // change), and row[20] says the receiver was an Array at prime
        // time -- which the `length`-word bump below requires. The runtime
        // primes the row on its own push fast path, so a pure-push
        // workload arms the row on its first (helper) push.
        if argc == 1 && builtin_arms && self.script_names_push() {
            self.builtin_arm(|s, helper_blk| {
                let this_boxed = s.load_i64(s.vp, frame_off + 8);
                let arg_boxed = s.load_i64(s.vp, frame_off + 16);
                let is_push = bc_is(s, BC_ARR_PUSH);
                let this_obj = s.tag_eq(this_boxed, TAG_OBJECT as u32);
                let m = s.binop(Operator::I32And, is_push, this_obj, Type::I32);
                let hdr_blk = s.body.add_block();
                s.cond_br(m, hdr_blk, helper_blk);
                s.cur = hdr_blk;
                let objptr = s.unop(Operator::I32WrapI64, this_boxed, Type::I32);
                let elements = s.load_i32(objptr, OBJ_ELEMENTS_OFFSET);
                let back = |s: &mut Self, k: u32| {
                    let kc = s.i32_const(k);
                    s.binop(Operator::I32Sub, elements, kc, Type::I32)
                };
                let flags_addr = back(s, ELEMENTS_FLAGS_BACK);
                let flags = s.load_i32(flags_addr, 0);
                let initlen_addr = back(s, ELEMENTS_INITLEN_BACK);
                let initlen = s.load_i32(initlen_addr, 0);
                let cap_addr = back(s, ELEMENTS_CAPACITY_BACK);
                let cap = s.load_i32(cap_addr, 0);
                let len_addr = back(s, ELEMENTS_LENGTH_BACK);
                let len = s.load_i32(len_addr, 0);
                let bail_mask = s.i32_const(ELEMENTS_PUSH_BAIL_MASK);
                let bail_bits = s.binop(Operator::I32And, flags, bail_mask, Type::I32);
                let flags_ok = s.unop(Operator::I32Eqz, bail_bits, Type::I32);
                let len_eq = s.binop(Operator::I32Eq, len, initlen, Type::I32);
                let has_cap = s.binop(Operator::I32LtU, initlen, cap, Type::I32);
                let int_max = s.i32_const(0x7FFF_FFFF);
                let len_fits = s.binop(Operator::I32LtU, len, int_max, Type::I32);
                let ok_a = s.binop(Operator::I32And, flags_ok, len_eq, Type::I32);
                let ok_b = s.binop(Operator::I32And, has_cap, len_fits, Type::I32);
                let pre_ok = s.binop(Operator::I32And, ok_a, ok_b, Type::I32);
                let probe_blk = s.body.add_block();
                s.cond_br(pre_ok, probe_blk, helper_blk);
                s.cur = probe_blk;
                let shape = s.load_i32(objptr, SHAPE_OFFSET);
                let three_s = s.i32_const(3);
                let sh = s.binop(Operator::I32ShrU, shape, three_s, Type::I32);
                let k1 = s.i32_const(2654435761);
                let h = s.binop(Operator::I32Mul, sh, k1, Type::I32);
                let rmask = s.i32_const(APPEND_CACHE_SIZE - 1);
                let ridx = s.binop(Operator::I32And, h, rmask, Type::I32);
                let stride = s.i32_const(APPEND_CACHE_ENTRY_BYTES);
                let roff = s.binop(Operator::I32Mul, ridx, stride, Type::I32);
                let base = s.i32_const(s.helpers.append_cache_base);
                let row = s.binop(Operator::I32Add, base, roff, Type::I32);
                let row_shape = s.load_i32(row, 0);
                let row_hit = s.binop(Operator::I32Eq, shape, row_shape, Type::I32);
                let is_arr = s.load_i32(row, 20);
                let zero_a = s.i32_const(0);
                let arr_ok = s.binop(Operator::I32Ne, is_arr, zero_a, Type::I32);
                let hit_arr = s.binop(Operator::I32And, row_hit, arr_ok, Type::I32);
                let pguard_blk = s.body.add_block();
                s.cond_br(hit_arr, pguard_blk, helper_blk);
                s.cur = pguard_blk;
                let p0 = s.load_i32(row, 4);
                let s0 = s.load_i32(row, 8);
                let live0 = s.load_i32(p0, SHAPE_OFFSET);
                let p0_empty = s.unop(Operator::I32Eqz, p0, Type::I32);
                let m0 = s.binop(Operator::I32Eq, live0, s0, Type::I32);
                let ok0 = s.binop(Operator::I32Or, p0_empty, m0, Type::I32);
                let p1 = s.load_i32(row, 12);
                let s1 = s.load_i32(row, 16);
                let live1 = s.load_i32(p1, SHAPE_OFFSET);
                let p1_empty = s.unop(Operator::I32Eqz, p1, Type::I32);
                let m1 = s.binop(Operator::I32Eq, live1, s1, Type::I32);
                let ok1 = s.binop(Operator::I32Or, p1_empty, m1, Type::I32);
                let pok = s.binop(Operator::I32And, ok0, ok1, Type::I32);
                let store_blk = s.body.add_block();
                s.cond_br(pok, store_blk, helper_blk);
                s.cur = store_blk;
                let three = s.i32_const(3);
                let off = s.binop(Operator::I32Shl, initlen, three, Type::I32);
                let elem_addr = s.binop(Operator::I32Add, elements, off, Type::I32);
                let se = s.store_i64(elem_addr, 0, arg_boxed);
                s.tag_store(se, HeapKind::Elements);
                let one_i = s.i32_const(1);
                let newlen = s.binop(Operator::I32Add, initlen, one_i, Type::I32);
                let si = s.store_i32(initlen_addr, 0, newlen);
                s.tag_store(si, HeapKind::ElementsHeader);
                let sl = s.store_i32(len_addr, 0, newlen);
                s.tag_store(sl, HeapKind::ElementsHeader);
                s.emit_post_write_barrier_elem(this_boxed, initlen, arg_boxed);
                let result = s.box_int32(newlen);
                s.store_i64(s.vp, top_off, result);
                // The append mutated the receiver -- the continuation's
                // flags must carry the classified bit (scoped: the minted
                // OR must not leak into sibling arms). With the arm state
                // armed this is a keep continuation: the arm ran
                // helper-free and wrote elements only, so the value facts
                // and the track survive the append.
                s.builtin_mut_success_exit(&pre_keep, need, top_off, next_pc, merge, recv_bit);
            });
        }
        // Array.prototype.pop dense shrink. Bails under an active incremental
        // marking barrier (dropping the element drops a reference mid-mark)
        // and on a hole in the last slot (proto-lookup semantics).
        if argc == 0 && builtin_arms {
            self.builtin_arm(|s, helper_blk| {
                let this_boxed = s.load_i64(s.vp, frame_off + 8);
                let is_pop = bc_is(s, BC_ARR_POP);
                let this_obj = s.tag_eq(this_boxed, TAG_OBJECT as u32);
                let m = s.binop(Operator::I32And, is_pop, this_obj, Type::I32);
                let arr_blk = s.body.add_block();
                s.cond_br(m, arr_blk, helper_blk);
                s.cur = arr_blk;
                let objptr = s.unop(Operator::I32WrapI64, this_boxed, Type::I32);
                let shape = s.load_i32(objptr, SHAPE_OFFSET);
                let base = s.load_i32(shape, SHAPE_BASESHAPE_OFFSET);
                let clasp = s.load_i32(base, BASESHAPE_CLASP_OFFSET);
                let aslot = s.i32_const(s.helpers.array_class_slot);
                let arr_class = s.load_i32(aslot, 0);
                let is_arr = s.binop(Operator::I32Eq, clasp, arr_class, Type::I32);
                let hdr_blk = s.body.add_block();
                s.cond_br(is_arr, hdr_blk, helper_blk);
                s.cur = hdr_blk;
                let elements = s.load_i32(objptr, OBJ_ELEMENTS_OFFSET);
                let back = |s: &mut Self, k: u32| {
                    let kc = s.i32_const(k);
                    s.binop(Operator::I32Sub, elements, kc, Type::I32)
                };
                let flags_addr = back(s, ELEMENTS_FLAGS_BACK);
                let flags = s.load_i32(flags_addr, 0);
                let initlen_addr = back(s, ELEMENTS_INITLEN_BACK);
                let initlen = s.load_i32(initlen_addr, 0);
                let len_addr = back(s, ELEMENTS_LENGTH_BACK);
                let len = s.load_i32(len_addr, 0);
                let bail_mask = s.i32_const(ELEMENTS_POP_BAIL_MASK);
                let bail_bits = s.binop(Operator::I32And, flags, bail_mask, Type::I32);
                let zero_f = s.i32_const(0);
                let flags_ok = s.binop(Operator::I32Eq, bail_bits, zero_f, Type::I32);
                let len_eq = s.binop(Operator::I32Eq, len, initlen, Type::I32);
                let zero_l = s.i32_const(0);
                let len_pos = s.binop(Operator::I32Ne, len, zero_l, Type::I32);
                let zone = s.load_i32(s.cx, JSCONTEXT_ZONE_OFFSET);
                let needs = s.load_i32(zone, ZONE_NEEDS_BARRIER_OFFSET);
                let zero_n = s.i32_const(0);
                let no_barrier = s.binop(Operator::I32Eq, needs, zero_n, Type::I32);
                let ok_a = s.binop(Operator::I32And, flags_ok, len_eq, Type::I32);
                let ok_b = s.binop(Operator::I32And, len_pos, no_barrier, Type::I32);
                let ok = s.binop(Operator::I32And, ok_a, ok_b, Type::I32);
                let read_blk = s.body.add_block();
                s.cond_br(ok, read_blk, helper_blk);
                s.cur = read_blk;
                let one_i = s.i32_const(1);
                let newlen = s.binop(Operator::I32Sub, len, one_i, Type::I32);
                let three = s.i32_const(3);
                let off = s.binop(Operator::I32Shl, newlen, three, Type::I32);
                let elem_addr = s.binop(Operator::I32Add, elements, off, Type::I32);
                let elem = s.load_i64(elem_addr, 0);
                let is_hole = s.tag_eq(elem, TAG_MAGIC as u32);
                let shrink_blk = s.body.add_block();
                s.cond_br(is_hole, helper_blk, shrink_blk);
                s.cur = shrink_blk;
                let si = s.store_i32(initlen_addr, 0, newlen);
                s.tag_store(si, HeapKind::ElementsHeader);
                let sl = s.store_i32(len_addr, 0, newlen);
                s.tag_store(sl, HeapKind::ElementsHeader);
                s.store_i64(s.vp, top_off, elem);
                // The shrink mutated the receiver (see the push arm).
                s.builtin_mut_success_exit(&pre_keep, need, top_off, next_pc, merge, recv_bit);
            });
        }
        if let (1, Some(nf)) = (argc, native_fn) {
            self.builtin_arm(|s, helper_blk| {
                let arg_boxed = s.load_i64(s.vp, frame_off + 16);
                let is_sqrt = mn_is(s, nf, MN_SQRT);
                let is_abs = mn_is(s, nf, MN_ABS);
                let is_floor = mn_is(s, nf, MN_FLOOR);
                let is_ceil = mn_is(s, nf, MN_CEIL);
                let is_trunc = mn_is(s, nf, MN_TRUNC);
                let is_fround = mn_is(s, nf, MN_FROUND);
                let is_sin = mn_is(s, nf, MN_SIN);
                let is_cos = mn_is(s, nf, MN_COS);
                let or_a = s.binop(Operator::I32Or, is_sqrt, is_abs, Type::I32);
                let or_b = s.binop(Operator::I32Or, is_floor, is_sin, Type::I32);
                let or_c = s.binop(Operator::I32Or, is_ceil, is_trunc, Type::I32);
                let or_d = s.binop(Operator::I32Or, is_fround, is_cos, Type::I32);
                let or_ab = s.binop(Operator::I32Or, or_a, or_b, Type::I32);
                let or_cd = s.binop(Operator::I32Or, or_c, or_d, Type::I32);
                let any = s.binop(Operator::I32Or, or_ab, or_cd, Type::I32);
                let arg_num = s.is_number_tag(arg_boxed);
                let m = s.binop(Operator::I32And, any, arg_num, Type::I32);
                let math_blk = s.body.add_block();
                s.cond_br(m, math_blk, helper_blk);
                s.cur = math_blk;
                let f = s.unbox_number_f64(arg_boxed);
                let done_blk = s.body.add_block();
                let res_p = s.body.add_blockparam(done_blk, Type::F64);
                let is_trig = s.binop(Operator::I32Or, is_sin, is_cos, Type::I32);
                let trig_blk = s.body.add_block();
                let opc_blk = s.body.add_block();
                s.cond_br(is_trig, trig_blk, opc_blk);
                s.cur = trig_blk;
                let r_trig = s.call_f64(s.helpers.math_unary, &[is_cos, f]);
                s.body.set_terminator(
                    s.cur,
                    Terminator::Br {
                        target: BlockTarget {
                            block: done_blk,
                            args: vec![r_trig],
                        },
                    },
                );
                s.cur = opc_blk;
                let r_sqrt = s.unop(Operator::F64Sqrt, f, Type::F64);
                let r_abs = s.unop(Operator::F64Abs, f, Type::F64);
                let r_floor = s.unop(Operator::F64Floor, f, Type::F64);
                let r_ceil = s.unop(Operator::F64Ceil, f, Type::F64);
                let r_trunc = s.unop(Operator::F64Trunc, f, Type::F64);
                let f32v = s.unop(Operator::F32DemoteF64, f, Type::F32);
                let r_fround = s.unop(Operator::F64PromoteF32, f32v, Type::F64);
                // Priority chain (exactly one is_* holds under `any`).
                let sel = s.select(Type::F64, r_trunc, r_fround, is_trunc);
                let sel = s.select(Type::F64, r_ceil, sel, is_ceil);
                let sel = s.select(Type::F64, r_floor, sel, is_floor);
                let sel_af = s.select(Type::F64, r_abs, sel, is_abs);
                let r_opc = s.select(Type::F64, r_sqrt, sel_af, is_sqrt);
                s.body.set_terminator(
                    s.cur,
                    Terminator::Br {
                        target: BlockTarget {
                            block: done_blk,
                            args: vec![r_opc],
                        },
                    },
                );
                s.cur = done_blk;
                let resb = s.box_f64_canonical(res_p);
                s.store_i64(s.vp, top_off, resb);
                s.builtin_success_exit(&pre_keep, need, top_off, next_pc, merge);
            });
        }
        // Math.clz32: ToUint32(number) then wasm `i32.clz` (clz32(0) = 32,
        // which i32.clz gives). |f| < 2^63 truncates exactly and i32.clz
        // reads the same 32-bit pattern ToUint32 would produce.
        if let (1, Some(nf)) = (argc, native_fn) {
            self.builtin_arm(|s, helper_blk| {
                let arg_boxed = s.load_i64(s.vp, frame_off + 16);
                let is_clz = mn_is(s, nf, MN_CLZ32);
                let arg_num = s.is_number_tag(arg_boxed);
                let m = s.binop(Operator::I32And, is_clz, arg_num, Type::I32);
                let clz_blk = s.body.add_block();
                s.cond_br(m, clz_blk, helper_blk);
                s.cur = clz_blk;
                let f = s.unbox_number_f64(arg_boxed);
                let af = s.unop(Operator::F64Abs, f, Type::F64);
                let lim = s.f64_const(9223372036854775808.0);
                let in_range = s.binop(Operator::F64Lt, af, lim, Type::I32);
                let do_blk = s.body.add_block();
                s.cond_br(in_range, do_blk, helper_blk);
                s.cur = do_blk;
                let i = s.to_int32_from_f64(f);
                let clz = s.unop(Operator::I32Clz, i, Type::I32);
                let res = s.box_int32(clz);
                s.store_i64(s.vp, top_off, res);
                s.builtin_success_exit(&pre_keep, need, top_off, next_pc, merge);
            });
        }
        // parseInt(x), 1-arg: an int32 is an identity (base-10 reparse of
        // ToString(int32) is the int). A double truncates toward zero only
        // when the result provably matches the parse of its positional
        // decimal string -- integral part fits int32 and (|x| >= 1e-6 or
        // x == +-0), since smaller magnitudes ToString to exponent notation
        // where parseInt reads the mantissa.
        if argc == 1 && builtin_arms {
            self.builtin_arm(|s, helper_blk| {
                let arg_boxed = s.load_i64(s.vp, frame_off + 16);
                let is_pi = bc_is(s, BC_PARSE_INT);
                let pi_blk = s.body.add_block();
                s.cond_br(is_pi, pi_blk, helper_blk);
                s.cur = pi_blk;
                let is_int = s.tag_eq(arg_boxed, TAG_INT32 as u32);
                let int_blk = s.body.add_block();
                let dbl_chk_blk = s.body.add_block();
                s.cond_br(is_int, int_blk, dbl_chk_blk);
                s.cur = int_blk;
                s.store_i64(s.vp, top_off, arg_boxed);
                s.builtin_success_exit(&pre_keep, need, top_off, next_pc, merge);
                s.cur = dbl_chk_blk;
                let is_num = s.is_number_tag(arg_boxed);
                let dbl_blk = s.body.add_block();
                s.cond_br(is_num, dbl_blk, helper_blk);
                s.cur = dbl_blk;
                let f = s.unop(Operator::F64ReinterpretI64, arg_boxed, Type::F64);
                let t = s.unop(Operator::F64Trunc, f, Type::F64);
                let i = s.unop(Operator::I32TruncSatF64S, t, Type::I32);
                let back = s.unop(Operator::F64ConvertI32S, i, Type::F64);
                let fits = s.binop(Operator::F64Eq, back, t, Type::I32);
                let af = s.unop(Operator::F64Abs, f, Type::F64);
                let thresh = s.f64_const(1e-6);
                let big = s.binop(Operator::F64Ge, af, thresh, Type::I32);
                let zero_d = s.f64_const(0.0);
                let is_z = s.binop(Operator::F64Eq, f, zero_d, Type::I32);
                let okg = s.binop(Operator::I32Or, big, is_z, Type::I32);
                // parseInt(x) for x in (-1, -0.000001] is -0, a Double, not
                // Int32 0: a negative arg truncating to 0 misses the arm.
                let is_zero_i = s.unop(Operator::I32Eqz, i, Type::I32);
                let neg = s.binop(Operator::F64Lt, f, zero_d, Type::I32);
                let negzero_res = s.binop(Operator::I32And, is_zero_i, neg, Type::I32);
                let not_negzero_res = s.unop(Operator::I32Eqz, negzero_res, Type::I32);
                let okg = s.binop(Operator::I32And, okg, not_negzero_res, Type::I32);
                let ok = s.binop(Operator::I32And, fits, okg, Type::I32);
                let ret_blk = s.body.add_block();
                s.cond_br(ok, ret_blk, helper_blk);
                s.cur = ret_blk;
                let res = s.box_int32(i);
                s.store_i64(s.vp, top_off, res);
                s.builtin_success_exit(&pre_keep, need, top_off, next_pc, merge);
            });
        }
        if let (2, Some(nf)) = (argc, native_fn) {
            self.builtin_arm(|s, helper_blk| {
                let a_boxed = s.load_i64(s.vp, frame_off + 16);
                let b_boxed = s.load_i64(s.vp, frame_off + 24);
                let is_min = mn_is(s, nf, MN_MIN);
                let is_max = mn_is(s, nf, MN_MAX);
                let is_pow = mn_is(s, nf, MN_POW);
                let or_mm = s.binop(Operator::I32Or, is_min, is_max, Type::I32);
                let any = s.binop(Operator::I32Or, or_mm, is_pow, Type::I32);
                let both_num = s.both_number_tags(a_boxed, b_boxed);
                let m = s.binop(Operator::I32And, any, both_num, Type::I32);
                let math_blk = s.body.add_block();
                s.cond_br(m, math_blk, helper_blk);
                s.cur = math_blk;
                let fa = s.unbox_number_f64(a_boxed);
                let fb = s.unbox_number_f64(b_boxed);
                let done_blk = s.body.add_block();
                let res_p = s.body.add_blockparam(done_blk, Type::F64);
                let pow_blk = s.body.add_block();
                let mm_blk = s.body.add_block();
                s.cond_br(is_pow, pow_blk, mm_blk);
                s.cur = pow_blk;
                let r_pow = s.call_f64(s.helpers.math_pow, &[fa, fb]);
                s.body.set_terminator(
                    s.cur,
                    Terminator::Br {
                        target: BlockTarget {
                            block: done_blk,
                            args: vec![r_pow],
                        },
                    },
                );
                s.cur = mm_blk;
                let r_min = s.binop(Operator::F64Min, fa, fb, Type::F64);
                let r_max = s.binop(Operator::F64Max, fa, fb, Type::F64);
                let r_mm = s.select(Type::F64, r_min, r_max, is_min);
                s.body.set_terminator(
                    s.cur,
                    Terminator::Br {
                        target: BlockTarget {
                            block: done_blk,
                            args: vec![r_mm],
                        },
                    },
                );
                s.cur = done_blk;
                let resb = s.box_f64_canonical(res_p);
                s.store_i64(s.vp, top_off, resb);
                s.builtin_success_exit(&pre_keep, need, top_off, next_pc, merge);
            });
        }
        // Math.imul(a,b) = ToInt32(a)*ToInt32(b) mod 2^32 (wasm `i32.mul`
        // low 32 bits match exactly); |f| < 2^63 truncates exactly.
        if let (2, Some(nf)) = (argc, native_fn) {
            self.builtin_arm(|s, helper_blk| {
                let a_boxed = s.load_i64(s.vp, frame_off + 16);
                let b_boxed = s.load_i64(s.vp, frame_off + 24);
                let is_imul = mn_is(s, nf, MN_IMUL);
                let both_num = s.both_number_tags(a_boxed, b_boxed);
                let m = s.binop(Operator::I32And, is_imul, both_num, Type::I32);
                let imul_blk = s.body.add_block();
                s.cond_br(m, imul_blk, helper_blk);
                s.cur = imul_blk;
                let fa = s.unbox_number_f64(a_boxed);
                let fb = s.unbox_number_f64(b_boxed);
                let lim = s.f64_const(9223372036854775808.0);
                let aa = s.unop(Operator::F64Abs, fa, Type::F64);
                let ab = s.unop(Operator::F64Abs, fb, Type::F64);
                let sa = s.binop(Operator::F64Lt, aa, lim, Type::I32);
                let sb = s.binop(Operator::F64Lt, ab, lim, Type::I32);
                let safe = s.binop(Operator::I32And, sa, sb, Type::I32);
                let do_blk = s.body.add_block();
                s.cond_br(safe, do_blk, helper_blk);
                s.cur = do_blk;
                let ia = s.to_int32_from_f64(fa);
                let ib = s.to_int32_from_f64(fb);
                let r = s.binop(Operator::I32Mul, ia, ib, Type::I32);
                let res = s.box_int32(r);
                s.store_i64(s.vp, top_off, res);
                s.builtin_success_exit(&pre_keep, need, top_off, next_pc, merge);
            });
        }
        // String.prototype.charCodeAt / charAt on a linear string with an
        // in-bounds int32 index (pure char loads), plus String.fromCharCode
        // for a code < 256 (a static unit string). Ropes, two-byte charAt
        // above 255 and OOB (NaN / "") take the helper.
        if argc == 1 && builtin_arms {
            self.builtin_arm(|s, helper_blk| {
                let this_boxed = s.load_i64(s.vp, frame_off + 8);
                let arg_boxed = s.load_i64(s.vp, frame_off + 16);
                let ccat_cell = s.i32_const(s.helpers.str_ccat_cell);
                let ccat_bits = s.load_i64(ccat_cell, 0);
                let cat_cell = s.i32_const(s.helpers.str_cat_cell);
                let cat_bits = s.load_i64(cat_cell, 0);
                let is_ccat = s.binop(Operator::I64Eq, callee_boxed, ccat_bits, Type::I32);
                let is_cat = s.binop(Operator::I64Eq, callee_boxed, cat_bits, Type::I32);
                let is_either = s.binop(Operator::I32Or, is_ccat, is_cat, Type::I32);
                let this_str = s.tag_eq(this_boxed, TAG_STRING as u32);
                let arg_int = s.tag_eq(arg_boxed, TAG_INT32 as u32);
                let ta = s.binop(Operator::I32And, this_str, arg_int, Type::I32);
                let m1 = s.binop(Operator::I32And, is_either, ta, Type::I32);
                let flags_blk = s.body.add_block();
                let try_fcc_blk = s.body.add_block();
                s.cond_br(m1, flags_blk, try_fcc_blk);
                s.cur = try_fcc_blk;
                let fcc_cell = s.i32_const(s.helpers.str_fcc_cell);
                let fcc_bits = s.load_i64(fcc_cell, 0);
                let is_fcc = s.binop(Operator::I64Eq, callee_boxed, fcc_bits, Type::I32);
                let code = s.unop(Operator::I32WrapI64, arg_boxed, Type::I32);
                let lim = s.i32_const(256);
                let code_ok = s.binop(Operator::I32LtU, code, lim, Type::I32);
                let fa = s.binop(Operator::I32And, is_fcc, arg_int, Type::I32);
                let m_fcc = s.binop(Operator::I32And, fa, code_ok, Type::I32);
                let fcc_blk = s.body.add_block();
                s.cond_br(m_fcc, fcc_blk, helper_blk);
                s.cur = fcc_blk;
                let tbl_slot0 = s.i32_const(s.helpers.static_strings_slot);
                let tbl0 = s.load_i32(tbl_slot0, 0);
                let two0 = s.i32_const(2);
                let coff0 = s.binop(Operator::I32Shl, code, two0, Type::I32);
                let entry0 = s.binop(Operator::I32Add, tbl0, coff0, Type::I32);
                let atom0 = s.load_i32(entry0, 0);
                let pay0 = s.unop(Operator::I64ExtendI32U, atom0, Type::I64);
                let stag0 = s.boxed_const(TAG_STRING << 32);
                let sval0 = s.binop(Operator::I64Or, pay0, stag0, Type::I64);
                s.store_i64(s.vp, top_off, sval0);
                // A pure hit: the clean continuation, not the merge (the
                // merge inherits the helper arm's stepped state, which
                // would leave a hot loop calling
                // `String.fromCharCode`/`charCodeAt` Dirty on every call
                // even though the fast arm always hits).
                s.builtin_success_exit(&pre_keep, need, top_off, next_pc, merge);
                s.cur = flags_blk;
                let strptr = s.unop(Operator::I32WrapI64, this_boxed, Type::I32);
                let flags = s.load_i32(strptr, STRING_FLAGS_OFFSET);
                let lin_bit = s.i32_const(STRING_LINEAR_BIT);
                let lin_masked = s.binop(Operator::I32And, flags, lin_bit, Type::I32);
                let zero_lin = s.i32_const(0);
                let is_lin = s.binop(Operator::I32Ne, lin_masked, zero_lin, Type::I32);
                let len = s.load_i32(strptr, STRING_LENGTH_OFFSET);
                let idx = s.unop(Operator::I32WrapI64, arg_boxed, Type::I32);
                let in_bounds = s.binop(Operator::I32LtU, idx, len, Type::I32);
                let ok_read = s.binop(Operator::I32And, is_lin, in_bounds, Type::I32);
                let char_blk = s.body.add_block();
                s.cond_br(ok_read, char_blk, helper_blk);
                // The width branch dominates both loads, so neither can read
                // past the string's buffer.
                s.cur = char_blk;
                let inline_bit = s.i32_const(STRING_INLINE_CHARS_BIT);
                let is_inline = s.binop(Operator::I32And, flags, inline_bit, Type::I32);
                let noninline = s.load_i32(strptr, STRING_CHARS_OFFSET);
                let inline_addr = s.add_offset(strptr, STRING_CHARS_OFFSET);
                let chars = s.select(Type::I32, inline_addr, noninline, is_inline);
                let lat_bit = s.i32_const(STRING_LATIN1_CHARS_BIT);
                let is_lat = s.binop(Operator::I32And, flags, lat_bit, Type::I32);
                let code_blk = s.body.add_block();
                let c_param = s.body.add_blockparam(code_blk, Type::I32);
                let latin_blk = s.body.add_block();
                let two_blk = s.body.add_block();
                s.cond_br(is_lat, latin_blk, two_blk);
                s.cur = latin_blk;
                let caddr8 = s.binop(Operator::I32Add, chars, idx, Type::I32);
                let c8 = s.load8_u(caddr8, 0);
                s.body.set_terminator(
                    s.cur,
                    Terminator::Br {
                        target: BlockTarget {
                            block: code_blk,
                            args: vec![c8],
                        },
                    },
                );
                s.cur = two_blk;
                let one16 = s.i32_const(1);
                let off16 = s.binop(Operator::I32Shl, idx, one16, Type::I32);
                let caddr16 = s.binop(Operator::I32Add, chars, off16, Type::I32);
                let c16 = s.load16_u(caddr16, 0);
                s.body.set_terminator(
                    s.cur,
                    Terminator::Br {
                        target: BlockTarget {
                            block: code_blk,
                            args: vec![c16],
                        },
                    },
                );
                s.cur = code_blk;
                let ccat_blk = s.body.add_block();
                let cat_blk = s.body.add_block();
                s.cond_br(is_ccat, ccat_blk, cat_blk);
                s.cur = ccat_blk;
                let code_payload = s.unop(Operator::I64ExtendI32U, c_param, Type::I64);
                let int_tag = s.boxed_const(TAG_INT32 << 32);
                let code_val = s.binop(Operator::I64Or, code_payload, int_tag, Type::I64);
                s.store_i64(s.vp, top_off, code_val);
                s.builtin_success_exit(&pre_keep, need, top_off, next_pc, merge);
                s.cur = cat_blk;
                let unit_lim = s.i32_const(256);
                let unit_ok = s.binop(Operator::I32LtU, c_param, unit_lim, Type::I32);
                let cat_ok_blk = s.body.add_block();
                s.cond_br(unit_ok, cat_ok_blk, helper_blk);
                s.cur = cat_ok_blk;
                let tbl_slot = s.i32_const(s.helpers.static_strings_slot);
                let tbl = s.load_i32(tbl_slot, 0);
                let two = s.i32_const(2);
                let coff = s.binop(Operator::I32Shl, c_param, two, Type::I32);
                let entry_addr = s.binop(Operator::I32Add, tbl, coff, Type::I32);
                let atom = s.load_i32(entry_addr, 0);
                let atom_payload = s.unop(Operator::I64ExtendI32U, atom, Type::I64);
                let str_tag = s.boxed_const(TAG_STRING << 32);
                let char_val = s.binop(Operator::I64Or, atom_payload, str_tag, Type::I64);
                s.store_i64(s.vp, top_off, char_val);
                s.builtin_success_exit(&pre_keep, need, top_off, next_pc, merge);
            });
        }
        let argc_v2 = self.i32_const(u32::from(argc));
        // Native route. The classify already proved function clasp + no
        // BaseScript, so this is one branch on a value we hold: straight to
        // the native with the frame as `vp`, skipping `night_runtime_call`'s
        // whole arm chain. `fun_apply`/`fun_call`, the defineProperty fuse
        // intercept and the char-op rope flatten all punt back to
        // `night_runtime_call` from inside `native_dispatch`, so correctness
        // does not depend on predicting which native this is.
        if self.script.bytecode.len() <= NATIVE_ROUTE_SCRIPT_MAX_BYTECODE {
            let native_blk = self.body.add_block();
            let generic_blk = self.body.add_block();
            self.cond_br(callee_native, native_blk, generic_blk);
            self.cur = native_blk;
            let pre_e = pre_keep.as_ref().map(|_| self.emit_epoch_read());
            let pre_b = pre_keep.as_ref().and_then(|_| self.sample_bind_epoch());
            let ok_nat = self.call_i32(
                self.helpers.native_dispatch,
                &[self.cx, top, frame_base, argc_v2],
            );
            if let (Some(pre), Some(pre_e)) = (pre_keep.as_ref(), pre_e) {
                let next = next_pc.expect("native keep implies next_pc");
                let post = self.emit_epoch_read();
                let same = self.binop(Operator::I32Eq, pre_e, post, Type::I32);
                let keep = self.binop(Operator::I32And, ok_nat, same, Type::I32);
                let keep_blk = self.body.add_block();
                let cont_blk = self.body.add_block();
                self.cond_br(keep, keep_blk, cont_blk);
                self.cur = keep_blk;
                self.emit_census(49, self.root_source_id, next);
                let w = self.i32_const(FLAG_MUT_THIS | FLAG_MUT_OTHER | FLAG_BIND);
                self.emit_stamp_cont(pre, need, top_off, next, w, pre_b, set_result);
                self.cur = cont_blk;
            }
            let margs_x = self.merge_args(ok_nat);
            self.body.set_terminator(
                self.cur,
                Terminator::Br {
                    target: BlockTarget {
                        block: merge,
                        args: margs_x,
                    },
                },
            );
            self.cur = generic_blk;
        }
        let pre_e = pre_keep.as_ref().map(|_| self.emit_epoch_read());
        let pre_b = pre_keep.as_ref().and_then(|_| self.sample_bind_epoch());
        let ok_slow = self.call_i32(call_helper, &[self.cx, top, frame_base, argc_v2]);
        if let (Some(pre), Some(pre_e)) = (pre_keep.as_ref(), pre_e) {
            let next = next_pc.expect("native keep implies next_pc");
            let post = self.emit_epoch_read();
            let same = self.binop(Operator::I32Eq, pre_e, post, Type::I32);
            let keep = self.binop(Operator::I32And, ok_slow, same, Type::I32);
            let keep_blk = self.body.add_block();
            let cont_blk = self.body.add_block();
            self.cond_br(keep, keep_blk, cont_blk);
            self.cur = keep_blk;
            self.emit_census(49, self.root_source_id, next);
            let w = self.i32_const(FLAG_MUT_THIS | FLAG_MUT_OTHER | FLAG_BIND);
            self.emit_stamp_cont(pre, need, top_off, next, w, pre_b, set_result);
            self.cur = cont_blk;
        }
        let margs_x = self.merge_args(ok_slow);
        self.body.set_terminator(
            self.cur,
            Terminator::Br {
                target: BlockTarget {
                    block: merge,
                    args: margs_x,
                },
            },
        );

        self.cur = merge;
        if let Some(fp) = merge_flags_param {
            self.cur_flags = FlagsAcc::Dyn(fp, 0);
        }
        // Every arm that reaches this merge was offered the keep arm's
        // intactness proof and failed it, so the merge is the fork's dirty
        // side and leaves Opt.
        if let (Some(_), Some(next)) = (pre_keep.as_ref(), next_pc) {
            self.keep_fork_merge_stepped_track(next);
        }
        self.reload(n);
        let result = self.load_i64(self.vp, top_off);
        self.branch_on_err(ok_param);
        if set_result {
            // Setter-call site: the op's result is the STORED VALUE. Take
            // it off the reloaded stack (its spill slot is GC-updated;
            // facts ride the operand) rather than re-pushing a pre-call
            // SSA copy a moving GC could have stranded.
            let v = self
                .stack
                .last()
                .cloned()
                .expect("setter call carries a value operand");
            for _ in 0..need {
                self.stack.pop();
            }
            self.stack.push(v);
            return Ok(());
        }
        for _ in 0..need {
            self.stack.pop();
        }
        // Guard-at-defs, the call family: the generic call's result is
        // otherwise pure bottom; a likelier claim on the ret cell rides
        // the same one-tag-test ladder as every other def claim.
        if !self.gen_only {
            if let (Some(&claim), Some(op)) = (
                self.ctx
                    .facts
                    .call_types
                    .get(&Site::new(self.source_id, Pc::new(self.evid_pc(pc).get()))),
                self.cur_op,
            ) {
                self.push_load_typed(result, claim, pc + op.len(), Prov::C_CALLRET);
                return Ok(());
            }
        }
        self.push_boxed(result, self.def_type(pc, 0));
        Ok(())
    }

    /// Apply-forward: emit a recognized `T.apply(thisArg, arguments)` site
    /// as a direct forward. The frame is `[apply_fn, T, thisArg,
    /// argsPlaceholder]` (argc == 2); `arguments` was elided, so the
    /// placeholder is unused. `night_runtime_apply_fwd` forwards the
    /// caller's live actuals (at `self.sp[2..]`, `self.argc`) straight into
    /// T's compiled body and reconstructs faithfully on the cold fallback.
    /// Whether a body can observe an actual argument it did not declare as a
    /// formal -- the precondition for forwarding only the declared formals.
    fn observes_actuals(script: &Script) -> bool {
        script.parser().opcodes().any(|op| {
            matches!(
                op,
                JSOp::Arguments
                    | JSOp::ArgumentsLength
                    | JSOp::GetActualArg
                    | JSOp::GetFrameArg
                    | JSOp::Rest
            )
        })
    }

    /// The single resolved target of an apply-forward site, when the direct
    /// arm may call it (`apply_fwd_target_ok`).
    fn apply_fwd_direct_target(&self, pc: Pc) -> Option<(u32, u32)> {
        if self.gen_only {
            return None;
        }
        let site = Site::new(self.source_id, self.evid_pc(pc));
        // Inside a segment the body was entered from one known site, and
        // the analysis resolves the forward per entry (a shared wrapper's
        // `this.initialize` is one script per `new` site and many at the
        // body); the body-level resolution still applies where it exists.
        let per_entry = self
            .seg_entry_site()
            .and_then(|entry| self.ctx.facts.apply_targets_in.get(&(entry, site)));
        let sid = *per_entry.or_else(|| self.ctx.facts.apply_targets.get(&site))?;
        self.apply_fwd_target_ok(sid)
    }

    /// Every known target of an apply-forward site that the direct arm
    /// may call, for a site without a single one.
    fn apply_fwd_known_targets(&self, pc: Pc) -> Vec<(u32, u32)> {
        if self.gen_only {
            return Vec::new();
        }
        let site = Site::new(self.source_id, self.evid_pc(pc));
        let Some(set) = self.ctx.facts.apply_target_sets.get(&site) else {
            return Vec::new();
        };
        set.iter()
            .filter_map(|&t| self.apply_fwd_target_ok(t))
            .take(APPLY_FWD_MAX_TARGETS)
            .collect()
    }

    /// `(sid, nargs)` when `sid` is a body an apply-forward site may call
    /// directly: a compiled script, not a class ctor or a generator, with
    /// few enough formals that filling them from the caller's actuals is
    /// a handful of loads rather than a copy loop.
    fn apply_fwd_target_ok(&self, sid: ScriptId) -> Option<(u32, u32)> {
        let SourceObject::Script(s) = self.source.object(SourceObjectId::new(sid.get())) else {
            return None;
        };
        if s.is_class_ctor || s.is_generator_or_async {
            return None;
        }
        // The arm forwards exactly the callee's declared formals, not every
        // actual the caller received. That is the same call only if the
        // callee cannot observe the ones it does not declare, so every op
        // that exposes an actual past the formals disqualifies the target.
        //
        // The list is exhaustive on purpose: testing only `Arguments` would
        // give a wrong answer for `function g() { return arguments.length }`,
        // because `arguments.length` compiles to `ArgumentsLength` and
        // never materializes the object. `GetArg`/`SetArg` are absent
        // deliberately -- they name declared formals, which the arm does
        // supply.
        if s.has_mapped_args || Self::observes_actuals(s) {
            return None;
        }
        // A wide callee would be a long unrolled copy behind a guard that
        // holds less and less often.
        (u32::from(s.nargs) <= APPLY_FWD_MAX_ARGS).then_some((sid.get(), u32::from(s.nargs)))
    }

    /// One known-target arm of an apply-forward site: the site restacked
    /// as [target, this, formals...] (the actuals the target declares,
    /// undefined past the ones supplied) and a static call of the body
    /// through the patched direct stub, with the typed entry where the
    /// operands prove the callee's claims. Returns the call's result.
    #[allow(clippy::too_many_arguments)]
    fn emit_apply_fwd_known_arm(
        &mut self,
        pc: Pc,
        tsid: u32,
        nargs: u32,
        need: usize,
        seg_argc: Option<u16>,
        caller_sp: Value,
        caller_argc: Value,
        target_op: &Operand,
        this_op: &Operand,
        script: Value,
        expected: Value,
        recv_bit: u32,
    ) -> Operand {
        for _ in 0..need {
            self.stack.pop();
        }
        self.stack.push(target_op.clone());
        self.stack.push(this_op.clone());
        for i in 0..nargs {
            match seg_argc {
                Some(n) if i < u32::from(n) => {
                    self.read_arg(u16::try_from(i).unwrap(), bottom_ty(), None);
                }
                Some(_) => {
                    let undef = self.boxed_const(TAG_UNDEFINED << 32);
                    self.push_boxed(undef, prim_desc(PRIM_UNDEFINED));
                }
                None => {
                    // The caller's actual, or undefined past its argc: the
                    // slot beyond the actuals is readable frame memory the
                    // select discards.
                    let v = self.load_i64(caller_sp, 16 + 8 * i);
                    let idx = self.i32_const(i);
                    let have = self.binop(Operator::I32GtU, caller_argc, idx, Type::I32);
                    let undef = self.boxed_const(TAG_UNDEFINED << 32);
                    let v = self.select(Type::I64, v, undef, have);
                    self.push_boxed(v, bottom_ty());
                }
            }
        }
        let n16 = u16::try_from(nargs).expect("APPLY_FWD_MAX_ARGS fits u16");
        let fneed = nargs as usize + 2;
        let sel_argc = if self.callee_entry_proven(tsid, n16, fneed) {
            nargs | ARGC_SEL_BIT
        } else {
            nargs
        };
        let n = self.spill_all();
        let frame_off = self.operand_base + 8 * (n - u32::try_from(fneed).unwrap());
        let frame_base = self.add_offset(self.vp, frame_off);
        let top_off = self.operand_base + 8 * n;
        let top = self.add_offset(self.vp, top_off);
        let argc_v = self.i32_const(sel_argc);
        let undef_nt = self.boxed_const(TAG_UNDEFINED << 32);
        let args = [self.cx, frame_base, argc_v, top, script, undef_nt];
        let (callv, err, eff) = self.call_abi2(self.helpers.direct_call_stub2, &args);
        self.likely_patches.push((expected, callv, tsid));
        let efff = self.fold_callee_flags(eff, recv_bit);
        self.or_flags_word(efff);
        self.reload(n);
        let result = self.load_i64(self.vp, top_off);
        let ok = self.unop(Operator::I32Eqz, err, Type::I32);
        self.branch_on_err(ok);
        for _ in 0..fneed {
            self.stack.pop();
        }
        Operand::plain(result, Repr::Boxed, self.def_type(pc, 0))
    }

    /// `hasOwnProperty.call(o, k)` with the analysis's mono native target:
    /// the site's `.call` and its target are the pristine builtins.
    fn is_hasown_call_site(&self, pc: Pc) -> bool {
        if self.gen_only {
            return false;
        }
        let site = Site::new(self.source_id, self.evid_pc(pc));
        self.ctx.facts.apply_sites.get(&site) == Some(&crate::facts::CallForm::Call)
            && self.ctx.facts.apply_natives.get(&site)
                == Some(&crate::facts::ApplyNative::HasOwnProperty)
    }

    /// The native forward: guard the `.call` value and the target against
    /// their builtin cells, then run the `HasOwn` lowering over the
    /// shifted actuals (the site's `this` is the receiver, its first
    /// argument the key). Either guard failing takes the generic call.
    fn emit_hasown_call(&mut self, pc: Pc, need: usize) -> Result<(), String> {
        let len = self.stack.len();
        let call_op = self.stack[len - need].clone();
        let target_op = self.stack[len - need + 1].clone();
        let this_op = self.stack[len - need + 2].clone();
        let key_op = self.stack[len - need + 3].clone();
        let call_boxed = self.to_boxed(&call_op);
        let target_boxed = self.to_boxed(&target_op);
        let this_boxed = self.to_boxed(&this_op);
        let key_boxed = self.to_boxed(&key_op);
        let Some(op) = self.cur_op else {
            return self.emit_call_generic(pc, 2, need, true);
        };
        let next_pc = pc + op.len();
        let base = self.helpers.builtin_cells_base;
        let c1 = self.i32_const(base + 8 * crate::wasm::translate::BC_FUN_CALL);
        let bits1 = self.load_i64(c1, 0);
        self.eff(bits1, Eff::Read(HeapKind::EngineTable));
        let is_call = self.binop(Operator::I64Eq, call_boxed, bits1, Type::I32);
        let c2 = self.i32_const(base + 8 * crate::wasm::translate::BC_OBJ_HASOWN);
        let bits2 = self.load_i64(c2, 0);
        self.eff(bits2, Eff::Read(HeapKind::EngineTable));
        let is_hasown = self.binop(Operator::I64Eq, target_boxed, bits2, Type::I32);
        let hit = self.binop(Operator::I32And, is_call, is_hasown, Type::I32);
        let fast_blk = self.body.add_block();
        let slow_blk = self.body.add_block();
        self.cond_br(hit, fast_blk, slow_blk);
        self.side_arm(slow_blk, next_pc, move |s| {
            s.emit_call_generic_to(pc, 2, need, false, None, false)
                .expect("generic call");
            s.stack.pop().expect("the generic call pushes its result")
        });
        self.cur = fast_blk;
        let ty = self.result_ty_fact(pc, PRIM_BOOLEAN);
        let h = self.helpers.has_own;
        let result = self.rt_call_keep(h, need, Some(next_pc), &ty, vec![key_boxed, this_boxed]);
        self.push_known(result, Repr::Boxed, ty);
        Ok(())
    }

    pub(super) fn emit_apply_forward(&mut self, pc: Pc, need: usize) -> Result<(), String> {
        let len = self.stack.len();
        let apply_op = self.stack[len - need].clone();
        let target_op = self.stack[len - need + 1].clone();
        let this_op = self.stack[len - need + 2].clone();
        let apply_boxed = self.to_boxed(&apply_op);
        let target_boxed = self.to_boxed(&target_op);
        let this_boxed = self.to_boxed(&this_op);
        // The forwarded actuals: the root frame's own (`sp`, `argc`), or a
        // spliced wrapper's frame, whose actuals sit at its frame base
        // below its locals (`InlineSeg::nformals`) and whose count is the
        // splice site's, a constant.
        let seg_argc = self.cur_seg.map(|i| self.segs[i].argc);
        let (caller_sp, caller_argc) = match seg_argc {
            Some(n) => (
                self.add_offset(self.vp, self.frame_base),
                self.i32_const(u32::from(n)),
            ),
            None => (self.sp, self.argc),
        };
        // Direct-call fast arm. `night_runtime_apply_fwd` is an
        // `unknown()` helper: it returns no effect word and saturates the
        // lineage, so an apply-forward site can never keep the Opt track --
        // a sizable share of every departure, because generated
        // constructors are commonly `C.C.apply(this, arguments)`
        // wrappers. Calling the resolved target through the ordinary
        // generic path instead gives the site the callee's real (err, eff)
        // word, and with it the typed entry, the likely-direct arm and the
        // effect-flag fork.
        //
        // One runtime guard makes it equivalent to the helper's own fast
        // path: the `.apply` actually reached must be the pristine
        // `Function.prototype.apply` -- the helper's `native() ==
        // js::fun_apply` test as a value-identity compare against the
        // builtin cell. The forward is a fixed number of loads, exactly
        // the formals the callee declares: JS drops surplus actuals, and a
        // missing one is undefined (a select against `argc` at the root,
        // a compile-time decision in a segment). The guard failing takes
        // the helper, unchanged, as its own continuation.
        if let (Some((tsid, nargs)), Some(op)) = (self.apply_fwd_direct_target(pc), self.cur_op) {
            let next_pc = pc + op.len();
            let cell = self.i32_const(
                self.helpers.builtin_cells_base + 8 * crate::wasm::translate::BC_FUN_APPLY,
            );
            let bits = self.load_i64(cell, 0);
            self.eff(bits, Eff::Read(HeapKind::EngineTable));
            let is_apply = self.binop(Operator::I64Eq, apply_boxed, bits, Type::I32);
            let hit = is_apply;
            let fast_blk = self.body.add_block();
            let slow_blk = self.body.add_block();
            self.cond_br(hit, fast_blk, slow_blk);
            let h = self.helpers.apply_fwd;
            self.side_arm(slow_blk, next_pc, move |s| {
                let r = s
                    .rt_call(h, true, move |_s, _n| {
                        vec![
                            apply_boxed,
                            target_boxed,
                            this_boxed,
                            caller_sp,
                            caller_argc,
                        ]
                    })
                    .unwrap();
                for _ in 0..need {
                    s.stack.pop();
                }
                Operand::plain(r, Repr::Boxed, bottom_ty())
            });
            self.cur = fast_blk;
            // Restack as an ordinary call: [target, this, actual0 ..].
            // `emit_call_generic_to` spills these into the callee frame
            // itself, so there is no frame built by hand here.
            for _ in 0..need {
                self.stack.pop();
            }
            // Push the ORIGINAL operands, not fresh boxed values. A plain
            // `push_boxed` drops `src`, and `store_recv_bit` reads exactly
            // that to tell the frame's own `this` from any other receiver --
            // so a re-boxed receiver classifies MUT_OTHER, the callee's
            // own-this writes stop folding away, and the construct fork one
            // level up can never see a zero word.
            self.stack.push(target_op.clone());
            self.stack.push(this_op.clone());
            for i in 0..nargs {
                match seg_argc {
                    // The splice's actuals are the frame's formal slots,
                    // read with the facts the site's operands carried in.
                    Some(n) if i < u32::from(n) => {
                        self.read_arg(u16::try_from(i).unwrap(), bottom_ty(), None);
                    }
                    Some(_) => {
                        let undef = self.boxed_const(TAG_UNDEFINED << 32);
                        self.push_boxed(undef, prim_desc(PRIM_UNDEFINED));
                    }
                    None => {
                        // The caller's actual (at its frame base + 2
                        // slots), or undefined past its argc: the slot
                        // beyond the actuals is readable frame memory the
                        // select discards.
                        let v = self.load_i64(caller_sp, 16 + 8 * i);
                        let idx = self.i32_const(i);
                        let have = self.binop(Operator::I32GtU, caller_argc, idx, Type::I32);
                        let undef = self.boxed_const(TAG_UNDEFINED << 32);
                        let v = self.select(Type::I64, v, undef, have);
                        self.push_boxed(v, bottom_ty());
                    }
                }
            }
            let n16 = u16::try_from(nargs).expect("APPLY_FWD_MAX_ARGS fits u16");
            let fneed = nargs as usize + 2;
            // Now an ordinary mono call to the target: the splice admission
            // takes it on its own merits (the site's own call facts name
            // `apply`, so the target is handed in).
            if let Some(sids) = self.inline_candidates_for(pc, false, vec![ScriptId::new(tsid)]) {
                return self.emit_inline_call(pc, n16, fneed, &sids);
            }
            return self.emit_call_generic_to(pc, n16, fneed, true, Some(tsid), false);
        }
        // Dynamic-count direct arm, for a site with no single target (a
        // SHARED wrapper's dispatch -- one script, many prototypes -- at
        // its own body). The target is classified at run time like any
        // generic call's callee and entered through the module's own
        // `call_indirect`; the frame is [target, this] at the spilled
        // operand top plus the caller's actuals copied by count, and the
        // callee reads `argc` as a value. Only a non-pristine `.apply`, a
        // non-dispatchable target or a full AOT stack takes the helper.
        if let (false, Some(op)) = (self.gen_only, self.cur_op) {
            let next_pc = pc + op.len();
            let cell = self.i32_const(
                self.helpers.builtin_cells_base + 8 * crate::wasm::translate::BC_FUN_APPLY,
            );
            let bits = self.load_i64(cell, 0);
            self.eff(bits, Eff::Read(HeapKind::EngineTable));
            let is_apply = self.binop(Operator::I64Eq, apply_boxed, bits, Type::I32);
            let (funcidx, script, _native) = self.emit_inline_classify(target_boxed);
            let zero = self.i32_const(0);
            let dispatchable = self.binop(Operator::I32Ne, funcidx, zero, Type::I32);
            // The frame the arm builds: [target, this] where the popped
            // operands were, actuals above, the out-slot past them.
            let frame_off = self.operand_base + 8 * u32::try_from(len - need).unwrap();
            let eight = self.i32_const(8);
            let bytes = self.binop(Operator::I32Mul, caller_argc, eight, Type::I32);
            let dst = self.add_offset(self.vp, frame_off + 16);
            let top = self.binop(Operator::I32Add, dst, bytes, Type::I32);
            let fits = self.emit_stack_fits(top, 0);
            let a = self.binop(Operator::I32And, is_apply, dispatchable, Type::I32);
            let hit = self.binop(Operator::I32And, a, fits, Type::I32);
            let fast_blk = self.body.add_block();
            let slow_blk = self.body.add_block();
            // Known-target arms first: one patched identity compare per
            // target the analysis saw the site reach, each a static
            // direct call of that body over exactly its formals -- the
            // single-target arm above, repeated by callee identity. The
            // dynamic arm is their miss.
            let known = self.apply_fwd_known_targets(pc);
            let max_nargs = known.iter().map(|&(_, n)| n).max().unwrap_or(0);
            let chain_ok = if known.is_empty() {
                None
            } else {
                let top_k = self.add_offset(self.vp, frame_off + 16 + 8 * max_nargs);
                let fits_k = self.emit_stack_fits(top_k, 0);
                Some(self.binop(Operator::I32And, is_apply, fits_k, Type::I32))
            };
            let recv_bit = self.store_recv_bit(&this_op);
            if let Some(chain_ok) = chain_ok {
                let chain_blk = self.body.add_block();
                let dyn_blk = self.body.add_block();
                self.cond_br(chain_ok, chain_blk, dyn_blk);
                self.cur = chain_blk;
                for (i, &(tsid, nargs)) in known.iter().enumerate() {
                    let expected = self.i32_const(u32::MAX);
                    self.likely_patches.push((expected, expected, tsid));
                    let take = self.binop(Operator::I32Eq, funcidx, expected, Type::I32);
                    let arm_blk = self.body.add_block();
                    let next_blk = if i + 1 == known.len() {
                        dyn_blk
                    } else {
                        self.body.add_block()
                    };
                    self.cond_br(take, arm_blk, next_blk);
                    let (target_op, this_op) = (target_op.clone(), this_op.clone());
                    let nargs = nargs.min(APPLY_FWD_MAX_ARGS);
                    self.side_arm_keep(arm_blk, next_pc, move |s| {
                        s.emit_apply_fwd_known_arm(
                            pc,
                            tsid,
                            nargs,
                            need,
                            seg_argc,
                            caller_sp,
                            caller_argc,
                            &target_op,
                            &this_op,
                            script,
                            expected,
                            recv_bit,
                        )
                    });
                    self.cur = next_blk;
                }
                self.cond_br(hit, fast_blk, slow_blk);
            } else {
                self.cond_br(hit, fast_blk, slow_blk);
            }
            let h = self.helpers.apply_fwd;
            self.side_arm(slow_blk, next_pc, move |s| {
                let r = s
                    .rt_call(h, true, move |_s, _n| {
                        vec![
                            apply_boxed,
                            target_boxed,
                            this_boxed,
                            caller_sp,
                            caller_argc,
                        ]
                    })
                    .unwrap();
                for _ in 0..need {
                    s.stack.pop();
                }
                Operand::plain(r, Repr::Boxed, bottom_ty())
            });
            self.cur = fast_blk;
            if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
                crate::diag_line!(
                    "night: bbv apply-fwd-dyn sid#{} pc {}",
                    self.source_id,
                    self.evid_pc(pc)
                );
            }
            for _ in 0..need {
                self.stack.pop();
            }
            self.stack.push(target_op.clone());
            self.stack.push(this_op.clone());
            let n = self.spill_all();
            debug_assert_eq!(self.operand_base + 8 * (n - 2), frame_off);
            let src = self.add_offset(caller_sp, 16);
            self.memory_copy(dst, src, bytes);
            let frame_base = self.add_offset(self.vp, frame_off);
            let undef_nt = self.boxed_const(TAG_UNDEFINED << 32);
            let args = [self.cx, frame_base, caller_argc, top, script, undef_nt];
            let (_v, err, eff) = self.call_indirect_abi2(&args, funcidx);
            let efff = self.fold_callee_flags(eff, recv_bit);
            self.or_flags_word(efff);
            self.reload(n);
            let result = self.load_i64(top, 0);
            let ok = self.unop(Operator::I32Eqz, err, Type::I32);
            self.branch_on_err(ok);
            self.stack.pop();
            self.stack.pop();
            self.push_boxed(result, self.def_type(pc, 0));
            return Ok(());
        }
        let h = self.helpers.apply_fwd;
        // The unresolved-target tail (GEN, or no continuation op). The
        // helper forwards
        // faithfully but is an unconditional main-line CallGc: without help
        // its site saturates the wrapper's word and dirties its lineage on
        // every invocation. The epoch keep-facts fork applies here exactly
        // as at flag sites -- sampled at op level, so the dominance problem
        // that forbids a per-helper accumulator bridge does not arise:
        // epoch unchanged across the helper proves every stamp-guarded
        // fact, the facts restore, and the word ORs MUT bits without
        // FLAG_STAMPS so the callers' construct forks keep their arms too.
        // No mapped-args gate here: an apply-forward body has nargs == 0
        // by `compute_apply_fwd_pcs`, so there are no formals a callee
        // could write through the (elided anyway) arguments object.
        let fork_ok = !self.gen_only
            && self.cur_track != Track::Dirty
            && self.flags_threading()
            && self.cur_op.is_some();
        let (pre_state, pre_e, pre_b) = if fork_ok {
            let p = self.arm_state();
            let e = self.emit_epoch_read();
            let b = self.sample_bind_epoch();
            (Some(p), Some(e), b)
        } else {
            (None, None, None)
        };
        let result = self
            .rt_call(h, true, move |_s, _n| {
                vec![
                    apply_boxed,
                    target_boxed,
                    this_boxed,
                    caller_sp,
                    caller_argc,
                ]
            })
            .unwrap();
        if let (Some(pre), Some(pre_e), Some(op)) = (pre_state, pre_e, self.cur_op) {
            let fnext = pc + op.len();
            let post = self.emit_epoch_read();
            let same = self.binop(Operator::I32Eq, pre_e, post, Type::I32);
            let keep_blk = self.body.add_block();
            let cont_blk = self.body.add_block();
            self.cond_br(same, keep_blk, cont_blk);
            self.cur = keep_blk;
            self.emit_census(49, self.root_source_id, fnext);
            let k_state = self.arm_state();
            self.arm_restore(pre);
            for _ in 0..need {
                self.stack.pop();
            }
            self.reload_gc_values();
            self.or_flags_const(FLAG_MUT_THIS | FLAG_MUT_OTHER | FLAG_BIND);
            self.push_boxed(result, bottom_ty());
            self.gcells_keep(None, pre_b, fnext);
            let target = self.cont(fnext);
            self.body
                .set_terminator(self.cur, Terminator::Br { target });
            self.arm_restore(k_state);
            self.cur = cont_blk;
        }
        for _ in 0..need {
            self.stack.pop();
        }
        self.push_boxed(result, self.def_type(pc, 0));
        Ok(())
    }

    /// Guard hoisting at the construct site. A choke census finds that
    /// every store site still paying the choke has a receiver with no class
    /// fact and no slot provenance -- they are construct results. `new C(...)` at a site resolving mono to a ctor
    /// with a stamp row produces an object whose class word the ctor's own
    /// exit stamp *usually* sets to `layout_id + 1`, but nothing proves it
    /// (the cell may be cold, the generic arm may have run, the exit stamp
    /// re-validates the live shape and can decline). One word compare here
    /// turns "usually" into a fact, and that fact then rides the value into
    /// its local: every later field store on it elides the choke and every
    /// later field load is checkless. This is the fullword discipline's
    /// "one guard buys the lineage" applied where the lineage is born.
    ///
    /// The SHALLOW half rides along when set, which is the case a fresh
    /// object hits: its masked fields were initialised by the ctor and
    /// nothing has cleared the flags yet.
    pub(super) fn emit_construct_class_guard(&mut self, pc: Pc, next_pc: Pc) {
        if self.gen_only {
            return;
        }
        let Some(k) = self
            .likely_call_target(pc)
            .and_then(|sid| self.ctx.stamp_ctors_in.get(&ScriptId::new(sid)))
            .or_else(|| {
                self.ctx
                    .construct_sites_in
                    .get(&Site::new(self.source_id, self.evid_pc(pc)))
            })
            .map(|si| si.layout_id + 1)
        else {
            return;
        };
        if self.opts.diagnostics.bbv {
            crate::diag_line!(
                "night: bbv ctor-guard sid#{} pc {} k {k}",
                self.source_id,
                self.evid_pc(pc)
            );
        }
        let Some(res) = self.stack.pop() else { return };
        let boxed = self.to_boxed(&res);
        let ptr = self.unop(Operator::I32WrapI64, boxed, Type::I32);
        let w = self.load_i32(ptr, OBJ_CLASS_IDX_OFFSET);
        self.eff(w, Eff::ReadBits(HeapKind::ClassWord));
        // SLOTS fused into the ctor result guard: a hit mints both bits
        // (a SHALLOW-valid result that lost SLOTS to a harmful ctor add
        // now misses into the plain lineage -- the tiny population the
        // add census bounds).
        let m = self.i32_const(0xFFFF | CLASS_WORD_SHALLOW | CLASS_WORD_SLOTS);
        let t = self.binop(Operator::I32And, w, m, Type::I32);
        let kv = self.i32_const(k | CLASS_WORD_SHALLOW | CLASS_WORD_SLOTS);
        let eq = self.binop(Operator::I32Eq, t, kv, Type::I32);
        let hit_blk = self.body.add_block();
        let miss_blk = self.body.add_block();
        self.cond_br(eq, hit_blk, miss_blk);
        let plain = res.clone();
        self.side_arm(miss_blk, next_pc, move |_| plain);
        self.cur = hit_blk;
        let kk = u16::try_from(k).unwrap();
        let mut refined = res;
        refined.val = boxed;
        refined.repr = Repr::Boxed;
        refined.cls = Some((kk, kk));
        refined.cls_shallow = true;
        refined.cls_slots = true;
        self.stack.push(refined);
    }

    /// The ctor full-layout slot count for the `new` at `pc`.
    pub(super) fn construct_nslots(&self, pc: Pc) -> u32 {
        if let Some(f) = self.likely_mono(pc) {
            if let Some(&n) = self.ctx.ctor_nslots_in.get(&f) {
                return n;
            }
        }
        if let Some(si) = self
            .ctx
            .construct_sites_in
            .get(&Site::new(self.source_id, self.evid_pc(pc)))
        {
            return u32::try_from(si.fields.len()).unwrap().min(16);
        }
        NO_NSLOTS
    }

    /// The allocation-time class word for the construct at `pc` (copied
    /// from translate.rs `construct_alloc_word`).
    pub(super) fn construct_alloc_word(&self, pc: Pc) -> u32 {
        let word_of = |si: &StampCtorIn| {
            early_stamp_word(
                si.layout_id + 1,
                si.masks.iter().any(|m| m.prims() != Prims::EMPTY),
                si.ranges.iter().any(Option::is_some),
            )
        };
        if let Some(f) = self.likely_mono(pc) {
            if let Some(si) = self.ctx.stamp_ctors_in.get(&f) {
                return word_of(si);
            }
        }
        if let Some(si) = self
            .ctx
            .construct_sites_in
            .get(&Site::new(self.source_id, self.evid_pc(pc)))
        {
            return word_of(si);
        }
        // No key: SLOTS still seeds -- the delegate flows' static add
        // checks maintain it (positions are absolute, so an inconsistent
        // flow self-detects by position mismatch), and every unchecked
        // add path clears it conservatively (engine keyless clear; the
        // compiled runtime form's keyless arm).
        CLASS_WORD_SENTINEL | CLASS_WORD_SHALLOW | CLASS_WORD_SLOTS | CLASS_WORD_RANGES
    }

    /// Create the construct `this` for the `new` at `pc`: per-site construct
    /// cell -- if C's shape+gen match and its live `.prototype` equals the
    /// cached proto, nursery-bump an empty `this` with the cached this-shape
    /// -- else the create_this reactor. Every live operand must already be
    /// rooted below `top`. Leaves `this` at `*top_off` (the create_this
    /// out-slot ABI) and lands in a fresh current block; returns the
    /// reactor's ok flag (1 on the bump path).
    pub(super) fn emit_construct_this(
        &mut self,
        pc: Pc,
        top: Value,
        top_off: u32,
        callee_boxed: Value,
        nt_boxed: Value,
        funcidx: Option<Value>,
        want_delta: bool,
    ) -> (Value, Option<Value>) {
        // Site resolved: the compile-time full-layout count. Unresolved
        // but classified: the per-funcidx nslots region (0 = unknown maps
        // to the NO_NSLOTS sentinel), so a dynamically-dispatched ctor
        // still allocates its full layout and its field stores stay on
        // the fixed-slot inline arms.
        let nslots_static = self.construct_nslots(pc);
        let static_word = self.i32_const(self.construct_alloc_word(pc));
        // Region entries pack `nslots | (stampKey+1) << 16` so a
        // dynamically-classified ctor seeds the full keyed alloc word (its
        // instances' adds are then checkable and SLOTS can survive to the
        // stamp -- the generic-path population was bare-sentinel before).
        let (nslots_v, alloc_word_v) = if nslots_static != NO_NSLOTS {
            (self.i32_const(nslots_static), static_word)
        } else if let Some(fidx) = funcidx {
            let base = self.i32_const(NSLOTS_REGION_PLACEHOLDER);
            if self.mode == EmitMode::Code {
                self.ctor_nslots_patches.push(base);
            }
            let four = self.i32_const(4);
            let off = self.binop(Operator::I32Mul, fidx, four, Type::I32);
            let addr = self.binop(Operator::I32Add, base, off, Type::I32);
            let entry = self.load_i32(addr, 0);
            let sent = self.i32_const(NO_NSLOTS);
            let zero_n = self.i32_const(0);
            let nz = self.binop(Operator::I32Ne, entry, zero_n, Type::I32);
            let m16 = self.i32_const(0xFFFF);
            let n16 = self.binop(Operator::I32And, entry, m16, Type::I32);
            let n_v = self.select(Type::I32, n16, sent, nz);
            let sh16 = self.i32_const(16);
            let key = self.binop(Operator::I32ShrU, entry, sh16, Type::I32);
            let ksh = self.i32_const(EARLY_KEY_SHIFT);
            let keybits = self.binop(Operator::I32Shl, key, ksh, Type::I32);
            let seeded = self.i32_const(
                CLASS_WORD_SENTINEL | CLASS_WORD_SHALLOW | CLASS_WORD_SLOTS | CLASS_WORD_RANGES,
            );
            let keyed_w = self.binop(Operator::I32Or, seeded, keybits, Type::I32);
            let k_nz = self.binop(Operator::I32Ne, key, zero_n, Type::I32);
            let bare = self.i32_const(
                CLASS_WORD_SENTINEL | CLASS_WORD_SHALLOW | CLASS_WORD_SLOTS | CLASS_WORD_RANGES,
            );
            let w1 = self.select(Type::I32, keyed_w, bare, k_nz);
            let w_v = self.select(Type::I32, w1, static_word, nz);
            (n_v, w_v)
        } else {
            (self.i32_const(NO_NSLOTS), static_word)
        };
        let cell = {
            // `Code`-only allocation (see emit_instanceof's cell note).
            let idx = if self.mode == EmitMode::Code {
                self.atoms.next_construct_cell()
            } else {
                0
            };
            let c = self.i32_const(CONSTRUCT_CELL_ADDR_PLACEHOLDER);
            self.construct_cell_patches.push((c, idx + 1));
            c
        };
        let done = self.body.add_block();
        let ok_param = self.body.add_blockparam(done, Type::I32);
        // The alloc diamond's per-path effect delta rides a
        // param (bump arm cannot GC and contributes 0; the create_this
        // reactor is may-GC and contributes all-set), so the bump path
        // does not inherit the reactor arm's emission-state saturation
        // and the construct fork can test construct-local cleanliness.
        let entry_flags = self.cur_flags;
        let delta_param = (want_delta || self.flags_threading())
            .then(|| self.body.add_blockparam(done, Type::I32));
        let ct_call_blk = self.body.add_block();
        let one = self.i32_const(1);

        let cptr0 = self.unop(Operator::I32WrapI64, callee_boxed, Type::I32);
        let ashape = self.load_i32(cell, 0);
        let cctorshape = self.load_i32(cell, CONSTRUCT_CELL_CTORSHAPE);
        let cgen = self.load_i32(cell, CONSTRUCT_CELL_GEN);
        let cproto = self.load_i32(cell, CONSTRUCT_CELL_PROTOPTR);
        let cslotenc = self.load_i32(cell, CONSTRUCT_CELL_PROTOSLOTENC);
        let live_ctorshape = self.load_i32(cptr0, SHAPE_OFFSET);
        let gen_addr = self.i32_const(self.helpers.prop_ic_gen_base);
        let live_gen = self.load_i32(gen_addr, 0);
        let zero = self.i32_const(0);
        let g1 = self.binop(Operator::I32Ne, ashape, zero, Type::I32);
        let g2 = self.binop(Operator::I32Eq, cctorshape, live_ctorshape, Type::I32);
        let g3 = self.binop(Operator::I32Eq, cgen, live_gen, Type::I32);
        let ga = self.binop(Operator::I32And, g1, g2, Type::I32);
        let gb = self.binop(Operator::I32And, ga, g3, Type::I32);
        let ck_proto = self.body.add_block();
        self.cond_br(gb, ck_proto, ct_call_blk);

        // ck_proto: Live `.prototype` off C's cached slot == cached proto?
        // (a reassignment leaves C's shape but changes the this-proto.)
        self.cur = ck_proto;
        let pval = self.emit_slot_load(cptr0, cslotenc);
        let p_is_obj = self.tag_eq(pval, TAG_OBJECT as u32);
        let pptr = self.unop(Operator::I32WrapI64, pval, Type::I32);
        let proto_match = self.binop(Operator::I32Eq, pptr, cproto, Type::I32);
        let proto_ok = self.binop(Operator::I32And, p_is_obj, proto_match, Type::I32);
        let bump_blk = self.body.add_block();
        self.cond_br(proto_ok, bump_blk, ct_call_blk);

        // bump_blk: nursery room, then bump + stamp. No room -> reactor.
        self.cur = bump_blk;
        let (store_blk, posp, pos, newpos) = self.emit_nursery_room_guard(cell, 4, ct_call_blk);

        self.cur = store_blk;
        let sc = self.store_i32(posp, 0, newpos);
        self.tag_store(sc, HeapKind::AllocCursor);
        let hdr = self.load_i32(cell, 16);
        let sh = self.store_i32(pos, 0, hdr);
        self.tag_store(sh, HeapKind::Fresh);
        let hdr_bytes = self.i32_const(NURSERY_HEADER_BYTES);
        let obj = self.binop(Operator::I32Add, pos, hdr_bytes, Type::I32);
        let s0 = self.store_i32(obj, SHAPE_OFFSET, ashape);
        self.tag_store(s0, HeapKind::Fresh);
        // Construct allocation: the CONSTRUCTING sentinel + optimistic
        // validity bits, with the early class key when the site (or the
        // region entry) resolved.
        let s1 = self.store_i32(obj, OBJ_CLASS_IDX_OFFSET, alloc_word_v);
        self.tag_store(s1, HeapKind::Fresh);
        let slotsw = self.load_i32(cell, 8);
        let s2 = self.store_i32(obj, OBJ_SLOTS_OFFSET, slotsw);
        self.tag_store(s2, HeapKind::Fresh);
        let elemsw = self.load_i32(cell, 12);
        let s3 = self.store_i32(obj, OBJ_ELEMENTS_OFFSET, elemsw);
        self.tag_store(s3, HeapKind::Fresh);
        let payload = self.unop(Operator::I64ExtendI32U, obj, Type::I64);
        let tag = self.boxed_const(TAG_OBJECT << 32);
        let this_v = self.binop(Operator::I64Or, payload, tag, Type::I64);
        self.store_i64(self.vp, top_off, this_v);
        let mut bump_args = vec![one];
        if delta_param.is_some() {
            bump_args.push(self.i32_const(0));
        }
        self.body.set_terminator(
            self.cur,
            Terminator::Br {
                target: BlockTarget {
                    block: done,
                    args: bump_args,
                },
            },
        );

        self.cur = ct_call_blk;
        let ok_ct = self.call_i32(
            self.helpers.create_this,
            &[
                self.cx,
                top,
                callee_boxed,
                nt_boxed,
                nslots_v,
                cell,
                alloc_word_v,
            ],
        );
        let mut ct_args = vec![ok_ct];
        if delta_param.is_some() {
            ct_args.push(self.i32_const(FLAGS_ALL));
        }
        self.body.set_terminator(
            self.cur,
            Terminator::Br {
                target: BlockTarget {
                    block: done,
                    args: ct_args,
                },
            },
        );
        self.cur = done;
        if let Some(fp) = delta_param {
            // Continuation accumulator = the entry word OR the path delta
            // (the reactor arm's emission-state saturation is discarded --
            // it belongs to that path alone).
            self.cur_flags = entry_flags;
            self.or_flags_word(fp);
        }
        (ok_param, delta_param)
    }

    /// Direct ctor dispatch: a script-backed constructor with
    /// `newTarget == callee` creates `this` inline (per-site construct cell
    /// nursery bump, else the create_this
    /// reactor) and `call_indirect`s the compiled ctor body over the same
    /// frame -- no EnterNight bounce. Everything else falls to the generic
    /// construct helper.
    /// Returns whether the site's MERGE left the Opt track, in which case
    /// the caller must not emit the construct class guard: the guard's
    /// refined fact would be dropped at the next edge.
    pub(super) fn emit_construct_classify(
        &mut self,
        pc: Pc,
        argc: u16,
        need: usize,
        funcidx_in: Option<Value>,
    ) -> Result<bool, String> {
        let len = self.stack.len();
        let callee_op = self.stack[len - need].clone();
        let nt_op = self.stack[len - 1].clone();
        let callee_boxed = self.to_boxed(&callee_op);
        let nt_boxed = self.to_boxed(&nt_op);
        let idx_this = len - need + 1;

        // Arm-free outlined form: the generic construct alone (the
        // this-substitute select kept -- it is the merge tail's semantics).
        // Dirty construct sites never fork (all pre states below are
        // cur_track-gated), so no admission is lost.
        if self.outline_generic() && !self.gen_only && funcidx_in.is_none() {
            let n = self.spill_all();
            let frame_off = self.operand_base + 8 * (n - need as u32);
            let frame_base = self.add_offset(self.vp, frame_off);
            let top_off = self.operand_base + 8 * n;
            let top = self.add_offset(self.vp, top_off);
            let argc_v = self.i32_const(u32::from(argc));
            let nslots_v = self.i32_const(self.construct_nslots(pc));
            let stamp_v = self.i32_const(self.construct_alloc_word(pc));
            let ok = self.call_i32(
                self.helpers.construct,
                &[self.cx, top, frame_base, argc_v, nslots_v, stamp_v],
            );
            self.reload(n);
            let result = self.load_i64(self.vp, top_off);
            let reloaded_this = self.stack[idx_this].val;
            self.branch_on_err(ok);
            for _ in 0..need {
                self.stack.pop();
            }
            let is_obj = self.tag_eq(result, TAG_OBJECT as u32);
            let final_v = self.select(Type::I64, result, reloaded_this, is_obj);
            self.push_boxed(final_v, self.def_type(pc, 0));
            return Ok(false);
        }

        let n = self.spill_all();
        let frame_off = self.operand_base + 8 * (n - need as u32);
        let frame_base = self.add_offset(self.vp, frame_off);
        let top_off = self.operand_base + 8 * n;
        let top = self.add_offset(self.vp, top_off);
        // A splice's miss arm hands down the classify it already ran (the
        // dominating funcidx): the ladder is one compare, not a repeat.
        let funcidx = match funcidx_in {
            Some(f) => f,
            None => self.emit_inline_classify(callee_boxed).0,
        };
        // Construct clean fork gate: a resolved ctor whose scan can
        // yield a clean word, on a live lineage. The clean arm's proof is
        // the construct-local word (create_this delta | ctor word masked
        // of MUT_THIS): 0 = bump-path alloc + a ctor that wrote nothing
        // but its own fresh this and ran no may-GC helper -- the caller's
        // facts, carriers and track all survive.
        let ctor_sid = self.likely_call_target(pc);
        let next_pc = self.cur_op.map(|op| pc + op.len());
        let ctor_scan = ctor_sid.and_then(|sid| {
            let src = self.source;
            match src.object(SourceObjectId::new(sid)) {
                SourceObject::Script(cs) => Some(self.ret_clean_for(ScriptId::new(sid), cs)),
                _ => None,
            }
        });
        // The `new Array()` bump-arm gate -- computed early so the
        // arm can save its own pre-call state: the callee is unresolved
        // (a native), so the ctor-scan gate below never covers it; the
        // arm's identity compare + quiet alloc are themselves the proof.
        let array_arm = funcidx_in.is_none()
            && argc == 0
            && !self.gen_only
            && self.likely_call_target(pc).is_none()
            && self.script_names_array();
        let pre_array = if array_arm && self.cur_track != Track::Dirty && next_pc.is_some() {
            Some(self.arm_state())
        } else {
            None
        };
        let ctor_fork_ok = funcidx_in.is_none()
            && !self.gen_only
            && self.cur_track != Track::Dirty
            && next_pc.is_some()
            && ctor_scan.is_some_and(|c| c != ScanClass::Fail);
        // Which gate turned a construct site down, so the population is a
        // number rather than a guess -- the `flagsite-miss` twin. A site
        // that does not fork has a Dirty continuation for the rest of the
        // body, and construct sites are a meaningful share of departures.
        if self.opts.diagnostics.bbv && self.mode == EmitMode::Code && !ctor_fork_ok {
            let why = if funcidx_in.is_some() {
                "funcidx"
            } else if self.gen_only {
                "gen"
            } else if self.cur_track == Track::Dirty {
                "dirty"
            } else if next_pc.is_none() {
                "nonext"
            } else {
                match ctor_scan {
                    None => "nolikely",
                    Some(ScanClass::Fail) => "scan-fail",
                    Some(_) => "unreachable",
                }
            };
            crate::diag_line!(
                "night: bbv construct-fork-miss sid#{} pc {} why {why} track {:?}",
                self.source_id,
                self.evid_pc(pc),
                self.cur_track,
            );
        }
        // An UNRESOLVED ctor (`new x(...)` through a local) gets the
        // epoch-proven keep arm on its indirect path -- the scripted flag
        // fork's admission, no callee knowledge needed.
        let ctor_keep_ok = funcidx_in.is_none()
            && !self.gen_only
            && self.cur_track != Track::Dirty
            && next_pc.is_some()
            && ctor_scan.is_none()
            && !self.mapped_args_reachable();
        let pre_ctor_unres = ctor_keep_ok.then(|| self.arm_state());
        let pre_ctor_unres_epoch = pre_ctor_unres.is_some().then(|| self.emit_epoch_read());
        let pre_ctor_unres_bind = pre_ctor_unres
            .as_ref()
            .and_then(|_| self.sample_bind_epoch());
        let pre_ctor = if ctor_fork_ok {
            if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
                crate::diag_line!(
                    "night: bbv construct-fork-site sid#{} pc {} ctor {}",
                    self.source_id,
                    self.evid_pc(pc),
                    ctor_sid.unwrap_or(u32::MAX)
                );
            }
            Some(self.arm_state())
        } else {
            None
        };
        let pre_ctor_epoch = pre_ctor.is_some().then(|| self.emit_epoch_read());
        let pre_ctor_bind = pre_ctor.as_ref().and_then(|_| self.sample_bind_epoch());

        let ctor_blk = self.body.add_block();
        let fast_blk = self.body.add_block();
        let fast2_blk = self.body.add_block();
        let slow_blk = self.body.add_block();
        let merge = self.body.add_block();
        let ok_param = self.body.add_blockparam(merge, Type::I32);
        // Construct masking: the merge carries the accumulator as a
        // param so the ctor-call arms can OR the callee's word masked of
        // MUT_THIS (the ctor's own-this writes land in this site's fresh
        // create_this alloc -- and masking only
        // removes MUT_THIS, so the may-GC saturation still arrives as
        // MUT_OTHER and no consumer restores carriers over a GC).
        let merge_flags_param = self
            .flags_threading()
            .then(|| self.body.add_blockparam(merge, Type::I32));
        // `new Array()` bump arm: compare the callee against the
        // pristine-Array-ctor identity cell (a shadowed Array is a
        // different value and self-misses into the generic construct). On
        // hit the result is exactly what `[]` builds -- the
        // emit_alloc_inline machinery in place: a quiet alloc, so the arm
        // enters its own clean continuation (facts, carriers and track
        // intact, result fresh; arm selection is the proof) or, on a
        // lineage the fork gate declined, joins the merge with an
        // untouched flags word.
        let native_tgt = if array_arm {
            self.body.add_block()
        } else {
            slow_blk
        };
        self.cond_br(funcidx, ctor_blk, native_tgt);
        if array_arm {
            self.cur = native_tgt;
            let cellc = self.i32_const(self.helpers.builtin_cells_base + 8 * BC_ARRAY_CTOR);
            let bits = self.load_i64(cellc, 0);
            let is_arr = self.binop(Operator::I64Eq, callee_boxed, bits, Type::I32);
            let arr_blk = self.body.add_block();
            self.cond_br(is_arr, arr_blk, slow_blk);
            self.cur = arr_blk;
            self.emit_alloc_inline(Some(0));
            let arr = self.stack.pop().expect("alloc pushed the array");
            if let Some(pre) = pre_array.as_ref() {
                let pre = pre.clone();
                let next = next_pc.expect("construct fork implies next_pc");
                let k_state = self.arm_state();
                self.arm_restore(pre.clone());
                for _ in 0..need {
                    self.stack.pop();
                }
                self.reload_gc_values();
                self.stack.push(arr);
                let target = self.cont(next);
                self.body
                    .set_terminator(self.cur, Terminator::Br { target });
                self.arm_restore(k_state);
            } else {
                let ab = self.to_boxed(&arr);
                self.store_i64(self.vp, top_off, ab);
                let one = self.i32_const(1);
                let mut margs = vec![one];
                if merge_flags_param.is_some() {
                    margs.push(self.materialize_flags());
                }
                self.body.set_terminator(
                    self.cur,
                    Terminator::Br {
                        target: BlockTarget {
                            block: merge,
                            args: margs,
                        },
                    },
                );
            }
        }

        // Constructor-shape guards (loads safe: funcidx != 0 proves a
        // script-backed JSFunction).
        self.cur = ctor_blk;
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
        let fits = self.emit_stack_fits(top, argc);
        let a = self.binop(Operator::I32And, is_ctor, is_normal, Type::I32);
        let b = self.binop(Operator::I32And, nt_eq, fits, Type::I32);
        let take_fast = self.binop(Operator::I32And, a, b, Type::I32);
        self.cond_br(take_fast, fast_blk, slow_blk);

        // Fast arm step 1: create `this` (operands already spilled/rooted).
        self.cur = fast_blk;
        let (ok_ct, ct_delta) = self.emit_construct_this(
            pc,
            top,
            top_off,
            callee_boxed,
            nt_boxed,
            Some(funcidx),
            pre_ctor.is_some(),
        );
        let zero_ok = self.i32_const(0);
        let mut fail_args = vec![zero_ok];
        if merge_flags_param.is_some() {
            fail_args.push(self.materialize_flags());
        }
        self.body.set_terminator(
            self.cur,
            Terminator::CondBr {
                cond: ok_ct,
                if_true: BlockTarget {
                    block: fast2_blk,
                    args: vec![],
                },
                if_false: BlockTarget {
                    block: merge,
                    args: fail_args,
                },
            },
        );

        // Fast arm step 2: splice `this` into frame[1] (memory, both arms
        // share the spilled frame), re-derive the callee script from the
        // reloaded frame slot (create_this may have GC-moved it), and call
        // the ctor body with the real new.target reloaded likewise.
        self.cur = fast2_blk;
        let this_val = self.load_i64(self.vp, top_off);
        self.store_i64(self.vp, frame_off + 8, this_val);
        let callee_re = self.load_i64(self.vp, frame_off);
        let cptr = self.unop(Operator::I32WrapI64, callee_re, Type::I32);
        let script2 = self.load_i32(cptr, FUNC_SCRIPT_SLOT_OFFSET);
        let idx2 = self.load_i32(script2, BASESCRIPT_NIGHTFUNCINDEX_OFFSET);
        let argc_v = self.i32_const(u32::from(argc));
        let nt_re = self.load_i64(self.vp, frame_off + 8 * (2 + u32::from(argc)));
        let args = [self.cx, frame_base, argc_v, top, script2, nt_re];
        // Likely-ctor direct arm: the same static-target principle as the
        // call side, applied to construct dispatch. This is what serves a
        // class-factory idiom (`Class.create`-style wrappers), whose sites
        // decline every splice as `mapped-args` and would otherwise have the
        // classify's `call_indirect` as their whole dispatch. The kind/ctor-shape
        // guards above already routed class ctors to the generic arm, so the
        // resolved target here is always an ordinary ctor body.
        if let Some(sid) = self.likely_call_target(pc) {
            let expected = self.i32_const(u32::MAX);
            let likely_blk = self.body.add_block();
            let indirect_blk = self.body.add_block();
            let is_likely = self.binop(Operator::I32Eq, idx2, expected, Type::I32);
            self.cond_br(is_likely, likely_blk, indirect_blk);
            self.cur = likely_blk;
            // Bodies carry the widened (err, eff) ABI, so the patched
            // direct call must too; construct sites do not fork on the
            // word but DO OR it into the accumulator masked of MUT_THIS
            // The ctor's own-this writes land in this site's
            // fresh create_this alloc and cannot falsify caller facts.
            let (callv, err, eff) = self.call_abi2(self.helpers.direct_call_stub2, &args);
            self.likely_patches.push((expected, callv, sid));
            let ok_likely = self.unop(Operator::I32Eqz, err, Type::I32);
            let saved = self.cur_flags;
            let mo = self.i32_const(FLAG_MUT_OTHER | FLAG_STAMPS | FLAG_BIND);
            let masked = self.binop(Operator::I32And, eff, mo, Type::I32);
            self.or_flags_word(masked);
            let mut margs = vec![ok_likely];
            if merge_flags_param.is_some() {
                margs.push(self.materialize_flags());
            }
            self.cur_flags = saved;
            if let (Some(pre), Some(delta)) = (pre_ctor.as_ref(), ct_delta) {
                let pre = pre.clone();
                let word = self.binop(Operator::I32Or, delta, masked, Type::I32);
                let mark_fresh = self.ctor_returns_this(ScriptId::new(sid));
                self.emit_construct_clean_fork(
                    ok_likely,
                    word,
                    &pre,
                    need,
                    top_off,
                    frame_off + 8,
                    pc,
                    next_pc.expect("construct fork implies next_pc"),
                    mark_fresh,
                    merge,
                    margs,
                    pre_ctor_epoch,
                    pre_ctor_bind,
                );
            } else {
                self.body.set_terminator(
                    self.cur,
                    Terminator::Br {
                        target: BlockTarget {
                            block: merge,
                            args: margs,
                        },
                    },
                );
            }
            self.cur = indirect_blk;
        }
        let (_iv, err, eff) = self.call_indirect_abi2(&args, idx2);
        let ok_fast = self.unop(Operator::I32Eqz, err, Type::I32);
        let mo = self.i32_const(FLAG_MUT_OTHER | FLAG_STAMPS | FLAG_BIND);
        let masked = self.binop(Operator::I32And, eff, mo, Type::I32);
        let saved = self.cur_flags;
        self.or_flags_word(masked);
        let mut margs = vec![ok_fast];
        if merge_flags_param.is_some() {
            margs.push(self.materialize_flags());
        }
        self.cur_flags = saved;
        if let (Some(pre), Some(pre_e)) = (pre_ctor_unres.as_ref(), pre_ctor_unres_epoch) {
            // The construct fork's arms (this-substitute included: a ctor
            // returning undefined constructs `this`), with a saturated word
            // so only the epoch admits the keep -- never `emit_flag_fork`,
            // whose continuation pushes the raw return value.
            let pre = pre.clone();
            let saturated = self.i32_const(FLAG_MUT_OTHER | FLAG_STAMPS | FLAG_BIND);
            self.emit_construct_clean_fork(
                ok_fast,
                saturated,
                &pre,
                need,
                top_off,
                frame_off + 8,
                pc,
                next_pc.expect("ctor keep implies next_pc"),
                false,
                merge,
                margs,
                Some(pre_e),
                pre_ctor_unres_bind,
            );
        } else {
            self.body.set_terminator(
                self.cur,
                Terminator::Br {
                    target: BlockTarget {
                        block: merge,
                        args: margs,
                    },
                },
            );
        }

        // Slow arm: the generic construct over the same frame.
        self.cur = slow_blk;
        let argc_v2 = self.i32_const(u32::from(argc));
        let nslots_v2 = self.i32_const(self.construct_nslots(pc));
        let stamp_v2 = self.i32_const(self.construct_alloc_word(pc));
        let pre_e_slow = pre_ctor_unres.as_ref().map(|_| self.emit_epoch_read());
        let pre_b_slow = pre_ctor_unres
            .as_ref()
            .and_then(|_| self.sample_bind_epoch());
        let ok_slow = self.call_i32(
            self.helpers.construct,
            &[self.cx, top, frame_base, argc_v2, nslots_v2, stamp_v2],
        );
        let mut slow_margs = vec![ok_slow];
        if merge_flags_param.is_some() {
            // The generic construct helper is may-GC: state is saturated.
            slow_margs.push(self.materialize_flags());
        }
        if let (Some(pre), Some(pre_e)) = (pre_ctor_unres.as_ref(), pre_e_slow) {
            // The generic construct (an unresolved or uncompiled ctor)
            // takes the same epoch-proven keep as the indirect path, through
            // the construct fork's arms (this-substitute included).
            let pre = pre.clone();
            let saturated = self.i32_const(FLAG_MUT_OTHER | FLAG_STAMPS | FLAG_BIND);
            self.emit_construct_clean_fork(
                ok_slow,
                saturated,
                &pre,
                need,
                top_off,
                frame_off + 8,
                pc,
                next_pc.expect("ctor keep implies next_pc"),
                false,
                merge,
                slow_margs,
                Some(pre_e),
                pre_b_slow,
            );
        } else {
            self.body.set_terminator(
                self.cur,
                Terminator::Br {
                    target: BlockTarget {
                        block: merge,
                        args: slow_margs,
                    },
                },
            );
        }

        // Merge: reload, this-substitute (the fast arm's ctor may return a
        // primitive; the generic arm always returns an object, so the
        // select is uniform).
        self.cur = merge;
        if let Some(fp) = merge_flags_param {
            self.cur_flags = FlagsAcc::Dyn(fp, 0);
        }
        self.reload(n);
        let result = self.load_i64(self.vp, top_off);
        let reloaded_this = self.stack[idx_this].val;
        self.branch_on_err(ok_param);
        for _ in 0..need {
            self.stack.pop();
        }
        let is_obj = self.tag_eq(result, TAG_OBJECT as u32);
        let final_v = self.select(Type::I64, result, reloaded_this, is_obj);
        self.push_boxed(final_v, self.def_type(pc, 0));
        // The construct result is fresh only when the resolved ctor
        // provably yields the site's own create_this alloc -- an
        // object-returning ctor substitutes an object we know nothing
        // about (it may be pre-existing).
        if let Some(sid) = self.likely_call_target(pc) {
            if self.ctor_returns_this(ScriptId::new(sid)) {
                if let Some(o) = self.stack.last_mut() {
                    o.fresh = true;
                }
            }
        }
        // The merge is not an Opt arrival when the site armed a clean or
        // keep continuation. Every arm that reaches it was offered a proof
        // of the construct's intactness and failed it, so by ruling 1 it
        // conforms to nothing and belongs on GEN -- the call side's
        // `keep_fork_merge_stepped_track`, at the site family that was
        // still missing it.
        //
        // Leaving it on Opt is not merely imprecise, it is destructive:
        // `next_pc`'s prediction is the join of EVERY Opt arrival there, so
        // this arm's fact-free context erases the caller's class facts for
        // the fork arms too, and the two arrivals are complementary (the
        // fork arms carry the caller's facts and not the result's class;
        // the merge carries the result's class and not the caller's facts),
        // so the join keeps neither. The merge is a rare arrival next to
        // the fork arms' takes, and disproportionately the weaker one
        // wherever a class fact is lost at that join.
        //
        // The trigger is the two RUNTIME INTACTNESS PROOFS and nothing else,
        // mirroring the call side's `flag_site`. The `new Array()` bump arm
        // is deliberately not one: its miss is an identity compare that
        // resolved to a different callee, and a classify is not an arm.
        let stepped = match next_pc {
            Some(next) if pre_ctor.is_some() || pre_ctor_unres.is_some() => {
                self.keep_fork_merge_stepped_track(next);
                true
            }
            _ => false,
        };
        Ok(stepped)
    }

    /// Whether `sid`'s body can only complete with rval = undefined (no
    /// Return, no SetRval anywhere): the construct's this-substitute then
    /// always selects the fresh `this`. Memoized.
    pub(super) fn ctor_returns_this(&mut self, sid: ScriptId) -> bool {
        if let Some(&b) = self.ctor_ret_this.get(&sid) {
            return b;
        }
        let b = match self.source.object(sid.source()) {
            SourceObject::Script(cs) => !cs
                .parser()
                .opcodes()
                .any(|op| matches!(op, JSOp::Return | JSOp::SetRval)),
            _ => false,
        };
        self.ctor_ret_this.insert(sid, b);
        b
    }
}
