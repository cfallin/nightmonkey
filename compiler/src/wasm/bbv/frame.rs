/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Frame-level lowerings: the prologue, exception unwinding, GC write
//! barriers, environments and aliased slots, local/argument access, and the
//! return path.

use super::*;
use crate::source::ScopeData;

// --- exceptions ----------------------------------------------------------

/// Which slot holds the object a layout stamp writes.
#[derive(Clone, Copy)]
pub(super) enum StampRecv {
    This,
    Formal(u32),
    /// An already-loaded boxed value (a local's carrier).
    Boxed(Value),
}

impl<'a> Bbv<'a> {
    /// Walk the try-notes for an exception at `self.cur_pc` exactly as the
    /// interpreter's `TryNoteIter::settle` + `ProcessTryNotes` do.
    pub(super) fn walk_try_notes(
        &self,
        cur_depth: usize,
    ) -> (Vec<UnwindClose>, Option<(Pc, u32, bool)>) {
        self.walk_try_notes_impl(cur_depth, false)
    }

    /// The same walk with every `Catch` note passed over, which is what a
    /// generator body's forced-`.return()` unwind does: only finallys run.
    /// Mirrors `ProcessTryNotes`' `isClosingGenerator` skip.
    pub(super) fn walk_try_notes_skip_catches(
        &self,
        cur_depth: usize,
    ) -> (Vec<UnwindClose>, Option<(Pc, u32, bool)>) {
        self.walk_try_notes_impl(cur_depth, true)
    }

    fn walk_try_notes_impl(
        &self,
        cur_depth: usize,
        skip_catches: bool,
    ) -> (Vec<UnwindClose>, Option<(Pc, u32, bool)>) {
        let pc = self.cur_pc;
        let notes = &self.script.try_notes;
        let n = notes.len();
        let in_range = |t: &crate::bytecode::TryNote| pc >= t.start && pc < t.start + t.length;
        let mut forin = Vec::new();
        let mut i = 0;
        while i < n {
            let t = &notes[i];
            if !in_range(t) {
                i += 1;
                continue;
            }
            if matches!(t.kind, TryNoteKind::ForOfIterClose) {
                let mut depth = 1u32;
                i += 1;
                while depth > 0 && i < n {
                    let u = &notes[i];
                    if in_range(u) {
                        match u.kind {
                            TryNoteKind::ForOfIterClose => depth += 1,
                            TryNoteKind::ForOf => depth -= 1,
                            _ => {}
                        }
                    }
                    i += 1;
                }
                continue;
            }
            if usize::try_from(t.stack_depth).unwrap() > cur_depth {
                i += 1;
                continue;
            }
            match t.kind {
                TryNoteKind::Catch => {
                    if skip_catches {
                        i += 1;
                        continue;
                    }
                    return (forin, Some((t.start + t.length, t.stack_depth, false)));
                }
                TryNoteKind::Finally => {
                    return (forin, Some((t.start + t.length, t.stack_depth, true)));
                }
                TryNoteKind::ForIn => {
                    forin.push(UnwindClose::ForIn(t.stack_depth));
                    i += 1;
                }
                TryNoteKind::Destructuring => {
                    forin.push(UnwindClose::Destructuring(t.stack_depth));
                    i += 1;
                }
                TryNoteKind::ForOf | TryNoteKind::Loop | TryNoteKind::ForOfIterClose => {
                    i += 1;
                }
            }
        }
        (forin, None)
    }

    /// The handler landing target: catch/finally landing pad, or the error
    /// epilogue when none.
    pub(super) fn handler_target(&mut self, handler: Option<(Pc, u32, bool)>) -> BlockTarget {
        let target = match handler {
            Some((handler_pc, stack_depth, false)) => self.edge_to_unwound(handler_pc, stack_depth),
            Some((handler_pc, stack_depth, true)) => self.edge_to_finally(handler_pc, stack_depth),
            None => BlockTarget {
                block: self.error_block(),
                args: vec![],
            },
        };
        match handler {
            Some((handler_pc, _, _)) => self.unwind_env_to(handler_pc, target),
            None => target,
        }
    }

    /// The scopes of `script` that own an environment object: the operands
    /// of the ops that push one. A block scope absent here adds nothing to
    /// the frame's environment chain.
    fn env_scopes_of(script: &Script) -> Vec<u32> {
        let mut out = Vec::new();
        let mut p = script.parser();
        while let Some(op) = p.next_op() {
            let len = usize::try_from(op.len()).unwrap();
            if matches!(
                op,
                JSOp::PushLexicalEnv | JSOp::PushClassBodyEnv | JSOp::PushVarEnv | JSOp::EnterWith
            ) {
                match p.next_uint32() {
                    Some(idx) => out.push(idx),
                    None => break,
                }
                if len > 5 && p.advance(len - 5).is_none() {
                    break;
                }
            } else if len > 1 && p.advance(len - 1).is_none() {
                break;
            }
        }
        out
    }

    /// How many environment objects the frame's chain holds above the
    /// body's own at `pc`: the env-bearing block scopes whose notes cover it.
    fn env_depth_at(&mut self, pc: Pc) -> u32 {
        if self.env_scopes.is_none() {
            self.env_scopes = Some(Self::env_scopes_of(self.script));
        }
        let scopes = self.env_scopes.as_ref().unwrap();
        let n = self
            .script
            .scope_notes
            .iter()
            .filter(|n| pc >= n.start && pc < n.start + n.length)
            .filter(|n| scopes.contains(&n.gcthing_index))
            .count();
        u32::try_from(n).unwrap()
    }

    /// A handler runs at its `Try`'s environment, while a throw from a
    /// deeper block leaves the frame's env slot on that block's
    /// environment. The difference is static (the scope notes), so the
    /// edge pops it in a trampoline, as the interpreter's UnwindEnvironment
    /// does on the way to the handler.
    fn unwind_env_to(&mut self, handler_pc: Pc, target: BlockTarget) -> BlockTarget {
        if !self.needs_env || self.cur_seg.is_some() {
            return target;
        }
        let Some(try_start) = self
            .script
            .try_notes
            .iter()
            .find(|t| {
                matches!(t.kind, TryNoteKind::Catch | TryNoteKind::Finally)
                    && t.start + t.length == handler_pc
            })
            .map(|t| t.start)
        else {
            return target;
        };
        // The `Try` op precedes the note's range (UnwindEnvironmentToTryPc).
        let try_pc = Pc::new(try_start.get() - 1);
        let site = self.cur_pc;
        let k = self
            .env_depth_at(site)
            .saturating_sub(self.env_depth_at(try_pc));
        if k == 0 {
            return target;
        }
        let tramp = self.body.add_block();
        let save = self.cur;
        self.cur = tramp;
        let mut env = self.load_i64(self.vp, self.env_slot_off);
        for _ in 0..k {
            let envptr = self.unop(Operator::I32WrapI64, env, Type::I32);
            env = self.load_i64(envptr, FIXED_SLOTS_BASE);
        }
        self.store_i64(self.vp, self.env_slot_off, env);
        self.body.set_terminator(tramp, Terminator::Br { target });
        self.cur = save;
        BlockTarget {
            block: tramp,
            args: Vec::new(),
        }
    }

    /// The branch target for an exception raised at `self.cur_pc`.
    /// Handler continuations enter the GEN version: an exception path is a
    /// slow path, and a slow path carries no facts.
    pub(super) fn exception_target(&mut self) -> BlockTarget {
        let (closes, handler) = self.walk_try_notes(self.stack.len());
        // A generator body whose innermost handler is a CATCH needs the
        // closing split (generator.rs): a forced `.return()` unwind skips
        // catches, so which handler this edge lands on is a runtime test.
        if self.is_generator && matches!(handler, Some((_, _, false))) {
            return self.exception_target_gen_catch(closes, handler);
        }
        if closes.is_empty() {
            return self.handler_target(handler);
        }
        let needs_spill = closes
            .iter()
            .any(|c| matches!(c, UnwindClose::Destructuring(_)));
        let saved_cur = self.cur;
        let t = self.body.add_block();
        self.cur = t;
        let target = if !needs_spill {
            for c in &closes {
                if let UnwindClose::ForIn(depth) = *c {
                    let iter = self.stack[depth as usize - 1].clone();
                    let ib = self.to_boxed(&iter);
                    let ei = self.helpers.end_iter;
                    self.call_void(ei, &[self.cx, ib]);
                }
            }
            self.handler_target(handler)
        } else {
            let n = self.stack.len() as u32;
            for i in 0..n {
                let o = self.stack[i as usize].clone();
                let b = self.to_boxed(&o);
                self.store_i64(self.vp, self.operand_base + 8 * i, b);
            }
            let top = self.add_offset(self.vp, self.operand_base + 8 * n);
            for c in &closes {
                match *c {
                    UnwindClose::ForIn(depth) => {
                        let ib = self.load_i64(self.vp, self.operand_base + 8 * (depth - 1));
                        let ei = self.helpers.end_iter;
                        self.call_void(ei, &[self.cx, ib]);
                    }
                    UnwindClose::Destructuring(depth) => {
                        let db = self.load_i64(self.vp, self.operand_base + 8 * (depth - 1));
                        let ib = self.load_i64(self.vp, self.operand_base + 8 * (depth - 2));
                        let cife = self.helpers.close_iter_for_exception;
                        self.call_void(cife, &[self.cx, top, db, ib]);
                    }
                }
            }
            let mut reloaded = self.stack.clone();
            for i in 0..n {
                let v = self.load_i64(self.vp, self.operand_base + 8 * i);
                reloaded[i as usize].val = v;
                reloaded[i as usize].repr = Repr::Boxed;
            }
            let saved_stack = std::mem::replace(&mut self.stack, reloaded);
            let target = self.handler_target(handler);
            self.stack = saved_stack;
            target
        };
        self.body.set_terminator(t, Terminator::Br { target });
        self.cur = saved_cur;
        BlockTarget {
            block: t,
            args: vec![],
        }
    }

    /// Edge to a finally's exceptional-entry landing pad.
    ///
    /// The landing is shared by every throw site of the try range (one
    /// token class), so every site-specific write-back -- the deferred raw
    /// stores of this site's stale locals, the parent frame's carriers --
    /// happens in the site's own block; the shared pad flushes nothing,
    /// since a pad that flushed one site's values would corrupt every
    /// other site sharing it.
    pub(super) fn edge_to_finally(&mut self, finally_pc: Pc, stack_depth: u32) -> BlockTarget {
        self.flush_stale_locals(&[]);
        self.frame_stale.clear();
        let empty = Ctx::default();
        self.flush_outer_dropped(None, &empty);
        let depth = usize::try_from(stack_depth).unwrap();
        let args: Vec<Value> = (0..depth)
            .map(|i| {
                let o = self.stack[i].clone();
                self.to_boxed(&o)
            })
            .collect();
        let toks = self.out_tokens_for(finally_pc);
        let lp = self.get_or_build_finally_landing(finally_pc, stack_depth, toks);
        BlockTarget { block: lp, args }
    }

    pub(super) fn get_or_build_finally_landing(
        &mut self,
        finally_pc: Pc,
        stack_depth: u32,
        toks: Vec<(u32, u64)>,
    ) -> Block {
        if let Some(&b) = self.finally_landing.get(&(finally_pc.get(), toks.clone())) {
            return b;
        }
        let lp = self.body.add_block();
        let depth = usize::try_from(stack_depth).unwrap();
        let mut base_params = Vec::with_capacity(depth);
        for _ in 0..depth {
            base_params.push(self.body.add_blockparam(lp, Type::I64));
        }
        self.finally_landing
            .insert((finally_pc.get(), toks.clone()), lp);
        let saved_cur = self.cur;
        let base_stack: Vec<Operand> = base_params
            .iter()
            .map(|&v| Operand::plain(v, Repr::Boxed, bottom_ty()))
            .collect();
        let saved_stack = std::mem::replace(&mut self.stack, base_stack);
        self.cur = lp;
        let exc_off = self.operand_base + 8 * stack_depth;
        let stack_off = exc_off + 8;
        let exc_addr = self.add_offset(self.vp, exc_off);
        let stack_addr = self.add_offset(self.vp, stack_off);
        let gef = self.helpers.get_exception_for_finally;
        let ok = self.call_i32(gef, &[self.cx, exc_addr, stack_addr]);
        let saved_pc = self.cur_pc;
        self.cur_pc = finally_pc;
        self.branch_on_err(ok);
        self.cur_pc = saved_pc;
        let exc = self.load_i64(self.vp, exc_off);
        let exc_stack = self.load_i64(self.vp, stack_off);
        let true_val = self.boxed_const((TAG_BOOLEAN << 32) | 1);
        self.push_boxed(exc, prim_desc(Prims::EMPTY));
        self.push_boxed(exc_stack, prim_desc(Prims::EMPTY));
        self.push_boxed(true_val, prim_desc(PRIM_BOOLEAN));
        // The landing is shared across the try range's throw sites within
        // one token class: its continuation is fact-stripped by definition
        // -- a slow path carries no facts -- never the facts of whichever
        // emission happened to build it.
        let depth_here = self.stack.len();
        // No site's write-backs belong in the shared pad (see
        // `edge_to_finally`): the seam sees nothing stale and no carriers.
        let saved_stale = std::mem::take(&mut self.frame_stale);
        let n_outer = self.outer_ssa.len();
        let saved_outer_ssa = std::mem::replace(&mut self.outer_ssa, vec![None; n_outer]);
        let target = self.cont_stripped(finally_pc, depth_here);
        self.frame_stale = saved_stale;
        self.outer_ssa = saved_outer_ssa;
        self.body
            .set_terminator(self.cur, Terminator::Br { target });
        self.cur = saved_cur;
        self.stack = saved_stack;
        lp
    }

    /// Edge to the catch handler at `pc`, unwinding to `stack_depth`.
    /// Fact-stripped and on the `Dirty` track like every other exceptional
    /// landing. It goes through the ordinary continuation seam, so
    /// `cont_at` and `run_version` cannot disagree about the param layout.
    pub(super) fn edge_to_unwound(&mut self, pc: Pc, stack_depth: u32) -> BlockTarget {
        let depth = usize::try_from(stack_depth).unwrap();
        self.cont_stripped(pc, depth)
    }

    // --- write barriers --------------------------------------------------

    pub(super) fn emit_pre_write_barrier_addr(&mut self, slot_addr: Value) {
        let zone = self.load_i32(self.cx, JSCONTEXT_ZONE_OFFSET);
        let flag = self.load_i32(zone, ZONE_NEEDS_BARRIER_OFFSET);
        let marking_blk = self.body.add_block();
        let cont_blk = self.body.add_block();
        self.body.set_terminator(
            self.cur,
            Terminator::CondBr {
                cond: flag,
                if_true: BlockTarget {
                    block: marking_blk,
                    args: vec![],
                },
                if_false: BlockTarget {
                    block: cont_blk,
                    args: vec![],
                },
            },
        );
        self.cur = marking_blk;
        let oldval = self.load_i64(slot_addr, 0);
        let pwb = self.helpers.pre_write_barrier;
        self.call_void(pwb, &[oldval]);
        self.body.set_terminator(
            marking_blk,
            Terminator::Br {
                target: BlockTarget {
                    block: cont_blk,
                    args: vec![],
                },
            },
        );
        self.cur = cont_blk;
    }

    pub(super) fn emit_owner_tenured_gate(&mut self, owner_boxed: Value, cont_blk: Block) {
        let owner_cell = self.unop(Operator::I32WrapI64, owner_boxed, Type::I32);
        let mask = self.i32_const(NOT_CHUNK_MASK);
        let owner_chunk = self.binop(Operator::I32And, owner_cell, mask, Type::I32);
        let owner_sb = self.load_i32(owner_chunk, CHUNK_STORE_BUFFER_OFFSET);
        let tenured_blk = self.body.add_block();
        self.body.set_terminator(
            self.cur,
            Terminator::CondBr {
                cond: owner_sb,
                if_true: BlockTarget {
                    block: cont_blk,
                    args: vec![],
                },
                if_false: BlockTarget {
                    block: tenured_blk,
                    args: vec![],
                },
            },
        );
        self.cur = tenured_blk;
    }

    pub(super) fn emit_post_write_barrier(
        &mut self,
        owner_boxed: Value,
        slot_v: Value,
        val_boxed: Value,
    ) {
        let helper = self.helpers.post_write_barrier;
        self.emit_post_write_barrier_common(owner_boxed, slot_v, val_boxed, helper);
    }

    /// Element form of the generational post-write barrier: records the
    /// element store-buffer edge, passing the element `idx`.
    pub(super) fn emit_post_write_barrier_elem(
        &mut self,
        owner_boxed: Value,
        idx: Value,
        val_boxed: Value,
    ) {
        let helper = self.helpers.post_write_barrier_elem;
        self.emit_post_write_barrier_common(owner_boxed, idx, val_boxed, helper);
    }

    pub(super) fn emit_post_write_barrier_common(
        &mut self,
        owner_boxed: Value,
        slot_v: Value,
        val_boxed: Value,
        helper: Func,
    ) {
        let cont_blk = self.body.add_block();
        self.emit_owner_tenured_gate(owner_boxed, cont_blk);
        let shift = self.boxed_const(32);
        let tag64 = self.binop(Operator::I64ShrU, val_boxed, shift, Type::I64);
        let tag = self.unop(Operator::I32WrapI64, tag64, Type::I32);
        let min = self.i32_const(VAL_GCTHING_TAG_MIN);
        let is_gc = self.binop(Operator::I32GeU, tag, min, Type::I32);
        let gc_blk = self.body.add_block();
        self.body.set_terminator(
            self.cur,
            Terminator::CondBr {
                cond: is_gc,
                if_true: BlockTarget {
                    block: gc_blk,
                    args: vec![],
                },
                if_false: BlockTarget {
                    block: cont_blk,
                    args: vec![],
                },
            },
        );
        self.cur = gc_blk;
        let cell = self.unop(Operator::I32WrapI64, val_boxed, Type::I32);
        let mask = self.i32_const(NOT_CHUNK_MASK);
        let chunk = self.binop(Operator::I32And, cell, mask, Type::I32);
        let sb = self.load_i32(chunk, CHUNK_STORE_BUFFER_OFFSET);
        let barrier_blk = self.body.add_block();
        self.body.set_terminator(
            gc_blk,
            Terminator::CondBr {
                cond: sb,
                if_true: BlockTarget {
                    block: barrier_blk,
                    args: vec![],
                },
                if_false: BlockTarget {
                    block: cont_blk,
                    args: vec![],
                },
            },
        );
        self.cur = barrier_blk;
        self.call_void(helper, &[owner_boxed, slot_v, val_boxed]);
        self.body.set_terminator(
            barrier_blk,
            Terminator::Br {
                target: BlockTarget {
                    block: cont_blk,
                    args: vec![],
                },
            },
        );
        self.cur = cont_blk;
    }

    // --- prologue / env / closures ---------------------------------------

    pub(super) fn emit_formal_padding(&mut self) {
        let nargs = u32::from(self.script.nargs);
        if nargs == 0 {
            return;
        }
        let undef = self.boxed_const(TAG_UNDEFINED << 32);
        for i in 0..nargs {
            let off = 16 + 8 * i;
            let cur = self.load_i64(self.sp, off);
            let i_const = self.i32_const(i);
            let keep = self.binop(Operator::I32LtU, i_const, self.argc, Type::I32);
            let v = self.select(Type::I64, cur, undef, keep);
            self.store_i64(self.sp, off, v);
        }
    }

    /// A Function body scope without its own environment: env head =
    /// `callee->environment()`.
    pub(super) fn env_is_plain(&self) -> bool {
        let Some(bs_id) = self.script.body_scope else {
            return false;
        };
        matches!(
            self.source.object(bs_id),
            SourceObject::Scope(ScopeData {
                kind: 0,
                has_environment: false,
                ..
            })
        )
    }

    pub(super) fn emit_env_setup(&mut self) {
        let undef = self.boxed_const(TAG_UNDEFINED << 32);
        self.store_i64(self.vp, self.env_slot_off, undef);
        if self.env_is_plain() {
            let callee_boxed = self.load_i64(self.sp, 0);
            let callee_ptr = self.unop(Operator::I32WrapI64, callee_boxed, Type::I32);
            let env_boxed = self.load_i64(callee_ptr, FUNC_ENV_SLOT_OFFSET);
            self.store_i64(self.vp, self.env_slot_off, env_boxed);
            return;
        }
        let es = self.helpers.env_setup;
        let sp = self.sp;
        let script = self.cur_script_value();
        let result = self.rt_call(es, true, |_, _| vec![sp, script]).unwrap();
        self.store_i64(self.vp, self.env_slot_off, result);
    }

    /// The (boxed env, slot address) of aliased binding `(hops, slot)` at
    /// `pc`. The environment object's fixed-slot count is a property of its
    /// scope's template shape, so when the snapshot carried it the slot is
    /// addressed statically -- one load per hop and one for the slot --
    /// instead of decoding the fixed/dynamic split from the live shape on
    /// every access (5 loads and 11 alu).
    pub(super) fn emit_aliased_addr(&mut self, pc: Pc, hops: u16, slot: u32) -> (Value, Value) {
        let mut env_boxed = self.load_i64(self.vp, self.env_slot_off);
        let mut envptr = self.unop(Operator::I32WrapI64, env_boxed, Type::I32);
        for _ in 0..hops {
            env_boxed = self.load_i64(envptr, FIXED_SLOTS_BASE);
            envptr = self.unop(Operator::I32WrapI64, env_boxed, Type::I32);
        }
        if let Some(nfixed) = self.aliased_env_nfixed(pc, hops) {
            let addr = if slot < nfixed {
                self.add_offset(envptr, FIXED_SLOTS_BASE + 8 * slot)
            } else {
                let slots_ptr = self.load_i32(envptr, NATIVE_SLOTS_OFFSET);
                self.add_offset(slots_ptr, 8 * (slot - nfixed))
            };
            return (env_boxed, addr);
        }
        let shape = self.load_i32(envptr, SHAPE_OFFSET);
        let imm = self.load_i32(shape, SHAPE_IMMUTABLE_FLAGS_OFFSET);
        let shift = self.i32_const(SHAPE_FIXED_SLOTS_SHIFT);
        let sh = self.binop(Operator::I32ShrU, imm, shift, Type::I32);
        let mask = self.i32_const(SHAPE_FIXED_SLOTS_MASK_BITS);
        let fixed = self.binop(Operator::I32And, sh, mask, Type::I32);
        let slot_v = self.i32_const(slot);
        let is_dynamic = self.binop(Operator::I32GeU, slot_v, fixed, Type::I32);
        let slot_minus = self.binop(Operator::I32Sub, slot_v, fixed, Type::I32);
        let idx = self.select(Type::I32, slot_minus, slot_v, is_dynamic);
        let fixed_base = self.add_offset(envptr, FIXED_SLOTS_BASE);
        let slots_ptr = self.load_i32(envptr, NATIVE_SLOTS_OFFSET);
        let base = self.select(Type::I32, slots_ptr, fixed_base, is_dynamic);
        let three = self.i32_const(3);
        let off = self.binop(Operator::I32Shl, idx, three, Type::I32);
        let addr = self.binop(Operator::I32Add, base, off, Type::I32);
        (env_boxed, addr)
    }

    /// `numFixedSlots` of the environment `hops` scopes up from `pc`'s
    /// scope, when the snapshot recorded that scope's template shape.
    fn aliased_env_nfixed(&self, pc: Pc, hops: u16) -> Option<u32> {
        let seg_base = self.cur_seg.map(|i| self.segs[i].base).unwrap_or(0);
        let lpc = pc - seg_base;
        let scope = crate::source::aliased_scope_at(self.source, self.script, lpc, hops)?;
        match self.source.object(scope) {
            SourceObject::Scope(ScopeData { env_nfixed, .. }) => *env_nfixed,
            _ => None,
        }
    }

    pub(super) fn emit_get_aliased(&mut self, pc: Pc, hops: u16, slot: u32) {
        let (_env, addr) = self.emit_aliased_addr(pc, hops, slot);
        let result = self.load_i64(addr, 0);
        let key = Site::new(self.source_id, self.evid_pc(pc));
        if let Some(&claim) = self.ctx.facts.aliased_sites.get(&key) {
            let next_pc = pc + JSOp::GetAliasedVar.len();
            self.push_load_typed(result, claim, next_pc, Prov::C_ALIAS);
            return;
        }
        self.push_boxed(result, self.def_type(pc, 0));
    }

    pub(super) fn emit_set_aliased(&mut self, pc: Pc, hops: u16, slot: u32) -> Result<(), String> {
        let val = self
            .stack
            .last()
            .cloned()
            .ok_or("SetAliasedVar on empty stack")?;
        let val_boxed = self.to_boxed(&val);
        let top = self.stack.len() - 1;
        self.stack[top] = Operand::plain(val_boxed, Repr::Boxed, val.ty);
        let (env_boxed, addr) = self.emit_aliased_addr(pc, hops, slot);
        self.emit_pre_write_barrier_addr(addr);
        let st = self.store_i64(addr, 0, val_boxed);
        self.tag_store(st, HeapKind::Slot);
        let slot_v = self.i32_const(slot);
        self.emit_post_write_barrier(env_boxed, slot_v, val_boxed);
        Ok(())
    }

    pub(super) fn emit_lambda(&mut self, _pc: Pc, func_index: u32) {
        let env = self.load_i64(self.vp, self.env_slot_off);
        let fidx_v = self.i32_const(func_index);
        let lam = self.helpers.lambda;
        let script = self.cur_script_value();
        let result = self
            .rt_call(lam, true, |_, _| vec![env, script, fidx_v])
            .unwrap();
        self.push_boxed(result, obj_only_ty());
    }

    pub(super) fn emit_exception(&mut self, pc: Pc) {
        let exc = self.helpers.exception;
        let result = self.rt_call(exc, true, |_, _| vec![]).unwrap();
        self.push_boxed(result, self.def_type(pc, 0));
    }

    pub(super) fn emit_exception_and_stack(&mut self) {
        let n = self.spill_all();
        let exc_off = self.operand_base + 8 * n;
        let stack_off = exc_off + 8;
        let exc_addr = self.add_offset(self.vp, exc_off);
        let stack_addr = self.add_offset(self.vp, stack_off);
        let gef = self.helpers.get_exception_for_finally;
        let ok = self.call_i32(gef, &[self.cx, exc_addr, stack_addr]);
        self.branch_on_err(ok);
        self.reload(n);
        let exc = self.load_i64(self.vp, exc_off);
        let exc_stack = self.load_i64(self.vp, stack_off);
        self.push_boxed(exc, prim_desc(Prims::EMPTY));
        self.push_boxed(exc_stack, prim_desc(Prims::EMPTY));
    }

    pub(super) fn emit_throw(&mut self) -> Result<(), String> {
        let val = self.pop()?;
        let val_boxed = self.to_boxed(&val);
        let throw = self.helpers.throw;
        self.rt_throw(throw, &[val_boxed]);
        Ok(())
    }

    pub(super) fn emit_throw_with_stack(&mut self) -> Result<(), String> {
        let stack = self.pop()?;
        let value = self.pop()?;
        let stack_boxed = self.to_boxed(&stack);
        let value_boxed = self.to_boxed(&value);
        let tws = self.helpers.throw_with_stack;
        self.rt_throw(tws, &[value_boxed, stack_boxed]);
        Ok(())
    }

    /// `SpreadCall`/`SpreadNew`/`SpreadSuperCall`.
    pub(super) fn emit_spread_call(&mut self, pc: Pc, construct: bool) -> Result<(), String> {
        let need = if construct { 4usize } else { 3usize };
        if self.stack.len() < need {
            return Err(format!("spread call at pc {pc}: stack underflow"));
        }
        let len = self.stack.len();
        let callee = self.stack[len - need].clone();
        let thisv = self.stack[len - need + 1].clone();
        let arr = self.stack[len - need + 2].clone();
        let callee_b = self.to_boxed(&callee);
        let thisv_b = self.to_boxed(&thisv);
        let arr_b = self.to_boxed(&arr);
        let new_target_b = if construct {
            let nt = self.stack[len - need + 3].clone();
            self.to_boxed(&nt)
        } else {
            self.boxed_const(TAG_NULL << 32)
        };
        let constructing_v = self.i32_const(u32::from(construct));
        let sc = self.helpers.spread_call;
        let result = self
            .rt_call(sc, true, move |_, _| {
                vec![callee_b, thisv_b, arr_b, new_target_b, constructing_v]
            })
            .unwrap();
        for _ in 0..need {
            self.stack.pop();
        }
        self.push_boxed(result, self.def_type(pc, 0));
        Ok(())
    }

    /// `TableSwitch`.
    pub(super) fn emit_table_switch(
        &mut self,
        pc: Pc,
        default_off: i32,
        low: i32,
        high: i32,
        first_resume: u32,
    ) -> Result<(), String> {
        let index = self.pop()?;
        let low_v = self.i32_const(low as u32);
        let oob = self.i32_const(u32::MAX);
        let value = if matches!(index.repr, Repr::I32 | Repr::Bool) || is_exact_int32(&index.ty) {
            let idx_i32 = self.to_i32(&index);
            self.binop(Operator::I32Sub, idx_i32, low_v, Type::I32)
        } else {
            let boxed = self.to_boxed(&index);
            let is_int32 = self.tag_eq(boxed, TAG_INT32 as u32);
            let payload = self.unop(Operator::I32WrapI64, boxed, Type::I32);
            let v_int = self.binop(Operator::I32Sub, payload, low_v, Type::I32);
            let is_dbl = self.is_double_tag(boxed);
            let d = self.unop(Operator::F64ReinterpretI64, boxed, Type::F64);
            let ti = self.unop(Operator::I32TruncSatF64S, d, Type::I32);
            let back = self.unop(Operator::F64ConvertI32S, ti, Type::F64);
            let dbl_ok = self.binop(Operator::F64Eq, back, d, Type::I32);
            let v_dbl_sub = self.binop(Operator::I32Sub, ti, low_v, Type::I32);
            let v_dbl = self.select(Type::I32, v_dbl_sub, oob, dbl_ok);
            let v_not_int = self.select(Type::I32, v_dbl, oob, is_dbl);
            self.select(Type::I32, v_int, v_not_int, is_int32)
        };
        let count = usize::try_from((i64::from(high) - i64::from(low) + 1).max(0)).unwrap();
        let mut targets = Vec::with_capacity(count);
        for i in 0..count {
            let ro_idx = usize::try_from(first_resume).unwrap() + i;
            let resume_pc = *self
                .script
                .resume_offsets
                .get(ro_idx)
                .ok_or_else(|| format!("TableSwitch resume index {ro_idx} out of range"))?;
            targets.push(self.edge_to(resume_pc));
        }
        let default = self.edge_to(branch_target(pc, default_off));
        self.body.set_terminator(
            self.cur,
            Terminator::Select {
                value,
                targets,
                default,
            },
        );
        Ok(())
    }

    /// `FunctionThis` (source: translate.rs `emit_function_this`), in the
    /// per-op continuation form.
    ///
    /// The strict thisv slot is immutable, so the read simply carries the
    /// tracked fact and This provenance. Non-strict `this` needs boxing, and
    /// the two arms must not be merged: merging throws the provenance away,
    /// because the merged value is the boxed `this` while the frame slot
    /// holds the unwrapped one. No `this.field` guard in a non-strict body
    /// could then write its class fact back to the slot, so every later
    /// `this.field` access re-guards and pays the store choke afresh.
    ///
    /// So fork instead: on the object arm the frame slot IS the boxed value,
    /// so it falls through refined (object-only, This provenance) and arg 0
    /// is refined with it -- one guard then buys the whole lineage, which is
    /// the fullword discipline applied to `this`. The primitive/nullish arm
    /// branches to the next pc's version carrying the helper's result with
    /// no provenance (the wrapper is a different object than the slot).
    pub(super) fn emit_function_this(&mut self, pc: Pc) {
        let v = if self.cur_seg.is_some() {
            self.load_i64(self.vp, self.frame_base + 8)
        } else {
            self.load_i64(self.sp, 8)
        };
        let slot = self.args_ctx.first().copied().unwrap_or(SlotCtx::TOP);
        if self.script.strict || is_object_only(&slot.to_ty()) {
            // Object-only already proven: the boxing is a no-op, so the
            // non-strict read is the strict one.
            self.stack.push(Operand::from_slot(v, slot, SlotRef::This));
            return;
        }
        let next_pc = pc + JSOp::FunctionThis.len();
        let is_obj = self.tag_eq(v, TAG_OBJECT as u32);
        let obj_blk = self.body.add_block();
        let box_blk = self.body.add_block();
        self.cond_br(is_obj, obj_blk, box_blk);
        self.side_arm(box_blk, next_pc, |s| {
            let h = s.helpers.box_nonstrict_this;
            let boxed = s.rt_call(h, true, move |_, _| vec![v]).unwrap();
            Operand::plain(boxed, Repr::Boxed, obj_only_ty())
        });
        self.cur = obj_blk;
        let refined = SlotCtx {
            prims: Prims::EMPTY,
            outside: true,
            range: RangeBucket::Top,
            cls: slot.cls,
            cls_shallow: slot.cls_shallow,
            cls_slots: slot.cls_slots,
            ta: slot.ta,
            likely_cls: slot.likely_cls,
            src: None,
            iv: None,
            iv_grow: 0,
            prov: slot.prov.or(Prov::T_FRAME),
        };
        if let Some(cell) = self.args_ctx.get_mut(0) {
            if let Some(m) = cell.meet(refined) {
                *cell = m;
            }
        }
        let slot = self.args_ctx.first().copied().unwrap_or(refined);
        self.stack.push(Operand::from_slot(v, slot, SlotRef::This));
    }

    /// `l instanceof r`: a per-site cell caching the rhs function's shape
    /// plus its `.prototype` slot, then an inline `[[Prototype]]` walk. The
    /// reactor call fills the cell and is the miss arm for every
    /// shape/gen/lazy-proto/depth failure. Without the inline arm the cell
    /// is allocated and patched but never read, and `instanceof` can
    /// dominate a program's generic helper traffic.
    pub(super) fn emit_instanceof(&mut self, pc: Pc) -> Result<(), String> {
        let rval = self.pop()?;
        let lval = self.pop()?;
        let r_boxed = self.to_boxed(&rval);
        let l_boxed = self.to_boxed(&lval);
        let ty = self.result_ty_fact(pc, PRIM_BOOLEAN);
        let iof = self.helpers.instanceof_;

        // Allocate the persistent cell index in `Code` only: a fixpoint
        // round's body is discarded, and bumping the shared counter there
        // renumbers every later cell with the round count (the patch list
        // is per-pass, so 0 is never applied).
        let idx = if self.mode == EmitMode::Code {
            self.atoms.next_iof_cell()
        } else {
            0
        };
        let cell_addr = self.i32_const(IOF_CELL_ADDR_PLACEHOLDER);
        self.iof_cell_patches.push((cell_addr, idx + 1));

        // Deferred spills: the hit path is pure loads, so only the miss block
        // spills (rooting for the reactor call, which may GC) and reloads.
        let pre = self.diamond_begin();
        let d = self.diamond_merge(pre, Some(Type::I64));

        // Shared constants in the entry block (it dominates every successor).
        let one = self.i32_const(1);
        let two = self.i32_const(2);
        let zero = self.i32_const(0);
        let depth0 = self.i32_const(IOF_WALK_DEPTH);
        let true_bits = self.boxed_const((TAG_BOOLEAN << 32) | 1);
        let false_bits = self.boxed_const(TAG_BOOLEAN << 32);

        let chk_shape = self.body.add_block();
        let read_proto = self.body.add_block();
        let chk_lhs = self.body.add_block();
        let false_blk = self.body.add_block();
        let true_blk = self.body.add_block();
        let slow_blk = self.body.add_block();
        let walk = self.body.add_block();
        let walk_cur = self.body.add_blockparam(walk, Type::I32);
        let walk_depth = self.body.add_blockparam(walk, Type::I32);
        let w_a = self.body.add_block();
        let w_b = self.body.add_block();
        let w_cont = self.body.add_block();
        let w_next = self.body.add_block();

        // Entry: load the cell + the live generation; guard rhs is an object.
        let cshape = self.load_i32(cell_addr, 0);
        let cgen = self.load_i32(cell_addr, IOF_CELL_GEN);
        let cslotenc = self.load_i32(cell_addr, IOF_CELL_SLOTENC);
        let gen_addr = self.i32_const(self.helpers.prop_ic_gen_base);
        let live_gen = self.load_i32(gen_addr, 0);
        let r_is_obj = self.tag_eq(r_boxed, TAG_OBJECT as u32);
        self.cond_br(r_is_obj, chk_shape, slow_blk);

        // chk_shape: rhs shape == cached funShape and cached gen == live gen
        // (an empty cell holds funShape 0, never a live shape -> miss).
        self.cur = chk_shape;
        let rptr = self.unop(Operator::I32WrapI64, r_boxed, Type::I32);
        let rshape = self.load_i32(rptr, SHAPE_OFFSET);
        let shape_ok = self.binop(Operator::I32Eq, rshape, cshape, Type::I32);
        let gen_ok = self.binop(Operator::I32Eq, cgen, live_gen, Type::I32);
        let hit = self.binop(Operator::I32And, shape_ok, gen_ok, Type::I32);
        self.cond_br(hit, read_proto, slow_blk);

        // read_proto: the live `.prototype` from the cached own slot. A
        // non-object prototype (reassigned to a primitive) would make
        // OrdinaryHasInstance throw, so that leaves to the reactor.
        self.cur = read_proto;
        let pval = self.emit_slot_load(rptr, cslotenc);
        let p_is_obj = self.tag_eq(pval, TAG_OBJECT as u32);
        self.cond_br(p_is_obj, chk_lhs, slow_blk);

        // chk_lhs: a primitive lhs is never `instanceof` anything (false, no
        // throw); an object lhs enters the proto walk.
        self.cur = chk_lhs;
        let pptr = self.unop(Operator::I32WrapI64, pval, Type::I32);
        let lptr = self.unop(Operator::I32WrapI64, l_boxed, Type::I32);
        let l_is_obj = self.tag_eq(l_boxed, TAG_OBJECT as u32);
        self.body.set_terminator(
            chk_lhs,
            Terminator::CondBr {
                cond: l_is_obj,
                if_true: BlockTarget {
                    block: walk,
                    args: vec![lptr, depth0],
                },
                if_false: BlockTarget {
                    block: false_blk,
                    args: vec![],
                },
            },
        );

        // The two constant results. These arms are pure (no spill), so they
        // carry the live operand values rather than reloading the slots.
        for (blk, bits) in [(false_blk, false_bits), (true_blk, true_bits)] {
            let mut args = d.vals.clone();
            args.push(bits);
            args.push(one);
            self.body.set_terminator(
                blk,
                Terminator::Br {
                    target: BlockTarget {
                        block: d.merge,
                        args,
                    },
                },
            );
        }

        // walk(cur, depth): read cur's `[[Prototype]]` (shape -> baseShape ->
        // proto_); `proto == P` is a hit.
        self.cur = walk;
        let wshape = self.load_i32(walk_cur, SHAPE_OFFSET);
        let wbase = self.load_i32(wshape, SHAPE_BASESHAPE_OFFSET);
        let proto = self.load_i32(wbase, BASESHAPE_PROTO_OFFSET);
        let found = self.binop(Operator::I32Eq, proto, pptr, Type::I32);
        self.cond_br(found, true_blk, w_a);

        // w_a: a TaggedProto below 2 is null (0) or LazyProto (1).
        self.cur = w_a;
        let is_low = self.binop(Operator::I32LtU, proto, two, Type::I32);
        self.cond_br(is_low, w_b, w_cont);

        // w_b: null ends the chain (false); LazyProto cannot be walked here.
        self.cur = w_b;
        let is_null = self.binop(Operator::I32Eq, proto, zero, Type::I32);
        self.cond_br(is_null, false_blk, slow_blk);

        // w_cont: a real object proto (>1); bound the walk depth.
        self.cur = w_cont;
        let depth_zero = self.binop(Operator::I32Eq, walk_depth, zero, Type::I32);
        self.cond_br(depth_zero, slow_blk, w_next);

        // w_next: one hop up.
        self.cur = w_next;
        let nd = self.binop(Operator::I32Sub, walk_depth, one, Type::I32);
        self.body.set_terminator(
            w_next,
            Terminator::Br {
                target: BlockTarget {
                    block: walk,
                    args: vec![proto, nd],
                },
            },
        );

        // slow_blk: the reactor call, which also populates the cell. A
        // side continuation, not a merge predecessor: merging it back
        // would join the helper's stepped state into the inline arms'
        // path, even when the inline arms hit every time. Its
        // epoch-proven keep arm continues at next_pc with the lineage's
        // facts (a prototype walk the inline arms declined writes no
        // stamped heap); a moved epoch continues as a Dirty lineage.
        self.cur = slow_blk;
        let arm_st = self.arm_state();
        let pre_e = self.emit_epoch_read();
        let pre_b = self.sample_bind_epoch();
        let n = self.spill_all();
        let top = self.add_offset(self.vp, d.top_off);
        let ok = self.call_i32(iof, &[self.cx, top, l_boxed, r_boxed, cell_addr]);
        let slow_res = self.load_i64(self.vp, d.top_off);
        let next_pc = pc + JSOp::Instanceof.len();
        self.epoch_keep_tail(
            arm_st.clone(),
            pre_e,
            pre_b,
            ok,
            Some((slow_res, ty)),
            next_pc,
        );
        self.reload(n);
        self.branch_on_err(ok);
        self.push_boxed(slow_res, ty);
        let target = self.dirty_edge_to(next_pc);
        self.body
            .set_terminator(self.cur, Terminator::Br { target });
        self.arm_restore(arm_st);

        self.diamond_join(&d);
        self.push_known(d.res_param.unwrap(), Repr::Boxed, ty);
        Ok(())
    }

    pub(super) fn emit_arguments_lazy(&mut self, pc: Pc) {
        let result_ty = self.def_type(pc, 0);
        let cached = self.load_i64(self.vp, self.args_obj_slot_off);
        let is_undef = self.tag_eq(cached, TAG_UNDEFINED as u32);
        let pre = self.diamond_begin();
        let build_blk = self.body.add_block();
        let d = self.diamond_merge(pre, Some(Type::I64));
        let one = self.i32_const(1);
        let mut fast_args = d.vals.clone();
        fast_args.push(cached);
        fast_args.push(one);
        self.body.set_terminator(
            self.cur,
            Terminator::CondBr {
                cond: is_undef,
                if_true: BlockTarget {
                    block: build_blk,
                    args: vec![],
                },
                if_false: BlockTarget {
                    block: d.merge,
                    args: fast_args,
                },
            },
        );
        self.cur = build_blk;
        self.spill_all();
        let top = self.add_offset(self.vp, d.top_off);
        let args_h = self.helpers.arguments_;
        let ok = self.call_i32(args_h, &[self.cx, top, self.sp, self.argc]);
        let built = self.load_i64(self.vp, d.top_off);
        self.store_i64(self.vp, self.args_obj_slot_off, built);
        self.diamond_slow_br(&d, &[built, ok]);
        self.diamond_join(&d);
        self.push_boxed(d.res_param.unwrap(), result_ty);
    }

    // --- returns / atoms / misc ------------------------------------------

    /// At each return of a layout ctor, stamp the completed `this`. Without
    /// this the bbv lane would never stamp and every class-fact guard would
    /// miss.
    pub(super) fn emit_class_idx_stamp(&mut self) {
        let Some(si) = self.ctx.stamp_ctors_in.get(&self.source_id) else {
            return;
        };
        let si = si.clone();
        self.emit_class_idx_stamp_impl(&si, false, StampRecv::This);
    }

    /// Two-phase re-stamp at each return of an init delegate: the
    /// prefix-stamped word advances to the full key once the live shape
    /// matches the full row.
    pub(super) fn emit_class_idx_restamp(&mut self) {
        let Some(si) = self.ctx.deleg_restamps_in.get(&self.source_id) else {
            return;
        };
        let si = si.clone();
        self.emit_class_idx_stamp_impl(&si, true, StampRecv::This);
    }

    /// The formal-receiver form: at each return of a fill script, advance
    /// the named formal's object (the fresh-object-then-fill idiom, where
    /// the two-phase suffix is written through an argument rather than
    /// `this`). Same descriptor, same gates; only the receiver slot
    /// differs.
    pub(super) fn emit_class_idx_arg_restamp(&mut self) {
        let Some(&(formal, ref si)) = self.ctx.arg_restamps_in.get(&self.source_id) else {
            return;
        };
        let si = si.clone();
        self.emit_class_idx_stamp_impl(&si, true, StampRecv::Formal(formal));
    }

    /// The local-receiver form: after the last add of a post-construction
    /// fill sequence (`local_restamps`), advance the named local's object
    /// to the full key. Same descriptor, same gates.
    pub(super) fn emit_class_idx_local_restamp(&mut self, pc: Pc) {
        let site = crate::ids::Site::new(self.source_id, self.evid_pc(pc));
        let Some(&(local, ref si)) = self.ctx.local_restamps_in.get(&site) else {
            return;
        };
        let si = si.clone();
        if local & crate::facts::RESTAMP_FORMAL != 0 {
            let argno = u16::try_from(local & !crate::facts::RESTAMP_FORMAL).unwrap();
            self.read_arg(argno, super::ctx::bottom_ty(), None);
        } else {
            self.push_local(local);
        }
        let Ok(o) = self.pop() else { return };
        let boxed = self.to_boxed(&o);
        self.emit_class_idx_stamp_impl(&si, true, StampRecv::Boxed(boxed));
    }

    pub(super) fn emit_class_idx_stamp_impl(
        &mut self,
        si: &StampCtorIn,
        is_restamp: bool,
        recv: StampRecv,
    ) {
        let layout_id = si.layout_id;
        // Stamp classification: a stamp writes the class
        // word's identity half -- the one store "stores preserve identity"
        // does not cover. For a first stamp that is still alias-safe: no
        // cls fact is mintable on a not-yet-stamped object (the
        // CONSTRUCTING sentinel fails every identity guard), so nothing a
        // caller holds can be falsified -- it classifies MUT_THIS (the
        // receiver is the frame's own `this` by construction), which
        // construct sites mask (their own fresh alloc) and the this-only
        // arm covers with the receiver kill. A restamp advances a
        // guardable prefix key, so pre-existing alias facts are real --
        // it stays MUT_OTHER. OR at the diamond's entry (dominates every
        // arm; the no-write arms over-report, conservative).
        self.or_flags_const(if is_restamp {
            FLAG_MUT_OTHER
        } else {
            FLAG_MUT_THIS
        });
        // Frame-view relative: a segment's `this` sits at its own frame
        // base in the vp-relative operand space (splice callers never
        // rebase vp -- needs_args_obj declines candidacy -- so the root
        // form is unchanged). A formal receiver sits at the formal slots
        // above it; a call that omitted the argument leaves undefined
        // there, which the not-object gate below refuses.
        let recv_off = match recv {
            StampRecv::Formal(i) => 16 + 8 * i,
            StampRecv::This => 8,
            StampRecv::Boxed(_) => 0,
        };
        let thisv = match (recv, self.cur_seg) {
            (StampRecv::Boxed(v), _) => v,
            (_, Some(_)) => self.load_i64(self.vp, self.frame_base + recv_off),
            (_, None) => self.load_i64(self.sp, recv_off),
        };
        let done = self.body.add_block();
        let zero_arg: Option<Value> = None;
        // The stamp-outcome census: the class-fact guards' hit rate is
        // bounded above by how often this store actually runs, and each of
        // the three gates below refuses a different population.
        let cbase = if is_restamp {
            census::RESTAMP_BASE
        } else {
            census::STAMP_BASE
        };
        let is_obj = self.tag_eq(thisv, TAG_OBJECT as u32);
        let chk_blk = self.body.add_block();
        let notobj = self.stamp_census_blk(done, cbase + census::STAMP_NOT_OBJECT, zero_arg);
        self.cond_br(is_obj, chk_blk, notobj);
        self.cur = chk_blk;
        let objptr = self.unop(Operator::I32WrapI64, thisv, Type::I32);
        let w0 = self.load_i32(objptr, OBJ_CLASS_IDX_OFFSET);
        self.eff(w0, Eff::ReadBits(HeapKind::ClassWord));
        // Ownership gate (replaces the guard cell, the keyed walk, and the
        // early-idx interplay): stamp only a receiver whose bit history is
        // trustworthy for this clump. First stamp: a still-set CONSTRUCTING
        // sentinel whose early key is ours or absent (a foreign ctor's key
        // means the outer ctor owns the word). Restamp: fast-out on an
        // already-full idx; advance a prefix-stamped idx (its bits were
        // maintained since alloc), or the sentinel form for the
        // empty-prefix two-phase flow.
        let sent_key_ok = |slf: &mut Self| {
            let sentb = slf.i32_const(CLASS_WORD_SENTINEL);
            let sent = slf.binop(Operator::I32And, w0, sentb, Type::I32);
            let z0 = slf.i32_const(0);
            let s_nz = slf.binop(Operator::I32Ne, sent, z0, Type::I32);
            let keym = slf.i32_const(EARLY_KEY_MAX << EARLY_KEY_SHIFT);
            let key = slf.binop(Operator::I32And, w0, keym, Type::I32);
            let mine = slf.i32_const((layout_id + 1) << EARLY_KEY_SHIFT);
            let k_z = slf.binop(Operator::I32Eq, key, z0, Type::I32);
            let k_mine = slf.binop(Operator::I32Eq, key, mine, Type::I32);
            let mut k_ok = slf.binop(Operator::I32Or, k_z, k_mine, Type::I32);
            // A restamp meeting the sentinel mid-construction: the alloc
            // wrote the CTOR's early key (the prefix layout), not the full
            // target's, so the prefix ids own the word too. Without this a
            // two-phase init delegate that runs inside the ctor (crypto's
            // `fromString`) can never advance, and the object leaves
            // construction prefix-stamped forever.
            if is_restamp {
                for &p in &si.prefix_keys {
                    let pk = slf.i32_const((p + 1) << EARLY_KEY_SHIFT);
                    let k_p = slf.binop(Operator::I32Eq, key, pk, Type::I32);
                    k_ok = slf.binop(Operator::I32Or, k_ok, k_p, Type::I32);
                }
            }
            slf.binop(Operator::I32And, s_nz, k_ok, Type::I32)
        };
        let gate_blk = self.body.add_block();
        if is_restamp {
            let m16 = self.i32_const(0xFFFF);
            let idx = self.binop(Operator::I32And, w0, m16, Type::I32);
            let want = self.i32_const(layout_id + 1);
            let already = self.binop(Operator::I32Eq, idx, want, Type::I32);
            let work_blk = self.body.add_block();
            let hadit = self.stamp_census_blk(done, cbase + census::STAMP_ALREADY, zero_arg);
            self.cond_br(already, hadit, work_blk);
            self.cur = work_blk;
            let mut ok = sent_key_ok(self);
            // The prefix-advance admission additionally requires the word
            // NOT be marked advance-ineligible: an unpredicted-key add
            // beyond the prefix left the own predictions true but the
            // extension span dirty, so certifying this longer layout over
            // it would bake wrong slots.
            let advm = self.i32_const(CLASS_WORD_ADV_INELIGIBLE);
            let advb = self.binop(Operator::I32And, w0, advm, Type::I32);
            let z_a = self.i32_const(0);
            let adv_ok = self.binop(Operator::I32Eq, advb, z_a, Type::I32);
            for &p in &si.prefix_keys {
                let pv = self.i32_const(p + 1);
                let e = self.binop(Operator::I32Eq, idx, pv, Type::I32);
                let e = self.binop(Operator::I32And, e, adv_ok, Type::I32);
                ok = self.binop(Operator::I32Or, ok, e, Type::I32);
            }
            let refused = self.stamp_census_blk(done, cbase + census::STAMP_NOT_OWNED, zero_arg);
            self.cond_br(ok, gate_blk, refused);
        } else {
            let ok = sent_key_ok(self);
            let refused = self.stamp_census_blk(done, cbase + census::STAMP_NOT_OWNED, zero_arg);
            self.cond_br(ok, gate_blk, refused);
        }
        self.cur = gate_blk;
        // Stamp validation: num-props (slotSpan) >= the static prefix
        // length; the SLOTS/TYPES history in the word carries the rest
        // (the prefix is a name<->slot bijection and the engine assigns
        // add slots sequentially, so surviving SLOTS + count>=N implies
        // the first N slots hold the predicted names). The capped
        // small-slot-span encoding reads as its max, which still
        // satisfies the >= check.
        let shape = self.load_i32(objptr, SHAPE_OFFSET);
        self.eff(shape, Eff::Read(HeapKind::Shape));
        let imm = self.load_i32(shape, SHAPE_IMMUTABLE_FLAGS_OFFSET);
        let sh11 = self.i32_const(SHAPE_SMALL_SLOTSPAN_SHIFT);
        let spanp = self.binop(Operator::I32ShrU, imm, sh11, Type::I32);
        let smax = self.i32_const(SHAPE_SMALL_SLOTSPAN_MASK_BITS);
        let span = self.binop(Operator::I32And, spanp, smax, Type::I32);
        let n_v = self.i32_const(u32::try_from(si.fields.len()).unwrap());
        let m = self.binop(Operator::I32GeU, span, n_v, Type::I32);
        let stamp_blk = self.body.add_block();
        let short = self.stamp_census_blk(done, cbase + census::STAMP_SHORT_SPAN, zero_arg);
        self.cond_br(m, stamp_blk, short);
        self.cur = stamp_blk;
        self.emit_guard_census(cbase + census::STAMP_OK, self.cur_pc);
        if self.guard_census_on() {
            let k = self.i32_const(census::STAMP_EXIT_WORD);
            self.emit_guard_census_dyn_id(k, w0);
        }
        // The new word: the idx plus the surviving validity bits; the
        // sentinel and early key drop. SHALLOW survives only when the
        // layout HAS masked fields, RANGES only when it has range claims:
        // keeping a vacuous bit would still cost a demote-and-bump on
        // every engine-path non-number store, even though no consumer
        // tests a vacuous bit for this idx.
        let keep_shallow = si.masks.iter().any(|m| m.prims() != Prims::EMPTY);
        let keep_ranges = si.ranges.iter().any(Option::is_some);
        let bits_m = self.i32_const(
            CLASS_WORD_SLOTS
                | if keep_shallow { CLASS_WORD_SHALLOW } else { 0 }
                | if keep_ranges { CLASS_WORD_RANGES } else { 0 },
        );
        let bits = self.binop(Operator::I32And, w0, bits_m, Type::I32);
        let k_v = self.i32_const(layout_id + 1);
        let w = self.binop(Operator::I32Or, k_v, bits, Type::I32);
        let st = self.store_i32(objptr, OBJ_CLASS_IDX_OFFSET, w);
        self.eff_store(
            st,
            Eff::Write(HeapKind::ClassWord),
            if is_restamp {
                FLAG_MUT_OTHER
            } else {
                FLAG_MUT_THIS
            },
        );
        // No stamps flag and no epoch bump: the only non-sentinel word the
        // gates admit is a prefix-stamped one, and advancing it to the full
        // key falsifies nothing a caller carries -- the prefix slots keep
        // their positions and the SLOTS history survives, exactly as a
        // predicted add. A guard on the prefix key misses, which is safe.
        self.body.set_terminator(
            stamp_blk,
            Terminator::Br {
                target: BlockTarget {
                    block: done,
                    args: vec![],
                },
            },
        );
        self.cur = done;
    }

    /// Instrument-only interposer on one of the exit stamp's refusal
    /// edges: tick and fall on into `done`. Returns `done` when the census
    /// is off, so production codegen is untouched.
    fn stamp_census_blk(&mut self, done: Block, kind: u32, done_arg: Option<Value>) -> Block {
        if !self.guard_census_on() && done_arg.is_none() {
            return done;
        }
        let saved = self.cur;
        let b = self.body.add_block();
        self.cur = b;
        self.emit_guard_census(kind, self.cur_pc);
        self.body.set_terminator(
            b,
            Terminator::Br {
                target: BlockTarget {
                    block: done,
                    args: done_arg.into_iter().collect(),
                },
            },
        );
        self.cur = saved;
        b
    }

    pub(super) fn emit_return_value(&mut self, o: Operand) {
        // Inline frame: the return is an edge to the caller-space
        // continuation carrying [reloaded caller operands..., retval].
        // The caller operands were rooted at the call site (the GC tracer
        // updates the slots in place). The caller's frame facts are
        // restored from the segment ctx (the splice cannot reassign caller
        // slots), the retval carries the callee's proven fact, and the
        // segment-site token mapping keeps the continuation in the caller's
        // loop lineage, dirty iff the splice emitted a may-GC call.
        if let Some(si) = self.cur_seg {
            let (ret_pc, depth) = (self.segs[si].ret_pc, self.segs[si].caller_depth);
            // A ctor splice completes construction here: stamp the
            // ctor-exit class word and substitute `is_object(ret) ? ret :
            // this`. "Stamps stay root-only" holds only for PLAIN splices,
            // whose `this` is never a completing construction. The delegate
            // re-stamp fires on plain segment returns too, since an init
            // delegate is usually a post-construction plain call.
            let is_construct = self.segs[si].is_construct;
            if is_construct {
                self.emit_class_idx_stamp();
            }
            self.emit_class_idx_restamp();
            self.emit_class_idx_arg_restamp();
            // Inline v2 nesting: the caller is the parent segment or the
            // root frame; its dims size the restored fact vectors and its
            // operand base is where the rooted caller operands live.
            let caller_ob = self.segs[si].caller_operand_base;
            let (c_nlocals, c_nargs) = match self.segs[si].parent {
                Some(p) => (
                    max_locals(self.segs[p].script) as usize,
                    usize::from(self.segs[p].script.nargs),
                ),
                None => (
                    self.root_nlocals as usize,
                    usize::from(self.root_script.nargs),
                ),
            };
            // The value rides the edge in its own repr: a raw double is
            // converted only if the landing's slot is not raw. A ctor's
            // substitution needs the boxed form.
            let (rb, rrepr) = if is_construct {
                let rb = self.to_boxed(&o);
                let this_v = self.load_i64(self.vp, self.frame_base + 8);
                let is_obj = self.tag_eq(rb, TAG_OBJECT as u32);
                (self.select(Type::I64, rb, this_v, is_obj), Repr::Boxed)
            } else if self.fanout_off {
                (self.to_boxed(&o), Repr::Boxed)
            } else {
                (o.val, o.repr)
            };
            let saved_stack = std::mem::take(&mut self.stack);
            let restored_locals: Vec<SlotCtx> = (0..c_nlocals)
                .map(|i| {
                    self.caller_locals_ctx
                        .get(i)
                        .copied()
                        .unwrap_or(SlotCtx::TOP)
                })
                .collect();
            let restored_args: Vec<SlotCtx> = (0..1 + c_nargs)
                .map(|i| self.caller_args_ctx.get(i).copied().unwrap_or(SlotCtx::TOP))
                .collect();
            let saved_locals = std::mem::replace(&mut self.locals_ctx, restored_locals);
            let saved_args = std::mem::replace(&mut self.args_ctx, restored_args);
            // Pop one frame off the outer chain into the caller slot: the
            // frame we are returning INTO now has its own caller again.
            let saved_outer = self.outer_ctx.clone();
            let mut rest = std::mem::take(&mut self.outer_ctx);
            let next = if rest.is_empty() {
                CallerFrame::default()
            } else {
                rest.remove(0)
            };
            let saved_caller_locals = std::mem::replace(&mut self.caller_locals_ctx, next.locals);
            let saved_caller_args = std::mem::replace(&mut self.caller_args_ctx, next.args);
            self.outer_ctx = rest;
            for i in 0..depth {
                let v = self.load_i64(self.vp, caller_ob + 8 * i);
                self.stack.push(Operand::plain(v, Repr::Boxed, bottom_ty()));
            }
            let (rty, rrange) = if is_construct {
                // The substitution's result is an object either way.
                (
                    TypeDesc {
                        prims: Prims::EMPTY,
                        outside: true,
                    },
                    RangeBucket::Top,
                )
            } else if self.fanout_off {
                (bottom_ty(), RangeBucket::Top)
            } else {
                (o.ty, o.range)
            };
            self.stack.push(Operand {
                val: rb,
                repr: rrepr,
                ty: rty,
                range: rrange,
                cls: None,
                cls_shallow: false,
                cls_slots: false,
                ta: None,
                likely_cls: None,
                src: None,
                iv: None,
                fresh: false,
                prov: o.prov,
            });
            let target = self.edge_to(ret_pc);
            self.body
                .set_terminator(self.cur, Terminator::Br { target });
            self.stack = saved_stack;
            self.locals_ctx = saved_locals;
            self.args_ctx = saved_args;
            self.caller_locals_ctx = saved_caller_locals;
            self.caller_args_ctx = saved_caller_args;
            self.outer_ctx = saved_outer;
            return;
        }
        self.emit_class_idx_stamp();
        self.emit_class_idx_restamp();
        self.emit_class_idx_arg_restamp();
        let boxed = self.to_boxed(&o);
        self.store_i64(self.retval_out, 0, boxed);
        let zero = self.i32_const(0);
        // Effect-provenance flag, a compile-time constant per return
        // version. The per-lineage half of its proof is the track: a
        // non-Dirty-track return ran no Alloc/Unknown helper. The
        // callee-effect half is made body-globally: a body call does not
        // step the track, so every accumulator OR a non-threaded body
        // cannot record lands in `untracked_flags` and revokes this
        // constant at pass end. Combined with the static heap-readonly
        // scan, a constant that survives revocation says the whole
        // invocation did no heap mutation -- the caller's facts survive.
        // (Not "no GC": the word is mutation-only, and every fork arm
        // reloads its GC-movable operands.) gen_only bodies have no
        // per-lineage track and always report dirty.
        let scan_ok = !self.gen_only && self.script_ret_clean() != ScanClass::Fail;
        let clean = scan_ok && self.cur_track != Track::Dirty;
        if clean && self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
            crate::diag_line!(
                "night: bbv clean-ret sid#{} pc {}",
                self.source_id,
                self.cur_pc
            );
        }
        // Return shapes. A threaded body returns
        // the accumulator on every lineage: it is the per-path accounting
        // of record -- inline store arms OR their classified MUT bit at
        // the op (segments included), leaf writers and may-GC helpers OR
        // theirs, callee words join folded at call sites, and the
        // second-chance clean edges OR their store's bit -- so no
        // provisional constant and no body-wide revocation apply. A
        // non-threaded body keeps the compile-time shapes: clean lineages
        // carry a provisional zero the pass end revokes to the body's
        // classified write word (splice stores and leaf writers the
        // bytecode scan never sees); everything else is const all-set.
        let flags = if self.flags_threading() {
            let w = self.materialize_flags();
            // Census kind 46: threaded return words, id = sid<<16 |
            // (word & 7) -- the per-body returned-word distribution, the
            // ground truth for why a caller's fork arm did or did not take.
            if self.guard_census_on() {
                let before = self.body.values.len();
                let k = self.i32_const(46);
                let m = self.i32_const(7);
                let wb = self.binop(Operator::I32And, w, m, Type::I32);
                let sc = self.i32_const(self.source_id.get() << 16);
                let idv = self.binop(Operator::I32Or, sc, wb, Type::I32);
                self.instrument_values += self.body.values.len() - before;
                self.emit_guard_census_dyn_id(k, idv);
            }
            w
        } else if clean {
            let c = self.i32_const(0);
            if self.mode == EmitMode::Code {
                self.clean_ret_flag_patches.push(c);
            }
            c
        } else {
            self.i32_const(FLAGS_ALL)
        };
        self.body.set_terminator(
            self.cur,
            Terminator::Return {
                values: vec![zero, flags],
            },
        );
    }

    /// The scan class of this script (see `script_heap_scan`). ReadOnly:
    /// any mutation the body could do runs through an Alloc/Unknown helper
    /// (which steps the track, so a non-Dirty return lineage did not run
    /// one) or a body call (which does not step the track any more, and is
    /// accounted for by the accumulator in a threaded body and by
    /// `untracked_flags` revocation in a non-threaded one).
    /// The list is an allowlist (anything not named disqualifies):
    /// frame-private writes are fine, Leaf-helper writes (aliased vars,
    /// iterator state, generator state) and inline heap stores
    /// (Set*/Init*/literal construction) are not. StoreOnly: the
    /// only disqualifying ops are prop stores, whose receivers emission
    /// classifies (own-this vs other) -- the body's word becomes the
    /// classified accounting instead of const all-set.
    pub(super) fn script_ret_clean(&mut self) -> ScanClass {
        let script = self.script;
        self.ret_clean_for(self.source_id, script)
    }

    pub(super) fn ret_clean_for(&mut self, sid: ScriptId, script: &Script) -> ScanClass {
        if let Some(&b) = self.ret_clean.get(&sid) {
            return b;
        }
        let ok = script_heap_scan(script, sid, &self.ctx.facts.apply_sites);
        self.ret_clean.insert(sid, ok);
        ok
    }
}

impl<'a> Bbv<'a> {
    pub(super) fn emit_ret_rval(&mut self) {
        let boxed = self.load_i64(self.vp, self.rval_slot_off);
        // bottom_ty, not an empty desc: the inline return path forwards
        // this operand's fact into the continuation ctx, and an empty
        // claim reads as proven-none there.
        let o = Operand::plain(boxed, Repr::Boxed, bottom_ty());
        self.emit_return_value(o);
    }

    pub(super) fn skip_operands(&self, p: &mut BytecodeParser, op: JSOp) {
        let imm = usize::try_from(op.len()).unwrap() - 1;
        if imm > 0 {
            p.advance(imm).expect("operand bytes present");
        }
    }

    pub(super) fn resolve_atom(&mut self, name_index: u32) -> Result<u32, String> {
        let name = self.name_for(name_index)?;
        Ok(self.atoms.intern(name))
    }

    /// Does the currently-viewed script ever name `push`? The dense push
    /// arm is gated on this, and the gate is the measured half of the arm:
    /// call-free or not, it is ~30 blocks at every 1-arg call site, and the
    /// standing law that an arm costs where it never fires reproduces
    /// exactly: emitted unconditionally it is a large win on array-append
    /// code and a comparable loss on 1-arg scripted dispatch that never
    /// pushes. A script
    /// that never mentions the name cannot reach the arm's identity
    /// compare, so declining there costs nothing and is not a prediction.
    pub(super) fn script_names_push(&mut self) -> bool {
        if let Some(&b) = self.push_named.get(&self.source_id) {
            return b;
        }
        // `gcthings` carries the `other()` sentinel for entries that are not
        // source objects at all; `object()` indexes unchecked, so the scan
        // must skip them (the bytecode-driven caller never sees one).
        let found = self.script.gcthings.iter().any(|&gc| {
            !gc.is_other()
                && match self.source.object(gc) {
                    SourceObject::String(s) => s.chars().iter().copied().eq("push".encode_utf16()),
                    _ => false,
                }
        });
        self.push_named.insert(self.source_id, found);
        found
    }

    /// Does the currently-viewed script ever name `Array`? The `new
    /// Array()` bump arm is gated on this (same law as the push arm: an
    /// arm costs where it never fires, and a script that never mentions
    /// the name cannot reach its identity compare).
    pub(super) fn script_names_array(&mut self) -> bool {
        if let Some(&b) = self.array_named.get(&self.source_id) {
            return b;
        }
        let found = self.script.gcthings.iter().any(|&gc| {
            !gc.is_other()
                && match self.source.object(gc) {
                    SourceObject::String(st) => {
                        st.chars().iter().copied().eq("Array".encode_utf16())
                    }
                    _ => false,
                }
        });
        self.array_named.insert(self.source_id, found);
        found
    }

    /// Resolve a gcthing index to the compilation's id for that name.
    /// Interning rather than copying: the string table is shared with the
    /// analysis, so a name it already saw costs one hash and no allocation,
    /// and every fact table is keyed by the id this returns.
    pub(super) fn name_for(&mut self, name_index: u32) -> Result<NameId, String> {
        let gc = *self
            .script
            .gcthings
            .get(usize::try_from(name_index).unwrap())
            .ok_or_else(|| format!("prop name_index {name_index} out of range"))?;
        match self.source.object(gc) {
            SourceObject::String(s) => Ok(self.atoms.names.intern(s)),
            _ => Err(format!("prop name_index {name_index} is not a string atom")),
        }
    }

    /// This frame's `JSScript*`, re-derived from a ROOTED slot on every use.
    ///
    /// The compiled-body ABI hands the script in as a bare i32, and a wasm
    /// local holding it survives every may-GC call in the body -- but
    /// `SCRIPT` is a compacting GC kind, so a shrinking GC relocates the
    /// script out from under it and the next use reads a freed cell. The
    /// fix is not to keep it: `sp[0]` is a slot the AOT value stack traces
    /// and the GC forwards, so deriving from it is always current. A
    /// function body finds its callee there and reads the callee's own
    /// script pointer (which `JSFunction`'s tracer keeps live); a global
    /// body has no callee, so `EnterNightGlobal` stages the script itself
    /// there as a private-GC-thing Value.
    ///
    /// Root-frame only, and deliberately so: a spliced callee resolves its
    /// gcthings against the root's script (the splice blocklist names this
    /// as one of the lowerings that reaches around `enter_frame_view`).
    pub(super) fn cur_script_value(&mut self) -> Value {
        let slot0 = self.load_i64(self.sp, 0);
        let low = self.unop(Operator::I32WrapI64, slot0, Type::I32);
        if self.is_global {
            return low;
        }
        self.load_i32(low, FUNC_SCRIPT_SLOT_OFFSET)
    }

    /// The op at `pc` in the current frame's script; `pc` may be synthetic
    /// (segment-space) -- parse at the frame-local offset, not the raw pc
    /// (a raw synthetic offset into a small-based segment's callee lands
    /// in bounds misaligned: a garbage peek or an invalid-bytecode panic).
    pub(super) fn op_at(&self, pc: Pc) -> Option<JSOp> {
        let mut p = self.script.parser();
        p.advance(usize::try_from(self.evid_pc(pc).get()).unwrap())?;
        p.next_op()
    }

    pub(super) fn read_arg(&mut self, argno: u16, ty: TypeDesc, guard_next_pc: Option<Pc>) {
        // Args are cached the way locals are, per version: the frame slot is
        // the rooted truth and every write goes through it, so the first
        // read of an arg in a version can serve the rest. Without this every
        // `GetArg` was a frame load -- locals have had a carrier since
        // locals-into-SSA and args never did.
        let cached = if self.script.has_mapped_args {
            None
        } else {
            self.args_ssa.get(usize::from(argno)).copied().flatten()
        };
        let (v, repr) = match cached {
            Some(c) => c,
            None => {
                let v = if self.cur_seg.is_some() {
                    self.load_i64(self.vp, self.frame_base + 16 + 8 * u32::from(argno))
                } else {
                    self.load_i64(self.sp, 16 + 8 * u32::from(argno))
                };
                if let Some(c) = self.args_ssa.get_mut(usize::from(argno)) {
                    *c = Some((v, Repr::Boxed));
                }
                (v, Repr::Boxed)
            }
        };
        // Args are ctx slots like locals: the read carries the
        // tracked fact and its provenance, and the carrier's repr -- a
        // formal assigned an unboxed value serves later reads unboxed, the
        // GetLocal discipline. Mapped-args frames alias the slots through
        // the arguments object: no facts, no provenance, no carrier.
        let idx = 1 + usize::from(argno);
        if self.script.has_mapped_args || idx >= self.args_ctx.len() {
            self.push_boxed(v, ty);
            return;
        }
        let slot = self.args_ctx[idx];
        let o = Operand {
            val: v,
            repr,
            ty: slot.to_ty(),
            range: slot.range,
            cls: slot.cls,
            cls_shallow: slot.cls_shallow,
            cls_slots: slot.cls_slots,
            ta: slot.ta,
            likely_cls: slot.likely_cls,
            src: Some(SlotRef::Arg(argno)),
            iv: slot.iv.map(|r| (r.lo, r.hi, false)),
            fresh: false,
            prov: slot.prov,
        };
        // Guard-at-defs: if the likelier claims
        // a type for this formal and the ctx does not already imply it,
        // one tag test aligns the Opt track with the prediction -- the
        // positive side continues at next_pc carrying the fact, the other
        // side joins the weaker lineage (the load discipline; one new
        // lineage per site). A def whose type already implies the claim
        // takes no guard and keeps the tighter type. For object claims
        // the test usually migrates rather than multiplies: downstream
        // receiver-tag tests elide against the proven type.
        if let Some(next_pc) = guard_next_pc {
            if !self.gen_only {
                if let Some(&m) = self
                    .ctx
                    .facts
                    .arg_types
                    .get(&(self.source_id, ArgIndex::formal(u32::from(argno))))
                {
                    if !arg_claim_implied(&o, m) {
                        self.guard_arg_claim(o, m, next_pc);
                        // Test-once-per-version: a passed numeric guard's
                        // unboxed carrier serves later reads of this formal
                        // in the version (arg_claim_implied is true for
                        // unboxed reprs, so they skip the re-guard). The
                        // write happens on the fall-through lineage only --
                        // side_arm saved and restored the pre-guard cache
                        // for the miss arm. The frame slot still holds the
                        // boxed truth, so no dirty mark is owed.
                        if let Some(top) = self.stack.last() {
                            if !matches!(top.repr, Repr::Boxed) {
                                let (val, repr) = (top.val, top.repr);
                                if let Some(c) = self.args_ssa.get_mut(usize::from(argno)) {
                                    *c = Some((val, repr));
                                }
                            }
                        }
                        return;
                    }
                }
            }
        }
        self.stack.push(o);
    }

    /// One-tag-test def guard for a likely arg claim (`arg_types`).
    /// Object claims keep the operand's provenance so downstream class
    /// guards can still refine the arg slot; numeric claims ride the
    /// existing typed-load ladder.
    pub(super) fn guard_arg_claim(&mut self, o: Operand, claim: Claim, next_pc: Pc) {
        if claim.is_object() {
            let boxed = o.val;
            let is_obj = self.tag_eq(boxed, TAG_OBJECT as u32);
            let obj_blk = self.body.add_block();
            let other_blk = self.body.add_block();
            self.cond_br(is_obj, obj_blk, other_blk);
            self.side_arm(other_blk, next_pc, move |_| {
                Operand::plain(boxed, Repr::Boxed, bottom_ty())
            });
            self.cur = obj_blk;
            let mut r = o;
            r.ty = obj_only_ty();
            self.stack.push(r);
        } else {
            self.push_load_typed(o.val, claim, next_pc, Prov::C_ARG);
        }
    }

    /// SetLocal: write-through store + strong update of the local's tracked
    /// ctx fact + carrier install (the frame slot stays the rooted
    /// boxed truth; reads and edges use the SSA value in its produced
    /// repr); the value stays on the stack with its facts intact.
    /// A raw-repr local's frame store is deferred: the value is not a GC
    /// thing, so the frame copy exists only for readers that take it from
    /// the frame -- a version that does not carry the local, or the other
    /// side of a seam -- and `flush_stale_locals` writes it there.
    /// Everything else (boxed and pointer reprs) stores eagerly: the GC
    /// traces the frame, not wasm locals. GEN-only bodies keep the eager
    /// form throughout.
    pub(super) fn write_local(&mut self, localno: u32, o: Operand) {
        debug_assert!(localno & STALE_ARG == 0);
        let defer = !self.gen_only
            && matches!(o.repr, Repr::I32 | Repr::F64 | Repr::Bool | Repr::I64)
            && self.locals_ssa.len() > localno as usize;
        if defer {
            self.frame_stale.insert(localno);
        } else {
            self.frame_stale.remove(&localno);
            let boxed = self.to_boxed(&o);
            self.store_i64(self.vp, self.local_base + 8 * localno, boxed);
        }
        self.locals_ctx[localno as usize] = o.slot_cell();
        if let Some(c) = self.locals_ssa.get_mut(localno as usize) {
            *c = Some((o.val, o.repr));
        }
        self.clear_stale_src(SlotRef::Local(localno));
        let mut r = o;
        r.src = Some(SlotRef::Local(localno));
        self.stack.push(r);
    }

    /// Store the dead stale raw slots `dead` (local and `STALE_ARG` keys)
    /// in the cheapest tracer-safe form: nothing but the GC reads a dead
    /// slot, so a double goes in as its bits, uncanonicalized. The point
    /// is the use, not the value (the loop-exit flush).
    pub(super) fn flush_dead_raw(&mut self, dead: &[u32]) {
        for &l in dead {
            let (ssa, addr) = if l & STALE_ARG != 0 {
                let argno = l & !STALE_ARG;
                let ssa = self.args_ssa.get(argno as usize).copied().flatten();
                let addr = if self.cur_seg.is_some() {
                    (self.vp, self.frame_base + 16 + 8 * argno)
                } else {
                    (self.sp, 16 + 8 * argno)
                };
                (ssa, addr)
            } else {
                (
                    self.locals_ssa.get(l as usize).copied().flatten(),
                    (self.vp, self.local_base + 8 * l),
                )
            };
            let Some((val, repr)) = ssa else {
                debug_assert!(false, "dead stale slot {l} without an SSA value");
                continue;
            };
            let boxed = match repr {
                Repr::F64 => self.unop(Operator::I64ReinterpretF64, val, Type::I64),
                Repr::I32 | Repr::Bool => {
                    let payload = self.unop(Operator::I64ExtendI32U, val, Type::I64);
                    let tag = if repr == Repr::I32 {
                        TAG_INT32
                    } else {
                        TAG_BOOLEAN
                    };
                    let tag = self.boxed_const(tag << 32);
                    self.binop(Operator::I64Or, payload, tag, Type::I64)
                }
                Repr::I64 => self.box_i64_canonical(val),
                _ => {
                    let mut o = Operand::plain(val, repr, super::ctx::bottom_ty());
                    o.repr = repr;
                    self.to_boxed(&o)
                }
            };
            self.store_i64(addr.0, addr.1, boxed);
        }
    }

    /// Write every stale local not in `keep` to its frame slot, and every
    /// stale formal (`STALE_ARG | argno` keys: formals are never carried
    /// across versions, so no keep set covers them). `keep` is the target
    /// version's carried set; on a seam crossing it is empty.
    ///
    /// The set is NOT cleared by a flush: the stores land in the current
    /// block, and a later edge of the same op may be emitted in a sibling
    /// arm that block does not dominate (the poly splice dispatch emits
    /// its per-target arms back to back with no arm-state bracket). A
    /// version entry resets the set, so the cost of keeping it is at most
    /// one duplicate store per extra edge inside one op.
    pub(super) fn flush_stale_locals(&mut self, keep: &[u32]) {
        if self.frame_stale.is_empty() {
            return;
        }
        let mut stale: Vec<u32> = self.frame_stale.iter().copied().collect();
        stale.sort_unstable();
        for l in stale {
            if keep.contains(&l) {
                continue;
            }
            if l & STALE_ARG != 0 {
                let argno = l & !STALE_ARG;
                let Some((val, repr)) = self.args_ssa.get(argno as usize).copied().flatten() else {
                    debug_assert!(false, "stale formal {argno} without an SSA value");
                    self.frame_stale.remove(&l);
                    continue;
                };
                let slot = self
                    .args_ctx
                    .get(1 + argno as usize)
                    .copied()
                    .unwrap_or(SlotCtx::TOP);
                let mut o = Operand::from_slot(val, slot, SlotRef::Arg(argno as u16));
                o.repr = repr;
                let boxed = self.to_boxed(&o);
                if self.cur_seg.is_some() {
                    self.store_i64(self.vp, self.frame_base + 16 + 8 * argno, boxed);
                } else {
                    self.store_i64(self.sp, 16 + 8 * argno, boxed);
                }
                continue;
            }
            let Some((val, repr)) = self.locals_ssa.get(l as usize).copied().flatten() else {
                debug_assert!(false, "stale local {l} without an SSA value");
                self.frame_stale.remove(&l);
                continue;
            };
            let slot = self
                .locals_ctx
                .get(l as usize)
                .copied()
                .unwrap_or(SlotCtx::TOP);
            let mut o = Operand::from_slot(val, slot, SlotRef::Local(l));
            o.repr = repr;
            let boxed = self.to_boxed(&o);
            self.store_i64(self.vp, self.local_base + 8 * l, boxed);
        }
    }

    /// Guard-pass write-back: a passed type test on an
    /// operand read from a frame slot refines that slot's tracked fact --
    /// the proof holds for the lineage's remaining body.
    /// The property arm's second evidence source: a receiver whose class-idx
    /// fact pins it to one layout tells us the field's fixed slot and value
    /// mask directly, so a site with no per-site row can still take the
    /// class-fact arm instead of falling to the generic inline IC. Sound by
    /// the same argument the per-site arm rests on -- a stamped class-idx
    /// names a validated fixed-slot layout -- and the arm re-checks nothing
    /// the fact does not already prove.
    ///
    /// Only an exact fact (lo == hi) qualifies: a predictor-group range does
    /// not pin the field's slot, and guessing one member's layout would be
    /// a guess, not evidence.
    pub(super) fn layout_site_for(&self, recv: &Operand, name: NameId) -> Option<PropSiteIn> {
        let exact = match (recv.cls, recv.likely_cls) {
            (Some((lo, hi)), _) if lo == hi => Some(lo),
            // The LAZY tier: an ADVISORY exact hint from the analysis's
            // per-site value class (`field_cls_sites`), never yet checked.
            // `cls_implied` cannot fire from it (recv.cls stays None), so
            // the synthesized row's form emits its own idx guard -- the
            // hint transitions to a proven cls via the hit arm's
            // refine_src, exactly the "guard lazily, at first use" rule. A
            // wrong hint costs one guarded miss into the IC arm the site
            // would have taken anyway.
            (None, Some((lo, hi))) if lo == hi => Some(lo),
            _ => None,
        };
        if let Some(k) = exact {
            if let Some(layout_id) = u32::from(k).checked_sub(1) {
                if let Some(&(slot, claim, range)) = self
                    .layout_fields
                    .get(&layout_id)
                    .and_then(|f| f.get(&name))
                {
                    return Some(PropSiteIn {
                        shallow_possible: true,
                        cell_addr: 0,
                        slot,
                        layout_id,
                        hi_layout_id: layout_id,
                        claim,
                        range: (!claim.is_none()).then_some(range).flatten(),
                    });
                }
            }
        }
        // No fallback on evidence weaker than an exact class or an exact
        // advisory hint. The script's own predicted layout is not used as
        // a fallback: the class-idx guards already miss about a quarter of
        // the time, and every miss pays the full inline-IC probe behind
        // it. Arming more arms on weaker evidence adds misses, not hits.
        None
    }

    /// Durable-fact write-back. The provenance it needs does not survive
    /// The version seam: `Operand::ranged`, which `run_version` rebuilds
    /// every stack operand with, has `src: None`, and in per-op BBV every
    /// operand a guard sees arrived as a block param. Without provenance
    /// every call early-returns here, so no guard ever makes its fact
    /// durable and no property access sees a class fact. Recovering the
    /// slot by value identity does not work: across the seam the value IS
    /// a different SSA value (the block param). The fix has to put
    /// provenance in the ctx, the way `cls` already rides it.
    pub(super) fn refine_src(&mut self, o: &Operand, fact: SlotCtx) {
        // Class facts only: numeric facts lose because they retype ctx
        // slots, which hands out different carrier reprs and pays a
        // conversion on every edge. The class fact is the one the property
        // arms consume, and it is the one that pays.
        let src = if fact.cls.is_some() || fact.ta.is_some() {
            o.src
        } else {
            None
        };
        let Some(src) = src else { return };
        let cell = match src {
            SlotRef::This => self.args_ctx.get_mut(0),
            SlotRef::Arg(i) => {
                if self.script.has_mapped_args {
                    return;
                }
                self.args_ctx.get_mut(1 + usize::from(i))
            }
            SlotRef::Local(i) => self.locals_ctx.get_mut(i as usize),
            // Binding facts carry no class part (see `install_gcell`).
            SlotRef::GCell(_) => None,
        };
        let Some(cell) = cell else { return };
        if let Some(m) = cell.meet(fact) {
            *cell = m;
        }
    }

    /// The slot was reassigned: any live operand still claiming it as its
    /// source must stop (a later guard on the old value would otherwise
    /// refine the slot with stale facts).
    pub(super) fn clear_stale_src(&mut self, slot: SlotRef) {
        for o in &mut self.stack {
            if o.src == Some(slot) {
                o.src = None;
            }
        }
    }

    /// Generic boxed binop/compare helper call.
    pub(super) fn emit_value_binop(
        &mut self,
        helper: Func,
        kind: u32,
        a: &Operand,
        b: &Operand,
    ) -> Value {
        let a_boxed = self.to_boxed(a);
        let b_boxed = self.to_boxed(b);
        let kind_v = self.i32_const(kind);
        self.rt_call(helper, true, |_, _| vec![kind_v, a_boxed, b_boxed])
            .unwrap()
    }

    // --- ToBoolean -------------------------------------------------------

    pub(super) fn to_bool_i32(&mut self, o: &Operand) -> Result<Value, String> {
        match o.repr {
            Repr::Bool | Repr::I32 => Ok(o.val),
            Repr::I64 => {
                let z = self.unop(Operator::I64Eqz, o.val, Type::I32);
                Ok(self.unop(Operator::I32Eqz, z, Type::I32))
            }
            Repr::Boxed if is_exact_int32(&o.ty) || is_exact_bool(&o.ty) => Ok(self.to_i32(o)),
            _ => {
                let boxed = self.to_boxed(o);
                let sh = self.boxed_const(32);
                let hi64 = self.binop(Operator::I64ShrU, boxed, sh, Type::I64);
                let hi = self.unop(Operator::I32WrapI64, hi64, Type::I32);
                let merge = self.body.add_block();
                let t_param = self.body.add_blockparam(merge, Type::I32);
                let dbl_blk = self.body.add_block();
                let rest_blk = self.body.add_block();
                let str_blk = self.body.add_block();
                let rest2_blk = self.body.add_block();
                let bi_blk = self.body.add_block();
                let simple_blk = self.body.add_block();

                let clear = self.i32_const(TAG_CLEAR);
                let is_dbl = self.binop(Operator::I32LtU, hi, clear, Type::I32);
                self.body.set_terminator(
                    self.cur,
                    Terminator::CondBr {
                        cond: is_dbl,
                        if_true: BlockTarget {
                            block: dbl_blk,
                            args: vec![],
                        },
                        if_false: BlockTarget {
                            block: rest_blk,
                            args: vec![],
                        },
                    },
                );

                self.cur = dbl_blk;
                let d = self.unop(Operator::F64ReinterpretI64, boxed, Type::F64);
                let zero_f = self.f64_const(0.0);
                let nz = self.binop(Operator::F64Ne, d, zero_f, Type::I32);
                let ord = self.binop(Operator::F64Eq, d, d, Type::I32);
                let t_dbl = self.binop(Operator::I32And, nz, ord, Type::I32);
                self.body.set_terminator(
                    dbl_blk,
                    Terminator::Br {
                        target: BlockTarget {
                            block: merge,
                            args: vec![t_dbl],
                        },
                    },
                );

                self.cur = rest_blk;
                let strt = self.i32_const(TAG_STRING as u32);
                let is_str = self.binop(Operator::I32Eq, hi, strt, Type::I32);
                self.body.set_terminator(
                    rest_blk,
                    Terminator::CondBr {
                        cond: is_str,
                        if_true: BlockTarget {
                            block: str_blk,
                            args: vec![],
                        },
                        if_false: BlockTarget {
                            block: rest2_blk,
                            args: vec![],
                        },
                    },
                );

                self.cur = str_blk;
                let low2 = self.unop(Operator::I32WrapI64, boxed, Type::I32);
                let len = self.load_i32(low2, STRING_LENGTH_OFFSET);
                let zero_i = self.i32_const(0);
                let t_str = self.binop(Operator::I32Ne, len, zero_i, Type::I32);
                self.body.set_terminator(
                    str_blk,
                    Terminator::Br {
                        target: BlockTarget {
                            block: merge,
                            args: vec![t_str],
                        },
                    },
                );

                self.cur = rest2_blk;
                let bit = self.i32_const(TAG_BIGINT_HI);
                let is_bi = self.binop(Operator::I32Eq, hi, bit, Type::I32);
                self.body.set_terminator(
                    rest2_blk,
                    Terminator::CondBr {
                        cond: is_bi,
                        if_true: BlockTarget {
                            block: bi_blk,
                            args: vec![],
                        },
                        if_false: BlockTarget {
                            block: simple_blk,
                            args: vec![],
                        },
                    },
                );

                self.cur = bi_blk;
                let tb = self.helpers.to_boolean;
                let t_bi = self.call_i32(tb, &[self.cx, boxed]);
                self.body.set_terminator(
                    bi_blk,
                    Terminator::Br {
                        target: BlockTarget {
                            block: merge,
                            args: vec![t_bi],
                        },
                    },
                );

                self.cur = simple_blk;
                let t_simple = self.emit_low32_truthy_with_dda(boxed);
                self.body.set_terminator(
                    self.cur,
                    Terminator::Br {
                        target: BlockTarget {
                            block: merge,
                            args: vec![t_simple],
                        },
                    },
                );

                self.cur = merge;
                Ok(t_param)
            }
        }
    }

    pub(super) fn emit_low32_truthy_with_dda(&mut self, boxed: Value) -> Value {
        let low = self.unop(Operator::I32WrapI64, boxed, Type::I32);
        let zero = self.i32_const(0);
        let low_t = self.binop(Operator::I32Ne, low, zero, Type::I32);
        let emu = self.emit_emu_undefined_gated(boxed);
        let not_emu = self.unop(Operator::I32Eqz, emu, Type::I32);
        self.binop(Operator::I32And, low_t, not_emu, Type::I32)
    }

    pub(super) fn emit_emu_undefined_gated(&mut self, boxed: Value) -> Value {
        let is_obj = self.tag_eq(boxed, TAG_OBJECT as u32);
        let obj_blk = self.body.add_block();
        let done_blk = self.body.add_block();
        let emu_param = self.body.add_blockparam(done_blk, Type::I32);
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
                    block: done_blk,
                    args: vec![zero],
                },
            },
        );
        self.cur = obj_blk;
        let fuse_word_addr = match self.dda_fuse_word_addr_ssa {
            Some(a) => a,
            None => {
                let fuse_slot = self.i32_const(self.helpers.dda_fuse_addr_slot);
                self.load_i32(fuse_slot, 0)
            }
        };
        let fuse_word = self.load_i32(fuse_word_addr, 0);
        let full_blk = self.body.add_block();
        self.body.set_terminator(
            self.cur,
            Terminator::CondBr {
                cond: fuse_word,
                if_true: BlockTarget {
                    block: full_blk,
                    args: vec![],
                },
                if_false: BlockTarget {
                    block: done_blk,
                    args: vec![zero],
                },
            },
        );
        self.cur = full_blk;
        let objptr = self.unop(Operator::I32WrapI64, boxed, Type::I32);
        let emu = self.emit_object_emulates_undefined_full(boxed, objptr);
        self.body.set_terminator(
            self.cur,
            Terminator::Br {
                target: BlockTarget {
                    block: done_blk,
                    args: vec![emu],
                },
            },
        );
        self.cur = done_blk;
        emu_param
    }

    pub(super) fn emit_object_emulates_undefined_full(
        &mut self,
        boxed: Value,
        objptr: Value,
    ) -> Value {
        let shape = self.load_i32(objptr, SHAPE_OFFSET);
        self.eff(shape, Eff::Read(HeapKind::Shape));
        let imm = self.load_i32(shape, SHAPE_IMMUTABLE_FLAGS_OFFSET);
        let nbit = self.i32_const(SHAPE_IS_NATIVE_BIT);
        let is_native = self.binop(Operator::I32And, imm, nbit, Type::I32);
        let native_blk = self.body.add_block();
        let helper_blk = self.body.add_block();
        let done_blk = self.body.add_block();
        let emu_param = self.body.add_blockparam(done_blk, Type::I32);
        self.body.set_terminator(
            self.cur,
            Terminator::CondBr {
                cond: is_native,
                if_true: BlockTarget {
                    block: native_blk,
                    args: vec![],
                },
                if_false: BlockTarget {
                    block: helper_blk,
                    args: vec![],
                },
            },
        );
        self.cur = native_blk;
        let base = self.load_i32(shape, SHAPE_BASESHAPE_OFFSET);
        self.eff(base, Eff::Read(HeapKind::Shape));
        let clasp = self.load_i32(base, BASESHAPE_CLASP_OFFSET);
        self.eff(clasp, Eff::Read(HeapKind::Shape));
        let flags = self.load_i32(clasp, CLASP_FLAGS_OFFSET);
        let emu_bit = self.i32_const(JSCLASS_EMULATES_UNDEFINED);
        let masked = self.binop(Operator::I32And, flags, emu_bit, Type::I32);
        let z = self.i32_const(0);
        let emu_native = self.binop(Operator::I32Ne, masked, z, Type::I32);
        self.body.set_terminator(
            native_blk,
            Terminator::Br {
                target: BlockTarget {
                    block: done_blk,
                    args: vec![emu_native],
                },
            },
        );
        self.cur = helper_blk;
        let tb = self.helpers.to_boolean;
        let truthy = self.call_i32(tb, &[self.cx, boxed]);
        let emu_helper = self.unop(Operator::I32Eqz, truthy, Type::I32);
        self.body.set_terminator(
            self.cur,
            Terminator::Br {
                target: BlockTarget {
                    block: done_blk,
                    args: vec![emu_helper],
                },
            },
        );
        self.cur = done_blk;
        emu_param
    }
}
