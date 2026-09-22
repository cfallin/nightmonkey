/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Generator and async-function bodies: the suspend/resume state machine.
//!
//! A generator body is entered twice over: once as an ordinary call, and
//! again for every resume. The engine half (runtime/NightGenerator.cpp) owns
//! the saved state -- locals and live operands go into the generator
//! object's stack storage, keyed by a resume index the frontend assigned --
//! and the interpreter's `JSOp::Resume` re-enters the compiled body through
//! `EnterNightResume` rather than trying to resume it itself.
//!
//! Two things make this fit BBV. First, the body is pinned to the GEN rung
//! (`gen_only`): a version's identity carries a *location* in the body --
//! its loop-token class and its track -- and a suspend crosses out of the
//! body entirely, so there is no arriving version for the resume to name.
//! On the GEN rung there is exactly one version per pc, which the resume can
//! name by pc alone. Second, a resume arrives with nothing proven: locals
//! and operands come back out of the generator's storage as boxed values and
//! the formal slots are not restored at all, so the landing version is
//! interned against an all-bottom arrival ctx and every later join with it
//! stays bottom.
//!
//! The physical entry dispatches fresh-vs-resume on the frame `this` slot: a
//! resume stages the JS_GENERATOR_CLOSING magic there, which no ordinary
//! call can produce, so the ABI needs no extra parameter.
//!
//! TODO(perf): the GEN rung is a correctness floor, not a target. These
//! bodies get generic-lane code -- one facts-empty version per pc, so no
//! type is ever proven and every property read, arithmetic op and call takes
//! its unspeculated form. That is the whole point today: the bar is beating
//! the C++ interpreter, which it clears, and a generator body is usually a
//! driver around work that lives elsewhere. Raising it means versioning
//! across a suspend, which is the thing the pin exists to avoid -- a version
//! names a location inside the body and a resume arrives from outside it.
//! The tractable middle is to version the STRAIGHT-LINE REGIONS between
//! suspend points (each is entered only from its own predecessors, so it can
//! carry facts) while every landing pc stays the single bottom version a
//! resume can name. Nobody has measured what that would buy; do that first.
//! See docs/TODO 2.1.

use super::*;

/// The `[sent value, generator, resume kind]` triple the interpreter's
/// resume protocol pushes onto the operand stack at the landing pc.
const RESUME_TRIPLE: u32 = 3;

impl<'a> Bbv<'a> {
    /// `JSOp::Generator`: create this frame's generator object from the
    /// callee and the env chain. May GC.
    pub(super) fn emit_generator(&mut self, pc: Pc) {
        let callee = self.load_i64(self.sp, 0);
        let env = if self.needs_env {
            self.load_i64(self.vp, self.env_slot_off)
        } else {
            self.boxed_const(TAG_UNDEFINED << 32)
        };
        let h = self.helpers.create_generator;
        let r = self
            .rt_call(h, true, move |_, _| vec![callee, env])
            .unwrap();
        self.push_boxed(r, self.def_type(pc, 0));
    }

    /// `InitialYield` / `Yield` / `Await`: save the frame into the
    /// generator's storage, register the resume label, and return to the
    /// caller -- the generator object for `InitialYield` (`[gen] ->`), the
    /// result object for the other two (`[rval, gen] ->`).
    pub(super) fn emit_yield(&mut self, pc: Pc, op: JSOp, k: u32) -> Result<(), String> {
        let gen_op = self.pop()?;
        let gen_b = self.to_boxed(&gen_op);
        let rval_b = if op == JSOp::InitialYield {
            gen_b
        } else {
            let rv = self.pop()?;
            self.to_boxed(&rv)
        };
        // The live operands go to their frame slots (the engine half copies
        // the region wholesale); the locals are already there, since
        // `write_local` is write-through.
        let d = self.spill_all();
        let env = if self.needs_env {
            self.load_i64(self.vp, self.env_slot_off)
        } else {
            self.boxed_const(0)
        };
        let lp = self.add_offset(self.vp, self.local_base);
        let nl = self.i32_const(self.nlocals);
        let op_ptr = self.add_offset(self.vp, self.operand_base);
        let kv = self.i32_const(k);
        let dv = self.i32_const(d);
        let gs = self.helpers.gen_suspend;
        let _ = self.call_i32(gs, &[self.cx, gen_b, kv, lp, nl, op_ptr, dv, env]);
        self.store_i64(self.retval_out, 0, rval_b);
        let zero = self.i32_const(0);
        let flags = self.i32_const(FLAGS_ALL);
        self.body.set_terminator(
            self.cur,
            Terminator::Return {
                values: vec![zero, flags],
            },
        );
        self.register_resume(pc + op.len(), k, d);
        self.stack.clear();
        Ok(())
    }

    /// Intern the version a resume at label `k` lands on, and record it for
    /// the dispatcher. The arrival ctx is written out explicitly rather than
    /// taken from the suspend point: what a resume delivers is the frame the
    /// engine half restored, which proves nothing about any slot.
    fn register_resume(&mut self, after_pc: Pc, k: u32, depth: u32) {
        let saved = self.arm_state();
        // Only the operands' FACTS reach the version ctx; the dispatcher
        // supplies the values. `Value::invalid()` rather than a fresh const,
        // so nothing is appended to the (already terminated) suspend block
        // and any accidental use is loud instead of silently wrong.
        self.stack = (0..depth + RESUME_TRIPLE)
            .map(|_| Operand::plain(Value::invalid(), Repr::Boxed, bottom_ty()))
            .collect();
        self.locals_ctx = vec![SlotCtx::TOP; self.locals_ctx.len()];
        self.args_ctx = vec![SlotCtx::TOP; self.args_ctx.len()];
        self.cur_track = Track::Opt;
        let ver = self.succ_version(after_pc);
        self.ensure_version_block(ver, None);
        self.gen_resume.push((k, ver, depth));
        self.arm_restore(saved);
    }

    /// The fresh-vs-resume fork at the physical entry, emitted ahead of the
    /// prologue so a resume skips it entirely (the prologue would clobber
    /// the restored frame). Leaves `self.cur` on the fresh arm.
    pub(super) fn emit_gen_entry_fork(&mut self) {
        // Both arms use these, and neither dominates the other.
        self.emit_entry_word_loads();
        let disp = self.body.add_block();
        let fresh = self.body.add_block();
        self.gen_dispatch_blk = Some(disp);
        let thisv = self.load_i64(self.sp, 8);
        let sentinel = self.boxed_const((TAG_MAGIC << 32) | MAGIC_GENERATOR_CLOSING);
        let is_resume = self.binop(Operator::I64Eq, thisv, sentinel, Type::I32);
        self.cond_br(is_resume, disp, fresh);
        self.cur = fresh;
    }

    /// Build the resume dispatcher, once the whole body is emitted and every
    /// landing version therefore exists: reload what the Resume hook staged,
    /// hand the frame back to the engine half, then `Select` on the saved
    /// resume index into a per-label preamble that reloads the saved
    /// operands and enters the landing version.
    pub(super) fn finalize_gen_dispatch(&mut self) {
        let Some(disp) = self.gen_dispatch_blk else {
            return;
        };
        let saved_cur = self.cur;
        self.cur = disp;
        // The hook-staged descriptor -- [resume index i32, resume kind i32,
        // gen Value, arg Value] -- sits at the frame's local base and
        // OVERLAPS the local region, so all four fields are read before any
        // store into the frame below.
        let desc = self.add_offset(self.vp, self.local_base);
        let ridx = self.load_i32(desc, 0);
        let rkind = self.load_i32(desc, 4);
        let rgen = self.load_i64(desc, 8);
        let rarg = self.load_i64(desc, 16);
        // Every rooted frame slot must hold a valid boxed Value before the
        // first may-GC op. The engine half fills locals and the env head;
        // rval and new.target start undefined, since the prologue that would
        // normally do that is exactly what a resume skipped.
        let undef = self.boxed_const(TAG_UNDEFINED << 32);
        self.store_i64(self.vp, self.rval_slot_off, undef);
        if self.needs_new_target {
            self.store_i64(self.vp, self.new_target_slot_off, undef);
        }
        let lp = self.add_offset(self.vp, self.local_base);
        let nl = self.i32_const(self.nlocals);
        let ep = if self.needs_env {
            self.add_offset(self.vp, self.env_slot_off)
        } else {
            self.i32_const(0)
        };
        let op_ptr = self.add_offset(self.vp, self.operand_base);
        let gr = self.helpers.gen_restore;
        let _ = self.call_i32(gr, &[self.cx, rgen, lp, nl, ep, op_ptr]);
        // A resume index with no label is unreachable for a well-formed
        // generator; report an error rather than branch somewhere plausible.
        let err_blk = self.body.add_block();
        self.cur = err_blk;
        let one = self.i32_const(1);
        let all = self.i32_const(FLAGS_ALL);
        self.body.set_terminator(
            err_blk,
            Terminator::Return {
                values: vec![one, all],
            },
        );
        let labels = std::mem::take(&mut self.gen_resume);
        let max_k = labels.iter().map(|&(k, _, _)| k).max().unwrap_or(0);
        let mut targets: Vec<BlockTarget> = vec![
            BlockTarget {
                block: err_blk,
                args: vec![],
            };
            (max_k + 1) as usize
        ];
        for (k, ver, depth) in labels {
            let pre = self.body.add_block();
            self.cur = pre;
            let mut args: Vec<Value> = Vec::with_capacity((depth + RESUME_TRIPLE) as usize);
            for j in 0..depth {
                args.push(self.load_i64(self.vp, self.operand_base + 8 * j));
            }
            // The interpreter's resume protocol, as the AfterYield landing
            // expects it: the sent value, the generator, and the boxed
            // resume kind.
            args.push(rarg);
            args.push(rgen);
            let k64 = self.unop(Operator::I64ExtendI32U, rkind, Type::I64);
            let ktag = self.boxed_const(TAG_INT32 << 32);
            let kboxed = self.binop(Operator::I64Or, ktag, k64, Type::I64);
            args.push(kboxed);
            let block = self.blocks[&ver];
            debug_assert_eq!(
                self.block_params[&ver].len(),
                args.len(),
                "resume preamble arg count differs from the landing version's params"
            );
            self.body.set_terminator(
                pre,
                Terminator::Br {
                    target: BlockTarget { block, args },
                },
            );
            targets[k as usize] = BlockTarget {
                block: pre,
                args: vec![],
            };
        }
        self.body.set_terminator(
            disp,
            Terminator::Select {
                value: ridx,
                targets,
                default: BlockTarget {
                    block: err_blk,
                    args: vec![],
                },
            },
        );
        self.cur = saved_cur;
    }

    /// `CheckResumeKind`: `[val, gen, kind] -> [val]`. Next falls through
    /// with `val`; Throw and Return both leave through the helper, which
    /// always raises -- Throw as the value itself, Return by staging `val`
    /// in the rval register and raising the JS_GENERATOR_CLOSING magic, so
    /// the enclosing finallys run (they observe it through `IsGenClosing`)
    /// and the error epilogue turns a surviving magic into a normal return.
    pub(super) fn emit_check_resume_kind(&mut self) -> Result<(), String> {
        let kind_op = self.pop()?;
        let gen_op = self.pop()?;
        let val_op = self
            .stack
            .last()
            .cloned()
            .ok_or("CheckResumeKind on empty stack")?;
        let kind_i = self.to_i32(&kind_op);
        let gen_b = self.to_boxed(&gen_op);
        let val_b = self.to_boxed(&val_op);
        let cont = self.body.add_block();
        let slow = self.body.add_block();
        let is_next = self.unop(Operator::I32Eqz, kind_i, Type::I32);
        self.cond_br(is_next, cont, slow);
        let saved = self.arm_state();
        self.cur = slow;
        let rval_addr = self.add_offset(self.vp, self.rval_slot_off);
        let h = self.helpers.gen_check_resume;
        self.rt_call(h, false, move |_, _| vec![gen_b, val_b, kind_i, rval_addr]);
        // The helper always raises, so this tail is unreachable.
        let one = self.i32_const(1);
        let all = self.i32_const(FLAGS_ALL);
        self.body.set_terminator(
            self.cur,
            Terminator::Return {
                values: vec![one, all],
            },
        );
        self.arm_restore(saved);
        self.cur = cont;
        Ok(())
    }

    /// The generator form of the error epilogue: a pending
    /// JS_GENERATOR_CLOSING magic means a forced `.return()` finished
    /// unwinding its finallys, so the frame returns the rval register
    /// normally instead of propagating an error -- exactly what the
    /// interpreter's `HandleError` does for a generator frame.
    pub(super) fn emit_gen_error_epilogue(&mut self, b: Block) {
        self.cur = b;
        let gc = self.helpers.gen_closing;
        let closing = self.call_i32(gc, &[self.cx]);
        let ret_blk = self.body.add_block();
        let err_blk = self.body.add_block();
        self.cond_br(closing, ret_blk, err_blk);
        // Each arm mints its own constants: a value belongs to the block it
        // was emitted into, and neither arm dominates the other.
        self.cur = ret_blk;
        let rval = self.load_i64(self.vp, self.rval_slot_off);
        self.store_i64(self.retval_out, 0, rval);
        let zero = self.i32_const(0);
        let all = self.i32_const(FLAGS_ALL);
        self.body.set_terminator(
            ret_blk,
            Terminator::Return {
                values: vec![zero, all],
            },
        );
        self.cur = err_blk;
        let one = self.i32_const(1);
        let all = self.i32_const(FLAGS_ALL);
        self.body.set_terminator(
            err_blk,
            Terminator::Return {
                values: vec![one, all],
            },
        );
    }

    /// The exception trampoline for a CATCH handler in a generator body: a
    /// forced `.return()` unwind (a pending JS_GENERATOR_CLOSING) skips
    /// catches -- only finallys run -- so the catch edge tests the magic at
    /// runtime and reroutes to whatever the skip-catches walk finds instead
    /// (the next finally, or the error epilogue's closing-to-return
    /// conversion). Mirrors `ProcessTryNotes`' `isClosingGenerator` skip.
    ///
    /// The test is the PEEK-only helper: the magic has to stay pending for
    /// the rerouted unwind's finallys and for the epilogue, which is what
    /// clears it.
    pub(super) fn exception_target_gen_catch(
        &mut self,
        closes: Vec<UnwindClose>,
        handler: Option<(Pc, u32, bool)>,
    ) -> BlockTarget {
        let (closes_full, handler2) = self.walk_try_notes_skip_catches(self.stack.len());
        debug_assert!(closes_full.len() >= closes.len());
        let needs_spill = closes_full
            .iter()
            .any(|c| matches!(c, UnwindClose::Destructuring(_)));
        let saved_cur = self.cur;
        let t = self.body.add_block();
        self.cur = t;
        let gc = self.helpers.gen_is_closing;
        let closing_blk = self.body.add_block();
        if !needs_spill {
            // Every close on both arms is a leaf `CloseIterator`: nothing
            // GCs, so the operand SSA stays valid for the landing-pad args.
            self.emit_leaf_closes(&closes);
            let closing = self.call_i32(gc, &[self.cx]);
            let catch_tgt = self.handler_target(handler);
            self.body.set_terminator(
                self.cur,
                Terminator::CondBr {
                    cond: closing,
                    if_true: BlockTarget {
                        block: closing_blk,
                        args: vec![],
                    },
                    if_false: catch_tgt,
                },
            );
            self.cur = closing_blk;
            self.emit_leaf_closes(&closes_full[closes.len()..]);
            let tgt2 = self.handler_target(handler2);
            self.body
                .set_terminator(self.cur, Terminator::Br { target: tgt2 });
        } else {
            // A close can GC (a destructuring `return()`): spill every live
            // operand once, run each arm's closes out of the slots, and
            // compute each landing target from the reloaded (post-GC) view.
            let n = self.stack.len() as u32;
            for i in 0..n {
                let o = self.stack[i as usize].clone();
                let b = self.to_boxed(&o);
                self.store_i64(self.vp, self.operand_base + 8 * i, b);
            }
            self.emit_spilled_closes(&closes, n);
            let closing = self.call_i32(gc, &[self.cx]);
            let saved = self.arm_state();
            self.reload_spilled_stack(n);
            let catch_tgt = self.handler_target(handler);
            self.arm_restore(saved);
            self.body.set_terminator(
                self.cur,
                Terminator::CondBr {
                    cond: closing,
                    if_true: BlockTarget {
                        block: closing_blk,
                        args: vec![],
                    },
                    if_false: catch_tgt,
                },
            );
            self.cur = closing_blk;
            self.emit_spilled_closes(&closes_full[closes.len()..], n);
            let saved = self.arm_state();
            self.reload_spilled_stack(n);
            let tgt2 = self.handler_target(handler2);
            self.arm_restore(saved);
            self.body
                .set_terminator(self.cur, Terminator::Br { target: tgt2 });
        }
        self.cur = saved_cur;
        BlockTarget {
            block: t,
            args: vec![],
        }
    }

    /// Run the unwind closes against the live operand SSA (leaf closes only).
    fn emit_leaf_closes(&mut self, closes: &[UnwindClose]) {
        for c in closes {
            if let UnwindClose::ForIn(depth) = *c {
                let iter = self.stack[depth as usize - 1].clone();
                let ib = self.to_boxed(&iter);
                let ei = self.helpers.end_iter;
                self.call_void(ei, &[self.cx, ib]);
            }
        }
    }

    /// Run the unwind closes against the spilled operand slots, for the arm
    /// that holds a may-GC destructuring close. `n` is the spilled depth.
    fn emit_spilled_closes(&mut self, closes: &[UnwindClose], n: u32) {
        let top = self.add_offset(self.vp, self.operand_base + 8 * n);
        for c in closes {
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
    }

    /// Re-point the live operand stack at the spilled slots after a close
    /// that may have GC'd.
    fn reload_spilled_stack(&mut self, n: u32) {
        for i in 0..n {
            let v = self.load_i64(self.vp, self.operand_base + 8 * i);
            self.stack[i as usize].val = v;
            self.stack[i as usize].repr = Repr::Boxed;
        }
    }
}
