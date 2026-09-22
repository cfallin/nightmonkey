/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! `emit_op`: the per-op dispatch. One version lowers exactly one op.

use super::*;

// --- op lowerings (GEN-only generic forms; each arm cites its source
// emitter in translate.rs emit_op unless noted) ---------------------------

impl<'a> Bbv<'a> {
    // --- ctx-consulting operator arms ------------------------------------
    //
    // Each numeric operator ladder: (1) ctx-proven forms emit tag-free code
    // straight-line (emission consults the ctx directly); (2) otherwise the
    // tag-tested arms the generic lane already pays for become per-arm
    // continuations -- the strongest arm falls through refined (the version
    // keeps emitting under the implication), the weaker arms branch to the
    // next pc's version under their own ctx, and theta routes them (OPT /
    // ovf / GEN). Deopt is thereby ordinary control flow: no merge-backs,
    // no pre-split landings. Copied lowering bodies cite translate.rs
    // (emit_add / emit_arith / emit_tagguarded_arith / emit_compare /
    // emit_tonumeric_with / emit_neg / to_int32_js).

    /// Push local `localno`'s current value: its carrier, else the frame
    /// slot (which the version entry marked fresh).
    pub(super) fn push_local(&mut self, localno: u32) {
        let slot = self.locals_ctx[localno as usize];
        let (val, repr) = match self.locals_ssa.get(localno as usize).copied().flatten() {
            Some(c) => c,
            None => {
                let v = self.load_i64(self.vp, self.local_base + 8 * localno);
                if let Some(c) = self.locals_ssa.get_mut(localno as usize) {
                    *c = Some((v, Repr::Boxed));
                }
                (v, Repr::Boxed)
            }
        };
        self.stack.push(Operand {
            val,
            repr,
            ty: slot.to_ty(),
            range: slot.range,
            cls: slot.cls,
            cls_shallow: slot.cls_shallow,
            cls_slots: slot.cls_slots,
            ta: slot.ta,
            likely_cls: slot.likely_cls,
            src: Some(SlotRef::Local(localno)),
            iv: slot.iv.map(|r| (r.lo, r.hi, false)),
            fresh: false,
            prov: slot.prov,
        });
    }

    pub(super) fn emit_op(
        &mut self,
        p: &mut BytecodeParser,
        pc: Pc,
        op: JSOp,
    ) -> Result<(), String> {
        use JSOp::*;
        self.cur_op = Some(op);
        if Self::op_kills_proto_cell(op) {
            self.kill_proto_cell();
        }
        match op {
            Nop | Lineno | JumpTarget | LoopHead | Debugger | NopDestructuring | NopIsAssignOp
            | TryDestructuring | DebugLeaveLexicalEnv | Finally => {
                self.skip_operands(p, op);
            }

            // --- constants ---
            Undefined => {
                self.skip_operands(p, op);
                let v = self.boxed_const(TAG_UNDEFINED << 32);
                self.push_literal(v, Repr::Boxed, prim_desc(PRIM_UNDEFINED));
            }
            Void => {
                self.skip_operands(p, op);
                self.pop()?;
                let v = self.boxed_const(TAG_UNDEFINED << 32);
                self.push_literal(v, Repr::Boxed, prim_desc(PRIM_UNDEFINED));
            }
            Null => {
                self.skip_operands(p, op);
                let v = self.boxed_const(TAG_NULL << 32);
                self.push_literal(v, Repr::Boxed, prim_desc(PRIM_NULL));
            }
            False => {
                self.skip_operands(p, op);
                let v = self.i32_const(0);
                self.push_literal(v, Repr::Bool, prim_desc(PRIM_BOOLEAN));
            }
            True => {
                self.skip_operands(p, op);
                let v = self.i32_const(1);
                self.push_literal(v, Repr::Bool, prim_desc(PRIM_BOOLEAN));
            }
            Zero => {
                self.skip_operands(p, op);
                let v = self.i32_const(0);
                self.push_int_literal(v, 0);
            }
            One => {
                self.skip_operands(p, op);
                let v = self.i32_const(1);
                self.push_int_literal(v, 1);
            }
            Int8 => {
                let imm = p.next_int8().unwrap();
                let v = self.i32_const(imm as i32 as u32);
                self.push_int_literal(v, i64::from(imm));
            }
            Uint16 => {
                let imm = p.next_uint16().unwrap();
                let v = self.i32_const(u32::from(imm));
                self.push_int_literal(v, i64::from(imm));
            }
            Uint24 => {
                let imm = p.next_uint24().unwrap();
                let v = self.i32_const(imm);
                self.push_int_literal(v, i64::from(imm));
            }
            Int32 => {
                let imm = p.next_int32().unwrap();
                let v = self.i32_const(imm as u32);
                self.push_int_literal(v, i64::from(imm));
            }
            Double => {
                let bits = p.next_uint64().unwrap();
                let v = self.boxed_const(bits);
                let f = f64::from_bits(bits);
                let range = if f.fract() == 0.0 && f.abs() <= 9007199254740992.0 && bits != 1 << 63
                {
                    RangeBucket::I53
                } else {
                    RangeBucket::Top
                };
                // An integral double imm seeds an interval only outside
                // int32 range: the value is double-tagged raw bits, and an
                // in-int32 interval would let the canonical-tag inference
                // wrongly claim an Int32 tag for it (intra's rule, ported).
                let iv = if range == RangeBucket::I53
                    && (f < i32::MIN as i64 as f64 || f > i32::MAX as i64 as f64)
                {
                    Some((f as i64, f as i64, false))
                } else {
                    None
                };
                self.stack.push(
                    Operand::ranged(v, Repr::Boxed, prim_desc(PRIM_DOUBLE), range).with_iv(iv),
                );
            }
            Hole => {
                self.skip_operands(p, op);
                let v = self.boxed_const((TAG_MAGIC << 32) | MAGIC_ELEMENTS_HOLE);
                self.push_literal(v, Repr::Boxed, self.def_type(pc, 0));
            }
            Uninitialized => {
                self.skip_operands(p, op);
                let v = self.boxed_const((TAG_MAGIC << 32) | MAGIC_UNINITIALIZED_LEXICAL);
                self.push_boxed(v, prim_desc(Prims::EMPTY));
            }
            String => {
                let name_index = p.next_uint32().unwrap();
                let atom_id = self.resolve_atom(name_index)?;
                self.emit_string_literal(atom_id);
            }
            GetIntrinsic => {
                let name_index = p.next_uint32().unwrap();
                let atom_id = self.resolve_atom(name_index)?;
                self.emit_get_intrinsic(atom_id, pc + op.len());
            }
            Object | CallSiteObj => {
                let object_index = p.next_uint32().unwrap();
                let idx_v = self.i32_const(object_index);
                let script = self.cur_script_value();
                let obj = self.helpers.object;
                let result = self.call_i64(obj, &[self.cx, script, idx_v]);
                self.push_boxed(result, self.def_type(pc, 0));
            }
            Symbol => {
                let code = p.next_uint8().unwrap();
                let code_v = self.i32_const(u32::from(code));
                let sym = self.helpers.symbol;
                let result = self.call_i64(sym, &[self.cx, code_v]);
                self.push_boxed(result, prim_desc(Prims::EMPTY));
            }
            RegExp => {
                let index = p.next_uint32().unwrap();
                let idx_v = self.i32_const(index);
                let script_v = self.cur_script_value();
                let h = self.helpers.regexp;
                let result = self.rt_call(h, true, |_, _| vec![script_v, idx_v]).unwrap();
                self.push_boxed(result, self.def_type(pc, 0));
            }

            // --- checks / coercions ---
            IsNullOrUndefined => {
                self.skip_operands(p, op);
                let v = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or("IsNullOrUndefined on empty stack")?;
                let vb = self.to_boxed(&v);
                let is_u = self.tag_eq(vb, TAG_UNDEFINED as u32);
                let is_n = self.tag_eq(vb, TAG_NULL as u32);
                let b = self.binop(Operator::I32Or, is_u, is_n, Type::I32);
                let b64 = self.unop(Operator::I64ExtendI32U, b, Type::I64);
                let tag = self.boxed_const(TAG_BOOLEAN << 32);
                let boxed = self.binop(Operator::I64Or, tag, b64, Type::I64);
                self.push_boxed(boxed, prim_desc(PRIM_BOOLEAN));
            }
            ToString => {
                self.skip_operands(p, op);
                let v = self.pop()?;
                // A string is its own ToString; anything else through the
                // epoch-kept helper (a number's conversion allocates, an
                // object's may run user code). The self-hosted String
                // builtins commonly open with this coercion.
                if is_string_only(&v.ty) || self.outline_generic() {
                    if is_string_only(&v.ty) {
                        self.stack.push(v);
                    } else {
                        let vb = self.to_boxed(&v);
                        let ts = self.helpers.tostring;
                        let r = self.rt_unary_boxed(ts, vb);
                        self.push_boxed(r, prim_desc(PRIM_STRING));
                    }
                } else {
                    let vb = self.to_boxed(&v);
                    let is_s = self.tag_eq(vb, TAG_STRING as u32);
                    let str_blk = self.body.add_block();
                    let conv_blk = self.body.add_block();
                    self.cond_br(is_s, str_blk, conv_blk);
                    let next_pc = pc + op.len();
                    self.side_arm_keep(conv_blk, next_pc, move |s| {
                        let ts = s.helpers.tostring;
                        let r =
                            s.rt_call_keep(ts, 0, Some(next_pc), &prim_desc(PRIM_STRING), vec![vb]);
                        Operand::plain(r, Repr::Boxed, prim_desc(PRIM_STRING))
                    });
                    self.cur = str_blk;
                    let mut sv = v;
                    sv.ty = prim_desc(PRIM_STRING);
                    self.stack.push(sv);
                }
            }
            ToPropertyKey => {
                self.skip_operands(p, op);
                let v = self.pop()?;
                // An int32 or string is already a property key: no helper
                // (compound `a[i] op= v` sites resolve their key
                // statically). Proven by type, or by one tag test with the
                // coercing helper on a side continuation.
                let key_ty =
                    !v.ty.outside && v.ty.prims.is_nonempty_subset_of(PRIM_INT32.or(PRIM_STRING));
                if key_ty || self.outline_generic() {
                    if key_ty {
                        self.stack.push(v);
                    } else {
                        let v_b = self.to_boxed(&v);
                        let h = self.helpers.to_property_key;
                        let result = self.rt_unary_boxed(h, v_b);
                        self.push_boxed(result, self.def_type(pc, 0));
                    }
                } else {
                    // Exact int32 on the fall-through (the element access
                    // behind it wants the int32 fact, not int32|string),
                    // a string on its own numeric-category arm, the
                    // coercing helper on the stepping arm.
                    let v_b = self.to_boxed(&v);
                    let is_int = self.tag_eq(v_b, TAG_INT32 as u32);
                    let int_blk = self.body.add_block();
                    let rest_blk = self.body.add_block();
                    self.cond_br(is_int, int_blk, rest_blk);
                    self.cur = rest_blk;
                    let is_str = self.tag_eq(v_b, TAG_STRING as u32);
                    let str_blk = self.body.add_block();
                    let slow_blk = self.body.add_block();
                    self.cond_br(is_str, str_blk, slow_blk);
                    let next_pc = pc + op.len();
                    let rty = self.def_type(pc, 0);
                    self.side_arm(slow_blk, next_pc, move |s| {
                        let h = s.helpers.to_property_key;
                        let r = s.rt_unary_boxed(h, v_b);
                        Operand::plain(r, Repr::Boxed, rty)
                    });
                    self.side_arm(str_blk, next_pc, move |_| {
                        Operand::plain(v_b, Repr::Boxed, prim_desc(PRIM_STRING))
                    });
                    self.cur = int_blk;
                    let mut k = v;
                    k.ty = prim_desc(PRIM_INT32);
                    self.stack.push(k);
                }
            }
            CheckObjCoercible => {
                self.skip_operands(p, op);
                let v = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or("CheckObjCoercible on empty stack")?;
                let vb = self.to_boxed(&v);
                let h = self.helpers.check_obj_coercible;
                self.rt_call(h, false, |_, _| vec![vb]);
            }
            CheckClassHeritage => {
                self.skip_operands(p, op);
                let v = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or("CheckClassHeritage on empty stack")?;
                let vb = self.to_boxed(&v);
                let h = self.helpers.check_class_heritage;
                self.rt_call(h, false, |_, _| vec![vb]);
            }
            CheckIsObj => {
                let kind = p.next_uint8().unwrap();
                let kind_v = self.i32_const(u32::from(kind));
                let v = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or("CheckIsObj on empty stack")?;
                let vb = self.to_boxed(&v);
                let h = self.helpers.check_is_obj;
                self.rt_call(h, false, |_, _| vec![vb, kind_v]);
            }
            CheckThis => {
                self.skip_operands(p, op);
                let v = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or("CheckThis on empty stack")?;
                let vb = self.to_boxed(&v);
                let h = self.helpers.check_this;
                self.rt_call(h, false, |_, _| vec![vb]);
            }
            CheckThisReinit => {
                self.skip_operands(p, op);
                let v = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or("CheckThisReinit on empty stack")?;
                let vb = self.to_boxed(&v);
                let h = self.helpers.check_this_reinit;
                self.rt_call(h, false, |_, _| vec![vb]);
            }
            CheckReturn => {
                self.skip_operands(p, op);
                let thisv = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or("CheckReturn on empty stack")?;
                let tb = self.to_boxed(&thisv);
                let rval = self.load_i64(self.vp, self.rval_slot_off);
                let h = self.helpers.check_return;
                let r = self.rt_call(h, true, |_, _| vec![tb, rval]).unwrap();
                self.pop()?;
                self.push_boxed(r, self.def_type(pc, 0));
            }
            CheckLexical | CheckAliasedLexical => {
                self.skip_operands(p, op);
                let v = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or("CheckLexical on empty stack")?;
                let vb = self.to_boxed(&v);
                let script = self.cur_script_value();
                let pc_v = self.i32_const(pc.get());
                let h = self.helpers.check_lexical;
                self.rt_call(h, false, |_, _| vec![vb, script, pc_v]);
            }
            ThrowSetConst => {
                self.skip_operands(p, op);
                let script = self.cur_script_value();
                let pc_v = self.i32_const(pc.get());
                let h = self.helpers.throw_set_const;
                self.rt_throw(h, &[script, pc_v]);
            }
            ThrowMsg => {
                let kind = p.next_uint8().unwrap();
                let kind_v = self.i32_const(u32::from(kind));
                let h = self.helpers.throw_msg;
                self.rt_throw(h, &[kind_v]);
            }
            BuiltinObject => {
                let kind = p.next_uint8().unwrap();
                self.emit_builtin_object(u32::from(kind), pc + op.len());
            }

            // --- frame values ---
            Callee => {
                self.skip_operands(p, op);
                let callee = self.load_i64(self.sp, 0);
                self.push_boxed(callee, self.def_type(pc, 0));
            }
            NewTarget => {
                self.skip_operands(p, op);
                let nt = self.load_i64(self.vp, self.new_target_slot_off);
                self.push_boxed(nt, self.def_type(pc, 0));
            }
            IsConstructing => {
                self.skip_operands(p, op);
                let v = self.boxed_const((TAG_MAGIC << 32) | MAGIC_IS_CONSTRUCTING);
                self.push_boxed(v, prim_desc(Prims::EMPTY));
            }
            FunctionThis => {
                self.skip_operands(p, op);
                self.emit_function_this(pc);
            }
            GlobalThis => {
                self.skip_operands(p, op);
                let h = self.helpers.global_this;
                let result = self.rt_call(h, true, |_, _| vec![]).unwrap();
                self.push_boxed(result, self.def_type(pc, 0));
            }
            ArgumentsLength => {
                self.skip_operands(p, op);
                self.push_known(self.argc, Repr::I32, prim_desc(PRIM_INT32));
            }
            GetActualArg => {
                self.skip_operands(p, op);
                let index = self.pop()?;
                let idx = self.to_i32(&index);
                let eight = self.i32_const(8);
                let byte_off = self.binop(Operator::I32Mul, idx, eight, Type::I32);
                let base = self.binop(Operator::I32Add, self.sp, byte_off, Type::I32);
                let v = self.load_i64(base, 16);
                self.push_boxed(v, self.def_type(pc, 0));
            }
            Rest => {
                self.skip_operands(p, op);
                let nformal = u32::from(self.script.nargs).saturating_sub(1);
                let h = self.helpers.rest;
                let r = self
                    .rt_call(h, true, |s, _| {
                        let nf = s.i32_const(nformal);
                        vec![s.sp, s.argc, nf]
                    })
                    .unwrap();
                self.push_boxed(r, self.def_type(pc, 0));
            }
            Arguments => {
                self.skip_operands(p, op);
                if self.apply_fwd_pcs_here().is_empty() {
                    self.emit_arguments_lazy(pc);
                } else {
                    // Apply-forward: this script's arguments object is
                    // proven unobservable (it only flows into resolved apply
                    // forwards, recognized by pc) -- push a placeholder and
                    // skip the build; the forward reuses the caller's live
                    // actuals -- the root frame's, or a spliced wrapper's
                    // frame, which keeps them below its locals.
                    let undef = self.boxed_const(TAG_UNDEFINED << 32);
                    self.push_boxed(undef, bottom_ty());
                }
            }

            // --- locals / args ---
            GetArg => {
                let argno = p.next_uint16().unwrap();
                if self.script.has_mapped_args {
                    let obj = self.load_i64(self.vp, self.args_obj_slot_off);
                    let idx = self.i32_const(u32::from(argno));
                    let v = self.call_i64(self.helpers.get_mapped_arg, &[obj, idx]);
                    self.push_boxed(v, self.def_type(pc, 0));
                } else {
                    self.read_arg(argno, self.def_type(pc, 0), Some(pc + JSOp::GetArg.len()));
                }
            }
            GetFrameArg => {
                let argno = p.next_uint16().unwrap();
                self.read_arg(
                    argno,
                    self.def_type(pc, 0),
                    Some(pc + JSOp::GetFrameArg.len()),
                );
            }
            SetArg => {
                let argno = p.next_uint16().unwrap();
                let o = self.pop()?;
                if self.script.has_mapped_args {
                    let boxed = self.to_boxed(&o);
                    let obj = self.load_i64(self.vp, self.args_obj_slot_off);
                    let idx = self.i32_const(u32::from(argno));
                    self.call_void(self.helpers.set_mapped_arg, &[obj, idx, boxed]);
                    self.push_boxed(boxed, o.ty);
                } else {
                    // The `write_local` discipline for a formal: a raw-repr
                    // value keeps its carrier raw and defers the frame store
                    // to `flush_stale_locals` (every version edge, since
                    // formals are never carried); everything else stores
                    // eagerly, the GC tracing the frame.
                    let key = STALE_ARG | u32::from(argno);
                    let defer = !self.gen_only
                        && matches!(o.repr, Repr::I32 | Repr::F64 | Repr::Bool | Repr::I64)
                        && self.args_ssa.len() > usize::from(argno);
                    let (val, repr) = if defer {
                        self.frame_stale.insert(key);
                        (o.val, o.repr)
                    } else {
                        self.frame_stale.remove(&key);
                        let boxed = self.to_boxed(&o);
                        if self.cur_seg.is_some() {
                            self.store_i64(
                                self.vp,
                                self.frame_base + 16 + 8 * u32::from(argno),
                                boxed,
                            );
                        } else {
                            self.store_i64(self.sp, 16 + 8 * u32::from(argno), boxed);
                        }
                        (boxed, Repr::Boxed)
                    };
                    if let Some(c) = self.args_ssa.get_mut(usize::from(argno)) {
                        *c = Some((val, repr));
                    }
                    let idx = 1 + usize::from(argno);
                    if idx < self.args_ctx.len() {
                        self.args_ctx[idx] = o.slot_cell();
                    }
                    self.clear_stale_src(SlotRef::Arg(argno));
                    let mut r = Operand::ranged(val, repr, o.ty, o.range);
                    r.src = Some(SlotRef::Arg(argno));
                    self.stack.push(r);
                }
            }
            GetLocal => {
                let localno = p.next_uint24().unwrap();
                self.push_local(localno);
            }
            SetLocal | InitLexical => {
                let localno = p.next_uint24().unwrap();
                let o = self.pop()?;
                self.write_local(localno, o);
            }

            // --- closures / env ---
            GetAliasedVar | GetAliasedDebugVar => {
                let hops = p.next_uint16().unwrap();
                let slot = p.next_uint24().unwrap();
                self.emit_get_aliased(pc, hops, slot);
            }
            SetAliasedVar | InitAliasedLexical => {
                let hops = p.next_uint16().unwrap();
                let slot = p.next_uint24().unwrap();
                self.emit_set_aliased(pc, hops, slot)?;
            }
            Lambda => {
                let func_index = p.next_uint32().unwrap();
                self.emit_lambda(pc, func_index);
            }
            PushLexicalEnv => {
                self.skip_operands(p, op);
                let h = self.helpers.push_lexical_env;
                self.emit_env_replace(h, |s, env| {
                    let script = s.cur_script_value();
                    let pc_v = s.i32_const(pc.get());
                    vec![env, script, pc_v]
                });
            }
            PushClassBodyEnv => {
                self.skip_operands(p, op);
                let h = self.helpers.push_class_body_env;
                self.emit_env_replace(h, |s, env| {
                    let script = s.cur_script_value();
                    let pc_v = s.i32_const(pc.get());
                    vec![env, script, pc_v]
                });
            }
            FreshenLexicalEnv => {
                self.skip_operands(p, op);
                let h = self.helpers.freshen_lexical_env;
                self.emit_env_replace(h, |_, env| vec![env]);
            }
            RecreateLexicalEnv => {
                self.skip_operands(p, op);
                let h = self.helpers.recreate_lexical_env;
                self.emit_env_replace(h, |_, env| vec![env]);
            }
            PopLexicalEnv | LeaveWith => {
                self.skip_operands(p, op);
                let env = self.load_i64(self.vp, self.env_slot_off);
                let envptr = self.unop(Operator::I32WrapI64, env, Type::I32);
                let enclosing = self.load_i64(envptr, FIXED_SLOTS_BASE);
                self.store_i64(self.vp, self.env_slot_off, enclosing);
            }
            PushVarEnv => {
                self.skip_operands(p, op);
                let h = self.helpers.push_var_env;
                self.emit_env_replace(h, |s, env| {
                    let script = s.cur_script_value();
                    let pc_v = s.i32_const(pc.get());
                    vec![env, script, pc_v]
                });
            }
            EnterWith => {
                self.skip_operands(p, op);
                let val = self.pop()?;
                let val_boxed = self.to_boxed(&val);
                let h = self.helpers.enter_with;
                self.emit_env_replace(h, |s, env| {
                    let script = s.cur_script_value();
                    let pc_v = s.i32_const(pc.get());
                    vec![env, val_boxed, script, pc_v]
                });
            }
            ImplicitThis => {
                self.skip_operands(p, op);
                let env = self.pop()?;
                let eb = self.to_boxed(&env);
                let h = self.helpers.implicit_this;
                let r = self.rt_unary_boxed(h, eb);
                self.push_boxed(r, self.def_type(pc, 0));
            }
            ObjWithProto => {
                self.skip_operands(p, op);
                let proto = self.pop()?;
                let pb = self.to_boxed(&proto);
                let h = self.helpers.obj_with_proto;
                let r = self.rt_unary_boxed(h, pb);
                self.push_boxed(r, self.def_type(pc, 0));
            }
            FunWithProto => {
                let func_index = p.next_uint32().unwrap();
                let proto = self.pop()?;
                let pb = self.to_boxed(&proto);
                let env = self.load_i64(self.vp, self.env_slot_off);
                let script = self.cur_script_value();
                let fi = self.i32_const(func_index);
                let h = self.helpers.fun_with_proto;
                let r = self
                    .rt_call(h, true, |_, _| vec![env, pb, script, fi])
                    .unwrap();
                self.push_boxed(r, self.def_type(pc, 0));
            }
            SetFunName => {
                let prefix = p.next_uint8().unwrap();
                let name = self.pop()?;
                let nb = self.to_boxed(&name);
                let fun = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or("SetFunName on empty stack")?;
                let fb = self.to_boxed(&fun);
                let pk = self.i32_const(u32::from(prefix));
                let h = self.helpers.set_fun_name;
                self.rt_call(h, false, |_, _| vec![fb, nb, pk]);
            }

            // --- names over the env chain ---
            InitGLexical => {
                self.skip_operands(p, op);
                let val = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or("InitGLexical on empty stack")?;
                let val_boxed = self.to_boxed(&val);
                let script = self.cur_script_value();
                let pc_v = self.i32_const(pc.get());
                let h = self.helpers.init_glexical;
                self.rt_call(h, false, |_, _| vec![val_boxed, script, pc_v]);
            }
            GetName => {
                let name_index = p.next_uint32().unwrap();
                let for_typeof = matches!(self.op_at(pc + op.len()), Some(Typeof | TypeofEq));
                let atom_id = self.resolve_atom(name_index)?;
                let env = self.load_i64(self.vp, self.env_slot_off);
                let atom_v = self.i32_const(atom_id);
                let tof_v = self.i32_const(u32::from(for_typeof));
                let h = self.helpers.get_name;
                let r = self
                    .rt_call(h, true, |_, _| vec![env, atom_v, tof_v])
                    .unwrap();
                self.push_boxed(r, self.def_type(pc, 0));
            }
            BindName => {
                let name_index = p.next_uint32().unwrap();
                let atom_id = self.resolve_atom(name_index)?;
                let env = self.load_i64(self.vp, self.env_slot_off);
                let atom_v = self.i32_const(atom_id);
                let h = self.helpers.bind_name;
                let r = self.rt_call(h, true, |_, _| vec![env, atom_v]).unwrap();
                self.push_boxed(r, self.def_type(pc, 0));
            }
            BindUnqualifiedName => {
                let name_index = p.next_uint32().unwrap();
                let atom_id = self.resolve_atom(name_index)?;
                let env = self.load_i64(self.vp, self.env_slot_off);
                let atom_v = self.i32_const(atom_id);
                let h = self.helpers.bind_unqualified_name;
                let r = self.rt_call(h, true, |_, _| vec![env, atom_v]).unwrap();
                self.push_boxed(r, self.def_type(pc, 0));
            }
            GetBoundName => {
                let name_index = p.next_uint32().unwrap();
                let atom_id = self.resolve_atom(name_index)?;
                let env = self.pop()?;
                let env_boxed = self.to_boxed(&env);
                let atom_v = self.i32_const(atom_id);
                let h = self.helpers.get_bound_name;
                let r = self
                    .rt_call(h, true, |_, _| vec![env_boxed, atom_v])
                    .unwrap();
                self.push_boxed(r, self.def_type(pc, 0));
            }
            BindVar => {
                self.skip_operands(p, op);
                let env = self.load_i64(self.vp, self.env_slot_off);
                let h = self.helpers.bind_var;
                let r = self.rt_unary_boxed(h, env);
                self.push_boxed(r, self.def_type(pc, 0));
            }
            DelName => {
                let name_index = p.next_uint32().unwrap();
                let atom_id = self.resolve_atom(name_index)?;
                let env = self.load_i64(self.vp, self.env_slot_off);
                let atom_v = self.i32_const(atom_id);
                let h = self.helpers.del_name;
                let r = self.rt_call(h, true, |_, _| vec![env, atom_v]).unwrap();
                self.push_boxed(r, self.def_type(pc, 0));
            }
            GlobalOrEvalDeclInstantiation => {
                let last_fun = p.next_uint32().unwrap();
                let idx_v = self.i32_const(last_fun);
                let script = self.cur_script_value();
                let gdi = self.helpers.global_decl_instantiation;
                self.rt_call(gdi, false, |_, _| vec![script, idx_v]);
            }

            // --- stack manipulation ---
            Pop => {
                self.skip_operands(p, op);
                self.pop()?;
            }
            Dup => {
                self.skip_operands(p, op);
                let o = self.stack.last().cloned().ok_or("Dup on empty stack")?;
                self.stack.push(o);
            }
            Dup2 => {
                self.skip_operands(p, op);
                let l = self.stack.len();
                if l < 2 {
                    return Err("Dup2 on short stack".into());
                }
                let a = self.stack[l - 2].clone();
                let b = self.stack[l - 1].clone();
                self.stack.push(a);
                self.stack.push(b);
            }
            PopN => {
                let n = p.next_uint16().unwrap();
                for _ in 0..n {
                    self.pop()?;
                }
            }
            Pick => {
                let i = usize::from(p.next_uint8().unwrap());
                let l = self.stack.len();
                if l < i + 1 {
                    return Err(format!("Pick {i} on {l} operands"));
                }
                let o = self.stack.remove(l - 1 - i);
                self.stack.push(o);
            }
            DupAt => {
                let depth = p.next_uint24().unwrap() as usize;
                let len = self.stack.len();
                if depth >= len {
                    return Err(format!("DupAt {depth} on stack of {len}"));
                }
                let o = self.stack[len - 1 - depth].clone();
                self.stack.push(o);
            }
            Swap => {
                self.skip_operands(p, op);
                let n = self.stack.len();
                if n < 2 {
                    return Err("Swap on <2 operands".into());
                }
                self.stack.swap(n - 1, n - 2);
            }
            Unpick => {
                let i = usize::from(p.next_uint8().unwrap());
                let n = self.stack.len();
                if n < i + 1 {
                    return Err(format!("Unpick {i} on {n} operands"));
                }
                let top = self.stack.remove(n - 1);
                self.stack.insert(n - 1 - i, top);
            }

            // --- arithmetic (ctx-consulting operator arms) ---
            Add => {
                self.skip_operands(p, op);
                self.emit_addsub_op(true, pc + op.len())?;
            }
            Sub => {
                self.skip_operands(p, op);
                self.emit_addsub_op(false, pc + op.len())?;
            }
            Mul | Div => {
                self.skip_operands(p, op);
                let kind = if matches!(op, Mul) {
                    BINOP_MUL
                } else {
                    BINOP_DIV
                };
                self.emit_muldiv_op(kind, pc + op.len())?;
            }
            Mod => {
                self.skip_operands(p, op);
                self.emit_mod_op(pc + op.len())?;
            }
            BitAnd | BitOr | BitXor | Lsh | Rsh => {
                self.skip_operands(p, op);
                let (wasm_op, kind) = match op {
                    BitAnd => (Operator::I32And, BINOP_BITAND),
                    BitOr => (Operator::I32Or, BINOP_BITOR),
                    BitXor => (Operator::I32Xor, BINOP_BITXOR),
                    Lsh => (Operator::I32Shl, BINOP_LSH),
                    _ => (Operator::I32ShrS, BINOP_RSH),
                };
                self.emit_bitop(wasm_op, kind, pc + op.len())?;
            }
            Ursh => {
                self.skip_operands(p, op);
                self.emit_ursh_op(pc + op.len())?;
            }
            Inc | Dec => {
                self.skip_operands(p, op);
                self.emit_incdec_op(matches!(op, Inc), pc + op.len())?;
            }
            BitNot => {
                self.skip_operands(p, op);
                self.emit_bitnot_op(pc + op.len())?;
            }
            Pow => {
                self.skip_operands(p, op);
                let b = self.pop()?;
                let a = self.pop()?;
                let ab = self.to_boxed(&a);
                let bb = self.to_boxed(&b);
                let pw = self.helpers.pow;
                let r = self.rt_call(pw, true, |_, _| vec![ab, bb]).unwrap();
                self.push_boxed(r, self.def_type(pc, 0));
            }
            Neg => {
                self.skip_operands(p, op);
                self.emit_neg_op(pc + op.len())?;
            }
            ToNumeric => {
                self.skip_operands(p, op);
                self.emit_tonumeric_op(true, pc + op.len())?;
            }
            Pos => {
                self.skip_operands(p, op);
                self.emit_tonumeric_op(false, pc + op.len())?;
            }

            // --- compares (ctx-consulting forms of emit_compare) ---
            Lt | Gt | Le | Ge | Eq | Ne | StrictEq | StrictNe => {
                self.skip_operands(p, op);
                let kind = match op {
                    Lt => CMP_LT,
                    Gt => CMP_GT,
                    Le => CMP_LE,
                    Ge => CMP_GE,
                    Eq => CMP_EQ,
                    Ne => CMP_NE,
                    StrictEq => CMP_STRICTEQ,
                    _ => CMP_STRICTNE,
                };
                let succ_pc = pc + op.len();
                self.emit_compare_op(kind, succ_pc)?;
            }
            Not => {
                self.skip_operands(p, op);
                let o = self.pop()?;
                let c = self.to_bool_i32(&o)?;
                let zero = self.i32_const(0);
                let r = self.binop(Operator::I32Eq, c, zero, Type::I32);
                self.push_known(r, Repr::Bool, prim_desc(PRIM_BOOLEAN));
            }

            // --- typeof / strict-constant compare ---
            Typeof | TypeofExpr => {
                self.skip_operands(p, op);
                let o = self.pop()?;
                let boxed = self.to_boxed(&o);
                let tf = self.helpers.typeof_;
                let result = self.call_i64(tf, &[self.cx, boxed]);
                let ty = self.result_ty_fact(pc, PRIM_STRING);
                self.push_known(result, Repr::Boxed, ty);
            }
            TypeofEq => {
                let operand = p.next_uint8().unwrap();
                let o = self.pop()?;
                let boxed = self.to_boxed(&o);
                let operand_v = self.i32_const(u32::from(operand));
                let tfe = self.helpers.typeof_eq;
                let r = self.call_i32(tfe, &[self.cx, boxed, operand_v]);
                self.push_known(r, Repr::Bool, prim_desc(PRIM_BOOLEAN));
            }
            StrictConstantEq | StrictConstantNe => {
                let operand = p.next_uint16().unwrap();
                let o = self.pop()?;
                let boxed = self.to_boxed(&o);
                let ty_byte = (operand >> 8) & 0xFF;
                let lo_byte = (operand & 0xFF) as u8;
                let eq = {
                    let hi = {
                        let shift = self.boxed_const(32);
                        let hi64 = self.binop(Operator::I64ShrU, boxed, shift, Type::I64);
                        self.unop(Operator::I32WrapI64, hi64, Type::I32)
                    };
                    match ty_byte {
                        0x03 => {
                            let tag = self.i32_const(TAG_UNDEFINED as u32);
                            self.binop(Operator::I32Eq, hi, tag, Type::I32)
                        }
                        0x04 => {
                            let tag = self.i32_const(TAG_NULL as u32);
                            self.binop(Operator::I32Eq, hi, tag, Type::I32)
                        }
                        0x02 => {
                            let b = u64::from(lo_byte & 1);
                            let want = (TAG_BOOLEAN << 32) | b;
                            let want_v = self.boxed_const(want);
                            self.binop(Operator::I64Eq, boxed, want_v, Type::I32)
                        }
                        _ => {
                            let v = i32::from(lo_byte as i8);
                            let int32_tag = self.i32_const(TAG_INT32 as u32);
                            let is_int32 = self.binop(Operator::I32Eq, hi, int32_tag, Type::I32);
                            let low = self.unop(Operator::I32WrapI64, boxed, Type::I32);
                            let v_v = self.i32_const(v as u32);
                            let low_eq = self.binop(Operator::I32Eq, low, v_v, Type::I32);
                            let int_match =
                                self.binop(Operator::I32And, is_int32, low_eq, Type::I32);
                            let is_double = self.binop(Operator::I32LtU, hi, int32_tag, Type::I32);
                            let f = self.unop(Operator::F64ReinterpretI64, boxed, Type::F64);
                            let dv = self.f64_const(f64::from(v));
                            let dbl_eq = self.binop(Operator::F64Eq, f, dv, Type::I32);
                            let dbl_match =
                                self.binop(Operator::I32And, is_double, dbl_eq, Type::I32);
                            self.binop(Operator::I32Or, int_match, dbl_match, Type::I32)
                        }
                    }
                };
                let r = if matches!(op, StrictConstantNe) {
                    let zero = self.i32_const(0);
                    self.binop(Operator::I32Eq, eq, zero, Type::I32)
                } else {
                    eq
                };
                self.push_known(r, Repr::Bool, prim_desc(PRIM_BOOLEAN));
            }

            // --- control flow (edges through the continuation seam) ---
            Goto => {
                let off = p.next_int32().unwrap();
                let target = self.edge_to(branch_target(pc, off));
                self.body
                    .set_terminator(self.cur, Terminator::Br { target });
            }
            JumpIfFalse => {
                let off = p.next_int32().unwrap();
                let cond = self.pop()?;
                let cond_i32 = self.to_bool_i32(&cond)?;
                let if_false = self.edge_to(branch_target(pc, off));
                let if_true = self.edge_to(pc + op.len());
                self.body.set_terminator(
                    self.cur,
                    Terminator::CondBr {
                        cond: cond_i32,
                        if_true,
                        if_false,
                    },
                );
            }
            JumpIfTrue => {
                let off = p.next_int32().unwrap();
                let cond = self.pop()?;
                let cond_i32 = self.to_bool_i32(&cond)?;
                let if_true = self.edge_to(branch_target(pc, off));
                // A for-in exit test: `MoreIter` left a property key or the
                // no-iter magic on the stack, and the taken branch just
                // left with the magic, so the fall-through holds a string
                // (for-in keys are strings: symbols are skipped, indexes
                // stringified).
                let refine = self.noiter_jump(pc) && !self.stack.is_empty();
                let saved = refine.then(|| {
                    let o = self.stack.last_mut().unwrap();
                    std::mem::replace(&mut o.ty, prim_desc(PRIM_STRING))
                });
                let if_false = self.edge_to(pc + op.len());
                if let Some(ty) = saved {
                    self.stack.last_mut().unwrap().ty = ty;
                }
                self.body.set_terminator(
                    self.cur,
                    Terminator::CondBr {
                        cond: cond_i32,
                        if_true,
                        if_false,
                    },
                );
            }
            Case => {
                let off = p.next_int32().unwrap();
                let cond = self.pop()?;
                let cond_i32 = self.to_bool_i32(&cond)?;
                let disc = self.pop()?;
                let if_true = self.edge_to(branch_target(pc, off));
                self.stack.push(disc);
                let if_false = self.edge_to(pc + op.len());
                self.body.set_terminator(
                    self.cur,
                    Terminator::CondBr {
                        cond: cond_i32,
                        if_true,
                        if_false,
                    },
                );
            }
            Default => {
                let off = p.next_int32().unwrap();
                self.pop()?;
                let target = self.edge_to(branch_target(pc, off));
                self.body
                    .set_terminator(self.cur, Terminator::Br { target });
            }
            And => {
                let off = p.next_int32().unwrap();
                let top = self.stack.last().cloned().ok_or("And on empty stack")?;
                let cond_i32 = self.to_bool_i32(&top)?;
                let if_false = self.edge_to(branch_target(pc, off));
                let if_true = self.edge_to(pc + op.len());
                self.body.set_terminator(
                    self.cur,
                    Terminator::CondBr {
                        cond: cond_i32,
                        if_true,
                        if_false,
                    },
                );
            }
            Or => {
                let off = p.next_int32().unwrap();
                let top = self.stack.last().cloned().ok_or("Or on empty stack")?;
                let cond_i32 = self.to_bool_i32(&top)?;
                let if_true = self.edge_to(branch_target(pc, off));
                let if_false = self.edge_to(pc + op.len());
                self.body.set_terminator(
                    self.cur,
                    Terminator::CondBr {
                        cond: cond_i32,
                        if_true,
                        if_false,
                    },
                );
            }
            Coalesce => {
                let off = p.next_int32().unwrap();
                let top = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or("Coalesce on empty stack")?;
                let vb = self.to_boxed(&top);
                let is_u = self.tag_eq(vb, TAG_UNDEFINED as u32);
                let is_n = self.tag_eq(vb, TAG_NULL as u32);
                let nullish = self.binop(Operator::I32Or, is_u, is_n, Type::I32);
                let zero = self.i32_const(0);
                let cond = self.binop(Operator::I32Eq, nullish, zero, Type::I32);
                let if_true = self.edge_to(branch_target(pc, off));
                let if_false = self.edge_to(pc + op.len());
                self.body.set_terminator(
                    self.cur,
                    Terminator::CondBr {
                        cond,
                        if_true,
                        if_false,
                    },
                );
            }
            TableSwitch => {
                let default_off = p.next_int32().unwrap();
                let low = p.next_int32().unwrap();
                let high = p.next_int32().unwrap();
                let first_resume = p.next_uint24().unwrap();
                self.emit_table_switch(pc, default_off, low, high, first_resume)?;
            }

            // --- returns ---
            Return => {
                self.skip_operands(p, op);
                let o = self.pop()?;
                self.emit_return_value(o);
            }
            SetRval => {
                self.skip_operands(p, op);
                let o = self.pop()?;
                let boxed = self.to_boxed(&o);
                self.store_i64(self.vp, self.rval_slot_off, boxed);
            }
            GetRval => {
                self.skip_operands(p, op);
                let v = self.load_i64(self.vp, self.rval_slot_off);
                self.push_boxed(v, prim_desc(Prims::EMPTY));
            }
            RetRval => {
                self.skip_operands(p, op);
                self.emit_ret_rval();
            }

            // --- calls / constructs ---
            Call | CallContent | CallIgnoresRv | CallIter | CallContentIter => {
                self.emit_call_op(p, pc, false, false)?;
            }
            New | NewContent | SuperCall => {
                self.emit_call_op(p, pc, true, op == SuperCall)?;
            }
            SpreadCall => {
                self.skip_operands(p, op);
                self.emit_spread_call(pc, false)?;
            }
            SpreadNew | SpreadSuperCall => {
                self.skip_operands(p, op);
                self.emit_spread_call(pc, true)?;
            }
            OptimizeSpreadCall => {
                self.skip_operands(p, op);
                let v = self.pop()?;
                let vb = self.to_boxed(&v);
                let osc = self.helpers.optimize_spread_call;
                let result = self.rt_call(osc, true, move |_, _| vec![vb]).unwrap();
                self.push_boxed(result, self.def_type(pc, 0));
            }

            // --- property access (generic helpers) ---
            GetProp => {
                let name_index = p.next_uint32().unwrap();
                let name = self.name_for(name_index)?;
                self.emit_get_property(pc, name)?;
                self.attach_likely_cls(pc);
            }
            SetProp | StrictSetProp => {
                // Property set IC; the value stays on the stack (def == use).
                let name_index = p.next_uint32().unwrap();
                let name = self.name_for(name_index)?;
                let atom_id = self.resolve_atom(name_index)?;
                if !self.outline_generic()
                    && (matches!(
                        self.ctx
                            .facts
                            .accessor_sites
                            .get(&Site::new(self.source_id, Pc::new(self.evid_pc(pc).get()))),
                        Some(&(_, 1))
                    ) || self.ctx.facts.accessor_names.contains(&name))
                {
                    return self.emit_accessor_prop(pc, atom_id, true);
                }
                let val = self.pop()?;
                let recv = self.pop()?;
                let val_boxed = self.to_boxed(&val);
                let recv_boxed = self.to_boxed(&recv);
                let elide_barrier = is_non_gc(&val.ty);
                // Choke elision: a statically numeric value violates no
                // claim; so does any store to a field the fact-proven
                // receiver layout leaves unmasked (the flags claim covers
                // masked fields only, so keeping them is sound even where
                // the engine path would clear conservatively).
                let site_unmasked = self
                    .ctx
                    .prop_sites_in
                    .get(&Site::new(self.source_id, self.evid_pc(pc)))
                    .is_some_and(|ps| {
                        ps.claim == Claim::NONE
                            && recv.cls.is_some_and(|(lo, hi)| {
                                u32::from(lo) > ps.layout_id && u32::from(hi) <= ps.hi_layout_id + 1
                            })
                    });
                // Layout-wide choke elision: the per-site row above only
                // exists where the analysis predicted a receiver for this
                // pc, which most store sites lack.
                // A proven class fact plus the layout's own field masks
                // answers the same question without a row: if the stored
                // name carries no number claim under every layout the fact
                // admits, the store violates no claim and the choke -- and
                // the shallow-fact kill it forces -- are both unnecessary.
                // Absent from the layout counts as unmasked: the claim
                // covers masked fields only, so adding a property leaves it
                // intact (same argument as `site_unmasked`).
                // An unknown layout counts as masked: only a layout we hold
                // the masks for can prove the field carries no claim.
                let layout_unmasked = recv.cls.is_some_and(|(lo, hi)| {
                    (u32::from(lo)..=u32::from(hi)).all(|k| {
                        self.ctx
                            .layout_field_masks_in
                            .get(&StampKey::new(k))
                            .is_some_and(|f| f.get(&name).is_none_or(|&m| m == Claim::NONE))
                    })
                });
                let val_is_num = store_value_numeric(&val) || site_unmasked || layout_unmasked;
                let next_pc = pc + op.len();
                // The site's predicted layout answers the store form, not
                // just the choke question: one class-idx guard (none at all
                // under a live fact) buys the raw fixed-slot write.
                if !self.outline_generic() {
                    let site = self
                        .ctx
                        .prop_sites_in
                        .get(&Site::new(self.source_id, self.evid_pc(pc)))
                        .cloned()
                        .or_else(|| self.layout_site_for(&recv, name));
                    if let Some(ps) = site {
                        let init_claim = self.ctor_init_claim(&recv, name);
                        let range_act = self.store_range_act(&recv, name, &val);
                        self.emit_class_fact_set(
                            &ps,
                            atom_id,
                            &recv,
                            &val,
                            recv_boxed,
                            val_boxed,
                            elide_barrier,
                            val_is_num,
                            next_pc,
                            init_claim,
                            range_act,
                        );
                        return Ok(());
                    }
                }
                let init_claim = self.ctor_init_claim(&recv, name);
                let range_act = self.store_range_act(&recv, name, &val);
                self.push_ranged(val_boxed, Repr::Boxed, val.ty, val.range);
                self.emit_set_prop_ic_inline(
                    &recv,
                    recv_boxed,
                    val_boxed,
                    elide_barrier,
                    val_is_num,
                    atom_id,
                    Some(next_pc.get()),
                    true,
                    init_claim,
                    range_act,
                );
            }
            GetElem => {
                self.skip_operands(p, op);
                self.emit_get_element(pc)?;
                self.attach_likely_cls(pc);
            }
            SetElem | StrictSetElem => {
                self.skip_operands(p, op);
                let strict = matches!(op, StrictSetElem);
                self.emit_set_element(pc, strict)?;
            }
            GetGName => {
                let name_index = p.next_uint32().unwrap();
                // The typeof-name kludge: a `GetGName` immediately followed
                // by `Typeof`/`TypeofEq` uses the non-throwing lookup.
                let for_typeof = matches!(self.op_at(pc + op.len()), Some(Typeof | TypeofEq));
                self.emit_get_gname(pc, name_index, for_typeof)?;
            }
            BindUnqualifiedGName => {
                // Push the binding object for a global-name assignment;
                // when the name resolves (guarded) to a cacheable own
                // global-object data slot, the binding object IS the global
                // object -- pushed inline, no helper call.
                let name_index = p.next_uint32().unwrap();
                let inline_bid = if !self.is_global && !self.outline_generic() {
                    self.name_for(name_index)
                        .ok()
                        .and_then(|n| self.ctx.syn_gnames.get(&n).copied().map(|b| (b, n)))
                } else {
                    None
                };
                if let Some((bid, name)) = inline_bid {
                    let atom_id = self.atoms.intern(name);
                    let next_pc = pc + op.len();
                    self.emit_bind_gname_inline(pc, bid, atom_id, Some(next_pc.get()));
                } else {
                    let atom_id = self.resolve_atom(name_index)?;
                    let atom_v = self.i32_const(atom_id);
                    let bug = self.helpers.bind_unqualified_gname;
                    // Epoch-kept: an implicitly created global's binding
                    // object (earley-boyer's `count++` counters) is a
                    // lookup, not a write.
                    let ty = self.def_type(pc, 0);
                    let result = self.rt_call_keep(bug, 0, Some(pc + op.len()), &ty, vec![atom_v]);
                    self.push_boxed(result, ty);
                }
            }
            SetGName | StrictSetGName | SetName | StrictSetName => {
                // `[env, value] -> [value]`. SetName/StrictSetName are the
                // unqualified forms (dynamic scope): the bound env may
                // shadow the global, so they force the generic helper.
                let name_index = p.next_uint32().unwrap();
                let unqualified = matches!(op, SetName | StrictSetName);
                let next_pc = pc + op.len();
                self.emit_set_name(
                    name_index,
                    matches!(op, StrictSetGName | StrictSetName),
                    unqualified,
                    Some(next_pc.get()),
                )?;
            }
            DelProp | StrictDelProp => {
                let name_index = p.next_uint32().unwrap();
                let name = self.name_for(name_index)?;
                let atom_id = self.atoms.intern(name);
                let val = self.pop()?;
                let val_boxed = self.to_boxed(&val);
                let atom_v = self.i32_const(atom_id);
                let strict_v = self.i32_const(matches!(op, StrictDelProp) as u32);
                let delp = self.helpers.del_prop;
                let result = self
                    .rt_call(delp, true, |_, _| vec![val_boxed, atom_v, strict_v])
                    .unwrap();
                let ty = self.result_ty_fact(pc, PRIM_BOOLEAN);
                self.push_known(result, Repr::Boxed, ty);
            }
            DelElem | StrictDelElem => {
                self.skip_operands(p, op);
                let key = self.pop()?;
                let val = self.pop()?;
                let key_b = self.to_boxed(&key);
                let val_b = self.to_boxed(&val);
                let strict_v = self.i32_const(matches!(op, StrictDelElem) as u32);
                let h = self.helpers.del_elem;
                let result = self
                    .rt_call(h, true, |_, _| vec![val_b, key_b, strict_v])
                    .unwrap();
                let ty = self.result_ty_fact(pc, PRIM_BOOLEAN);
                self.push_known(result, Repr::Boxed, ty);
            }
            In => {
                self.skip_operands(p, op);
                let obj = self.pop()?;
                let id = self.pop()?;
                let obj_b = self.to_boxed(&obj);
                let id_b = self.to_boxed(&id);
                let h = self.helpers.in_;
                let ty = self.result_ty_fact(pc, PRIM_BOOLEAN);
                let result = self.rt_call_keep(h, 0, Some(pc + op.len()), &ty, vec![id_b, obj_b]);
                self.push_known(result, Repr::Boxed, ty);
            }
            HasOwn => {
                self.skip_operands(p, op);
                if self.stack.len() < 2 {
                    return Err("HasOwn on short stack".to_string());
                }
                let val = self.stack[self.stack.len() - 1].clone();
                let id = self.stack[self.stack.len() - 2].clone();
                let val_b = self.to_boxed(&val);
                let id_b = self.to_boxed(&id);
                let h = self.helpers.has_own;
                let ty = self.result_ty_fact(pc, PRIM_BOOLEAN);
                let result = self.rt_call_keep(h, 2, Some(pc + op.len()), &ty, vec![id_b, val_b]);
                self.push_known(result, Repr::Boxed, ty);
            }
            Instanceof => {
                self.skip_operands(p, op);
                self.emit_instanceof(pc)?;
            }

            // --- super property access ---
            SuperBase => {
                self.skip_operands(p, op);
                let callee = self.pop()?;
                let callee_boxed = self.to_boxed(&callee);
                let h = self.helpers.super_base;
                let r = self.rt_unary_boxed(h, callee_boxed);
                self.push_boxed(r, self.def_type(pc, 0));
            }
            SuperFun => {
                self.skip_operands(p, op);
                let callee = self.pop()?;
                let callee_boxed = self.to_boxed(&callee);
                let h = self.helpers.super_fun;
                let r = self.rt_unary_boxed(h, callee_boxed);
                self.push_boxed(r, self.def_type(pc, 0));
            }
            GetPropSuper => {
                let name_index = p.next_uint32().unwrap();
                let name = self.name_for(name_index)?;
                let atom_id = self.atoms.intern(name);
                let super_base = self.pop()?;
                let receiver = self.pop()?;
                let sb_boxed = self.to_boxed(&super_base);
                let recv_boxed = self.to_boxed(&receiver);
                let atom_v = self.i32_const(atom_id);
                let h = self.helpers.get_prop_super;
                let r = self
                    .rt_call(h, true, |_, _| vec![recv_boxed, sb_boxed, atom_v])
                    .unwrap();
                self.push_boxed(r, self.def_type(pc, 0));
            }
            GetElemSuper => {
                self.skip_operands(p, op);
                let super_base = self.pop()?;
                let key = self.pop()?;
                let receiver = self.pop()?;
                let sb_boxed = self.to_boxed(&super_base);
                let key_boxed = self.to_boxed(&key);
                let recv_boxed = self.to_boxed(&receiver);
                let h = self.helpers.get_elem_super;
                let r = self
                    .rt_call(h, true, |_, _| vec![recv_boxed, key_boxed, sb_boxed])
                    .unwrap();
                self.push_boxed(r, self.def_type(pc, 0));
            }
            SetPropSuper | StrictSetPropSuper => {
                let name_index = p.next_uint32().unwrap();
                let name = self.name_for(name_index)?;
                let atom_id = self.atoms.intern(name);
                let strict = matches!(op, StrictSetPropSuper);
                let value = self.pop()?;
                let super_base = self.pop()?;
                let receiver = self.pop()?;
                let val_boxed = self.to_boxed(&value);
                let sb_boxed = self.to_boxed(&super_base);
                let recv_boxed = self.to_boxed(&receiver);
                let atom_v = self.i32_const(atom_id);
                let strict_v = self.i32_const(u32::from(strict));
                let h = self.helpers.set_prop_super;
                let r = self
                    .rt_call(h, true, |_, _| {
                        vec![recv_boxed, sb_boxed, atom_v, val_boxed, strict_v]
                    })
                    .unwrap();
                self.push_boxed(r, self.def_type(pc, 0));
            }
            SetElemSuper | StrictSetElemSuper => {
                self.skip_operands(p, op);
                let strict = matches!(op, StrictSetElemSuper);
                let value = self.pop()?;
                let super_base = self.pop()?;
                let key = self.pop()?;
                let receiver = self.pop()?;
                let val_boxed = self.to_boxed(&value);
                let sb_boxed = self.to_boxed(&super_base);
                let key_boxed = self.to_boxed(&key);
                let recv_boxed = self.to_boxed(&receiver);
                let strict_v = self.i32_const(u32::from(strict));
                let h = self.helpers.set_elem_super;
                let r = self
                    .rt_call(h, true, |_, _| {
                        vec![recv_boxed, key_boxed, sb_boxed, val_boxed, strict_v]
                    })
                    .unwrap();
                self.push_boxed(r, self.def_type(pc, 0));
            }

            // --- object / array literals (generic helper arms) ---
            NewInit | NewObject => {
                self.skip_operands(p, op);
                self.emit_alloc_inline(None);
            }
            NewArray => {
                let length = p.next_uint32().unwrap();
                self.emit_alloc_inline(Some(length));
            }
            InitProp | InitHiddenProp | InitLockedProp => {
                let name_index = p.next_uint32().unwrap();
                let attrs = match op {
                    InitProp => INIT_ATTR_ENUMERATE,
                    InitHiddenProp => INIT_ATTR_HIDDEN,
                    _ => INIT_ATTR_LOCKED,
                };
                let atom_id = self.resolve_atom(name_index)?;
                self.emit_init_prop(atom_id, attrs)?;
            }
            InitElem | InitHiddenElem | InitLockedElem => {
                self.skip_operands(p, op);
                let attrs = match op {
                    InitElem => INIT_ATTR_ENUMERATE,
                    InitHiddenElem => INIT_ATTR_HIDDEN,
                    _ => INIT_ATTR_LOCKED,
                };
                let val = self.pop()?;
                let key = self.pop()?;
                let val_boxed = self.to_boxed(&val);
                let key_boxed = self.to_boxed(&key);
                self.emit_init_elem_call(key_boxed, val_boxed, attrs)?;
            }
            InitElemArray => {
                let index = p.next_uint32().unwrap();
                self.emit_init_elem_array(index)?;
            }
            InitElemInc => {
                self.skip_operands(p, op);
                let val = self.pop()?;
                let index = self.pop()?;
                let val_boxed = self.to_boxed(&val);
                let index_boxed = self.to_boxed(&index);
                self.emit_init_elem_call(index_boxed, val_boxed, INIT_ATTR_ENUMERATE)?;
                let idx_i32 = self.to_i32(&index);
                let one = self.i32_const(1);
                let next = self.binop(Operator::I32Add, idx_i32, one, Type::I32);
                self.push(next, Repr::I32, prim_desc(PRIM_INT32));
            }
            MutateProto => {
                self.skip_operands(p, op);
                let proto = self.pop()?;
                let obj = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or("MutateProto on empty stack")?;
                let proto_boxed = self.to_boxed(&proto);
                let obj_boxed = self.to_boxed(&obj);
                let mp = self.helpers.mutate_proto;
                self.rt_call(mp, false, |_, _| vec![obj_boxed, proto_boxed]);
            }
            InitHomeObject => {
                self.skip_operands(p, op);
                let home = self.pop()?;
                let f = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or("InitHomeObject on empty stack")?;
                let home_boxed = self.to_boxed(&home);
                let fn_boxed = self.to_boxed(&f);
                let h = self.helpers.init_home_object;
                self.rt_call(h, false, |_, _| vec![fn_boxed, home_boxed]);
            }
            InitPropGetter | InitHiddenPropGetter | InitPropSetter | InitHiddenPropSetter => {
                let name_index = p.next_uint32().unwrap();
                let name = self.name_for(name_index)?;
                let atom_id = self.atoms.intern(name);
                let fnv = self.pop()?;
                let obj = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or("InitPropGetter on empty stack")?;
                let fn_b = self.to_boxed(&fnv);
                let obj_b = self.to_boxed(&obj);
                let atom_v = self.i32_const(atom_id);
                let kind = matches!(op, InitPropSetter | InitHiddenPropSetter) as u32
                    | ((matches!(op, InitHiddenPropGetter | InitHiddenPropSetter) as u32) << 1);
                let kind_v = self.i32_const(kind);
                let h = self.helpers.init_prop_getset;
                self.rt_call(h, false, |_, _| vec![obj_b, atom_v, fn_b, kind_v]);
            }
            InitElemGetter | InitHiddenElemGetter | InitElemSetter | InitHiddenElemSetter => {
                self.skip_operands(p, op);
                let fnv = self.pop()?;
                let keyv = self.pop()?;
                let obj = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or("InitElemGetter on empty stack")?;
                let fn_b = self.to_boxed(&fnv);
                let key_b = self.to_boxed(&keyv);
                let obj_b = self.to_boxed(&obj);
                let kind = matches!(op, InitElemSetter | InitHiddenElemSetter) as u32
                    | ((matches!(op, InitHiddenElemGetter | InitHiddenElemSetter) as u32) << 1);
                let kind_v = self.i32_const(kind);
                let h = self.helpers.init_elem_getset;
                self.rt_call(h, true, |_, _| vec![obj_b, key_b, fn_b, kind_v]);
            }
            NewPrivateName => {
                let name_index = p.next_uint32().unwrap();
                let name = self.name_for(name_index)?;
                let atom_id = self.atoms.intern(name);
                let atom_v = self.i32_const(atom_id);
                let h = self.helpers.new_private_name;
                let r = self.rt_unary_boxed(h, atom_v);
                self.push_boxed(r, prim_desc(Prims::EMPTY));
            }
            CheckPrivateField => {
                let cond = p.next_uint8().unwrap();
                let kind = p.next_uint8().unwrap();
                if self.stack.len() < 2 {
                    return Err("CheckPrivateField: stack underflow".into());
                }
                let key = self.stack[self.stack.len() - 1].clone();
                let obj = self.stack[self.stack.len() - 2].clone();
                let obj_b = self.to_boxed(&obj);
                let key_b = self.to_boxed(&key);
                let cond_v = self.i32_const(u32::from(cond));
                let kind_v = self.i32_const(u32::from(kind));
                let h = self.helpers.check_private_field;
                let r = self
                    .rt_call(h, true, |_, _| vec![obj_b, key_b, cond_v, kind_v])
                    .unwrap();
                self.push_boxed(r, prim_desc(PRIM_BOOLEAN));
            }

            // --- exceptions ---
            Try => {
                self.skip_operands(p, op);
            }
            Exception => {
                self.skip_operands(p, op);
                self.emit_exception(pc);
            }
            ExceptionAndStack => {
                self.skip_operands(p, op);
                self.emit_exception_and_stack();
            }
            Throw => {
                self.skip_operands(p, op);
                self.emit_throw()?;
            }
            ThrowWithStack => {
                self.skip_operands(p, op);
                self.emit_throw_with_stack()?;
            }

            // --- for-in / iterator protocol ---
            Iter => {
                self.skip_operands(p, op);
                let v = self.stack.last().cloned().ok_or("Iter on empty stack")?;
                let vb = self.to_boxed(&v);
                let it = self.helpers.iter_;
                // A for-in over a plain object enumerates without running
                // user code or writing stamps -- the epoch compare proves
                // it per call and keeps the loop's lineage.
                let ity = prim_desc(Prims::EMPTY);
                let res = self.rt_call_keep(it, 1, Some(pc + op.len()), &ity, vec![vb]);
                self.push_boxed(res, prim_desc(Prims::EMPTY));
            }
            MoreIter => {
                self.skip_operands(p, op);
                let iter = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or("MoreIter on empty stack")?;
                let ib = self.to_boxed(&iter);
                let mi = self.helpers.more_iter;
                let result = self.call_i64(mi, &[self.cx, ib]);
                self.push_boxed(result, prim_desc(Prims::EMPTY));
            }
            IsNoIter => {
                self.skip_operands(p, op);
                let v = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or("IsNoIter on empty stack")?;
                let vb = self.to_boxed(&v);
                let magic = self.boxed_const((TAG_MAGIC << 32) | MAGIC_NO_ITER_VALUE);
                let eq = self.binop(Operator::I64Eq, vb, magic, Type::I32);
                self.push_known(eq, Repr::Bool, prim_desc(PRIM_BOOLEAN));
            }
            EndIter => {
                self.skip_operands(p, op);
                let _val = self.pop()?;
                let iter = self.pop()?;
                let ib = self.to_boxed(&iter);
                let ei = self.helpers.end_iter;
                self.call_void(ei, &[self.cx, ib]);
            }
            OptimizeGetIterator => {
                self.skip_operands(p, op);
                let v = self.pop()?;
                let vb = self.to_boxed(&v);
                let ogi = self.helpers.optimize_get_iterator;
                let b = self.call_i32(ogi, &[self.cx, vb]);
                self.push_known(b, Repr::Bool, prim_desc(PRIM_BOOLEAN));
            }
            CloseIter => {
                let kind = p.next_uint8().unwrap();
                let kind_v = self.i32_const(u32::from(kind));
                let iter = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or("CloseIter on empty stack")?;
                let ib = self.to_boxed(&iter);
                let ci = self.helpers.close_iter;
                self.rt_call(ci, false, move |_, _| vec![ib, kind_v]);
                self.pop()?;
            }
            ToAsyncIter => {
                self.skip_operands(p, op);
                let next = self.pop()?;
                let iter = self.pop()?;
                let next_b = self.to_boxed(&next);
                let iter_b = self.to_boxed(&iter);
                let tai = self.helpers.to_async_iter;
                let result = self
                    .rt_call(tai, true, move |_, _| vec![iter_b, next_b])
                    .unwrap();
                self.push_boxed(result, self.def_type(pc, 0));
            }

            // --- generator / async (generator.rs) ---------------------
            Generator => {
                self.skip_operands(p, op);
                self.emit_generator(pc);
            }
            InitialYield | Yield | Await => {
                let k = p.next_uint24().ok_or("yield: missing resume index")?;
                self.emit_yield(pc, op, k)?;
            }
            AfterYield => {
                // Resume landing marker (IC/debugger bookkeeping only): the
                // resume dispatcher already rebuilt the operand stack.
                self.skip_operands(p, op);
            }
            FinalYieldRval => {
                // `[gen] ->`: the generator ran to completion; close it
                // (an async function with no awaits reaches here on its
                // INITIAL call, where the Resume hook's close backstop
                // never runs) and return the rval register.
                self.skip_operands(p, op);
                let gen_op = self.pop()?;
                let gen_b = self.to_boxed(&gen_op);
                let gf = self.helpers.gen_final;
                self.rt_call(gf, false, move |_, _| vec![gen_b]);
                self.emit_ret_rval();
            }
            ResumeKind => {
                let kind = p.next_uint8().ok_or("ResumeKind: missing immediate")?;
                let v = self.i32_const(u32::from(kind));
                self.push_literal(v, Repr::I32, prim_desc(PRIM_INT32));
            }
            IsGenClosing => {
                // `[v] -> [v, bool]`: whether `v` is the JS_GENERATOR_CLOSING
                // magic (a finally observing a forced `.return()`).
                self.skip_operands(p, op);
                let v = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or("IsGenClosing on empty stack")?;
                let vb = self.to_boxed(&v);
                let sentinel = self.boxed_const((TAG_MAGIC << 32) | MAGIC_GENERATOR_CLOSING);
                let eq = self.binop(Operator::I64Eq, vb, sentinel, Type::I32);
                self.push_literal(eq, Repr::Bool, prim_desc(PRIM_BOOLEAN));
            }
            CheckResumeKind => {
                self.skip_operands(p, op);
                self.emit_check_resume_kind()?;
            }
            AsyncAwait => {
                // `[value, gen] -> [promise]`: register the await
                // continuation on value's promise. May GC/throw.
                self.skip_operands(p, op);
                let gen_op = self.pop()?;
                let val_op = self.pop()?;
                let gen_b = self.to_boxed(&gen_op);
                let val_b = self.to_boxed(&val_op);
                let h = self.helpers.async_await;
                let r = self
                    .rt_call(h, true, move |_, _| vec![gen_b, val_b])
                    .unwrap();
                self.push_boxed(r, self.def_type(pc, 0));
            }
            AsyncResolve => {
                // `[value, gen] -> [promise]`: fulfill the result promise.
                self.skip_operands(p, op);
                let gen_op = self.pop()?;
                let val_op = self.pop()?;
                let gen_b = self.to_boxed(&gen_op);
                let val_b = self.to_boxed(&val_op);
                let h = self.helpers.async_resolve;
                let r = self
                    .rt_call(h, true, move |_, _| vec![gen_b, val_b])
                    .unwrap();
                self.push_boxed(r, self.def_type(pc, 0));
            }
            AsyncReject => {
                // `[reason, stack, gen] -> [promise]`: reject the result
                // promise.
                self.skip_operands(p, op);
                let gen_op = self.pop()?;
                let stack_op = self.pop()?;
                let reason_op = self.pop()?;
                let gen_b = self.to_boxed(&gen_op);
                let stack_b = self.to_boxed(&stack_op);
                let reason_b = self.to_boxed(&reason_op);
                let h = self.helpers.async_reject;
                let r = self
                    .rt_call(h, true, move |_, _| vec![gen_b, reason_b, stack_b])
                    .unwrap();
                self.push_boxed(r, self.def_type(pc, 0));
            }
            CanSkipAwait => {
                // `[v] -> [v, canSkip]`: whether awaiting `v` can skip the
                // suspension. May throw.
                self.skip_operands(p, op);
                let v = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or("CanSkipAwait on empty stack")?;
                let vb = self.to_boxed(&v);
                let h = self.helpers.can_skip_await;
                let r = self.rt_unary_boxed(h, vb);
                self.push_boxed(r, prim_desc(PRIM_BOOLEAN));
            }
            MaybeExtractAwaitValue => {
                // `[val, canSkip] -> [val', canSkip]`: when canSkip, replace
                // val with its resolved value. May GC/throw.
                self.skip_operands(p, op);
                let k_op = self.pop()?;
                let val_op = self.pop()?;
                let k_i = self.to_i32(&k_op);
                let val_b = self.to_boxed(&val_op);
                let h = self.helpers.maybe_extract_await;
                let r = self.rt_call(h, true, move |_, _| vec![val_b, k_i]).unwrap();
                self.push_boxed(r, self.def_type(pc, 0));
                let kb = self.to_boxed(&k_op);
                self.push_boxed(kb, prim_desc(PRIM_BOOLEAN));
            }

            // --- bail set: unsupported in the BBV lane; the script skips
            // to the interpreter (always sound). `Resume` is the caller's
            // half of the protocol and never appears in a compiled
            // generator body: the interpreter handles it, dispatching into
            // the compiled body through `EnterNightResume`.
            BigInt
            | NonSyntacticGlobalThis
            | SetIntrinsic
            | EnvCallee
            | Eval
            | SpreadEval
            | StrictEval
            | StrictSpreadEval
            | DynamicImport
            | ImportMeta
            | GetImport
            | AddDisposable
            | TakeDisposeCapability
            | CreateSuppressedError
            | ForceInterpreter
            | DebugCheckSelfHosted
            | Resume => {
                return self.bail(op);
            }
        }
        Ok(())
    }
}
