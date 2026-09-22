/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Allocation, literals and object/array initialisers, plus the IC-miss
//! second-chance arm shared by the property and element caches.

use super::*;
use crate::constants::INLINE_INIT_ELEM_CAP;

impl<'a> Bbv<'a> {
    // --- IC arms (ctx-independent in-version diamonds) -------------------

    /// The second-chance arm. An IC miss is not
    /// one event: most misses are served by a pure slot lookup that runs no
    /// user code, allocates nothing, GCs nothing and reshapes nothing, and
    /// such a miss cannot have invalidated anything the caller had proven.
    /// The helper reports it in bit 1 of its result, so the arm forks:
    ///
    ///   Clean -> restore the pre-call state (facts, carriers, track) and
    ///            take an ordinary edge, which rejoins the very version the
    ///            fall-through uses. It also skips `reload` entirely: with no
    ///            GC the operands never moved, so the unboxed stack survives.
    ///   else  -> today's behaviour: reload the spilled (re-boxed) operands
    ///            and continue on a DIRTY lineage.
    ///
    /// This is why it is not the arm-scoping trade: scoping an arm keeps the
    /// facts by splitting the lineage, and pays for it in version count.
    /// The clean edge
    /// joins an existing version, so it buys the facts for no versions at
    /// all -- what it costs is one test and one cold block per miss arm.
    pub(super) fn miss_second_chance(
        &mut self,
        ok: Value,
        n: u32,
        next_pc: Pc,
        arm_st: ArmState,
        push_result: impl Fn(&mut Self),
    ) {
        self.miss_second_chance_w(ok, n, next_pc, arm_st, 0, push_result);
    }

    /// `miss_second_chance` for store ops: the clean edge proved no
    /// GC and no user code, but the miss helper still performed the op's
    /// store -- `write_bits` is its classified MUT contribution, OR'd into
    /// the restored accumulator so the rejoining edge's flags arg accounts
    /// for it (scoped to the clean block: the minted OR must not leak to
    /// the caller's continuation, which is not dominated by it).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn miss_second_chance_w(
        &mut self,
        ok: Value,
        n: u32,
        next_pc: Pc,
        arm_st: ArmState,
        write_bits: u32,
        push_result: impl Fn(&mut Self),
    ) {
        let saved_stack = arm_st.stack.clone();
        // Under a mapped arguments object the clean bit is not trusted: the
        // helper's populate-path proof (data slot, no GC, no stamp moved)
        // does not cover a getter writing this frame's formals through a
        // leaked `arguments`.
        let two = self.i32_const(if self.mapped_args_reachable() { 0 } else { 2 });
        let clean = self.binop(Operator::I32And, ok, two, Type::I32);
        let clean_blk = self.body.add_block();
        let dirty_blk = self.body.add_block();
        self.cond_br(clean, clean_blk, dirty_blk);

        self.cur = dirty_blk;
        self.stack = saved_stack.clone();
        self.reload(n);
        push_result(self);
        let target = self.dirty_edge_to(next_pc);
        self.body
            .set_terminator(self.cur, Terminator::Br { target });

        self.cur = clean_blk;
        self.arm_restore(arm_st);
        let saved_flags = self.cur_flags;
        self.or_flags_const(write_bits);
        push_result(self);
        let target = self.edge_to(next_pc);
        self.body
            .set_terminator(self.cur, Terminator::Br { target });
        self.cur_flags = saved_flags;
        self.stack = saved_stack;
    }

    pub(super) fn convert_to_repr(&mut self, o: &Operand, r: Repr) -> Value {
        if o.repr == r {
            return o.val;
        }
        match r {
            Repr::Boxed => self.to_boxed(o),
            Repr::I32 | Repr::Bool => self.to_i32(o),
            // A boxed source takes the uniform unbox on purpose. `to_f64`
            // would use the operand's own facts to shortcut it (exact-Int32
            // -> wrap+convert, double-only -> bare reinterpret), which emits
            // different code per site for the same value and defeats the
            // gvn that collapses identical unboxes. The shortcut measures
            // as a net loss for exactly that reason.
            Repr::F64 if o.repr == Repr::Boxed => {
                let b = self.to_boxed(o);
                self.unbox_number_f64(b)
            }
            // An unboxed source converts in one op: an `I32` operand goes
            // straight through `f64.convert_i32_s`, with no box/unbox round
            // trip, which matters because `cont_at` types every edge
            // argument through here.
            Repr::F64 => self.to_f64(o),
            Repr::I64 => self.to_i64_exact(o),
            Repr::StrPtr | Repr::ObjPtr => self.to_ptr(o),
        }
    }

    /// `GetIntrinsic` through a per-intrinsic value cell (source:
    /// emit_get_intrinsic): an armed cell IS the value; the miss arm
    /// resolves-and-arms through `night_runtime_get_intrinsic_cell`.
    pub(super) fn emit_get_intrinsic(&mut self, atom_id: u32, next_pc: Pc) {
        let row = self.atoms.intrinsic_cell(atom_id);
        let h = self.helpers.get_intrinsic_cell;
        self.emit_value_cell_op(row, h, atom_id, next_pc);
    }

    /// `BuiltinObject` through the same armed-cell shape: the builtin is a
    /// realm constant, and the helper-per-read form off-ramped the lineage
    /// on every execution (regexp's self-hosted replace: 27k departures,
    /// 9.4M Dirty ops behind one site).
    pub(super) fn emit_builtin_object(&mut self, kind: u32, next_pc: Pc) {
        let row = self.atoms.builtin_object_cell(kind);
        let h = self.helpers.builtin_object_cell;
        self.emit_value_cell_op(row, h, kind, next_pc);
    }

    fn emit_value_cell_op(&mut self, row: u32, h: Func, arg: u32, next_pc: Pc) {
        let addr = self.i32_const(INTRINSIC_CELL_ADDR_PLACEHOLDER);
        self.intrinsic_cell_patches.push((addr, row));
        if self.outline_generic() {
            let arg_v = self.i32_const(arg);
            let r = self.rt_call(h, true, |_, _| vec![arg_v, addr]).unwrap();
            self.push_boxed(r, bottom_ty());
            return;
        }
        let bits = self.load_i64(addr, 0);
        let zero = self.boxed_const(0);
        let armed = self.binop(Operator::I64Ne, bits, zero, Type::I32);
        let fast_blk = self.body.add_block();
        let slow_blk = self.body.add_block();
        self.cond_br(armed, fast_blk, slow_blk);
        // The resolve-and-arm miss runs once per compacting GC; merged
        // back in-version its may-GC helper put an offramp on the ARMED
        // path's continuation too, so every read left the track for a
        // value that was already a pure load. It leaves as its own
        // post-call lineage instead.
        self.side_arm(slow_blk, next_pc, move |s| {
            let arg_v = s.i32_const(arg);
            let result = s.rt_call(h, true, |_, _| vec![arg_v, addr]).unwrap();
            Operand::plain(result, Repr::Boxed, bottom_ty())
        });
        self.cur = fast_blk;
        self.push_boxed(bits, bottom_ty());
    }

    /// The shared nursery bump-room guard (source: emit_nursery_room_guard).
    pub(super) fn emit_nursery_room_guard(
        &mut self,
        cell: Value,
        total_off: u32,
        miss_blk: Block,
    ) -> (Block, Value, Value, Value) {
        let posp_slot = self.i32_const(self.helpers.nursery_pos_slot);
        let posp = self.load_i32(posp_slot, 0);
        let pos = self.load_i32(posp, 0);
        let total = self.load_i32(cell, total_off);
        let newpos = self.binop(Operator::I32Add, pos, total, Type::I32);
        let endp_slot = self.i32_const(self.helpers.nursery_end_slot);
        let endp = self.load_i32(endp_slot, 0);
        let end = self.load_i32(endp, 0);
        let fits = self.binop(Operator::I32LeU, newpos, end, Type::I32);
        let store_blk = self.body.add_block();
        self.cond_br(fits, store_blk, miss_blk);
        (store_blk, posp, pos, newpos)
    }

    /// `JSOp::String`: the script's atom, exactly what the interpreter
    /// pushes -- one load off the startup-filled atom table (a pinned atom in
    /// the atoms zone never moves) and a tag. Not a fresh copy: a copy is an
    /// allocation per push, GC churn in proportion, and a value on which every
    /// `===` misses pointer equality and compares characters.
    pub(super) fn emit_string_literal(&mut self, atom_id: u32) {
        let slot = self.i32_const(self.helpers.atom_table_slot);
        let tbl = self.load_i32(slot, 0);
        self.eff(tbl, Eff::ReadBits(HeapKind::EngineTable));
        let ptr = self.load_i32(tbl, 4 * atom_id);
        self.eff(ptr, Eff::ReadBits(HeapKind::EngineTable));
        let payload = self.unop(Operator::I64ExtendI32U, ptr, Type::I64);
        let tag = self.boxed_const(TAG_STRING << 32);
        let result = self.binop(Operator::I64Or, payload, tag, Type::I64);
        self.push_known(result, Repr::Boxed, prim_desc(PRIM_STRING));
    }

    pub(super) fn emit_alloc_inline(&mut self, array_length: Option<u32>) {
        // `Code`-only allocation (see emit_instanceof's cell note).
        let cell_idx = if self.mode == EmitMode::Code {
            self.atoms.next_alloc_cell()
        } else {
            0
        };
        let cell = self.i32_const(ALLOC_CELL_ADDR_PLACEHOLDER);
        self.alloc_cell_patches.push((cell, cell_idx));

        let (reprs, vals) = self.diamond_snapshot();
        let top_off = self.operand_base + 8 * u32::try_from(reprs.len()).unwrap();

        let slow_blk = self.body.add_block();
        let merge = self.body.add_block();
        let op_params = self.diamond_params(merge, &reprs);
        let res_param = self.body.add_blockparam(merge, Type::I64);
        let ok_param = self.body.add_blockparam(merge, Type::I32);

        // Guard 1: the cell is filled (shape != 0).
        let shape = self.load_i32(cell, 0);
        let zero = self.i32_const(0);
        let filled = self.binop(Operator::I32Ne, shape, zero, Type::I32);
        let bump_blk = self.body.add_block();
        self.cond_br(filled, bump_blk, slow_blk);

        // Guard 2: room in the nursery chunk.
        self.cur = bump_blk;
        let (store_blk, posp, pos, newpos) = self.emit_nursery_room_guard(cell, 4, slow_blk);

        // The bump and header stamps.
        self.cur = store_blk;
        let sc = self.store_i32(posp, 0, newpos);
        self.tag_store(sc, HeapKind::AllocCursor);
        let hdr = self.load_i32(cell, 16);
        let sh = self.store_i32(pos, 0, hdr);
        self.tag_store(sh, HeapKind::Fresh);
        let hdr_bytes = self.i32_const(NURSERY_HEADER_BYTES);
        let obj = self.binop(Operator::I32Add, pos, hdr_bytes, Type::I32);
        let s0 = self.store_i32(obj, SHAPE_OFFSET, shape);
        self.tag_store(s0, HeapKind::Fresh);
        // Array stamp (increment 2): a claiming allocation site stamps the
        // fresh array here. The claim holds vacuously -- the array has no
        // elements yet -- and the element writes that follow carry the
        // maintenance duty, exactly as a ctor's checked init stores do for
        // the object stamp. Everything else allocates unstamped (word 0).
        let stamp = self
            .ctx
            .array_stamp_in
            .get(&Site::new(
                self.source_id,
                Pc::new(self.evid_pc(self.cur_pc).get()),
            ))
            .copied();
        let word0 = match stamp {
            Some(w) => self.i32_const(w),
            None => zero,
        };
        let s1 = self.store_i32(obj, OBJ_CLASS_IDX_OFFSET, word0);
        self.tag_store(s1, HeapKind::Fresh);
        let slotsw = self.load_i32(cell, 8);
        let s2 = self.store_i32(obj, OBJ_SLOTS_OFFSET, slotsw);
        self.tag_store(s2, HeapKind::Fresh);
        match array_length {
            None => {
                let elemsw = self.load_i32(cell, 12);
                let s3 = self.store_i32(obj, OBJ_ELEMENTS_OFFSET, elemsw);
                self.tag_store(s3, HeapKind::Fresh);
            }
            Some(_) => {
                let elem_off = self.load_i32(cell, 12);
                let elems = self.binop(Operator::I32Add, obj, elem_off, Type::I32);
                let s3 = self.store_i32(obj, OBJ_ELEMENTS_OFFSET, elems);
                self.tag_store(s3, HeapKind::Fresh);
                let ehdr_delta = self.i32_const(ELEMENTS_HEADER_BYTES.wrapping_neg());
                let ehdr = self.binop(Operator::I32Add, elems, ehdr_delta, Type::I32);
                let flags = self.load_i32(cell, 20);
                let e0 = self.store_i32(ehdr, 0, flags);
                self.tag_store(e0, HeapKind::Fresh);
                let e1 = self.store_i32(ehdr, 4, zero);
                self.tag_store(e1, HeapKind::Fresh);
                let cap = self.load_i32(cell, 24);
                let e2 = self.store_i32(ehdr, 8, cap);
                self.tag_store(e2, HeapKind::Fresh);
                let len = self.load_i32(cell, 28);
                let e3 = self.store_i32(ehdr, 12, len);
                self.tag_store(e3, HeapKind::Fresh);
            }
        }
        let payload = self.unop(Operator::I64ExtendI32U, obj, Type::I64);
        let tag = self.boxed_const(TAG_OBJECT << 32);
        let result = self.binop(Operator::I64Or, payload, tag, Type::I64);
        let one = self.i32_const(1);
        let mut fast_args = vals.clone();
        fast_args.push(result);
        fast_args.push(one);
        self.body.set_terminator(
            self.cur,
            Terminator::Br {
                target: BlockTarget {
                    block: merge,
                    args: fast_args,
                },
            },
        );

        // Slow arm: the generic helper (fills the cell when it can).
        self.cur = slow_blk;
        self.spill_all();
        let top = self.add_offset(self.vp, top_off);
        let ok = match array_length {
            None => {
                let helper = self.helpers.new_object;
                self.call_i32(helper, &[self.cx, top, cell])
            }
            Some(len) => {
                let len_v = self.i32_const(len);
                let helper = self.helpers.new_array;
                self.call_i32(helper, &[self.cx, top, len_v, cell])
            }
        };
        let slow_res = self.load_i64(self.vp, top_off);
        let mut margs = self.diamond_slow_args(&reprs);
        margs.push(slow_res);
        margs.push(ok);
        self.body.set_terminator(
            slow_blk,
            Terminator::Br {
                target: BlockTarget {
                    block: merge,
                    args: margs,
                },
            },
        );

        self.cur = merge;
        self.diamond_rebind(&op_params);
        self.branch_on_err(ok_param);
        // Object-literal stamp: the lit row always existed in the layout
        // key space (claims, runtime tables, add-prediction pairs), but
        // nothing ever STAMPED the allocation, leaving the literal-born
        // population as the "receiver never stamped" class-fact miss
        // bucket. SLOTS-only word: the init stores land at the row's
        // predicted slots by construction (first-write order IS the row),
        // and slow-arm engine adds match the add-prediction pairs, so the
        // bit survives; SHALLOW/RANGES stay off -- value maintenance
        // (the store duty on init values) is not emitted here, and a
        // vacuous bit would only feed the demote chokes. The word is
        // written after the merge, so both the inline-nursery and the
        // helper arm stamp; the object has not escaped, so no guard can
        // observe a half-initialized instance.
        if array_length.is_none() {
            if let Some(&lid) = self
                .ctx
                .lit_stamps_in
                .get(&Site::new(self.source_id, self.evid_pc(self.cur_pc)))
            {
                let objptr = self.unop(Operator::I32WrapI64, res_param, Type::I32);
                let w = self.i32_const((lid + 1) | CLASS_WORD_SLOTS);
                let st = self.store_i32(objptr, OBJ_CLASS_IDX_OFFSET, w);
                self.tag_store(st, HeapKind::ClassWord);
            }
        }
        self.push_boxed(res_param, obj_only_ty());
        // A literal allocation is fresh by construction.
        if let Some(o) = self.stack.last_mut() {
            o.fresh = true;
        }
    }

    pub(super) fn bail(&self, op: JSOp) -> Result<(), String> {
        Err(format!("bbv: unsupported op {op:?}"))
    }

    /// `InitProp name` on a literal under construction: inline
    /// add-transition replay off the site's prop-IC trans row (populated by
    /// the helper). The object stays on the stack (peeked). Defines never
    /// consult the proto chain, so the guards are just oldShape match +
    /// fixed slot + barrier gate. Hidden/Locked (rare) keep the plain helper
    /// call.
    pub(super) fn emit_init_prop(&mut self, atom_id: u32, attrs: u32) -> Result<(), String> {
        let val = self.pop()?;
        let obj = self
            .stack
            .last()
            .cloned()
            .ok_or("InitProp on empty stack")?;
        let val_boxed = self.to_boxed(&val);
        let obj_boxed = self.to_boxed(&obj);
        let atom_v = self.i32_const(atom_id);
        let attrs_v = self.i32_const(attrs);
        let ip = self.helpers.init_prop;
        if attrs != INIT_ATTR_ENUMERATE || self.outline_generic() {
            let no_site = self.i32_const(u32::MAX);
            self.rt_call(ip, false, |_, _| {
                vec![obj_boxed, atom_v, val_boxed, attrs_v, no_site]
            });
            return Ok(());
        }
        // `Code`-only allocation (see emit_instanceof's cell note).
        let cache_idx = if self.mode == EmitMode::Code {
            self.atoms.next_prop_cache()
        } else {
            0
        };
        let cache_v = self.i32_const(cache_idx);

        let (reprs, vals) = self.diamond_snapshot();
        let top_off = self.operand_base + 8 * u32::try_from(reprs.len()).unwrap();
        let slow_blk = self.body.add_block();
        let merge = self.body.add_block();
        let op_params = self.diamond_params(merge, &reprs);
        let ok_param = self.body.add_blockparam(merge, Type::I32);

        // The literal under construction is always an object; the row
        // probe needs its shape.
        let objptr = self.unop(Operator::I32WrapI64, obj_boxed, Type::I32);
        let shape = self.load_i32(objptr, SHAPE_OFFSET);
        self.eff(shape, Eff::Read(HeapKind::Shape));
        let row = self.i32_const(IC_WAY_ADDR_PLACEHOLDER);
        self.prop_ic_patches
            .push((row, cache_idx * INLINE_IC_STRIDE + IC_TRANS_ROW_OFF));
        let old_s = self.load_i32(row, IC_TRANS_OLDSHAPE);
        self.eff(old_s, Eff::Read(HeapKind::EngineTable));
        let m_old = self.binop(Operator::I32Eq, old_s, shape, Type::I32);
        let guard_blk = self.body.add_block();
        self.cond_br(m_old, guard_blk, slow_blk);
        self.cur = guard_blk;
        let slot_off = self.load_i32(row, IC_TRANS_SLOTOFF);
        let zero = self.i32_const(0);
        let ok_slot = self.binop(Operator::I32Ne, slot_off, zero, Type::I32);
        let replay_blk = self.body.add_block();
        self.cond_br(ok_slot, replay_blk, slow_blk);

        // Fresh-slot init store (no pre-barrier: no old value) + shape
        // swap + the standard post-write barrier gate -- pretenured
        // literals store GC things too. No add-arm SLOTS check here: the
        // receiver is a literal under construction, and literals never
        // carry a class word (alloc writes 0), so no SLOTS bit can be
        // falsely kept.
        self.cur = replay_blk;
        let recv_bit = self.store_recv_bit(&obj);
        let slot_addr = self.binop(Operator::I32Add, objptr, slot_off, Type::I32);
        let st = self.store_i64(slot_addr, 0, val_boxed);
        self.eff_store(st, Eff::Write(HeapKind::Slot), recv_bit);
        let new_s = self.load_i32(row, IC_TRANS_NEWSHAPE);
        let sw = self.store_i32(objptr, SHAPE_OFFSET, new_s);
        self.eff_store(sw, Eff::Write(HeapKind::Shape), recv_bit);
        if !is_non_gc(&val.ty) {
            let t_abs_slot = self.load_i32(row, IC_TRANS_ABSSLOT);
            self.emit_post_write_barrier(obj_boxed, t_abs_slot, val_boxed);
        }
        let one = self.i32_const(1);
        let mut fargs = vals.clone();
        fargs.push(one);
        self.body.set_terminator(
            self.cur,
            Terminator::Br {
                target: BlockTarget {
                    block: merge,
                    args: fargs,
                },
            },
        );

        self.cur = slow_blk;
        self.spill_all();
        let top = self.add_offset(self.vp, top_off);
        let ok = self.call_i32(
            ip,
            &[self.cx, top, obj_boxed, atom_v, val_boxed, attrs_v, cache_v],
        );
        let mut margs = self.diamond_slow_args(&reprs);
        margs.push(ok);
        self.body.set_terminator(
            self.cur,
            Terminator::Br {
                target: BlockTarget {
                    block: merge,
                    args: margs,
                },
            },
        );

        self.cur = merge;
        self.diamond_rebind(&op_params);
        for (i, &r) in reprs.iter().enumerate() {
            self.stack[i].repr = r;
        }
        self.branch_on_err(ok_param);
        // Per-lineage accounting: both merge arms defined a
        // prop on the literal -- a fresh receiver contributes nothing.
        self.or_flags_const(recv_bit);
        Ok(())
    }

    /// `InitElemArray index`: inline dense-element store when the guards
    /// prove the plain literal fill (dense writable packed array with
    /// initializedLength == index and room, non-GC-thing non-magic value
    /// so no barriers or hole marking are needed); the port of
    /// translate.rs `emit_init_elem_array`, generic helper past the cap.
    pub(super) fn emit_init_elem_array(&mut self, index: u32) -> Result<(), String> {
        let key = (TAG_INT32 << 32) | u64::from(index);
        let val = self.pop()?;
        let val_boxed = self.to_boxed(&val);
        if index >= INLINE_INIT_ELEM_CAP || self.outline_generic() {
            let key_v = self.boxed_const(key);
            return self.emit_init_elem_call(key_v, val_boxed, INIT_ATTR_ENUMERATE);
        }
        let arr = self
            .stack
            .last()
            .cloned()
            .ok_or("InitElemArray on empty stack")?;
        let arr_boxed = self.to_boxed(&arr);

        let (reprs, vals) = self.diamond_snapshot();
        let top_off = self.operand_base + 8 * u32::try_from(reprs.len()).unwrap();
        let slow_blk = self.body.add_block();
        let merge = self.body.add_block();
        let op_params = self.diamond_params(merge, &reprs);
        let ok_param = self.body.add_blockparam(merge, Type::I32);

        // Value must be neither a GC thing (would need a post barrier when
        // the array is tenured) nor the elements-hole magic (would need
        // the NON_PACKED flag): tag < MAGIC covers doubles too.
        let sh = self.i32_const(32);
        let sh64 = self.unop(Operator::I64ExtendI32U, sh, Type::I64);
        let hi = self.binop(Operator::I64ShrU, val_boxed, sh64, Type::I64);
        let val_tag = self.unop(Operator::I32WrapI64, hi, Type::I32);
        let magic_tag = self.i32_const(TAG_MAGIC as u32);
        let val_ok = self.binop(Operator::I32LtU, val_tag, magic_tag, Type::I32);
        let arr_ok = if is_object_only(&arr.ty) {
            val_ok
        } else {
            let is_obj = self.tag_eq(arr_boxed, TAG_OBJECT as u32);
            self.binop(Operator::I32And, val_ok, is_obj, Type::I32)
        };
        let hdr_blk = self.body.add_block();
        self.cond_br(arr_ok, hdr_blk, slow_blk);

        // Dense guards: no flags beyond fixed (writable, packed,
        // extensible, not frozen/shared), initializedLength == index,
        // capacity > index, length > index.
        self.cur = hdr_blk;
        let objptr = self.unop(Operator::I32WrapI64, arr_boxed, Type::I32);
        let elems = self.load_i32(objptr, OBJ_ELEMENTS_OFFSET);
        self.eff(elems, Eff::Read(HeapKind::ElementsHeader));
        let ehdr_delta = self.i32_const(ELEMENTS_HEADER_BYTES.wrapping_neg());
        let ehdr = self.binop(Operator::I32Add, elems, ehdr_delta, Type::I32);
        let flags = self.load_i32(ehdr, 0);
        self.eff(flags, Eff::ReadBits(HeapKind::ElementsHeader));
        let initlen = self.load_i32(ehdr, 4);
        self.eff(initlen, Eff::ReadBits(HeapKind::ElementsHeader));
        let cap = self.load_i32(ehdr, 8);
        self.eff(cap, Eff::ReadBits(HeapKind::ElementsHeader));
        let len = self.load_i32(ehdr, 12);
        self.eff(len, Eff::ReadBits(HeapKind::ElementsHeader));
        let zero = self.i32_const(0);
        let idx_v = self.i32_const(index);
        let not_fixed = self.i32_const(!ELEMENTS_FLAG_FIXED);
        let flags_rest = self.binop(Operator::I32And, flags, not_fixed, Type::I32);
        let f_ok = self.binop(Operator::I32Eq, flags_rest, zero, Type::I32);
        let i_ok = self.binop(Operator::I32Eq, initlen, idx_v, Type::I32);
        let c_ok = self.binop(Operator::I32GtU, cap, idx_v, Type::I32);
        let l_ok = self.binop(Operator::I32GtU, len, idx_v, Type::I32);
        let fi = self.binop(Operator::I32And, f_ok, i_ok, Type::I32);
        let cl = self.binop(Operator::I32And, c_ok, l_ok, Type::I32);
        let all_ok = self.binop(Operator::I32And, fi, cl, Type::I32);
        let store_blk = self.body.add_block();
        self.cond_br(all_ok, store_blk, slow_blk);

        self.cur = store_blk;
        let recv_bit = self.store_recv_bit(&arr);
        let st = self.store_i64(elems, index * 8, val_boxed);
        self.eff_store(st, Eff::Write(HeapKind::Elements), recv_bit);
        self.emit_elem_store_duty(objptr, &val);
        let newlen = self.i32_const(index + 1);
        let sl = self.store_i32(ehdr, 4, newlen);
        self.eff_store(sl, Eff::Write(HeapKind::ElementsHeader), recv_bit);
        let one = self.i32_const(1);
        let mut fargs = vals.clone();
        fargs.push(one);
        self.body.set_terminator(
            self.cur,
            Terminator::Br {
                target: BlockTarget {
                    block: merge,
                    args: fargs,
                },
            },
        );

        // Slow arm: the generic boxed-key init_elem helper.
        self.cur = slow_blk;
        self.spill_all();
        let top = self.add_offset(self.vp, top_off);
        let key_v = self.boxed_const(key);
        let attrs_v = self.i32_const(INIT_ATTR_ENUMERATE);
        let ie = self.helpers.init_elem;
        let ok = self.call_i32(ie, &[self.cx, top, arr_boxed, key_v, val_boxed, attrs_v]);
        let mut margs = self.diamond_slow_args(&reprs);
        margs.push(ok);
        self.body.set_terminator(
            self.cur,
            Terminator::Br {
                target: BlockTarget {
                    block: merge,
                    args: margs,
                },
            },
        );

        self.cur = merge;
        self.diamond_rebind(&op_params);
        for (i, &r) in reprs.iter().enumerate() {
            self.stack[i].repr = r;
        }
        self.branch_on_err(ok_param);
        // Per-lineage accounting (see emit_init_prop).
        self.or_flags_const(recv_bit);
        Ok(())
    }

    pub(super) fn emit_init_elem_call(
        &mut self,
        key_boxed: Value,
        val_boxed: Value,
        attrs: u32,
    ) -> Result<(), String> {
        let obj = self
            .stack
            .last()
            .cloned()
            .ok_or("InitElem on empty stack")?;
        let obj_boxed = self.to_boxed(&obj);
        let attrs_v = self.i32_const(attrs);
        let ie = self.helpers.init_elem;
        self.rt_call(ie, false, |_, _| {
            vec![obj_boxed, key_boxed, val_boxed, attrs_v]
        });
        Ok(())
    }
}
