/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Global-name lowerings: the slot-table prologue and the inline guarded
//! get/bind/set arms.

use super::*;

impl<'a> Bbv<'a> {
    // --- gname inline arms -----------------------------------------------
    //
    // The guarded arm is unconditional on the get side. The bind/set inline
    // arms are gated on `!is_global`: a global (top-level) script performs
    // the declaration writes the fused-gname prime protocol observes through
    // the generic helpers, and runs once anyway.

    /// The global's slot address from a v2 `gGlobalSlots` entry (bit1
    /// dynamic, bit2 writable, idx at bits[31:3]): the byte offset is
    /// `idx * 8` plus the fixed-slot base when the slot is fixed.
    pub(super) fn gname_entry_slot_addr(&mut self, global: Value, entry: Value) -> Value {
        let one = self.i32_const(1);
        let sh = self.binop(Operator::I32ShrU, entry, one, Type::I32);
        let is_dyn = self.binop(Operator::I32And, sh, one, Type::I32);
        let mask = self.i32_const(!7);
        let idx8 = self.binop(Operator::I32And, entry, mask, Type::I32);
        let zero = self.i32_const(0);
        let fixed_base = self.i32_const(FIXED_SLOTS_BASE);
        let add = self.select(Type::I32, zero, fixed_base, is_dyn);
        let off = self.binop(Operator::I32Add, idx8, add, Type::I32);
        self.emit_slot_addr_parts(global, is_dyn, off)
    }

    /// The guarded global-slot prologue shared by the inline get/bind/set
    /// GName arms: load the binding's cached `[entry, shape]` row and the
    /// live global object + its shape, then form `hit = resolved0 &&
    /// shape_ok`. Returns `(entry0, global, live_shape, one_c, hit)`.
    pub(super) fn emit_gname_slot_prologue(
        &mut self,
        bid: u32,
    ) -> (Value, Value, Value, Value, Value) {
        let base = self.i32_const(self.helpers.global_slots_base);
        // Fuse-cell semantics, not EngineTable: a shadowing
        // global lexical invalidates the binding by rewriting the row, not
        // by reshaping the global object -- the live-shape guard does not
        // cover it, so a stale hoisted row across a may-GC arm reads the
        // shadowed global slot instead of the lexical.
        let entry0 = self.load_i32(base, 8 * bid);
        self.eff(entry0, Eff::ReadBits(HeapKind::FuseCell));
        let shape0 = self.load_i32(base, 8 * bid + 4);
        self.eff(shape0, Eff::Read(HeapKind::FuseCell));
        let one_c = self.i32_const(1);
        let resolved0 = self.binop(Operator::I32And, entry0, one_c, Type::I32);
        let realm = self.load_i32(self.cx, JSCONTEXT_REALM_OFFSET);
        self.eff(realm, Eff::Read(HeapKind::EngineTable));
        let global = self.load_i32(realm, REALM_GLOBAL_OFFSET);
        self.eff(global, Eff::Read(HeapKind::EngineTable));
        let live_shape = self.load_i32(global, SHAPE_OFFSET);
        self.eff(live_shape, Eff::Read(HeapKind::Shape));
        let shape_ok = self.binop(Operator::I32Eq, shape0, live_shape, Type::I32);
        let hit = self.binop(Operator::I32And, resolved0, shape_ok, Type::I32);
        (entry0, global, live_shape, one_c, hit)
    }

    /// Maintain the per-binding value fuse (`gGlobalVals[bid]`) on an
    /// inline global store, mirroring `MaybeBlowBindingFuseId`: an armed
    /// cell (fuse word 1) whose stored value differs from the new value is
    /// UNARMED (0), and the leaf `night_runtime_binding_written` re-arms it
    /// from the stored value with the resolve-time checks. Blowing the
    /// cell instead (2, only a major GC resets it) would send every later
    /// read through the slot prologue instead of the fuse arm until the
    /// next major GC.
    pub(super) fn emit_blow_binding_value_fuse(&mut self, bid: u32, val_boxed: Value) {
        let vals_addr = self.helpers.global_vals_base + 16 * bid;
        let valsb = self.i32_const(vals_addr);
        let fw = self.load_i32(valsb, 8);
        let one = self.i32_const(1);
        let armed = self.binop(Operator::I32Eq, fw, one, Type::I32);
        let oldbits = self.load_i64(valsb, 0);
        let changed = self.binop(Operator::I64Ne, oldbits, val_boxed, Type::I32);
        let blow = self.binop(Operator::I32And, armed, changed, Type::I32);
        let blow_blk = self.body.add_block();
        let cont_blk = self.body.add_block();
        self.cond_br(blow, blow_blk, cont_blk);
        // A non-GC value (number, boolean, undefined, null) writes through:
        // the cell mirrors the slot and needs no rooting, so the armed cell
        // stays armed with no call (earley-boyer's global counters: the
        // leaf on every changed write cost it 6% of its instructions). A
        // GC thing unarms and hands the re-arm to the runtime, which has
        // the nursery list and the expected-callee check.
        self.cur = blow_blk;
        let shift = self.boxed_const(32);
        let tag64 = self.binop(Operator::I64ShrU, val_boxed, shift, Type::I64);
        let tag = self.unop(Operator::I32WrapI64, tag64, Type::I32);
        let str_tag = self.i32_const(TAG_STRING as u32);
        let is_gc = self.binop(Operator::I32GeU, tag, str_tag, Type::I32);
        let gc_blk = self.body.add_block();
        let plain_blk = self.body.add_block();
        self.cond_br(is_gc, gc_blk, plain_blk);
        self.cur = plain_blk;
        let st = self.store_i64(valsb, 0, val_boxed);
        self.tag_store(st, HeapKind::FuseCell);
        self.body.set_terminator(
            plain_blk,
            Terminator::Br {
                target: BlockTarget {
                    block: cont_blk,
                    args: vec![],
                },
            },
        );
        self.cur = gc_blk;
        let zero = self.i32_const(0);
        let st = self.store_i32(valsb, 8, zero);
        self.tag_store(st, HeapKind::FuseCell);
        let bid_v = self.i32_const(bid);
        self.call_void(self.helpers.binding_written, &[bid_v]);
        self.body.set_terminator(
            gc_blk,
            Terminator::Br {
                target: BlockTarget {
                    block: cont_blk,
                    args: vec![],
                },
            },
        );
        self.cur = cont_blk;
    }

    /// `GetGName`: the fused-gname literal arm, then the guarded
    /// syntactic-binding arm / generic helper tail.
    pub(super) fn emit_get_gname(
        &mut self,
        pc: Pc,
        name_index: u32,
        for_typeof: bool,
    ) -> Result<(), String> {
        let name = self.name_for(name_index)?;
        if self.outline_generic() {
            return self.emit_get_gname_generic(pc, name, for_typeof);
        }
        // Fused constant global: while the binding's fuse is armed (the
        // runtime saw exactly the predicted top-level literal written and
        // nothing since), the read IS the literal. Any other write, delete,
        // shadowing lexical, or interpreted script blows the fuse and reads
        // fall through to the guarded/generic arms forever.
        if let Some(&FusedGname {
            fuse_addr,
            boxed: literal,
        }) = self.ctx.fused_gnames.get(&name)
        {
            let next_pc = pc + JSOp::GetGName.len();
            let base = self.i32_const(fuse_addr);
            let f = self.load_i32(base, 0);
            self.eff(f, Eff::ReadBits(HeapKind::FuseCell));
            let one = self.i32_const(1);
            let armed = self.binop(Operator::I32Eq, f, one, Type::I32);
            let lit = self.boxed_const(literal);
            let slow_blk = self.body.add_block();
            let hit_blk = self.body.add_block();
            self.cond_br(armed, hit_blk, slow_blk);
            // The disarmed arm is scoped with its own continuation (the
            // side_arm shape, hand-rolled so the tail's Result propagates):
            // joining the helper-crossed lineage into the armed
            // fall-through instead would let the never-taken slow arm kill
            // the Opt track at every fused global read -- enough to lose a
            // whole method body to the constant reads at its top.
            {
                // The disarmed arm STEPS (Side, = Dirty at the key). A
                // non-stepping form would join the disarmed read's boxed
                // load with the armed arm's IR constant at next_pc, turning
                // the literal into a block param so every consumer loses
                // the fold. A blown fuse is a
                // permanent Dirty body for that read, so the fuse table
                // must only hold names that stay armed (`collect_fused_gnames`
                // drops names other scripts write; computed-key global
                // writes blow one fuse, not all).
                let st = self.arm_state();
                self.post_call = false;
                self.cur_track = self.cur_track.step(Track::Side);
                self.cur = slow_blk;
                self.emit_get_gname_tail(pc, name, for_typeof, Some(next_pc.get()))?;
                let target = if self.post_call {
                    self.dirty_edge_to(next_pc)
                } else {
                    self.edge_to(next_pc)
                };
                self.body
                    .set_terminator(self.cur, Terminator::Br { target });
                self.arm_restore(st);
            }
            self.cur = hit_blk;
            // The armed arm's value IS the literal: push it with the
            // literal's own type (and one-point interval for int32), not
            // TOP -- an all-TOP arm edge joining next_pc strips whatever
            // fact the other read arms proved, for every lineage there.
            let tag = literal >> 32;
            let o = match tag {
                TAG_INT32 => {
                    let v = i64::from(literal as u32 as i32);
                    Operand::plain(lit, Repr::Boxed, prim_desc(PRIM_INT32))
                        .with_iv(Some((v, v, false)))
                }
                TAG_BOOLEAN => Operand::plain(lit, Repr::Boxed, prim_desc(PRIM_BOOLEAN)),
                TAG_NULL => Operand::plain(lit, Repr::Boxed, prim_desc(PRIM_NULL)),
                TAG_UNDEFINED => Operand::plain(lit, Repr::Boxed, prim_desc(PRIM_UNDEFINED)),
                _ => Operand::plain(lit, Repr::Boxed, prim_desc(PRIM_DOUBLE)),
            };
            self.stack.push(o.with_prov(Prov::C_GNAME));
            return Ok(());
        }
        let next_pc = pc + JSOp::GetGName.len();
        self.emit_get_gname_tail(pc, name, for_typeof, Some(next_pc.get()))
    }

    /// The guarded syntactic arm when the binding is known, else the
    /// generic char-based helper.
    pub(super) fn emit_get_gname_tail(
        &mut self,
        pc: Pc,
        name: NameId,
        for_typeof: bool,
        slow_cont: Option<u32>,
    ) -> Result<(), String> {
        if !self.outline_generic() {
            if let Some(&bid) = self.ctx.syn_gnames.get(&name) {
                let atom_id = self.atoms.intern(name);
                let claim = self
                    .ctx
                    .facts
                    .gname_types
                    .get(&name)
                    .copied()
                    .map(Claim::sans_ta);
                self.emit_get_gname_inline_guarded(pc, bid, atom_id, for_typeof, slow_cont, claim);
                return Ok(());
            }
        }
        self.emit_get_gname_generic(pc, name, for_typeof)
    }

    /// The dynamic char-based helper (re-atomize + GetNameOperation) -- the
    /// The generic form.
    pub(super) fn emit_get_gname_generic(
        &mut self,
        pc: Pc,
        name: NameId,
        for_typeof: bool,
    ) -> Result<(), String> {
        let atom_id = self.atoms.intern(name);
        let atom_v = self.i32_const(atom_id);
        let tt = self.i32_const(u32::from(for_typeof));
        let getg = self.helpers.get_gname;
        // Epoch-kept: a name outside the syntactic binding table (e.g. an
        // implicitly created global, read at a loop's top) is still a
        // plain slot read almost always.
        let ty = self.def_type(pc, 0);
        let next_pc = self.cur_op.map(|op| pc + op.len());
        // Gname value claim (gname_types): the loaded value runs the
        // typed-load ladder, per read -- guarded likely, never proof, so
        // writes the analysis cannot see just take the miss arm.
        let claim = (!self.outline_generic())
            .then(|| self.ctx.facts.gname_types.get(&name).copied())
            .flatten()
            .map(Claim::sans_ta);
        let result = self.rt_call_keep_claim(
            getg,
            0,
            next_pc,
            &ty,
            vec![atom_v, tt],
            claim.map(|c| (c, Prov::C_GNAME)),
        );
        match (claim, next_pc) {
            (Some(c), Some(np)) => self.push_load_typed(result, c, np, Prov::C_GNAME),
            _ => self.push_boxed(result, ty),
        }
        Ok(())
    }

    /// `gGlobalSlots` (8-byte stride) holds `[entry, globalShape]`; a hit
    /// is `entry.bit0 && globalShape == live global shape` -- the shape
    /// guard is what makes an arbitrary (syntactic) binding sound: any
    /// global-object reshape (delete / redefine / add) misses, and the
    /// resolve leaf only caches own plain data slots not shadowed by a
    /// global lexical. Four arms: the per-binding value-fuse hit,
    /// inline slot load (hit), leaf re-resolve then slot load (cold /
    /// invalidated), the generic char-based helper (not cacheable --
    /// lexicals, TDZ, undeclared/typeof). Deferred spills: only the helper
    /// arm spills.
    pub(super) fn emit_get_gname_inline_guarded(
        &mut self,
        pc: Pc,
        bid: u32,
        atom_id: u32,
        for_typeof: bool,
        slow_cont: Option<u32>,
        claim: Option<Claim>,
    ) {
        let result_ty = self.def_type(pc, 0);
        // Whether this binding carries value facts (`Ctx::gcells`).
        let gcell = !self.gen_only && slow_cont.is_some() && self.ctx.gcell_bids.contains(&bid);
        let (reprs, vals) = self.diamond_snapshot();
        let top_off = self.operand_base + 8 * u32::try_from(reprs.len()).unwrap();

        let resolve_blk = self.body.add_block();
        let helper_blk = self.body.add_block();
        let use_blk = self.body.add_block();
        let entry_param = self.body.add_blockparam(use_blk, Type::I32);
        let merge = self.body.add_block();
        let op_params = self.diamond_params(merge, &reprs);
        let res_param = self.body.add_blockparam(merge, Type::I64);
        let ok_param = self.body.add_blockparam(merge, Type::I32);

        // Per-binding value-fuse arm FIRST: an armed (word 1) gGlobalVals
        // cell IS the value, and it is the steady arm of every global the
        // runtime finds constant (deltablue's `Direction`, an object the
        // fused-literal table cannot hold: 16 IR a read while the guarded
        // slot prologue -- five loads, the global's live shape -- ran
        // ahead of this test). The prologue is emitted on the miss side.
        let vals_addr = self.helpers.global_vals_base + 16 * bid;
        let valsb = self.i32_const(vals_addr);
        let cfw = self.load_i32(valsb, 8);
        self.eff(cfw, Eff::ReadBits(HeapKind::FuseCell));
        let one_fw = self.i32_const(1);
        let const_hit = self.binop(Operator::I32Eq, cfw, one_fw, Type::I32);
        let chit_blk = self.body.add_block();
        let noconst_blk = self.body.add_block();
        self.cond_br(const_hit, chit_blk, noconst_blk);
        self.cur = chit_blk;
        self.emit_guard_census(census::GNAME_FUSE_HIT, pc);
        let cbits = self.load_i64(valsb, 0);
        self.eff(cbits, Eff::Read(HeapKind::FuseCell));
        let one_i = self.i32_const(1);
        let mut chit_args = vals.clone();
        chit_args.push(cbits);
        chit_args.push(one_i);
        self.body.set_terminator(
            self.cur,
            Terminator::Br {
                target: BlockTarget {
                    block: merge,
                    args: chit_args,
                },
            },
        );
        self.cur = noconst_blk;
        let (entry0, global, _, one_c, hit) = self.emit_gname_slot_prologue(bid);
        self.body.set_terminator(
            self.cur,
            Terminator::CondBr {
                cond: hit,
                if_true: BlockTarget {
                    block: use_blk,
                    args: vec![entry0],
                },
                if_false: BlockTarget {
                    block: resolve_blk,
                    args: vec![],
                },
            },
        );

        // Cold: re-resolve (leaf; lookupPure + shape read, no GC). A zero
        // entry means "not cacheable" -> the generic helper.
        self.cur = resolve_blk;
        self.emit_guard_census(census::GNAME_RESOLVE, pc);
        let bid_v = self.i32_const(bid);
        let entry1 = self.call_i32(self.helpers.resolve_global_slot_guarded, &[self.cx, bid_v]);
        let resolved1 = self.binop(Operator::I32And, entry1, one_c, Type::I32);
        self.body.set_terminator(
            resolve_blk,
            Terminator::CondBr {
                cond: resolved1,
                if_true: BlockTarget {
                    block: use_blk,
                    args: vec![entry1],
                },
                if_false: BlockTarget {
                    block: helper_blk,
                    args: vec![],
                },
            },
        );

        // Hit / resolved: pure slot load off the live global (the resolve
        // leaf never moves objects, so `global` from the entry block stays
        // valid).
        self.cur = use_blk;
        self.emit_guard_census(census::GNAME_SLOT_HIT, pc);
        let slot_addr = self.gname_entry_slot_addr(global, entry_param);
        let result = self.load_i64(slot_addr, 0);
        self.eff(result, Eff::Read(HeapKind::Slot));
        let one = self.i32_const(1);
        let mut fast_args = vals.clone();
        fast_args.push(result);
        fast_args.push(one);
        self.body.set_terminator(
            use_blk,
            Terminator::Br {
                target: BlockTarget {
                    block: merge,
                    args: fast_args,
                },
            },
        );

        // Not cacheable: spill (rooting), the generic char-based helper
        // (GetNameOperation semantics: lexicals, TDZ, throw-on-undeclared,
        // typeof), reload through the merge params.
        self.cur = helper_blk;
        self.emit_guard_census(census::GNAME_HELPER, pc);
        let arm_st = self.arm_state();
        let pre_e = self.emit_epoch_read();
        let pre_b = self.sample_bind_epoch();
        let n = self.spill_all();
        let top = self.add_offset(self.vp, top_off);
        let atom_v = self.i32_const(atom_id);
        let tt = self.i32_const(u32::from(for_typeof));
        let getg = self.helpers.get_gname;
        let ok = self.call_i32(getg, &[self.cx, top, atom_v, tt]);
        let slow_res = self.load_i64(self.vp, top_off);
        match slow_cont {
            Some(next_pc) => {
                // Epoch-kept first: a non-cacheable binding (a global
                // lexical, a dictionary-mode global) is still a read. The
                // keep runs the same gname-claim ladder as the fast arms:
                // its bottom result joining the claimed merge at next_pc
                // was the fact-stripper (earley's counter reads).
                //
                // Not for a binding that carries value facts: its fast
                // arms install the fact at next_pc, and an Opt keep arm
                // arriving without it would strip it from the prediction
                // for every lineage there (the join law). This arm runs
                // only if the snapshot's own data property was since
                // deleted, redefined or shadowed, and then its reads are
                // a Dirty body -- the fused-literal arm's rule.
                if !gcell {
                    self.epoch_keep_tail_claim(
                        arm_st.clone(),
                        pre_e,
                        pre_b,
                        ok,
                        Some((slow_res, bottom_ty())),
                        claim.map(|c| (c, Prov::C_GNAME)),
                        Pc::new(next_pc),
                    );
                }
                self.reload(n);
                self.branch_on_err(ok);
                self.push_boxed(slow_res, bottom_ty());
                let target = self.dirty_edge_to(Pc::new(next_pc));
                self.body
                    .set_terminator(self.cur, Terminator::Br { target });
                self.arm_restore(arm_st);
            }
            None => {
                let mut margs = self.diamond_slow_args(&reprs);
                margs.push(slow_res);
                margs.push(ok);
                self.body.set_terminator(
                    helper_blk,
                    Terminator::Br {
                        target: BlockTarget {
                            block: merge,
                            args: margs,
                        },
                    },
                );
            }
        }

        self.cur = merge;
        self.diamond_rebind(&op_params);
        for (i, &r) in reprs.iter().enumerate() {
            self.stack[i].repr = r;
        }
        self.branch_on_err(ok_param);
        // The carried value fact serves the read with no ladder: the value
        // came from the armed cell or the guarded slot, and a fact about
        // the binding's value is a fact about both.
        if gcell {
            let held = self.gcell_fact(bid);
            let implied = !held.is_top()
                && claim.is_none_or(|c| {
                    claim_shape(c).is_some_and(|sh| held.implies_sans_iv(&claim_slot_ctx(sh)))
                });
            if implied {
                self.emit_guard_census(census::GNAME_FACT_HIT, pc);
                self.stack.push(
                    Operand::from_slot(res_param, held, SlotRef::GCell(bid))
                        .with_prov(Prov::C_GNAME),
                );
                return;
            }
        }
        // Gname value claim on the merged result (gname_types): same
        // per-read guarded ladder as the generic form.
        match (claim, slow_cont) {
            (Some(c), Some(cont)) => {
                self.push_load_typed(res_param, c, Pc::new(cont), Prov::C_GNAME)
            }
            _ => self.push_boxed(res_param, result_ty),
        }
        if gcell {
            self.install_gcell(bid, claim);
        }
    }

    /// Shape-guarded inline `BindUnqualifiedGName`. When the name
    /// resolves (guarded) to a cacheable own global-object data slot not
    /// shadowed by a lexical, the unqualified binding object IS the global
    /// object -> push it, re-derived from `cx`, with no reactor call. A
    /// non-cacheable name falls to the `bind_unqualified_gname` helper.
    pub(super) fn emit_bind_gname_inline(
        &mut self,
        pc: Pc,
        bid: u32,
        atom_id: u32,
        slow_cont: Option<u32>,
    ) {
        let (_, global, _, one_c, hit) = self.emit_gname_slot_prologue(bid);
        let global_boxed = {
            let pay = self.unop(Operator::I64ExtendI32U, global, Type::I64);
            let tag = self.boxed_const(TAG_OBJECT << 32);
            self.binop(Operator::I64Or, pay, tag, Type::I64)
        };

        let (reprs, vals) = self.diamond_snapshot();
        let top_off = self.operand_base + 8 * u32::try_from(reprs.len()).unwrap();

        let resolve_blk = self.body.add_block();
        let helper_blk = self.body.add_block();
        let hit_blk = self.body.add_block();
        let merge = self.body.add_block();
        let op_params = self.diamond_params(merge, &reprs);
        let res_param = self.body.add_blockparam(merge, Type::I64);
        let ok_param = self.body.add_blockparam(merge, Type::I32);

        self.cond_br(hit, hit_blk, resolve_blk);

        // Cold: re-resolve (leaf, no GC). Zero => not cacheable => helper.
        self.cur = resolve_blk;
        let bid_v = self.i32_const(bid);
        let entry1 = self.call_i32(self.helpers.resolve_global_slot_guarded, &[self.cx, bid_v]);
        let resolved1 = self.binop(Operator::I32And, entry1, one_c, Type::I32);
        self.cond_br(resolved1, hit_blk, helper_blk);

        // Hit / resolved: the binding object is the global object.
        self.cur = hit_blk;
        let one_i = self.i32_const(1);
        let mut fast_args = vals.clone();
        fast_args.push(global_boxed);
        fast_args.push(one_i);
        self.body.set_terminator(
            hit_blk,
            Terminator::Br {
                target: BlockTarget {
                    block: merge,
                    args: fast_args,
                },
            },
        );

        // Not cacheable: spill, helper bind (writes the env to *top),
        // reload.
        self.cur = helper_blk;
        let arm_st = self.arm_state();
        let n = self.spill_all();
        let atom_v = self.i32_const(atom_id);
        let top = self.add_offset(self.vp, top_off);
        let bug = self.helpers.bind_unqualified_gname;
        let ok = self.call_i32(bug, &[self.cx, top, atom_v]);
        let slow_res = self.load_i64(self.vp, top_off);
        match slow_cont {
            Some(next_pc) => {
                self.reload(n);
                self.branch_on_err(ok);
                self.push_boxed(slow_res, bottom_ty());
                let target = self.dirty_edge_to(Pc::new(next_pc));
                self.body
                    .set_terminator(self.cur, Terminator::Br { target });
                self.arm_restore(arm_st);
            }
            None => {
                let slow_tail = self.cur;
                let mut margs = self.diamond_slow_args(&reprs);
                margs.push(slow_res);
                margs.push(ok);
                self.body.set_terminator(
                    slow_tail,
                    Terminator::Br {
                        target: BlockTarget {
                            block: merge,
                            args: margs,
                        },
                    },
                );
            }
        }

        self.cur = merge;
        self.diamond_rebind(&op_params);
        for (i, &r) in reprs.iter().enumerate() {
            self.stack[i].repr = r;
        }
        self.branch_on_err(ok_param);
        self.push_boxed(res_param, self.def_type(pc, 0));
    }

    /// `SetGName`/`SetName` (+ strict): `[env, value] -> [value]`. The
    /// inline global-slot fast path stores directly to the global
    /// (ignoring the bound `env`), sound only for the qualified forms;
    /// unqualified `SetName` under a dynamic scope forces the generic
    /// env-walking helper.
    pub(super) fn emit_set_name(
        &mut self,
        name_index: u32,
        strict: bool,
        unqualified: bool,
        slow_cont: Option<u32>,
    ) -> Result<(), String> {
        let name = self.name_for(name_index)?;
        let atom_id = self.atoms.intern(name);
        if !unqualified && !self.is_global && !self.outline_generic() {
            if let Some(&bid) = self.ctx.syn_gnames.get(&name) {
                // A name with a compile-time literal fuse must have that
                // fuse arm/blow maintained inline (the generic set_name
                // does it via MaybeGnameFuse) -- else the read-side fuse
                // silently disables.
                let fuse = self.ctx.fused_gnames.get(&name).copied();
                let claim = self.ctx.facts.gname_types.get(&name).copied();
                let val = self.pop()?;
                let env = self.pop()?;
                let val_boxed = self.to_boxed(&val);
                let env_boxed = self.to_boxed(&env);
                self.push_ranged(val_boxed, Repr::Boxed, val.ty, val.range);
                self.emit_set_name_inline_guarded(
                    bid, atom_id, strict, val_boxed, env_boxed, fuse, slow_cont, claim,
                );
                return Ok(());
            }
        }
        let val = self.pop()?;
        let env = self.pop()?;
        let val_boxed = self.to_boxed(&val);
        let env_boxed = self.to_boxed(&env);
        // The value stays on the stack; push it so it is spilled+reloaded
        // too.
        self.push_ranged(val_boxed, Repr::Boxed, val.ty, val.range);
        let atom_v = self.i32_const(atom_id);
        let strict_v = self.i32_const(u32::from(strict));
        let sn = self.helpers.set_name;
        self.rt_call(sn, false, |_, _| {
            vec![env_boxed, atom_v, val_boxed, strict_v]
        });
        self.kill_gcells();
        Ok(())
    }

    /// Shape-guarded inline `SetGName` global-object slot store: guard
    /// the cached (`gGlobalSlots`) entry against the live global shape; on
    /// hit / cold resolve store into the binding's own data slot with the
    /// engine's pre+post write barriers and blow the per-binding value fuse
    /// exactly as the generic `set_name` does. A non-cacheable name
    /// (lexical shadow, accessor, undeclared) falls to the generic helper,
    /// which re-derives everything from the (real) env. The value stays on
    /// the stack (def == use); `val_boxed` was already re-pushed.
    pub(super) fn emit_set_name_inline_guarded(
        &mut self,
        bid: u32,
        atom_id: u32,
        strict: bool,
        val_boxed: Value,
        env_boxed: Value,
        fuse: Option<FusedGname>,
        slow_cont: Option<u32>,
        claim: Option<Claim>,
    ) {
        let (entry0, global, live_shape, one_c, hit) = self.emit_gname_slot_prologue(bid);

        let (reprs, vals) = self.diamond_snapshot();
        let top_off = self.operand_base + 8 * u32::try_from(reprs.len()).unwrap();

        let resolve_blk = self.body.add_block();
        let helper_blk = self.body.add_block();
        let use_blk = self.body.add_block();
        let entry_param = self.body.add_blockparam(use_blk, Type::I32);
        let merge = self.body.add_block();
        let op_params = self.diamond_params(merge, &reprs);
        let ok_param = self.body.add_blockparam(merge, Type::I32);

        // The write arm additionally requires the entry's writable bit
        // (bit2): a non-writable own data slot must take the generic helper
        // for the sloppy-ignore / strict-throw semantics.
        let two_c = self.i32_const(2);
        let w0 = {
            let sh = self.binop(Operator::I32ShrU, entry0, two_c, Type::I32);
            self.binop(Operator::I32And, sh, one_c, Type::I32)
        };
        let hit_w = self.binop(Operator::I32And, hit, w0, Type::I32);
        self.body.set_terminator(
            self.cur,
            Terminator::CondBr {
                cond: hit_w,
                if_true: BlockTarget {
                    block: use_blk,
                    args: vec![entry0],
                },
                if_false: BlockTarget {
                    block: resolve_blk,
                    args: vec![],
                },
            },
        );

        // Cold: re-resolve (leaf). A zero entry means "not cacheable" ->
        // the generic helper; a resolved non-writable entry does too.
        self.cur = resolve_blk;
        let bid_v = self.i32_const(bid);
        let entry1 = self.call_i32(self.helpers.resolve_global_slot_guarded, &[self.cx, bid_v]);
        let resolved1 = self.binop(Operator::I32And, entry1, one_c, Type::I32);
        let w1 = {
            let sh = self.binop(Operator::I32ShrU, entry1, two_c, Type::I32);
            self.binop(Operator::I32And, sh, one_c, Type::I32)
        };
        let resolved1_w = self.binop(Operator::I32And, resolved1, w1, Type::I32);
        self.body.set_terminator(
            resolve_blk,
            Terminator::CondBr {
                cond: resolved1_w,
                if_true: BlockTarget {
                    block: use_blk,
                    args: vec![entry1],
                },
                if_false: BlockTarget {
                    block: helper_blk,
                    args: vec![],
                },
            },
        );

        // Hit / resolved: store into the live global's slot with barriers,
        // blow the value fuse. The resolve leaf never moves objects, so
        // `global` and `live_shape` from the entry block stay valid.
        self.cur = use_blk;
        let slot_addr = self.gname_entry_slot_addr(global, entry_param);
        self.emit_pre_write_barrier_addr(slot_addr);
        let st = self.store_i64(slot_addr, 0, val_boxed);
        self.eff(st, Eff::Write(HeapKind::Slot));
        // Absolute slot for the post-barrier: idx = entry>>3 (v2 encoding);
        // if dynamic add the global's numFixedSlots.
        let three_c = self.i32_const(3);
        let idx = self.binop(Operator::I32ShrU, entry_param, three_c, Type::I32);
        let is_dyn = {
            let sh1 = self.binop(Operator::I32ShrU, entry_param, one_c, Type::I32);
            self.binop(Operator::I32And, sh1, one_c, Type::I32)
        };
        let nfixed = {
            let imm = self.load_i32(live_shape, SHAPE_IMMUTABLE_FLAGS_OFFSET);
            let shift = self.i32_const(SHAPE_FIXED_SLOTS_SHIFT);
            let sh = self.binop(Operator::I32ShrU, imm, shift, Type::I32);
            let mask = self.i32_const(SHAPE_FIXED_SLOTS_MASK_BITS);
            self.binop(Operator::I32And, sh, mask, Type::I32)
        };
        let idx_plus = self.binop(Operator::I32Add, idx, nfixed, Type::I32);
        let abs_slot = self.select(Type::I32, idx_plus, idx, is_dyn);
        let global_boxed = {
            let pay = self.unop(Operator::I64ExtendI32U, global, Type::I64);
            let tag = self.boxed_const(TAG_OBJECT << 32);
            self.binop(Operator::I64Or, pay, tag, Type::I64)
        };
        self.emit_post_write_barrier(global_boxed, abs_slot, val_boxed);
        self.emit_blow_binding_value_fuse(bid, val_boxed);
        self.emit_bind_epoch_bump();
        // Maintain the read-side literal fuse (the reactor's gname-fuse
        // handshake): a write of the predicted literal arms it (0->1); any
        // other value blows it (->2). Arming after the store is sound here
        // because the guarded raw slot store above cannot throw.
        if let Some(FusedGname {
            fuse_addr,
            boxed: literal,
        }) = fuse
        {
            let fb = self.i32_const(fuse_addr);
            let f = self.load_i32(fb, 0);
            self.eff(f, Eff::ReadBits(HeapKind::FuseCell));
            let lit = self.boxed_const(literal);
            let neq = self.binop(Operator::I64Ne, val_boxed, lit, Type::I32);
            let zero = self.i32_const(0);
            let is_zero = self.binop(Operator::I32Eq, f, zero, Type::I32);
            let one = self.i32_const(1);
            let two = self.i32_const(2);
            let armed = self.select(Type::I32, one, f, is_zero); // f==0 ? 1 : f
            let new_f = self.select(Type::I32, two, armed, neq); // neq ? 2 : armed
            let st = self.store_i32(fb, 0, new_f);
            self.tag_store(st, HeapKind::FuseCell);
        }
        // The barrier / fuse helpers split blocks, so terminate the current
        // block (not use_blk) into the merge.
        let one_i = self.i32_const(1);
        let mut fast_args = vals.clone();
        fast_args.push(one_i);
        let fast_tail = self.cur;
        self.body.set_terminator(
            fast_tail,
            Terminator::Br {
                target: BlockTarget {
                    block: merge,
                    args: fast_args,
                },
            },
        );

        // Not cacheable: spill (rooting), the generic set_name (which
        // manages the fuses + resolves the real binding object from the
        // env), reload.
        self.cur = helper_blk;
        let arm_st = self.arm_state();
        let n = self.spill_all();
        let atom_v = self.i32_const(atom_id);
        let strict_v = self.i32_const(u32::from(strict));
        let top = self.add_offset(self.vp, top_off);
        let sn = self.helpers.set_name;
        let ok = self.call_i32(sn, &[self.cx, top, env_boxed, atom_v, val_boxed, strict_v]);
        match slow_cont {
            Some(next_pc) => {
                self.reload(n);
                self.branch_on_err(ok);
                let target = self.dirty_edge_to(Pc::new(next_pc));
                self.body
                    .set_terminator(self.cur, Terminator::Br { target });
                self.arm_restore(arm_st);
            }
            None => {
                let mut margs = self.diamond_slow_args(&reprs);
                margs.push(ok);
                let slow_tail = self.cur;
                self.body.set_terminator(
                    slow_tail,
                    Terminator::Br {
                        target: BlockTarget {
                            block: merge,
                            args: margs,
                        },
                    },
                );
            }
        }

        self.cur = merge;
        self.diamond_rebind(&op_params);
        for (i, &r) in reprs.iter().enumerate() {
            self.stack[i].repr = r;
        }
        self.branch_on_err(ok_param);
        // Per-lineage accounting: every merge predecessor stored the
        // global's slot (the receiver is the global object, never `this`),
        // and a binding was written.
        self.or_flags_const(FLAG_MUT_OTHER | FLAG_BIND);
        // The binding facts. With the helper arm on its own Dirty
        // continuation (`slow_cont`), every merge predecessor stored the
        // stored value into THIS binding's own data slot and nothing else:
        // the other bindings' facts stand, and this one becomes the stored
        // value's tag fact (the value operand is the stack top) -- for a
        // fact-carrying binding; a binding outside the population just
        // loses whatever it had. The merge form (no continuation) reaches
        // the generic helper, which can run a setter: everything dies.
        if slow_cont.is_some() {
            if !self.gen_only && self.ctx.gcell_bids.contains(&bid) {
                self.install_gcell(bid, claim);
            } else {
                self.clear_stale_src(SlotRef::GCell(bid));
                self.gcells_ctx.retain(|(x, _)| *x != bid);
            }
        } else {
            self.kill_gcells();
        }
    }
}
