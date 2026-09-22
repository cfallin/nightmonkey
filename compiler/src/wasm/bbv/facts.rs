/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! What an emitted op does to the proven state: the sig2 flags word, effect
//! classification, fact kills, and the store duty (stamp checks and chokes).

use super::*;

impl<'a> Bbv<'a> {
    /// Whether the accumulator is threaded in this body (demanded
    /// scan-passing, non-gen rung).
    pub(super) fn flags_threading(&self) -> bool {
        self.flags_on && !self.gen_only
    }

    /// Materialize the tri-state to an i32 (edges and merges only).
    pub(super) fn materialize_flags(&mut self) -> Value {
        match self.cur_flags {
            FlagsAcc::Const(c) => self.i32_const(c),
            FlagsAcc::Dyn(v, 0) => v,
            FlagsAcc::Dyn(v, b) => {
                let bv = self.i32_const(b);
                self.binop(Operator::I32Or, v, bv, Type::I32)
            }
        }
    }

    /// The extra edge arg carrying the accumulator (None when this body
    /// does not thread it).
    pub(super) fn flags_edge_arg(&mut self) -> Option<Value> {
        self.flags_threading().then(|| self.materialize_flags())
    }

    /// [ok] plus the flags edge arg -- the call-op merge signature.
    pub(super) fn merge_args(&mut self, ok: Value) -> Vec<Value> {
        let mut v = vec![ok];
        if let Some(f) = self.flags_edge_arg() {
            v.push(f);
        }
        v
    }

    /// The body's proto-proof cell (see `proto_on`), or None when the
    /// body keeps none.
    pub(super) fn proto_cell(&mut self) -> Option<Value> {
        if !self.proto_on || self.gen_only {
            return None;
        }
        let idx = match self.proto_cell_idx {
            Some(i) => i,
            None => {
                let i = if self.mode == EmitMode::Code {
                    self.atoms.next_prop_cache()
                } else {
                    0
                };
                self.proto_cell_idx = Some(i);
                i
            }
        };
        let cell = self.i32_const(IC_WAY_ADDR_PLACEHOLDER);
        self.prop_ic_patches.push((cell, idx * INLINE_IC_STRIDE));
        Some(cell)
    }

    /// Invalidate the proto-proof cell: its receiver word is the validity
    /// marker (a zero matches no live object).
    pub(super) fn kill_proto_cell(&mut self) {
        if let Some(cell) = self.proto_cell() {
            let z = self.i32_const(0);
            let st = self.store_i32(cell, PROTO_CELL_RECV, z);
            self.effects.insert(st, Eff::Write(HeapKind::EngineTable));
        }
    }

    /// The receiver scope of the static add check: the frame's own `this`
    /// (the root body's `this` slot or a proven this-alias local, or a
    /// construct splice's).
    pub(super) fn recv_is_own_this(&self, recv: &Operand) -> bool {
        match self.cur_seg {
            None => self.store_recv_is_this(recv),
            Some(i) => {
                self.segs[i].is_construct
                    && match recv.src {
                        Some(SlotRef::This) => true,
                        Some(SlotRef::Local(n)) => self.segs[i].this_alias_locals.contains(&n),
                        _ => false,
                    }
            }
        }
    }

    /// Ops that can reshape an EXISTING object without a helper call the
    /// effect table would classify (helper paths kill through
    /// `note_call_eff` / `kill_cls_facts`; `SetProp` handles its own
    /// receiver). Conservative: every store-family op that is not a
    /// `this` property store, every call, and every environment/scope op.
    pub(super) fn op_kills_proto_cell(op: JSOp) -> bool {
        use JSOp::*;
        !matches!(
            op,
            Undefined
                | Null
                | False
                | True
                | Int32
                | Zero
                | One
                | Int8
                | Uint16
                | Uint24
                | Double
                | BigInt
                | String
                | Symbol
                | Void
                | Typeof
                | TypeofExpr
                | TypeofEq
                | Pos
                | Neg
                | BitNot
                | Not
                | BitOr
                | BitXor
                | BitAnd
                | Eq
                | Ne
                | StrictEq
                | StrictNe
                | StrictConstantEq
                | StrictConstantNe
                | Lt
                | Gt
                | Le
                | Ge
                | Lsh
                | Rsh
                | Ursh
                | Add
                | Sub
                | Inc
                | Dec
                | Mul
                | Div
                | Mod
                | Pow
                | NopIsAssignOp
                | ToNumeric
                | ToString
                | IsNullOrUndefined
                | GlobalThis
                | NewInit
                | NewObject
                | Object
                | InitProp
                | InitHiddenProp
                | InitLockedProp
                | InitElem
                | InitHiddenElem
                | InitLockedElem
                | GetProp
                | GetElem
                | SetProp
                | StrictSetProp
                | NewArray
                | InitElemArray
                | InitElemInc
                | Hole
                | Lambda
                | IsConstructing
                | JumpTarget
                | LoopHead
                | Goto
                | JumpIfFalse
                | JumpIfTrue
                | And
                | Or
                | Coalesce
                | Case
                | Default
                | TableSwitch
                | Return
                | GetRval
                | SetRval
                | RetRval
                | CheckReturn
                | InitLexical
                | CheckLexical
                | CheckAliasedLexical
                | CheckThis
                | GetName
                | GetGName
                | GetArg
                | GetFrameArg
                | GetLocal
                | ArgumentsLength
                | GetActualArg
                | GetAliasedVar
                | GetIntrinsic
                | Callee
                | SetArg
                | SetLocal
                | SetAliasedVar
                | Arguments
                | Rest
                | FunctionThis
                | Pop
                | PopN
                | Dup
                | Dup2
                | DupAt
                | Swap
                | Pick
                | Unpick
                | Nop
                | Lineno
                | NopDestructuring
        )
    }

    /// OR a dynamic word (a callee's returned flags) into the lineage.
    pub(super) fn or_flags_word(&mut self, w: Value) {
        if !self.flags_threading() {
            // A body with no accumulator cannot record a callee's word, so
            // its compile-time return constant is a lie from here on.
            self.untracked_flags |= FLAGS_ALL;
            return;
        }
        self.cur_flags = match self.cur_flags {
            FlagsAcc::Const(FLAGS_ALL) => FlagsAcc::Const(FLAGS_ALL),
            FlagsAcc::Const(c) => FlagsAcc::Dyn(w, c),
            FlagsAcc::Dyn(v, b) => FlagsAcc::Dyn(self.binop(Operator::I32Or, v, w, Type::I32), b),
        };
    }

    /// OR a compile-time word into the lineage (an inline store arm's
    /// classified MUT bit). Free in Const state; mints one I32Or in the
    /// current block in Dyn state -- callers must sit at a point that
    /// dominates the lineage's continuation (op-level fall-through or a
    /// post-diamond merge, never inside a Br-to-merge sibling arm).
    pub(super) fn or_flags_const(&mut self, bits: u32) {
        if bits == 0 {
            return;
        }
        if !self.flags_threading() {
            self.untracked_flags |= bits;
            return;
        }
        self.cur_flags = match self.cur_flags {
            FlagsAcc::Const(c) => FlagsAcc::Const(c | bits),
            FlagsAcc::Dyn(v, b) => FlagsAcc::Dyn(v, b | bits),
        };
    }

    /// A leaf writer helper's contribution (aliased vars, iterator and
    /// generator state -- never an own-this store). In Const state the OR
    /// is free and exact; in Dyn state saturate instead of minting an OR:
    /// note_call_eff fires inside in-version merge arms where a minted
    /// value would escape its dominance region (the section-Z trap).
    pub(super) fn or_flags_leaf_write(&mut self) {
        if !self.flags_threading() {
            self.untracked_flags |= FLAG_MUT_OTHER;
            return;
        }
        self.cur_flags = match self.cur_flags {
            FlagsAcc::Const(c) => FlagsAcc::Const(c | FLAG_MUT_OTHER),
            // The overlay makes this precise: no mint, no dominance
            // escape, and no saturation -- a leaf write is MUT_OTHER and
            // nothing else (in particular never FLAG_STAMPS: env, iterator
            // and generator state is not stamp-claimed).
            FlagsAcc::Dyn(v, b) => FlagsAcc::Dyn(v, b | FLAG_MUT_OTHER),
        };
    }

    /// Saturate the lineage (an unconditional effect: may-GC helper,
    /// construct merge). Pure state -- no code.
    pub(super) fn or_flags_all(&mut self) {
        if self.flags_threading() {
            self.cur_flags = FlagsAcc::Const(FLAGS_ALL);
        } else {
            self.untracked_flags |= FLAGS_ALL;
        }
    }

    /// Translate a callee's returned flags word into this frame's
    /// perspective before it joins the accumulator or a fork test: the
    /// callee's MUT_THIS names the callee's `this`, which is this frame's
    /// `this` only when the call receiver provably IS it (SlotRef::This
    /// provenance, root frame only -- a segment's `this` is not the
    /// root's). Everywhere else an own-this write by the callee is a write
    /// to some other object from here: fold MUT_THIS into MUT_OTHER.
    /// fold(w) == 0 iff w == 0, so clean tests are unaffected.
    pub(super) fn fold_callee_flags(&mut self, w: Value, recv_bit: u32) -> Value {
        if recv_bit == FLAG_MUT_THIS || !self.flags_threading() {
            return w;
        }
        if recv_bit == 0 {
            // Fresh receiver: the callee's own-this writes hit an object
            // no caller fact can reference -- drop MUT_THIS entirely.
            // FLAG_STAMPS and FLAG_BIND are receiver-independent and ride
            // through.
            let m = self.i32_const(FLAG_MUT_OTHER | FLAG_STAMPS | FLAG_BIND);
            return self.binop(Operator::I32And, w, m, Type::I32);
        }
        const _: () = assert!(FLAG_MUT_OTHER == FLAG_MUT_THIS << 1);
        let one = self.i32_const(1);
        let sh = self.binop(Operator::I32Shl, w, one, Type::I32);
        let or = self.binop(Operator::I32Or, w, sh, Type::I32);
        let m = self.i32_const(FLAG_MUT_OTHER | FLAG_STAMPS | FLAG_BIND);
        self.binop(Operator::I32And, or, m, Type::I32)
    }

    // --- the per-binding value facts (`Ctx::gcells`) ----------------------

    /// The binding's `gGlobalVals` cell: `[value i64][fuse word i32][..]`.
    fn gcell_addr(&mut self, bid: u32) -> Value {
        self.i32_const(self.helpers.global_vals_base + 16 * bid)
    }

    /// The cell's value word (a boxed Value; the binding's value only while
    /// the fuse is armed).
    pub(super) fn gcell_value_load(&mut self, bid: u32) -> Value {
        let base = self.gcell_addr(bid);
        let v = self.load_i64(base, 0);
        self.eff(v, Eff::Read(HeapKind::FuseCell));
        v
    }

    /// `fuse word == 1`: the cell mirrors the binding's slot.
    pub(super) fn gcell_armed(&mut self, bid: u32) -> Value {
        let base = self.gcell_addr(bid);
        let fw = self.load_i32(base, 8);
        self.eff(fw, Eff::ReadBits(HeapKind::FuseCell));
        let one = self.i32_const(1);
        self.binop(Operator::I32Eq, fw, one, Type::I32)
    }

    /// The binding's current value for a re-proof: the armed cell inline
    /// (a binding write in a callee is usually a write-through of a
    /// primitive -- earley-boyer's counters -- that leaves the cell armed,
    /// so the common re-proof is two loads and a tag test), else the leaf
    /// `night_runtime_binding_value` (guarded resolve, which refills the
    /// row and re-arms the cell so a major GC's zeroing costs one call and
    /// not a GEN body that never re-arms, then the slot; a name it can no
    /// longer serve -- deleted, redefined, shadowed since the snapshot --
    /// comes back as a magic Value). Emits a diamond; leaves `self.cur` at
    /// its merge and returns `(boxed value, ok)`.
    pub(super) fn gcell_current_value(&mut self, _pc: Pc, bid: u32) -> (Value, Value) {
        let merge = self.body.add_block();
        let val_param = self.body.add_blockparam(merge, Type::I64);
        let ok_param = self.body.add_blockparam(merge, Type::I32);
        let armed = self.gcell_armed(bid);
        let cell_blk = self.body.add_block();
        let leaf_blk = self.body.add_block();
        self.cond_br(armed, cell_blk, leaf_blk);
        self.cur = cell_blk;
        let v = self.gcell_value_load(bid);
        let one = self.i32_const(1);
        self.body.set_terminator(
            self.cur,
            Terminator::Br {
                target: BlockTarget {
                    block: merge,
                    args: vec![v, one],
                },
            },
        );
        self.cur = leaf_blk;
        let bid_v = self.i32_const(bid);
        let lv = self.call_i64(self.helpers.binding_value, &[self.cx, bid_v]);
        let is_magic = self.tag_eq(lv, TAG_MAGIC as u32);
        let lok = self.unop(Operator::I32Eqz, is_magic, Type::I32);
        self.body.set_terminator(
            self.cur,
            Terminator::Br {
                target: BlockTarget {
                    block: merge,
                    args: vec![lv, lok],
                },
            },
        );
        self.cur = merge;
        (val_param, ok_param)
    }

    /// The tracked fact for binding `bid`, TOP when none.
    pub(super) fn gcell_fact(&self, bid: u32) -> SlotCtx {
        self.gcells_ctx
            .iter()
            .find(|(x, _)| *x == bid)
            .map_or(SlotCtx::TOP, |(_, s)| *s)
    }

    /// Record binding `bid`'s value fact from the operand on top of the
    /// stack (a `GetGName` read that just passed its tag ladder, or a
    /// store's value) and mark the operand as sourced from the cell. The
    /// fact is the ANALYSIS's claim for the binding (`gname_types`), never
    /// the operand's own, narrower type: the claim is the join of every
    /// write the analysis sees, so a callee's legitimate write keeps it
    /// true where a fact minted from one stored literal (`x = null`, then a
    /// callee stores an object) would fail its re-proof at every call and
    /// send the lineage to GEN. No claim, or an operand that does not
    /// imply it: no fact.
    pub(super) fn install_gcell(&mut self, bid: u32, claim: Option<Claim>) {
        self.clear_stale_src(SlotRef::GCell(bid));
        self.gcells_ctx.retain(|(x, _)| *x != bid);
        let Some(top) = self.stack.last() else {
            return;
        };
        let Some(want) = claim.and_then(claim_shape).map(claim_slot_ctx) else {
            return;
        };
        if want.is_top() || !top.slot_cell().implies_sans_iv(&want) {
            return;
        }
        if let Some(top) = self.stack.last_mut() {
            top.src = Some(SlotRef::GCell(bid));
        }
        self.gcells_ctx.push((bid, want));
        self.gcells_ctx.sort_by_key(|(x, _)| *x);
    }

    /// A global binding was written by this body (any `SetGName`-family
    /// store): every binding fact dies. The generic form can reach a
    /// setter, which can write anything, so the kill is not per binding.
    pub(super) fn kill_gcells(&mut self) {
        for o in &mut self.stack {
            if matches!(o.src, Some(SlotRef::GCell(_))) {
                o.src = None;
            }
        }
        self.gcells_ctx.clear();
    }

    /// A keep continuation's duty to its binding facts: the callee's word
    /// (`word`, None for a helper that may have run user code) says whether
    /// a binding may have been written; if so, every carried binding fact
    /// is re-proven on the spot -- the current value's tag -- and a failing
    /// proof sends the lineage to GEN at `next_pc` (the same landing the
    /// fork's dirty arm takes). Call with the stack already in `next_pc`'s
    /// shape, right before the continuation edge is built. The binding
    /// facts are the one carried thing neither the stamp word nor the
    /// epoch covers: a binding is a slot of the global object, not a
    /// claimed layout, so a callee that reassigns one moves no stamp.
    pub(super) fn gcells_keep(
        &mut self,
        word: Option<Value>,
        pre_bind: Option<Value>,
        next_pc: Pc,
    ) {
        if self.gcells_ctx.is_empty() {
            return;
        }
        // Admission, cheapest first: the callee's word with FLAG_BIND clear
        // (no binding written anywhere below), else the binding epoch
        // unchanged across the call (the runtime truth that also covers
        // helpers, which return no word). Only a lineage neither admits
        // re-proves its facts one by one.
        let cont_blk = self.body.add_block();
        let chk_blk = self.body.add_block();
        let mut admit: Option<Value> = None;
        if let Some(w) = word {
            let bm = self.i32_const(FLAG_BIND);
            let bb = self.binop(Operator::I32And, w, bm, Type::I32);
            admit = Some(self.unop(Operator::I32Eqz, bb, Type::I32));
        }
        if let Some(pre) = pre_bind {
            let post = self.emit_bind_epoch_read();
            let same = self.binop(Operator::I32Eq, pre, post, Type::I32);
            admit = Some(match admit {
                Some(a) => self.binop(Operator::I32Or, a, same, Type::I32),
                None => same,
            });
        }
        match admit {
            Some(a) => self.cond_br(a, cont_blk, chk_blk),
            None => self.body.set_terminator(
                self.cur,
                Terminator::Br {
                    target: BlockTarget {
                        block: chk_blk,
                        args: vec![],
                    },
                },
            ),
        }
        self.cur = chk_blk;
        self.emit_guard_census(census::GCELL_RECHECK, next_pc);
        // Track census twins (kinds 63/64: re-proof entered / failed), so
        // the population is readable on the benches whose guard census
        // OOMs.
        self.emit_census(63, self.root_source_id, next_pc);
        let facts = self.gcells_ctx.clone();
        let mut ok: Option<Value> = None;
        for (bid, fact) in &facts {
            let (v, have) = self.gcell_current_value(next_pc, *bid);
            let tag_ok = self.proof_tag_cond(v, fact);
            let c = self.binop(Operator::I32And, have, tag_ok, Type::I32);
            ok = Some(match ok {
                Some(p) => self.binop(Operator::I32And, p, c, Type::I32),
                None => c,
            });
        }
        let fail_blk = self.body.add_block();
        self.cond_br(ok.expect("at least one binding fact"), cont_blk, fail_blk);
        self.cur = fail_blk;
        self.emit_census(64, self.root_source_id, next_pc);
        let st = self.arm_state();
        self.kill_gcells();
        let target = self.dirty_edge_to(next_pc);
        self.body
            .set_terminator(self.cur, Terminator::Br { target });
        self.arm_restore(st);
        self.cur = cont_blk;
    }

    /// Tag an emitted value's effect (side table). User-heap writes
    /// (anything but engine-table/fuse-cell rows) also set the body-wide
    /// classified write bits: the clean-ret scan cannot see spliced
    /// callees' inline stores, so emission is the accounting of record.
    /// This form is the
    /// conservative default (MUT_OTHER); store arms whose receiver is
    /// provably the root frame's `this` use `eff_this`.
    pub(super) fn eff(&mut self, v: Value, e: Eff) -> Value {
        if let Eff::Write(k) = e {
            if !matches!(k, HeapKind::EngineTable | HeapKind::FuseCell) {
                self.wrote_other = true;
            }
        }
        if self.opts.diagnostics.viz
            && self.mode == EmitMode::Code
            && matches!(e, Eff::Read(_) | Eff::ReadBits(_))
        {
            let sfx = format!(
                "pc {} lpc {} site {} path {}",
                self.cur_pc,
                self.evid_pc(self.cur_pc),
                self.viz_site(self.cur_pc),
                self.viz_path(self.cur_pc),
            );
            self.load_pcs.insert(v, sfx);
        }
        self.effects.insert(v, e);
        v
    }

    /// Tag-only Write recording (side table), without the `eff` flags
    /// accounting: for stores whose MUT contribution is settled elsewhere
    /// or does not apply (fast-arm stores under scoped or_flags, engine
    /// rows, fresh-object init, fuse blows). Never changes codegen or the
    /// clean-ret accounting -- the effects map feeds LICM only.
    pub(super) fn tag_store(&mut self, v: Value, k: HeapKind) -> Value {
        self.effects.insert(v, Eff::Write(k));
        v
    }

    /// `eff` for a store whose receiver classification the caller settled:
    /// `this_recv` = the receiver is the root frame's own `this`
    /// (SlotRef::This provenance and not inside a spliced segment -- a
    /// segment's `this` is some other object from the root's perspective).
    pub(super) fn eff_store(&mut self, v: Value, e: Eff, recv_bit: u32) -> Value {
        match recv_bit {
            0 => {
                self.effects.insert(v, e);
                v
            }
            FLAG_MUT_THIS => {
                self.wrote_this = true;
                self.effects.insert(v, e);
                v
            }
            _ => self.eff(v, e),
        }
    }

    /// The receiver classification for a store op about to be emitted:
    /// own-this only via provenance (the `this` slot itself, or a proven
    /// this-alias local -- `var __this = this`), never op shape, and never
    /// inside a segment (the flags word describes the root body's frame,
    /// and a segment's `this`/locals are the callee's).
    pub(super) fn store_recv_is_this(&self, recv: &Operand) -> bool {
        self.cur_seg.is_none()
            && match recv.src {
                Some(SlotRef::This) => true,
                Some(SlotRef::Local(n)) => self.this_alias_locals.contains(&n),
                _ => false,
            }
    }

    /// The store's classified MUT contribution: 0 for a fresh receiver
    /// (allocated during this frame -- no caller fact can reference it,
    /// A.4), MUT_THIS for the frame's own `this`, else MUT_OTHER.
    pub(super) fn store_recv_bit(&self, recv: &Operand) -> u32 {
        if recv.fresh {
            0
        } else if self.store_recv_is_this(recv) {
            FLAG_MUT_THIS
        } else {
            FLAG_MUT_OTHER
        }
    }

    /// Record a direct helper call's effect class (effects.rs table).
    /// A may-GC call sets the `post_call` accumulator, which `side_arm`
    /// reads to decide whether an arm's continuation is a DIRTY lineage,
    /// and kills every durable class fact (user JS can restamp or clear
    /// any object's class word).
    ///
    /// It does NOT step the track: killing facts weakens the prediction
    /// downstream, which is not the same thing as leaving the Opt track.
    /// See `Track`.
    pub(super) fn note_call_eff(&mut self, v: Value, func: Func) {
        let meta = self
            .helper_meta
            .get(&func)
            .copied()
            .unwrap_or(HelperMeta::UNLISTED);
        if meta.user_heap_writes {
            // Leaf writers target env/iterator/generator state -- never an
            // own-this store: MUT_OTHER, body-wide and per-lineage.
            self.wrote_other = true;
            self.or_flags_leaf_write();
        }
        let e = match meta.effect {
            EffectClass::Pure => Eff::CallPure,
            EffectClass::Leaf => Eff::CallLeaf(meta.leaf_writes),
            EffectClass::Alloc | EffectClass::Unknown => Eff::CallGc,
        };
        // A quiet alloc may GC, but a GC invalidates raw pointers only --
        // every ctx fact is a property of the value and moves with the
        // object, no user code runs, and nothing pre-existing is written.
        // So quiet allocs neither
        // saturate the word, nor step the track, nor kill facts; they
        // sweep raw-pointer carriers (the frame slot is the GC-updated
        // truth) and the fork restores reload the rest. Non-quiet
        // Alloc/Unknown helpers keep the full conservative treatment.
        // The sig2 scripted paths are exempt from the saturation: their
        // callee's own returned word is the truth and is OR'd at the
        // call (call_abi2 / call_indirect_abi2).
        let quiet = e == Eff::CallGc && meta.quiet;
        if e == Eff::CallGc && func != self.helpers.direct_call_stub2 && !quiet {
            // Saturation stays: note_call_eff fires inside merge-back arms
            // where any minted word escapes its dominance region (the
            // section-Z trap), so a per-helper runtime bridge cannot ride
            // the persistent accumulator. The FORK-SITE epoch comparison
            // (emit_flag_fork) recovers the precision instead: it samples
            // on the op's main line and covers everything the callee did,
            // helpers included.
            self.or_flags_all();
        }
        if quiet {
            self.kill_carriers();
        } else if e == Eff::CallGc {
            if self.opts.diagnostics.bbv && self.cur_track != Track::Dirty {
                use super::effects::helper_name;
                crate::diag_line!(
                    "night: bbv dirties sid#{} pc {} op {:?} helper {} track {:?} seg {:?} evid {}",
                    self.source_id,
                    self.cur_pc,
                    self.cur_op,
                    helper_name(&self.helpers, func),
                    self.cur_track,
                    self.cur_seg,
                    self.evid_pc(self.cur_pc),
                );
            }
            if self.opts.diagnostics.viz
                && self.mode == EmitMode::Code
                && self.cur_track != Track::Dirty
            {
                use super::effects::helper_name;
                crate::diag_line!(
                    "night: viz dirty sid#{} pc {} lpc {} site {} path {} op {} helper {} track {:?}",
                    self.root_source_id,
                    self.cur_pc,
                    self.evid_pc(self.cur_pc),
                    self.viz_site(self.cur_pc),
                    self.viz_path(self.cur_pc),
                    self.cur_op
                        .map_or_else(|| "-".to_string(), |o| format!("{o:?}")),
                    helper_name(&self.helpers, func),
                    self.cur_track
                );
            }
            // The POP half of the downstream-census bracket the call
            // emitter's `depart_bracket` pushed; it must precede the
            // departure tick so DIRTY_ENTER lands in the CALLER's cell.
            self.emit_depart_tick(census::FRAME_POP);
            // The DYNAMIC twin of the `bbv dirties` line above: one census
            // tick on the very block that leaves the Opt track, tagged with
            // the op family that owns the transition. The static census
            // counts entrances that EXIST; only this counts entrances that
            // are TAKEN, and the two answers differ by two orders of
            // magnitude -- a miss arm behind a guard is one static entrance
            // and near-zero executions, while a scripted call on the
            // dominating path is one static entrance and all of them.
            self.emit_guard_census(
                census::DIRTY_ENTER + Self::dirty_entrance_family(self.cur_op),
                self.cur_pc,
            );
            self.post_call = true;
            self.kill_cls_facts();
            self.kill_carriers();
        }
        let e = if quiet { Eff::CallGcQuiet } else { e };
        self.effects.insert(v, e);
    }

    /// The keep-fork's failing side leaves the Opt track: the merge join
    /// of a call site that also emitted a clean or keep-facts continuation.
    ///
    /// Every arm reaching that merge was offered a runtime intactness proof
    /// and did not pass it, so the lineage conforms to nothing and belongs
    /// on GEN by ruling 1. This is the separation the fork depends on: the
    /// clean and keep arms restore the pre-call state and enter `next_pc`
    /// on Opt; unless this side leaves Opt the two share the successor's
    /// one prediction and the join erases exactly the facts the fork
    /// preserves.
    ///
    /// Stepping at every call is a worse rule: a site with no keep
    /// continuation has no Opt lineage to protect, so stepping there only
    /// costs the weakly predicted tail its Opt code and buys no
    /// separation.
    ///
    /// Not scoped, unlike `dirty_edge_to`: the merge IS the main line from
    /// here on.
    ///
    /// `next_pc` arms the just-in-time on-ramp there
    /// (`try_call_return_onramp`): the callee's word is an all-or-nothing
    /// proof about the whole heap, and failing it is not the same as
    /// contradicting anything this lineage believes. The proof gets to
    /// ask the narrower question, fact by fact, on the way out.
    pub(super) fn keep_fork_merge_stepped_track(&mut self, next_pc: Pc) {
        self.cur_track = Track::Dirty;
        self.ret_onramp_pc = Some(next_pc);
    }

    /// Op families for the dynamic Dirty-entrance census, matching the
    /// buckets the static `bbv dirties` histogram is reported in.
    fn dirty_entrance_family(op: Option<JSOp>) -> u32 {
        match op {
            Some(
                JSOp::GetProp
                | JSOp::GetPropSuper
                | JSOp::GetElem
                | JSOp::GetElemSuper
                | JSOp::GetBoundName
                | JSOp::GetGName
                | JSOp::GetName,
            ) => 0,
            Some(
                JSOp::SetProp
                | JSOp::StrictSetProp
                | JSOp::SetElem
                | JSOp::StrictSetElem
                | JSOp::InitProp
                | JSOp::InitElem
                | JSOp::SetName
                | JSOp::SetGName,
            ) => 1,
            Some(
                JSOp::Add
                | JSOp::Sub
                | JSOp::Mul
                | JSOp::Div
                | JSOp::Mod
                | JSOp::Pow
                | JSOp::Inc
                | JSOp::Dec
                | JSOp::Neg
                | JSOp::Pos
                | JSOp::BitAnd
                | JSOp::BitOr
                | JSOp::BitXor
                | JSOp::BitNot
                | JSOp::Lsh
                | JSOp::Rsh
                | JSOp::Ursh
                | JSOp::ToNumeric,
            ) => 2,
            Some(
                JSOp::Call
                | JSOp::CallIgnoresRv
                | JSOp::CallIter
                | JSOp::CallContentIter
                | JSOp::New
                | JSOp::SuperCall
                | JSOp::SpreadCall
                | JSOp::SpreadNew,
            ) => 3,
            _ => 4,
        }
    }

    /// Drop every tracked class fact (locals, args, carried caller
    /// frame, live operands) -- the CallGc kill sweep.
    pub(super) fn kill_cls_facts(&mut self) {
        self.kill_proto_cell();
        for c in self
            .locals_ctx
            .iter_mut()
            .chain(self.args_ctx.iter_mut())
            .chain(self.caller_locals_ctx.iter_mut())
            .chain(self.caller_args_ctx.iter_mut())
            .chain(
                self.outer_ctx
                    .iter_mut()
                    .flat_map(|f| f.locals.iter_mut().chain(f.args.iter_mut())),
            )
        {
            c.cls = None;
            c.cls_shallow = false;
            c.cls_slots = false;
        }
        for o in &mut self.stack {
            o.cls = None;
            o.cls_shallow = false;
            o.cls_slots = false;
        }
    }

    /// Two-bit family: drop every proven-SLOTS bit (identity and shallow
    /// facts survive) -- the sweep for inline set-IC emissions, whose
    /// add-transition replay may clear an aliased object's SLOTS bit
    /// without changing its identity half. Value stores never clear
    /// SLOTS (the chokes are TYPES-only), so plain store arms keep it.
    pub(super) fn kill_slots_facts(&mut self) {
        for c in self
            .locals_ctx
            .iter_mut()
            .chain(self.args_ctx.iter_mut())
            .chain(self.caller_locals_ctx.iter_mut())
            .chain(self.caller_args_ctx.iter_mut())
            .chain(
                self.outer_ctx
                    .iter_mut()
                    .flat_map(|f| f.locals.iter_mut().chain(f.args.iter_mut())),
            )
        {
            c.cls_slots = false;
        }
        for o in &mut self.stack {
            o.cls_slots = false;
        }
    }

    /// Drop every proven-shallow half (identity facts survive) --
    /// the sweep for non-number inline stores, which may clear an aliased
    /// object's valid-types flags without changing its identity half.
    pub(super) fn kill_shallow_facts(&mut self) {
        for c in self
            .locals_ctx
            .iter_mut()
            .chain(self.args_ctx.iter_mut())
            .chain(self.caller_locals_ctx.iter_mut())
            .chain(self.caller_args_ctx.iter_mut())
            .chain(
                self.outer_ctx
                    .iter_mut()
                    .flat_map(|f| f.locals.iter_mut().chain(f.args.iter_mut())),
            )
        {
            c.cls_shallow = false;
        }
        for o in &mut self.stack {
            o.cls_shallow = false;
        }
    }

    /// The compiled-store half of the engine's nightStoreCheckOrClear
    /// choke (JSObject.h): a non-number store through an inline arm must
    /// clear the receiver's valid-types flags half, or a later
    /// fullword/SHALLOW-guarded load misreads the field. Number test
    /// first (pure alu), then the flags-half pre-test -- the common
    /// non-number store to an unstamped object loads and tests but never
    /// writes the header. Statically numeric values elide entirely.
    /// Census-only companion to the inline clear arms: report whether
    /// `half` (the flags half of the class word) actually holds one of
    /// `mask_bits` -- the clear that follows is then a real demotion. The
    /// masked value rides as the tick's ID and the runtime advances the
    /// stamp epoch only when it is nonzero, so no branch is needed here
    /// (the callers sit mid-arm where CFG surgery is not safe).
    fn emit_demote_census(&mut self, half: Value, mask_bits: u32) {
        if !self.guard_census_on() {
            return;
        }
        let before = self.body.values.len();
        let m = self.i32_const(mask_bits);
        let b = self.binop(Operator::I32And, half, m, Type::I32);
        let k = self.i32_const(census::STAMP_DEMOTE);
        self.instrument_values += self.body.values.len() - before;
        self.emit_guard_census_dyn_id(k, b);
    }

    /// The 0/1 epoch delta for one demote arm: 1 iff `half` (the flags
    /// half) actually carries one of `mask_bits` and is not the
    /// CONSTRUCTING sentinel -- the C++ chokes' exact bump conditions. An
    /// unconditional bump here is not merely imprecise, it is a standing
    /// false "stamps broken" signal to every fork's epoch comparison: a
    /// hot no-op clear (bits already gone, or a mid-construction object)
    /// would deny the keep-facts arm to its whole call chain.
    fn demote_delta(&mut self, half: Value, mask_bits: u32) -> Value {
        let cm = self.i32_const(mask_bits);
        let bits = self.binop(Operator::I32And, half, cm, Type::I32);
        let z = self.i32_const(0);
        let has = self.binop(Operator::I32Ne, bits, z, Type::I32);
        let sm = self.i32_const(CLASS_WORD_SENTINEL >> 16);
        let sent = self.binop(Operator::I32And, half, sm, Type::I32);
        let one = self.i32_const(1);
        let d0 = self.select(Type::I32, one, z, has);
        self.select(Type::I32, z, d0, sent)
    }

    pub(super) fn emit_clear_conform_flags(&mut self, objptr: Value) {
        let half = self.load16_u(objptr, OBJ_CLASS_FLAGS_OFFSET);
        self.eff(half, Eff::ReadBits(HeapKind::ClassWord));
        let d = self.demote_delta(half, (CLASS_WORD_SHALLOW | CLASS_WORD_RANGES) >> 16);
        self.emit_epoch_bump(Some(d));
        self.emit_demote_census(half, (CLASS_WORD_SHALLOW | CLASS_WORD_RANGES) >> 16);
        // RANGES goes with it, in the same immediate. Leaving it set
        // under a cleared TYPES would be harmless while the pair is read
        // together -- but a later restamp carries the surviving bits
        // forward, and would resurrect TYPES beside a range the store
        // just violated.
        let m = self.i32_const(0xFFFF & !((CLASS_WORD_SHALLOW | CLASS_WORD_RANGES) >> 16));
        let nw = self.binop(Operator::I32And, half, m, Type::I32);
        let st = self.store16(objptr, OBJ_CLASS_FLAGS_OFFSET, nw);
        self.effects.insert(st, Eff::Write(HeapKind::ClassWord));
    }

    /// Store-side shallow-conformance maintenance for a masked field:
    /// keep the flags when the stored value IS A number (the one claim every class's checker and
    /// claimer agree on -- delegation-proof), clear them otherwise. The
    /// caller only reaches here for non-statically-numeric values.
    /// Returns the runtime stamp-break word: FLAG_STAMPS iff the clear arm
    /// runs (the value did not conform), 0 on the conforming path.
    pub(super) fn emit_conform_check_or_clear(
        &mut self,
        objptr: Value,
        boxed: Value,
        mask: Prims,
    ) -> Option<Value> {
        debug_assert!(mask != Prims::EMPTY && mask.subset_of(PRIM_INT32 | PRIM_DOUBLE));
        let conform = match mask & (PRIM_INT32 | PRIM_DOUBLE) {
            m if m == PRIM_INT32 => self.tag_eq(boxed, TAG_INT32 as u32),
            m if m == PRIM_DOUBLE => self.is_double_tag(boxed),
            _ => self.is_number_tag(boxed),
        };
        let nonconform = self.unop(Operator::I32Eqz, conform, Type::I32);
        let sel = self.demote_word(
            objptr,
            nonconform,
            (CLASS_WORD_SHALLOW | CLASS_WORD_RANGES) >> 16,
        );
        let clear_blk = self.body.add_block();
        let cont = self.body.add_block();
        self.cond_br(conform, cont, clear_blk);
        self.cur = clear_blk;
        self.emit_clear_conform_flags(objptr);
        self.body.set_terminator(
            clear_blk,
            Terminator::Br {
                target: BlockTarget {
                    block: cont,
                    args: vec![],
                },
            },
        );
        self.cur = cont;
        Some(sel)
    }

    /// Clear the SLOTS bit of the receiver's likely-class word: an add
    /// whose assigned slot deviates from the clump's predictions
    /// invalidates the baked immediates for this object (and only the
    /// bit -- TYPES, the sentinel, and the early key are independent).
    pub(super) fn emit_clear_slots_bit(&mut self, objptr: Value) {
        let half = self.load16_u(objptr, OBJ_CLASS_FLAGS_OFFSET);
        self.eff(half, Eff::ReadBits(HeapKind::ClassWord));
        let d = self.demote_delta(half, CLASS_WORD_SLOTS >> 16);
        self.emit_epoch_bump(Some(d));
        self.emit_demote_census(half, CLASS_WORD_SLOTS >> 16);
        // Site-attributed twin of the kind-65 marker (which carries only
        // the masked bits): which ADD sites actually clear SLOTS.
        if self.guard_census_on() {
            self.emit_guard_census(67, self.cur_pc);
        }
        let m = self.i32_const(0xFFFF & !(CLASS_WORD_SLOTS >> 16));
        let nw = self.binop(Operator::I32And, half, m, Type::I32);
        let st = self.store16(objptr, OBJ_CLASS_FLAGS_OFFSET, nw);
        self.effects.insert(st, Eff::Write(HeapKind::ClassWord));
    }

    /// Add-arm SLOTS maintenance emitted after a transition replay's
    /// store+swap: compare the runtime-assigned slot offset against the
    /// receiver's predictions and clear SLOTS on deviation. `slot_off` is
    /// the replay row's fixed-slot byte offset.
    /// Returns the runtime stamp-break word: FLAG_STAMPS iff the SLOTS
    /// clear arm runs. The caller gates it on receiver freshness.
    pub(super) fn emit_add_slots_check(
        &mut self,
        objptr: Value,
        slot_off: Value,
        check: AddCheck,
    ) -> Option<Value> {
        let (clear, inel) = match check {
            AddCheck::Predicted(off) => {
                let pv = self.i32_const(off);
                let ne = self.binop(Operator::I32Ne, slot_off, pv, Type::I32);
                (ne, self.i32_const(0))
            }
            AddCheck::Unpredicted { bound, own } => {
                // Below the receiver's OWN layout: the prefix bijection is
                // falsified -- clear. In `own..bound` (a clump sibling's
                // extension span): the own prefix still holds, only the
                // prefix-ADVANCE certificate dies -- keep SLOTS, mark
                // advance-ineligible, and bump nothing.
                let bv = self.i32_const(bound);
                let in_b = self.binop(Operator::I32LtU, slot_off, bv, Type::I32);
                let ov = self.i32_const(own);
                let below = self.binop(Operator::I32LtU, slot_off, ov, Type::I32);
                let not_below = self.unop(Operator::I32Eqz, below, Type::I32);
                let inel = self.binop(Operator::I32And, in_b, not_below, Type::I32);
                let clear = self.binop(Operator::I32And, in_b, below, Type::I32);
                (clear, inel)
            }
            AddCheck::Runtime(pairs) => {
                // Runtime form: only a SLOTS-carrying keyed receiver with
                // an IN-bound assigned offset can be harmed. The early key
                // (bits 18..30, zero once stamped) and the stamped idx
                // (zero while constructing) are disjoint, so their OR is
                // the one live layout id; the static bound table holds the
                // clump's byte-offset bound (0 = unfilled ->
                // conservative). The atom's (key, off) prediction-pair
                // chain -- a legitimate prefix fill keeps the bit -- only
                // runs on the cold in-bound path.
                let w = self.load_i32(objptr, OBJ_CLASS_IDX_OFFSET);
                self.eff(w, Eff::ReadBits(HeapKind::ClassWord));
                let sm = self.i32_const(CLASS_WORD_SLOTS);
                let sb = self.binop(Operator::I32And, w, sm, Type::I32);
                let z = self.i32_const(0);
                let slots_set = self.binop(Operator::I32Ne, sb, z, Type::I32);
                let ksh = self.i32_const(EARLY_KEY_SHIFT);
                let kraw = self.binop(Operator::I32ShrU, w, ksh, Type::I32);
                let kmask = self.i32_const(EARLY_KEY_MAX);
                let k_sent = self.binop(Operator::I32And, kraw, kmask, Type::I32);
                let m16 = self.i32_const(0xFFFF);
                let k_idx = self.binop(Operator::I32And, w, m16, Type::I32);
                let k = self.binop(Operator::I32Or, k_sent, k_idx, Type::I32);
                let k_nz = self.binop(Operator::I32Ne, k, z, Type::I32);
                let three = self.i32_const(3);
                let koff = self.binop(Operator::I32Shl, k, three, Type::I32);
                let base = self.i32_const(self.helpers.this_cells_base.wrapping_sub(8));
                let addr = self.binop(Operator::I32Add, base, koff, Type::I32);
                let bound = self.load_i32(addr, 0);
                self.eff(bound, Eff::ReadBits(HeapKind::EngineTable));
                let own_v = self.load_i32(addr, 4);
                self.eff(own_v, Eff::ReadBits(HeapKind::EngineTable));
                let b_z = self.binop(Operator::I32Eq, bound, z, Type::I32);
                let lt = self.binop(Operator::I32LtU, slot_off, bound, Type::I32);
                let bad = self.binop(Operator::I32Or, b_z, lt, Type::I32);
                let keyed = self.binop(Operator::I32And, slots_set, k_nz, Type::I32);
                let keyed_bad = self.binop(Operator::I32And, keyed, bad, Type::I32);
                // Keyless-sentinel arm: a keyless seed's SLOTS is maintained
                // by static checks only, so an unknown-site in-prefix add on
                // one must clear (positions are absolute; the static sites
                // never route here).
                let k_z2 = self.unop(Operator::I32Eqz, k, Type::I32);
                let kb = self.i32_const(FIXED_SLOTS_BASE + 8 * 16);
                let klt = self.binop(Operator::I32LtU, slot_off, kb, Type::I32);
                let kl1 = self.binop(Operator::I32And, slots_set, k_z2, Type::I32);
                let keyless_bad = self.binop(Operator::I32And, kl1, klt, Type::I32);
                let inbound = self.binop(Operator::I32Or, keyed_bad, keyless_bad, Type::I32);
                let split = |s: &mut Self, res: Value| {
                    // Ineligible only for a STAMPED (non-sentinel) word
                    // with a filled own bound and a beyond-own offset;
                    // everything else keeps the conservative clear.
                    let z2 = s.i32_const(0);
                    let stamped = s.binop(Operator::I32Ne, k_idx, z2, Type::I32);
                    let own_nz = s.binop(Operator::I32Ne, own_v, z2, Type::I32);
                    let beyond = s.binop(Operator::I32GeU, slot_off, own_v, Type::I32);
                    let i1 = s.binop(Operator::I32And, stamped, own_nz, Type::I32);
                    let i2 = s.binop(Operator::I32And, i1, beyond, Type::I32);
                    let inel = s.binop(Operator::I32And, res, i2, Type::I32);
                    let not_i = s.unop(Operator::I32Eqz, inel, Type::I32);
                    let clear = s.binop(Operator::I32And, res, not_i, Type::I32);
                    (clear, inel)
                };
                if pairs.is_empty() {
                    split(self, inbound)
                } else {
                    let chk_blk = self.body.add_block();
                    let res_blk = self.body.add_block();
                    let res_param = self.body.add_blockparam(res_blk, Type::I32);
                    let zero_r = self.i32_const(0);
                    self.body.set_terminator(
                        self.cur,
                        Terminator::CondBr {
                            cond: inbound,
                            if_true: BlockTarget {
                                block: chk_blk,
                                args: vec![],
                            },
                            if_false: BlockTarget {
                                block: res_blk,
                                args: vec![zero_r],
                            },
                        },
                    );
                    self.cur = chk_blk;
                    let mut unmatched = self.i32_const(1);
                    for pred in pairs {
                        let pkv = self.i32_const(pred.key.get());
                        let k_eq = self.binop(Operator::I32Eq, k, pkv, Type::I32);
                        let pov = self.i32_const(pred.offset);
                        let o_eq = self.binop(Operator::I32Eq, slot_off, pov, Type::I32);
                        let m = self.binop(Operator::I32And, k_eq, o_eq, Type::I32);
                        let not_m = self.unop(Operator::I32Eqz, m, Type::I32);
                        unmatched = self.binop(Operator::I32And, unmatched, not_m, Type::I32);
                    }
                    self.body.set_terminator(
                        chk_blk,
                        Terminator::Br {
                            target: BlockTarget {
                                block: res_blk,
                                args: vec![unmatched],
                            },
                        },
                    );
                    self.cur = res_blk;
                    split(self, res_param)
                }
            }
        };
        let sel = self.demote_word(objptr, clear, CLASS_WORD_SLOTS >> 16);
        let clr_blk = self.body.add_block();
        let rest_blk = self.body.add_block();
        let cont_blk = self.body.add_block();
        self.cond_br(clear, clr_blk, rest_blk);
        self.cur = clr_blk;
        self.emit_clear_slots_bit(objptr);
        self.body.set_terminator(
            clr_blk,
            Terminator::Br {
                target: BlockTarget {
                    block: cont_blk,
                    args: vec![],
                },
            },
        );
        self.cur = rest_blk;
        let inel_blk = self.body.add_block();
        self.cond_br(inel, inel_blk, cont_blk);
        self.cur = inel_blk;
        self.emit_set_adv_ineligible(objptr);
        self.body.set_terminator(
            inel_blk,
            Terminator::Br {
                target: BlockTarget {
                    block: cont_blk,
                    args: vec![],
                },
            },
        );
        self.cur = cont_blk;
        Some(sel)
    }

    /// Mark a stamped word advance-ineligible: an unpredicted-key add
    /// landed beyond the receiver's own layout, so the own prefix
    /// predictions still hold (SLOTS stays, the epoch stays still) but
    /// the bit history no longer certifies a clump sibling's extension
    /// and the prefix-advance restamp must decline.
    pub(super) fn emit_set_adv_ineligible(&mut self, objptr: Value) {
        let half = self.load16_u(objptr, OBJ_CLASS_FLAGS_OFFSET);
        self.eff(half, Eff::ReadBits(HeapKind::ClassWord));
        let b = self.i32_const(CLASS_WORD_ADV_INELIGIBLE >> 16);
        let nw = self.binop(Operator::I32Or, half, b, Type::I32);
        let st = self.store16(objptr, OBJ_CLASS_FLAGS_OFFSET, nw);
        self.effects.insert(st, Eff::Write(HeapKind::ClassWord));
        if self.guard_census_on() {
            self.emit_guard_census(68, self.cur_pc);
        }
    }

    /// Resolve the add-check statically where the receiver's layout is
    /// known (the ctor_init_claim receiver scope: root own-this or a
    /// construct splice's this/alias); the delegate's full layout wins
    /// over the ctor's own prefix. Everything else takes the runtime
    /// table form.
    pub(super) fn ctor_add_check(&mut self, recv: &Operand, name: NameId) -> AddCheck {
        if !self.recv_is_own_this(recv) {
            return self.runtime_add_check(name);
        }
        let (fields, ext_bound) = if let Some(si) = self.ctx.deleg_restamps_in.get(&self.source_id)
        {
            (si.fields.clone(), si.ext_bound)
        } else if let Some(si) = self.ctx.stamp_ctors_in.get(&self.source_id) {
            (si.fields.clone(), si.ext_bound)
        } else {
            return self.runtime_add_check(name);
        };
        match fields.iter().position(|&f| f == name) {
            Some(pos) => AddCheck::Predicted(FIXED_SLOTS_BASE + 8 * u32::try_from(pos).unwrap()),
            None => AddCheck::Unpredicted {
                bound: ext_bound,
                own: FIXED_SLOTS_BASE + 8 * u32::try_from(fields.len()).unwrap(),
            },
        }
    }

    /// The atom's prefix-closed prediction pairs for the runtime add
    /// check; capped so a corpus-shared name cannot bloat every unknown
    /// add site (an over-full list degrades to the conservative form --
    /// clears are always sound).
    pub(super) fn runtime_add_check(&self, name: NameId) -> AddCheck {
        let pairs = self
            .ctx
            .layout_addpred_in
            .get(&name)
            .cloned()
            .unwrap_or_default();
        if pairs.len() > 16 {
            return AddCheck::Runtime(Vec::new());
        }
        AddCheck::Runtime(pairs)
    }

    /// The init-store mask for `this.<chars> = v` in a stamping-ctor /
    /// init-delegate body. Without it every ctor object-field store pays the
    /// blanket choke, wipes the CONSTRUCTING sentinel, and leaves the
    /// instance stamped without the shallow bit, so every shallow-gated
    /// typed read misses. Some(0) = the own layout leaves the field
    /// unclaimed (no flags action -- sound for foreign receivers because the
    /// activation prologue's foreign-this guard already cleared a
    /// foreign stamped `this`); Some(m) = conform-check-or-clear.
    /// Receiver scope: root-body own-this (the prologue guard covers the
    /// foreign-this corner), or own-this inside a construct splice -- a
    /// construct-spliced `this` is the freshly-created object by
    /// construction, so no foreign receiver is possible there at all.
    /// Non-construct splices keep the conservative choke.
    /// The range obligation of a store of `val` into field `chars` of
    /// `recv` (see `RangeAct`). The candidate layouts are the receiver's
    /// class fact when it has one, and otherwise every layout -- an
    /// unresolved receiver could be any of them, and only the field name
    /// narrows the set, which is why a name no layout range-claims costs
    /// nothing at all.
    pub(super) fn store_range_act(&self, recv: &Operand, name: NameId, val: &Operand) -> RangeAct {
        if self.ctx.layout_field_ranges_in.is_empty() {
            return RangeAct::Nothing;
        }
        let mut isect: Option<ValueRange> = None;
        let mut claimed = false;
        let mut fold = |r: Option<&ValueRange>| {
            if let Some(&r) = r {
                claimed = true;
                isect = Some(match isect {
                    None => r,
                    Some(a) => ValueRange::new(a.lo.max(r.lo), a.hi.min(r.hi)),
                });
            }
        };
        match recv.cls {
            Some((lo, hi)) => {
                for k in u32::from(lo)..=u32::from(hi) {
                    fold(
                        self.ctx
                            .layout_field_ranges_in
                            .get(&StampKey::new(k))
                            .and_then(|f| f.get(&name)),
                    );
                }
            }
            None => {
                for f in self.ctx.layout_field_ranges_in.values() {
                    fold(f.get(&name));
                }
            }
        }
        if !claimed {
            return RangeAct::Nothing;
        }
        let Some(ValueRange { lo, hi }) = isect.filter(|r| r.lo <= r.hi) else {
            return RangeAct::Clear;
        };
        // A statically bounded value proves itself. The claim is about
        // magnitude, not tag, so this holds whatever the value boxes as:
        // a double 5.0 landing in an int32-masked field clears TYPES, and
        // the pair is only ever consumed together.
        if let Some((vlo, vhi, _)) = op_iv(val) {
            if vlo >= lo && vhi <= hi {
                return RangeAct::Nothing;
            }
        }
        // The emitted check compares an int32 payload, so the bounds must
        // be expressible as i32. Clamping is exact for the int32 domain
        // (an i32 is >= a below-domain lo unconditionally); a window that
        // misses the domain entirely admits no int32 and must clear.
        let (clo, chi) = (lo.max(i32::MIN as i64), hi.min(i32::MAX as i64));
        if clo > chi {
            return RangeAct::Clear;
        }
        RangeAct::Check(clo, chi)
    }

    /// The duty a compiled element store owes an array's RANGES claim.
    ///
    /// Prove-OR-clear: a store whose value interval already sits inside
    /// the claim emits nothing at all (the digit-array shape,
    /// `a[i] = <masked expr>`, is exactly this), and anything else drops
    /// the bit. Runtime range compares on element stores are a separate
    /// concern, together with the R selection that makes a claim worth
    /// checking for.
    ///
    /// An unclassified receiver falls back to the intersection of every
    /// claim in the bundle, so proving once covers whichever population it
    /// turns out to be. Bundles that claim nothing emit nothing anywhere.
    pub(super) fn emit_elem_store_duty(&mut self, objptr: Value, val: &Operand) {
        let pc = self.cur_pc;
        let claim = self
            .ctx
            .array_elem_in
            .get(&Site::new(self.source_id, self.evid_pc(pc)))
            .map(|a| a.range)
            .or(self.ctx.array_any_claim);
        let Some(ValueRange { lo, hi }) = claim else {
            return;
        };
        if let Some((vlo, vhi, _)) = op_iv(val) {
            if vlo >= lo && vhi <= hi {
                return;
            }
        }
        // Test before writing: the bit is usually already clear on the
        // arrays that reach here, and an unconditional store would dirty
        // the header line on every element write forever.
        let half = self.load16_u(objptr, OBJ_CLASS_FLAGS_OFFSET);
        self.eff(half, Eff::ReadBits(HeapKind::ClassWord));
        let rb = self.i32_const(CLASS_WORD_RANGES >> 16);
        let set = self.binop(Operator::I32And, half, rb, Type::I32);
        let z = self.i32_const(0);
        let nz = self.binop(Operator::I32Ne, set, z, Type::I32);
        let clear_blk = self.body.add_block();
        let cont = self.body.add_block();
        self.cond_br(nz, clear_blk, cont);
        self.cur = clear_blk;
        self.emit_clear_ranges_bit(objptr);
        self.body.set_terminator(
            clear_blk,
            Terminator::Br {
                target: BlockTarget {
                    block: cont,
                    args: vec![],
                },
            },
        );
        self.cur = cont;
    }

    /// Clear the RANGES bit: this store did not show that the receiver's
    /// range predictions still hold.
    pub(super) fn emit_clear_ranges_bit(&mut self, objptr: Value) {
        let half = self.load16_u(objptr, OBJ_CLASS_FLAGS_OFFSET);
        self.eff(half, Eff::ReadBits(HeapKind::ClassWord));
        let d = self.demote_delta(half, CLASS_WORD_RANGES >> 16);
        self.emit_epoch_bump(Some(d));
        self.emit_demote_census(half, CLASS_WORD_RANGES >> 16);
        let m = self.i32_const(0xFFFF & !(CLASS_WORD_RANGES >> 16));
        let nw = self.binop(Operator::I32And, half, m, Type::I32);
        let st = self.store16(objptr, OBJ_CLASS_FLAGS_OFFSET, nw);
        self.effects.insert(st, Eff::Write(HeapKind::ClassWord));
    }

    /// Emit `RangeAct`: keep the RANGES bit only for an int32 payload
    /// inside the bounds. Non-int32 values fail into the clear arm, which
    /// costs them nothing -- the mask arm was going to clear TYPES anyway.
    /// Returns the act's runtime stamp-break word (FLAG_STAMPS when the
    /// clear arm will run, else 0), computed straight-line so it dominates
    /// the continuation; None when the act emits nothing.
    pub(super) fn emit_range_act(
        &mut self,
        objptr: Value,
        boxed: Value,
        act: RangeAct,
    ) -> Option<Value> {
        let (lo, hi) = match act {
            RangeAct::Nothing => return None,
            RangeAct::Clear => {
                self.emit_clear_ranges_bit(objptr);
                let one = self.i32_const(1);
                return Some(self.demote_word(objptr, one, CLASS_WORD_RANGES >> 16));
            }
            RangeAct::Check(lo, hi) => (lo, hi),
        };
        let is_i32 = self.tag_eq(boxed, TAG_INT32 as u32);
        let pay = self.unop(Operator::I32WrapI64, boxed, Type::I32);
        let lo_v = self.i32_const(lo as u32);
        let hi_v = self.i32_const(hi as u32);
        let ge = self.binop(Operator::I32GeS, pay, lo_v, Type::I32);
        let le = self.binop(Operator::I32LeS, pay, hi_v, Type::I32);
        let in_r = self.binop(Operator::I32And, ge, le, Type::I32);
        let ok = self.binop(Operator::I32And, is_i32, in_r, Type::I32);
        let bad = self.unop(Operator::I32Eqz, ok, Type::I32);
        let sel = self.demote_word(objptr, bad, CLASS_WORD_RANGES >> 16);
        let clear_blk = self.body.add_block();
        let cont = self.body.add_block();
        self.cond_br(ok, cont, clear_blk);
        self.cur = clear_blk;
        self.emit_clear_ranges_bit(objptr);
        self.body.set_terminator(
            clear_blk,
            Terminator::Br {
                target: BlockTarget {
                    block: cont,
                    args: vec![],
                },
            },
        );
        self.cur = cont;
        Some(sel)
    }

    pub(super) fn ctor_init_claim(&self, recv: &Operand, name: NameId) -> Option<Claim> {
        let recv_ok = match self.cur_seg {
            None => self.store_recv_is_this(recv),
            Some(i) => {
                self.segs[i].is_construct
                    && match recv.src {
                        Some(SlotRef::This) => true,
                        // The seg's own this-alias local (`var self = this`
                        // and the FunctionThis/SetLocal entry idiom a ctor
                        // that aliases its receiver compiles to).
                        Some(SlotRef::Local(n)) => self.segs[i].this_alias_locals.contains(&n),
                        _ => false,
                    }
            }
        };
        if !recv_ok {
            if self.opts.diagnostics.bbv
                && self.mode == EmitMode::Code
                && self.ctx.stamp_ctors_in.contains_key(&self.source_id)
            {
                crate::diag_line!(
                    "night: bbv initmask-decline sid#{} pc {} seg {:?} construct {:?} src {:?}",
                    self.source_id,
                    self.evid_pc(self.cur_pc),
                    self.cur_seg,
                    self.cur_seg.map(|i| self.segs[i].is_construct),
                    recv.src,
                );
            }
            return None;
        }
        if let Some(si) = self.ctx.stamp_ctors_in.get(&self.source_id) {
            let pos = si.fields.iter().position(|&n| n == name)?;
            return Some(si.masks.get(pos).copied().unwrap_or(Claim::NONE));
        }
        let li = self.ctx.this_layouts_in.get(&self.source_id)?;
        if !li.init_home {
            return None;
        }
        let pos = li.fields.iter().position(|&n| n == name)?;
        Some(li.masks.get(pos).copied().unwrap_or(Claim::NONE))
    }

    /// Activation-prologue guard for stamping-ctor bodies: a foreign
    /// stamped `this`
    /// (another layout's completed object reached via .call/.apply) gets
    /// its conform flags cleared up front, which is what licenses the
    /// Some(0) no-action arm of the init-store choke.
    pub(super) fn emit_stamp_ctor_foreign_this_guard(&mut self) {
        let Some(si) = self.ctx.stamp_ctors_in.get(&self.source_id) else {
            return;
        };
        let own_k = si.layout_id + 1;
        let v = self.load_i64(self.sp, 8);
        let is_obj = self.tag_eq(v, TAG_OBJECT as u32);
        let chk_blk = self.body.add_block();
        let clear_blk = self.body.add_block();
        let done_blk = self.body.add_block();
        self.cond_br(is_obj, chk_blk, done_blk);
        self.cur = chk_blk;
        let objptr = self.unop(Operator::I32WrapI64, v, Type::I32);
        let idx = self.load16_u(objptr, OBJ_CLASS_IDX_OFFSET);
        self.eff(idx, Eff::ReadBits(HeapKind::ClassWord));
        let zero = self.i32_const(0);
        let is_unstamped = self.binop(Operator::I32Eq, idx, zero, Type::I32);
        let kc = self.i32_const(own_k);
        let is_own = self.binop(Operator::I32Eq, idx, kc, Type::I32);
        let ok = self.binop(Operator::I32Or, is_unstamped, is_own, Type::I32);
        self.cond_br(ok, done_blk, clear_blk);
        self.cur = clear_blk;
        self.emit_clear_conform_flags(objptr);
        self.body.set_terminator(
            clear_blk,
            Terminator::Br {
                target: BlockTarget {
                    block: done_blk,
                    args: vec![],
                },
            },
        );
        self.cur = done_blk;
    }

    /// Returns the arm's stamp-break contribution as (static, dynamic):
    /// `static` is FLAG_STAMPS when a demote path exists at all against a
    /// non-fresh receiver -- the conservative word for merges that cannot
    /// carry a dynamic one -- and `dynamic` is the runtime-precise word
    /// (nonzero iff a clear actually runs), computed straight-line so it
    /// dominates the continuation. The runtime form is what keeps the
    /// callee's returned word honest: the gap between "may demote" and
    /// "did demote" is large in practice -- most receivers a demote path
    /// exists for never actually clear.
    /// The runtime stamp-break word for one demote arm: FLAG_STAMPS iff
    /// `cond` holds AND the receiver's flags half actually carries one of
    /// `claim_mask`'s bits AND the word is not the CONSTRUCTING sentinel
    /// (a mid-construction object's seed-bit drops falsify no caller fact
    /// -- the exact semantics of the C++ epoch's bump conditions). One
    /// load16 + a few ALU ops, straight-line, so the word dominates the
    /// continuation.
    fn demote_word(&mut self, objptr: Value, cond: Value, claim_mask: u32) -> Value {
        let half = self.load16_u(objptr, OBJ_CLASS_FLAGS_OFFSET);
        self.eff(half, Eff::ReadBits(HeapKind::ClassWord));
        let cm = self.i32_const(claim_mask);
        let bits = self.binop(Operator::I32And, half, cm, Type::I32);
        let z = self.i32_const(0);
        let has = self.binop(Operator::I32Ne, bits, z, Type::I32);
        let sm = self.i32_const(CLASS_WORD_SENTINEL >> 16);
        let sent = self.binop(Operator::I32And, half, sm, Type::I32);
        let real0 = self.binop(Operator::I32And, cond, has, Type::I32);
        let stk = self.i32_const(FLAG_STAMPS);
        let sel0 = self.select(Type::I32, stk, z, real0);
        // Sentinel wins: mid-construction receivers report 0.
        self.select(Type::I32, z, sel0, sent)
    }

    /// OR two optional runtime words (both dominate the current point).
    pub(super) fn or_opt_words(&mut self, a: Option<Value>, b: Option<Value>) -> Option<Value> {
        match (a, b) {
            (Some(x), Some(y)) => Some(self.binop(Operator::I32Or, x, y, Type::I32)),
            (x, None) => x,
            (None, y) => y,
        }
    }

    pub(super) fn emit_store_choke(
        &mut self,
        objptr: Value,
        val_boxed: Value,
        val_is_num: bool,
        recv_bit: u32,
        site_claim: Option<Claim>,
        range_act: RangeAct,
    ) -> (u32, Option<Value>) {
        let choke = if val_is_num {
            "elided"
        } else {
            match site_claim {
                Some(c) if c.is_none() => "init-unmasked",
                Some(_) => "init-conform",
                None => "PAID",
            }
        };
        self.op_choke = Some(choke);
        if self.opts.diagnostics.bbv {
            crate::diag_line!(
                "night: bbv choke sid#{} pc {} {choke}",
                self.source_id,
                self.evid_pc(self.cur_pc),
            );
        }
        // The arm's static stamp-break word: a demote path exists when the
        // range act can clear, or a non-numeric value meets a claimed field
        // (conform clear) or an unknown layout (the generic choke below).
        // A fresh receiver's demotions falsify no caller fact.
        let clears_mask = !val_is_num && !matches!(site_claim, Some(c) if c.is_none());
        let clears_range = !matches!(range_act, RangeAct::Nothing);
        let fresh_recv = recv_bit == 0;
        let stamp_static = if !fresh_recv && (clears_mask || clears_range) {
            FLAG_STAMPS
        } else {
            0
        };
        // The range obligation is independent of the mask one: a
        // statically-numeric value settles TYPES but says nothing about
        // magnitude, so this runs before the val_is_num short-circuit.
        let range_sel = self.emit_range_act(objptr, val_boxed, range_act);
        let range_sel = if fresh_recv { None } else { range_sel };
        if val_is_num {
            // Nothing is cleared, so the shallow facts survive.
            return (stamp_static, range_sel);
        }
        match site_claim {
            // The own layout leaves the field unclaimed: no flags action
            // (the foreign-this prologue guard covers foreign receivers).
            Some(c) if c.is_none() => return (stamp_static, range_sel),
            Some(c) => {
                let cf = self.emit_conform_check_or_clear(objptr, val_boxed, c.prims());
                let dyn_w = if fresh_recv {
                    None
                } else {
                    self.or_opt_words(range_sel, cf)
                };
                return (stamp_static, dyn_w);
            }
            None => {}
        }
        let is_num = self.is_number_tag(val_boxed);
        let chk_blk = self.body.add_block();
        let clear_blk = self.body.add_block();
        let cont = self.body.add_block();
        // The bit-precise stamp word rides `cont` as a param: 0 from the
        // numeric and no-flags edges, FLAG_STAMPS from the clear edge.
        let stamp_param = self.body.add_blockparam(cont, Type::I32);
        let z_edge = self.i32_const(0);
        self.body.set_terminator(
            self.cur,
            Terminator::CondBr {
                cond: is_num,
                if_true: BlockTarget {
                    block: cont,
                    args: vec![z_edge],
                },
                if_false: BlockTarget {
                    block: chk_blk,
                    args: vec![],
                },
            },
        );
        self.cur = chk_blk;
        let w = self.load_i32(objptr, OBJ_CLASS_IDX_OFFSET);
        self.eff(w, Eff::ReadBits(HeapKind::ClassWord));
        let fm = self.i32_const(CLASS_WORD_SHALLOW);
        let flags = self.binop(Operator::I32And, w, fm, Type::I32);
        let z = self.i32_const(0);
        let has_flags = self.binop(Operator::I32Ne, flags, z, Type::I32);
        self.body.set_terminator(
            self.cur,
            Terminator::CondBr {
                cond: has_flags,
                if_true: BlockTarget {
                    block: clear_blk,
                    args: vec![],
                },
                if_false: BlockTarget {
                    block: cont,
                    args: vec![z],
                },
            },
        );
        self.cur = clear_blk;
        if self.guard_census_on() {
            let before = self.body.values.len();
            let k = self.i32_const(census::STAMP_DEMOTE);
            self.instrument_values += self.body.values.len() - before;
            self.emit_guard_census_dyn_id(k, flags);
        }
        {
            // has_flags held (pre-tested); only the sentinel is left to
            // discharge before the bump counts.
            let sw = self.i32_const(CLASS_WORD_SENTINEL);
            let sent = self.binop(Operator::I32And, w, sw, Type::I32);
            let z = self.i32_const(0);
            let one = self.i32_const(1);
            let d = self.select(Type::I32, z, one, sent);
            self.emit_epoch_bump(Some(d));
        }
        let m = self.i32_const(!CLASS_WORD_SHALLOW);
        let nw = self.binop(Operator::I32And, w, m, Type::I32);
        let st = self.store_i32(objptr, OBJ_CLASS_IDX_OFFSET, nw);
        // The choke clears the receiver's own flags half -- classify like
        // the store it guards (aliases are the consumer's problem: the
        // this-only fork arm kills shallow facts globally).
        self.eff_store(st, Eff::Write(HeapKind::ClassWord), recv_bit);
        // The clear ran, but a CONSTRUCTING receiver's seed-bit drop is a
        // fresh-object action: its edge reports 0.
        let sw = self.i32_const(CLASS_WORD_SENTINEL);
        let sent = self.binop(Operator::I32And, w, sw, Type::I32);
        let z_e = self.i32_const(0);
        let stk_edge = self.i32_const(FLAG_STAMPS);
        let edge_w = self.select(Type::I32, z_e, stk_edge, sent);
        self.body.set_terminator(
            self.cur,
            Terminator::Br {
                target: BlockTarget {
                    block: cont,
                    args: vec![edge_w],
                },
            },
        );
        self.cur = cont;
        let dyn_w = if fresh_recv {
            None
        } else {
            self.or_opt_words(range_sel, Some(stamp_param))
        };
        (stamp_static, dyn_w)
    }
}
