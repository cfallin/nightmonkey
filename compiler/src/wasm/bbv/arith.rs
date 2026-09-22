/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Arithmetic lowerings: the ctx-consulting numeric ladders and their
//! per-arm continuations.

use super::*;

impl<'a> Bbv<'a> {
    /// The exact-integer result split: `sum` is an exact i64 (at most i33
    /// magnitude from an int32 +/- int32). The fits-int32 arm falls through
    /// with the wrapped i32; the overflow arm continues at `succ_pc` as an
    /// integral double (the ovf attractor's canonical feed).
    /// `riv` is the op's vocabulary result interval: it bounds the merged
    /// value on both arms, and attaching it everywhere is what keeps a
    /// chain's interval alive across the succ join (an arm pushing the
    /// same value without it would kill the slot fact for every lineage).
    pub(super) fn int_result_or_ovf(
        &mut self,
        sum: Value,
        succ_pc: Pc,
        riv: opsem::Iv,
        prov: Prov,
    ) {
        let w = self.unop(Operator::I32WrapI64, sum, Type::I32);
        // Interval elision: a clean result interval inside int32 makes
        // the overflow test dead. int32-tagged operands are never -0, so a flagged
        // interval cannot reach a sound elision here -- require clean.
        if let Some(r) = opsem::iv_clean(riv) {
            if r.lo >= opsem::I32_LO && r.hi <= opsem::I32_HI {
                self.emit_rely_census(census::RELY_IV_RUNG, prov);
                if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
                    crate::diag_line!(
                        "night: addcln sid#{} pc {}",
                        self.source_id,
                        self.evid_pc(self.cur_pc)
                    );
                }
                self.stack.push(
                    Operand::plain(w, Repr::I32, prim_desc(PRIM_INT32))
                        .with_iv(iv_clamp_i32(riv))
                        .with_prov(prov),
                );
                return;
            }
        }
        // Truncation demand: every consumer coerces through ToInt32, so
        // the wrapped i32 IS the observed value and the overflow arm is
        // dead. No result interval: the wrapped value's range is not the
        // op's (`riv` bounds the true sum, not the wrap).
        if self.trunc_demanded(self.cur_pc) {
            if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
                crate::diag_line!(
                    "night: addtrunc sid#{} pc {}",
                    self.source_id,
                    self.evid_pc(self.cur_pc)
                );
            }
            self.stack
                .push(Operand::plain(w, Repr::I32, prim_desc(PRIM_INT32)).with_prov(prov));
            return;
        }
        let sext = self.unop(Operator::I64ExtendI32S, w, Type::I64);
        let fits = self.binop(Operator::I64Eq, sext, sum, Type::I32);
        let ok_blk = self.body.add_block();
        let ovf_blk = self.body.add_block();
        self.cond_br(fits, ok_blk, ovf_blk);
        self.side_arm_num_if_frac(ovf_blk, succ_pc, move |s| {
            let f = s.unop(Operator::F64ConvertI64S, sum, Type::F64);
            let bits = s.unop(Operator::I64ReinterpretF64, f, Type::I64);
            Operand::ranged(bits, Repr::Boxed, prim_desc(PRIM_DOUBLE), RangeBucket::I53)
                .with_iv(riv)
                .with_prov(prov)
        });
        self.cur = ok_blk;
        // The passed fits-check proves int32: the arm's interval is the
        // op's, clamped -- a masked product's tight bound survives here,
        // which is what lets the downstream sum tighten and admit.
        self.stack.push(
            Operand::plain(w, Repr::I32, prim_desc(PRIM_INT32))
                .with_iv(iv_clamp_i32(riv))
                .with_prov(prov),
        );
    }

    /// The `*` mirror of `int_result_or_ovf`: `prod` is the exact i64
    /// product of two sign-extended int32s (at most i62). The fast arm
    /// needs the product to fit int32 and not to be -0 -- which is exactly
    /// a zero product from operands of differing sign. The exit arm redoes
    /// the multiply in f64, the only form that yields both the correctly
    /// rounded wide product and -0 itself.
    /// `check_fits` = false when the caller's result interval already
    /// proves the product inside int32 (the overflow half of the ladder
    /// is dead; only the -0 test remains -- am3's xh*l / h*xl / xh*h
    /// shape, where the shifted factor may be negative but the magnitude
    /// bound holds by construction).
    pub(super) fn int_mul_result_or_ovf(
        &mut self,
        prod: Value,
        a64: Value,
        b64: Value,
        succ_pc: Pc,
        riv: opsem::Iv,
        check_fits: bool,
        prov: Prov,
    ) {
        let w = self.unop(Operator::I32WrapI64, prod, Type::I32);
        let zero = self.boxed_const(0);
        let is_zero = self.binop(Operator::I64Eq, prod, zero, Type::I32);
        let signs = self.binop(Operator::I64Xor, a64, b64, Type::I64);
        let opposed = self.binop(Operator::I64LtS, signs, zero, Type::I32);
        let neg_zero = self.binop(Operator::I32And, is_zero, opposed, Type::I32);
        let not_neg_zero = self.unop(Operator::I32Eqz, neg_zero, Type::I32);
        let ok = if check_fits {
            let sext = self.unop(Operator::I64ExtendI32S, w, Type::I64);
            let fits = self.binop(Operator::I64Eq, sext, prod, Type::I32);
            self.binop(Operator::I32And, fits, not_neg_zero, Type::I32)
        } else {
            not_neg_zero
        };
        let ok_blk = self.body.add_block();
        let ovf_blk = self.body.add_block();
        self.cond_br(ok, ok_blk, ovf_blk);
        self.side_arm_num_if_frac(ovf_blk, succ_pc, move |s| {
            let af = s.unop(Operator::F64ConvertI64S, a64, Type::F64);
            let bf = s.unop(Operator::F64ConvertI64S, b64, Type::F64);
            let f = s.binop(Operator::F64Mul, af, bf, Type::F64);
            let bits = s.unop(Operator::I64ReinterpretF64, f, Type::I64);
            Operand::plain(bits, Repr::Boxed, prim_desc(PRIM_DOUBLE))
                .with_iv(riv)
                .with_prov(prov)
        });
        self.cur = ok_blk;
        self.stack.push(
            Operand::plain(w, Repr::I32, prim_desc(PRIM_INT32))
                .with_iv(iv_clamp_i32(riv))
                .with_prov(prov),
        );
    }

    /// Whether the arith site at the current pc carries fractional
    /// evidence (`fractional_arith_sites`): the double arm keeps the track
    /// only there. Without evidence the arm's numeric result joining the
    /// successor would degrade a pure-int32 chain's facts, so it keeps the
    /// track step. Ungating it boxes whole loops of otherwise-int32
    /// chains. What it costs is untyped field-add sites like
    /// `a.x + b.x` -- a fact-precision gap (the fields' types), not a
    /// policy to relax.
    fn frac_site(&self) -> bool {
        self.ctx
            .facts
            .fractional_arith_sites
            .contains(&crate::ids::Site::new(
                self.source_id,
                self.evid_pc(self.cur_pc),
            ))
    }

    /// Truncation demand, derived from the bytecode's own stack
    /// discipline: an Add/Sub whose every consumer coerces through
    /// ToInt32/ToUint32 (a bit op, directly or through further Add/Sub
    /// links) cannot have its overflow observed -- ToInt32 of the exact
    /// double sum equals the wrapped i64 sum (int32 +/- chains stay
    /// 2^53-exact), so the site lowers as a wrapping int32 op with no
    /// overflow arm and no side continuation. A Mul is demanded the same
    /// way but lowers wrapping only under an interval proof that the
    /// product stays f64-exact (see `emit_muldiv_op`): past 2^53 the
    /// double product ROUNDS before ToInt32, so an unproven wrapped
    /// integer product diverges from the spec.
    ///
    /// A stack temp has exactly one consumer, so the walk records one
    /// (producer, consumer-kind) edge per pop. Producers are tracked only
    /// through a closed set of fixed-arity, control-free ops; anything
    /// else (a branch, a call, an op outside the set) clears the abstract
    /// stack, so a producer whose consumer the walk cannot prove is
    /// simply never marked. `Set*` keeps its value on the real stack but
    /// stores a copy -- that store is an escaping consumer, so the
    /// producer is killed and the surviving slot forgets it.
    fn trunc_demanded(&mut self, pc: Pc) -> bool {
        let set = self.trunc_sites.entry(self.source_id).or_insert_with(|| {
            enum Cons {
                Trunc,
                Chain(Pc),
                Other,
            }
            // Spec-magnitude budget, in units of 2^31: an untracked operand
            // reaches a demanded op's int arm runtime-int32-guarded, so its
            // spec value is 1 unit; a tracked Add/Sub sums its operands'
            // units; a Mul claims 2^16 units (the lowering enforces the
            // matching +-2^47 interval, refusing the trunc form past it --
            // a refused node lowers with the full ladder, so its result's
            // spec IS its runtime int32 and the 1-unit leaf claim holds).
            // A node past 2^22 units (spec beyond 2^53, where f64 rounds
            // before ToInt32) is simply never tracked.
            const MUL_UNITS: u64 = 1 << 16;
            const CAP_UNITS: u64 = 1 << 22;
            let mut stack: Vec<Option<Pc>> = Vec::new();
            let mut cons: rustc_hash::FxHashMap<Pc, Vec<Cons>> = Default::default();
            let mut units: rustc_hash::FxHashMap<Pc, u64> = Default::default();
            let record =
                |slot: Option<Pc>, c: Cons, cons: &mut rustc_hash::FxHashMap<Pc, Vec<Cons>>| {
                    if let Some(p) = slot {
                        cons.entry(p).or_default().push(c);
                    }
                };
            let mut p = self.script.parser();
            let mut at = Pc::new(0);
            while let Some(op) = p.next_op() {
                if p.advance(usize::try_from(op.len()).unwrap() - 1).is_none() {
                    break;
                }
                match op {
                    JSOp::Zero
                    | JSOp::One
                    | JSOp::Int8
                    | JSOp::Int32
                    | JSOp::Uint16
                    | JSOp::Uint24
                    | JSOp::Double
                    | JSOp::GetLocal
                    | JSOp::GetArg
                    | JSOp::GetFrameArg
                    | JSOp::GetAliasedVar => stack.push(None),
                    JSOp::Add | JSOp::Sub => {
                        let sa = stack.pop().flatten();
                        let sb = stack.pop().flatten();
                        let u = sa.map_or(1, |p| units[&p]) + sb.map_or(1, |p| units[&p]);
                        record(sa, Cons::Chain(at), &mut cons);
                        record(sb, Cons::Chain(at), &mut cons);
                        if u <= CAP_UNITS {
                            units.insert(at, u);
                            stack.push(Some(at));
                        } else {
                            stack.push(None);
                        }
                    }
                    // A Mul can BE demanded (its lowering additionally
                    // requires the +-2^47 interval proof), but demand never
                    // propagates THROUGH it: wrapped operands feed a
                    // spec-side f64 product, so the operands' producers are
                    // escaping consumers.
                    JSOp::Mul => {
                        record(stack.pop().flatten(), Cons::Other, &mut cons);
                        record(stack.pop().flatten(), Cons::Other, &mut cons);
                        units.insert(at, MUL_UNITS);
                        stack.push(Some(at));
                    }
                    JSOp::BitAnd
                    | JSOp::BitOr
                    | JSOp::BitXor
                    | JSOp::Lsh
                    | JSOp::Rsh
                    | JSOp::Ursh => {
                        record(stack.pop().flatten(), Cons::Trunc, &mut cons);
                        record(stack.pop().flatten(), Cons::Trunc, &mut cons);
                        stack.push(None);
                    }
                    JSOp::BitNot => {
                        record(stack.pop().flatten(), Cons::Trunc, &mut cons);
                        stack.push(None);
                    }
                    JSOp::Pop => {
                        record(stack.pop().flatten(), Cons::Other, &mut cons);
                    }
                    JSOp::SetLocal | JSOp::SetArg | JSOp::SetAliasedVar => {
                        record(stack.pop().flatten(), Cons::Other, &mut cons);
                        stack.push(None);
                    }
                    JSOp::Dup => {
                        record(stack.pop().flatten(), Cons::Other, &mut cons);
                        stack.push(None);
                        stack.push(None);
                    }
                    _ => stack.clear(),
                }
                at += op.len();
            }
            // Demand fixpoint over the (acyclic, tiny) chain graph.
            let mut marked = rustc_hash::FxHashSet::default();
            loop {
                let mut changed = false;
                for (&p, cs) in &cons {
                    if marked.contains(&p) {
                        continue;
                    }
                    let ok = !cs.is_empty()
                        && cs.iter().all(|c| match c {
                            Cons::Trunc => true,
                            Cons::Chain(q) => marked.contains(q),
                            Cons::Other => false,
                        });
                    if ok {
                        marked.insert(p);
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }
            marked
        });
        set.contains(&pc)
    }

    /// `side_arm_num` when the site carries fractional evidence, the
    /// stepping `side_arm` otherwise.
    ///
    /// The gate looks wrong on its face (it asks whether the site's
    /// values are ever FRACTIONAL, while every arm reaching here produces
    /// a double because the int32 arm's RANGE proof failed), but ungating
    /// it widens the successor's prediction from int32 to numeric for
    /// every execution that falls through the range proof, compile-time
    /// boxing at exactly the site where it hurts most (the join law). The
    /// fix for an unproven product is to prove its interval, not to
    /// widen its category.
    fn side_arm_num_if_frac(
        &mut self,
        blk: Block,
        succ_pc: Pc,
        emit_arm: impl FnOnce(&mut Self) -> Operand,
    ) {
        if self.frac_site() {
            self.side_arm_num(blk, succ_pc, emit_arm);
        } else {
            self.side_arm(blk, succ_pc, emit_arm);
        }
    }

    pub(super) fn push_load_typed_arr(
        &mut self,
        boxed: Value,
        claim: Claim,
        next_pc: Pc,
        arr: Option<ArrFold>,
    ) {
        self.arr_fold = arr;
        self.push_load_typed(boxed, claim, next_pc, Prov::C_ELEM);
        self.arr_fold = None;
    }

    /// `prov` is the provenance of the claim's table: the positive arms'
    /// facts are the analysis's own predictions, validated.
    pub(super) fn push_load_typed(&mut self, boxed: Value, claim: Claim, next_pc: Pc, prov: Prov) {
        if self.outline_generic() {
            self.push_boxed(boxed, bottom_ty());
            return;
        }
        if claim.is_object() {
            // Object-only claim (the site_claim tier): one TAG_OBJECT test,
            // the fall-through commits to obj-only -- downstream receiver
            // tag tests elide against it and dead non-object arms (the
            // string-chars arm) never exist. Same ladder discipline: the
            // other arm joins the weaker lineage at next_pc.
            let is_obj = self.tag_eq(boxed, TAG_OBJECT as u32);
            let obj_blk = self.body.add_block();
            let other_blk = self.body.add_block();
            self.cond_br(is_obj, obj_blk, other_blk);
            self.side_arm(other_blk, next_pc, move |_| {
                Operand::plain(boxed, Repr::Boxed, bottom_ty())
            });
            self.cur = obj_blk;
            self.stack
                .push(Operand::plain(boxed, Repr::Boxed, obj_only_ty()).with_prov(prov));
            return;
        }
        // A MIXED Int32|Double mask takes the NUMERIC form: one number-tag
        // test admitting both tags, the fall-through keeping the value
        // BOXED with a numeric fact. This replaces the exact-first policies
        // (int32-first, and the double-first hint) for mixed masks: at a
        // site whose population genuinely flips -- and canonicalized JS
        // numerics flip by construction, a double landing on a small
        // integer value re-tags as int32 -- EITHER exact form routes the
        // other tag off the happy path, and since the Side->Dirty fold
        // that route is a full track deopt that a single hot site can pay
        // heavily. Widening the exact arm instead loses on the eager F64
        // carrier, not the branch; the boxed fall-through defers
        // representation to the consumers' existing number-tag dispatch
        // and keeps the dead non-numeric arms dead. Pure masks keep their
        // exact forms and raw carriers. The element-range fold stays on
        // the exact-i32 form (its seeded interval is int32-only
        // evidence).
        let prims = claim.prims();
        if prims == PRIM_INT32.or(PRIM_DOUBLE) && self.arr_fold.is_none() {
            let is_num = self.is_number_tag(boxed);
            let num_blk = self.body.add_block();
            let other_blk = self.body.add_block();
            self.cond_br(is_num, num_blk, other_blk);
            self.side_arm(other_blk, next_pc, move |_| {
                Operand::plain(boxed, Repr::Boxed, bottom_ty())
            });
            self.cur = num_blk;
            self.stack.push(
                Operand::plain(boxed, Repr::Boxed, prim_desc(PRIM_INT32.or(PRIM_DOUBLE)))
                    .with_prov(prov),
            );
            return;
        }
        if prims.intersects(PRIM_INT32) && prims.subset_of(PRIM_INT32 | PRIM_DOUBLE) {
            // Any int32-bearing numeric mask takes the exact-i32 form: on
            // masked-integer code a mixed Int32|Double mask is store-typing
            // imprecision, not a real double population, and an F64 carrier
            // there pessimizes the bitop traffic around it. A real double
            // just takes the boxed continuation: self-correcting, no deopt.
            self.int32_chk_census("push_load_typed");
            let is_int = self.tag_eq(boxed, TAG_INT32 as u32);
            let arr = self.arr_fold;
            let is_int = match arr {
                None => is_int,
                Some(a) => {
                    let w = self.load_i32(a.recv_ptr, OBJ_CLASS_IDX_OFFSET);
                    self.eff(w, Eff::ReadBits(HeapKind::ClassWord));
                    let wv = self.i32_const(a.want_word);
                    let ok = self.binop(Operator::I32Eq, w, wv, Type::I32);
                    self.binop(Operator::I32And, is_int, ok, Type::I32)
                }
            };
            let int_blk = self.body.add_block();
            let other_blk = self.body.add_block();
            self.cond_br(is_int, int_blk, other_blk);
            self.side_arm(other_blk, next_pc, move |_| {
                Operand::plain(boxed, Repr::Boxed, bottom_ty())
            });
            self.cur = int_blk;
            let w = self.unop(Operator::I32WrapI64, boxed, Type::I32);
            let o = Operand::plain(w, Repr::I32, prim_desc(PRIM_INT32)).with_prov(prov);
            self.stack.push(match arr {
                Some(a) => o.with_iv(opsem::iv_ok(a.range.lo, a.range.hi, false)),
                None => o,
            });
        } else if prims == PRIM_STRING || prims == PRIM_BOOLEAN || prims == PRIM_SYMBOL {
            // Single-tag non-numeric claims (the string/boolean tier;
            // symbols since the identity compares):
            // one tag test, the fall-through commits to the exact prim --
            // string ops and truthiness tests elide their re-tests against
            // it, a strict compare against a symbol is a bit compare, and
            // version seams hand out the StrPtr/Bool reprs from the slot
            // fact. The value stays boxed in-op; the repr payoff is the
            // seams'.
            let (tag, mask) = if prims == PRIM_STRING {
                (TAG_STRING, PRIM_STRING)
            } else if prims == PRIM_BOOLEAN {
                (TAG_BOOLEAN, PRIM_BOOLEAN)
            } else {
                (TAG_SYMBOL, PRIM_SYMBOL)
            };
            let is_hit = self.tag_eq(boxed, tag as u32);
            let hit_blk = self.body.add_block();
            let other_blk = self.body.add_block();
            self.cond_br(is_hit, hit_blk, other_blk);
            self.side_arm(other_blk, next_pc, move |_| {
                Operand::plain(boxed, Repr::Boxed, bottom_ty())
            });
            self.cur = hit_blk;
            self.stack
                .push(Operand::plain(boxed, Repr::Boxed, prim_desc(mask)).with_prov(prov));
        } else if prims == PRIM_DOUBLE {
            // The exact mirror of the int32 arm, and it must stay that
            // cheap: one tag compare and a bare reinterpret rather than a
            // branchless int/double select (a double-tagged nunbox IS its
            // f64 bits), and the fall-through commits to exact
            // `PRIM_DOUBLE`.
            //
            // Do not widen this arm to mixed `Int32|Double` masks. Measured
            // in both the select and the bare-reinterpret form, it is a
            // double-digit loss on numeric array code at identical version
            // and LICM counts. The prediction is not the problem -- the F64
            // carrier is, and it shows up as several times the L1
            // data-cache load misses per unit of work.
            let is_dbl = self.is_double_tag(boxed);
            let dbl_blk = self.body.add_block();
            let other_blk = self.body.add_block();
            self.cond_br(is_dbl, dbl_blk, other_blk);
            self.side_arm(other_blk, next_pc, move |_| {
                Operand::plain(boxed, Repr::Boxed, bottom_ty())
            });
            self.cur = dbl_blk;
            let f = self.unop(Operator::F64ReinterpretI64, boxed, Type::F64);
            let o = Operand::plain(f, Repr::F64, prim_desc(PRIM_DOUBLE)).with_prov(prov);
            self.stack.push(o);
        } else {
            self.push_boxed(boxed, bottom_ty());
        }
    }

    /// `Add`/`Sub` (source: emit_add / emit_arith + emit_tagguarded_arith).
    pub(super) fn emit_addsub_op(&mut self, is_add: bool, succ_pc: Pc) -> Result<(), String> {
        self.emit_guard_census(census::ARITH_FAST, self.cur_pc);
        if self.outline_generic() {
            if is_add {
                let b = self.pop()?;
                let a = self.pop()?;
                let ab = self.to_boxed(&a);
                let bb = self.to_boxed(&b);
                self.emit_guard_census(census::ARITH_SLOW, self.cur_pc);
                let add = self.helpers.add;
                let r = self.rt_call(add, true, |_, _| vec![ab, bb]).unwrap();
                self.push_boxed(r, bottom_ty());
                return Ok(());
            }
            return self.emit_generic_binop_kind(BINOP_SUB);
        }
        let b = refine_by_repr(&self.pop()?);
        let a = refine_by_repr(&self.pop()?);
        let i64_op = if is_add {
            Operator::I64Add
        } else {
            Operator::I64Sub
        };
        let f64_op = if is_add {
            Operator::F64Add
        } else {
            Operator::F64Sub
        };
        let riv = if is_add {
            opsem::iv_add(op_iv(&a), op_iv(&b))
        } else {
            opsem::iv_sub(op_iv(&a), op_iv(&b))
        };
        if is_exact_int32(&a.ty) && is_exact_int32(&b.ty) {
            self.emit_rely_census(census::RELY_ARITH_I32, a.prov.or(b.prov));
            let a64 = self.to_i64_exact(&a);
            let b64 = self.to_i64_exact(&b);
            let sum = self.binop(i64_op, a64, b64, Type::I64);
            self.int_result_or_ovf(sum, succ_pc, riv, a.prov.or(b.prov));
            return Ok(());
        }
        // Exact-integer track: the interval
        // analysis bounds the result to the i64 domain and both operands
        // materialize as exact i64s -- one i64 op, no conversions and no
        // overflow test, and the result rides `Repr::I64` to its consumers
        // (a bitop reads its low 32 bits AS the ToInt32).
        if self.opts.diagnostics.bbv
            && self.mode == EmitMode::Code
            && opsem::iv_clean(riv).is_none()
            && i64_arith_operand_ok(&a)
            && i64_arith_operand_ok(&b)
        {
            crate::diag_line!(
                "night: rungdecl addsub sid#{} pc {} track {:?} a({:?} m{:#x} iv{:?}) b({:?} m{:#x} iv{:?}) riv{:?}",
                self.source_id,
                self.evid_pc(self.cur_pc),
                self.cur_track,
                a.repr,
                a.ty.prims.bits(),
                op_iv(&a),
                b.repr,
                b.ty.prims.bits(),
                op_iv(&b),
                riv,
            );
        }
        if opsem::iv_clean(riv).is_some() && i64_arith_operand_ok(&a) && i64_arith_operand_ok(&b) {
            self.emit_rely_census(census::RELY_IV_RUNG, a.prov.or(b.prov));
            if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
                crate::diag_line!(
                    "night: rungadm addsub sid#{} pc {} track {:?}",
                    self.source_id,
                    self.evid_pc(self.cur_pc),
                    self.cur_track
                );
            }
            let ty = self.result_ty_iv(PRIM_INT32 | PRIM_DOUBLE, riv);
            let a64 = self.to_i64_exact(&a);
            let b64 = self.to_i64_exact(&b);
            let r = self.binop(i64_op, a64, b64, Type::I64);
            self.stack.push(
                Operand::ranged(r, Repr::I64, ty, RangeBucket::I53)
                    .with_iv(riv)
                    .with_prov(a.prov.or(b.prov)),
            );
            return Ok(());
        }
        if is_numeric(&a.ty) && is_numeric(&b.ty) {
            self.emit_rely_census(census::RELY_ARITH_NUM, a.prov.or(b.prov));
            // The interval rides the f64 result too: f64 evaluation of the
            // modeled ops over in-domain integer operands is bit-exact (the
            // opsem `Iv` contract).
            let ty = self.result_ty_iv(f64_result_prims(&a, &b), riv);
            let af = self.to_f64(&a);
            let bf = self.to_f64(&b);
            let r = self.binop(f64_op, af, bf, Type::F64);
            self.stack.push(
                Operand::plain(r, Repr::F64, ty)
                    .with_iv(riv)
                    .with_prov(a.prov.or(b.prov)),
            );
            return Ok(());
        }
        // String `+`: with a proven-string operand the result is a string
        // no matter what the other side holds. The both-string route calls
        // the quiet concat helper (no user code, no pre-existing-heap
        // writes: carriers sweep, facts and track stay); the residual
        // (other side not a string -- its ToPrimitive may run user code)
        // is the ordinary stepping arm through the generic add helper,
        // whose result is still a proven string.
        if is_add && (is_string_only(&a.ty) || is_string_only(&b.ty)) {
            let mut strp = Prov::NONE;
            if is_string_only(&a.ty) {
                strp = strp.or(a.prov);
            }
            if is_string_only(&b.ty) {
                strp = strp.or(b.prov);
            }
            self.emit_rely_census(census::RELY_STRING, strp);
            let ab = self.to_boxed(&a);
            let bb = self.to_boxed(&b);
            let str_ty = prim_desc(PRIM_STRING);
            let other = match (is_string_only(&a.ty), is_string_only(&b.ty)) {
                (true, true) => None,
                (true, false) => Some(bb),
                _ => Some(ab),
            };
            if let Some(other) = other {
                let is_s = self.tag_eq(other, TAG_STRING as u32);
                let cat_blk = self.body.add_block();
                let slow_blk = self.body.add_block();
                self.cond_br(is_s, cat_blk, slow_blk);
                let sty = str_ty;
                self.side_arm(slow_blk, succ_pc, move |s| {
                    s.emit_guard_census(census::ARITH_SLOW, s.cur_pc);
                    let add = s.helpers.add;
                    let r = s.rt_call(add, true, |_, _| vec![ab, bb]).unwrap();
                    Operand::plain(r, Repr::Boxed, sty)
                });
                self.cur = cat_blk;
            }
            let concat = self.helpers.concat;
            let r = self.rt_call(concat, true, |_, _| vec![ab, bb]).unwrap();
            let mut sp = Prov::NONE;
            if is_string_only(&a.ty) {
                sp = sp.or(a.prov);
            }
            if is_string_only(&b.ty) {
                sp = sp.or(b.prov);
            }
            self.stack
                .push(Operand::plain(r, Repr::Boxed, str_ty).with_prov(sp));
            return Ok(());
        }
        if self.opts.diagnostics.bbv {
            crate::diag_line!(
                "night: bbv arithgen sid#{} pc {} op {:?} a({:?} mask {:?} out {}) b({:?} mask {:?} out {}) ver {}",
                self.source_id, self.cur_pc, self.cur_op,
                a.repr, a.ty.prims, u8::from(a.ty.outside),
                b.repr, b.ty.prims, u8::from(b.ty.outside),
                {
                    let v = self.vers.ver(self.cur_ver);
                    format!("{:?}/class{}", v.track, v.class)
                }
            );
        }
        // One operand a raw f64 the analysis calls numeric and not int32,
        // the other untyped, at a fractional site: the int32 arm cannot
        // fall through (a non-int32 f64 operand never makes an int32
        // result), so the double arm IS the fall-through -- one number-tag
        // test on the untyped operand, its select unbox, the f64 op, an
        // F64 result. The ladder below canonically boxed the f64 to
        // tag-test it, ran the dead int32 tests, boxed the double result on
        // its side arm and had the successor unbox it again: 53 IR against
        // 14 on box2d's solver before its velocity fields had a class.
        // Gated on fractional evidence exactly as the side arm's keep is:
        // at an integer site the F64 fall-through would retype the chain.
        let a_rawf = raw_frac_operand(&a) && !is_numeric(&b.ty);
        let b_rawf = raw_frac_operand(&b) && !is_numeric(&a.ty);
        if self.frac_site() && (a_rawf || b_rawf) {
            self.emit_rely_census(census::RELY_ARITH_NUM, a.prov.or(b.prov));
            // The raw operand's box is the helper arm's alone: built there,
            // never on the fall-through.
            let other = if a_rawf { &b } else { &a };
            let ob = self.to_boxed(other);
            let (ab, bb) = if a_rawf {
                (None, Some(ob))
            } else {
                (Some(ob), None)
            };
            let is_num = self.is_number_tag(ob);
            let num_blk = self.body.add_block();
            let slow_blk = self.body.add_block();
            self.cond_br(is_num, num_blk, slow_blk);
            self.addsub_slow_arms(is_add, slow_blk, succ_pc, &a, &b, ab, bb, riv);
            self.cur = num_blk;
            let of = self.unbox_number_f64(ob);
            let (af, bf) = if a_rawf { (a.val, of) } else { (of, b.val) };
            let r = self.binop(f64_op, af, bf, Type::F64);
            self.stack.push(
                Operand::plain(r, Repr::F64, prim_desc(PRIM_INT32 | PRIM_DOUBLE))
                    .with_iv(riv)
                    .with_prov(Prov::T_ARITH),
            );
            return Ok(());
        }
        let ab = self.ladder_box(&a);
        let bb = self.ladder_box(&b);
        self.int32_chk_census("both_int32");
        let ta = self.int32_tag_test(&a, ab);
        let tb = self.int32_tag_test(&b, bb);
        let both = self.and_tests(ta, tb);
        let int_blk = self.body.add_block();
        let rest_blk = self.body.add_block();
        self.cond_br_opt(both, int_blk, rest_blk);
        self.cur = rest_blk;
        let na = self.number_tag_test(&a, ab);
        let nb = self.number_tag_test(&b, bb);
        let both_num = self.and_tests(na, nb);
        let f64_blk = self.body.add_block();
        let slow_blk = self.body.add_block();
        self.cond_br_opt(both_num, f64_blk, slow_blk);
        let (a2, b2) = (a.clone(), b.clone());
        self.side_arm_num_if_frac(f64_blk, succ_pc, move |s| {
            s.refine_src(&a2, NUMERIC_SLOT);
            s.refine_src(&b2, NUMERIC_SLOT);
            let af = s.f64_of(&a2, ab);
            let bf = s.f64_of(&b2, bb);
            let rf = s.binop(f64_op, af, bf, Type::F64);
            // The result rides out raw: the edge converts it to whatever
            // repr the successor's slot has, and boxing it canonically
            // here only ever paid twice (the successor's F64 slot unboxed
            // it straight back). The vocabulary result interval holds on
            // every arm (a Some riv means both operands were proven
            // numbers), and every arm must carry it or the succ join kills
            // the slot fact.
            Operand::plain(rf, Repr::F64, prim_desc(PRIM_INT32 | PRIM_DOUBLE))
                .with_iv(riv)
                .with_prov(Prov::T_ARITH)
        });
        self.addsub_slow_arms(is_add, slow_blk, succ_pc, &a, &b, ab, bb, riv);
        self.cur = int_blk;
        self.refine_src(&a, INT32_SLOT);
        self.refine_src(&b, INT32_SLOT);
        let ai = self.int32_payload(&a, ab);
        let bi = self.int32_payload(&b, bb);
        let a64 = self.unop(Operator::I64ExtendI32S, ai, Type::I64);
        let b64 = self.unop(Operator::I64ExtendI32S, bi, Type::I64);
        let sum = self.binop(i64_op, a64, b64, Type::I64);
        // The passed tag guard proves int32 operands: the arm-local result
        // interval holds whatever the static masks said.
        let arm_riv = if is_add {
            opsem::iv_add(opsem::IV_I32, opsem::IV_I32)
        } else {
            opsem::iv_sub(opsem::IV_I32, opsem::IV_I32)
        };
        self.int_result_or_ovf(sum, succ_pc, arm_riv, Prov::T_ARITH);
        Ok(())
    }

    /// The `Add`/`Sub` ladder's non-number arms from `slow_blk`: the
    /// both-string concat arm where the site has string evidence, then
    /// the stepping helper arm.
    #[allow(clippy::too_many_arguments)]
    fn addsub_slow_arms(
        &mut self,
        is_add: bool,
        slow_blk: Block,
        succ_pc: Pc,
        a: &Operand,
        b: &Operand,
        ab: Option<Value>,
        bb: Option<Value>,
        riv: opsem::Iv,
    ) {
        // Both-string concat arm, only at sites with string evidence on the
        // result cell (the string analog of the fractional gate): the arm
        // keeps the Opt track through the quiet concat helper, and its
        // string result joining a genuinely-numeric site's successor would
        // otherwise degrade the chain's facts for an arm that never runs.
        // Ungating it pays the join at compile time at every `+`, whether
        // or not a string ever arrives. The sites the analysis cannot
        // type (the self-hosted String.replace accumulators) stay on the
        // stepping arm.
        let mut slow_end = slow_blk;
        // An exact-int32 operand can never be a string: the concat arm is
        // dead at such a site.
        let string_site = is_add
            && self
                .ctx
                .facts
                .string_arith_sites
                .contains(&Site::new(self.source_id, self.evid_pc(self.cur_pc)));
        if let (true, Some(ab), Some(bb)) = (string_site, ab, bb) {
            self.cur = slow_blk;
            let a_s = self.tag_eq(ab, TAG_STRING as u32);
            let b_s = self.tag_eq(bb, TAG_STRING as u32);
            let both_s = self.binop(Operator::I32And, a_s, b_s, Type::I32);
            let cat_blk = self.body.add_block();
            let slow2 = self.body.add_block();
            self.cond_br(both_s, cat_blk, slow2);
            self.side_arm_num(cat_blk, succ_pc, move |s| {
                let concat = s.helpers.concat;
                let r = s.rt_call(concat, true, |_, _| vec![ab, bb]).unwrap();
                Operand::plain(r, Repr::Boxed, prim_desc(PRIM_STRING))
            });
            slow_end = slow2;
        }
        let (a3, b3) = (a.clone(), b.clone());
        // The helper arm steps: an epoch-kept `+` helper rejoins the
        // successor with a bottom-typed result and boxes the int32 chain
        // behind it (measured, see the concat gate above).
        self.side_arm(slow_end, succ_pc, move |s| {
            if is_add {
                s.emit_guard_census(census::ARITH_SLOW, s.cur_pc);
                let add = s.helpers.add;
                let ab = s.box_of(&a3, ab);
                let bb = s.box_of(&b3, bb);
                let r = s.rt_call(add, true, |_, _| vec![ab, bb]).unwrap();
                // `+` may concat: no result fact (a Some riv proves both
                // operands numbers, so the interval still holds).
                Operand::plain(r, Repr::Boxed, bottom_ty()).with_iv(riv)
            } else {
                s.emit_guard_census(census::ARITH_SLOW, s.cur_pc);
                let binop = s.helpers.binop;
                let r = s.emit_value_binop(binop, BINOP_SUB, &a3, &b3);
                s.bigint_result(r, PRIM_INT32 | PRIM_DOUBLE, riv, succ_pc)
            }
        });
    }

    /// `Mul`/`Div` (source: emit_arith numeric path + emit_tagguarded_f64_only).
    /// `/` has no exact form (float semantics); `*` of two exact int32s does
    /// -- see `int_mul_result_or_ovf`.
    pub(super) fn emit_muldiv_op(&mut self, kind: u32, succ_pc: Pc) -> Result<(), String> {
        self.emit_guard_census(census::ARITH_FAST, self.cur_pc);
        if self.outline_generic() {
            return self.emit_generic_binop_kind(kind);
        }
        let b = refine_by_repr(&self.pop()?);
        let a = refine_by_repr(&self.pop()?);
        let f64_op = f64_arith_op(kind).unwrap();
        // Disregard overflow. An int32 product is
        // typed exact Int32 with the rare overflow (and the rarer -0) taken
        // by a side arm, rather than typing every downstream use "might be
        // a double" -- an f64 result here poisons the whole consuming chain
        // off the exact-i32 track.
        let riv = if kind == BINOP_MUL {
            opsem::iv_mul(op_iv(&a), op_iv(&b))
        } else {
            None
        };
        if kind == BINOP_MUL && is_exact_int32(&a.ty) && is_exact_int32(&b.ty) {
            self.emit_rely_census(census::RELY_ARITH_I32, a.prov.or(b.prov));
            let a64 = self.to_i64_exact(&a);
            let b64 = self.to_i64_exact(&b);
            let prod = self.binop(Operator::I64Mul, a64, b64, Type::I64);
            // Interval elision: the full overflow/-0 ladder is a large
            // fraction of a hot integer multiply. A product interval inside
            // int32 makes the overflow half dead; a clean interval also
            // kills the -0 test; a -0-flagged in-range product keeps only
            // the slim -0 test in front of the same f64 side arm.
            match riv {
                Some((lo, hi, nz)) if lo >= opsem::I32_LO && hi <= opsem::I32_HI => {
                    self.emit_rely_census(census::RELY_IV_RUNG, a.prov.or(b.prov));
                    if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
                        crate::diag_line!(
                            "night: mulcln sid#{} pc {} nz {}",
                            self.source_id,
                            self.evid_pc(self.cur_pc),
                            u8::from(nz)
                        );
                    }
                    if nz {
                        self.int_mul_result_or_ovf(
                            prod,
                            a64,
                            b64,
                            succ_pc,
                            riv,
                            false,
                            a.prov.or(b.prov),
                        );
                    } else {
                        let w = self.unop(Operator::I32WrapI64, prod, Type::I32);
                        self.stack.push(
                            Operand::plain(w, Repr::I32, prim_desc(PRIM_INT32))
                                .with_iv(riv)
                                .with_prov(a.prov.or(b.prov)),
                        );
                    }
                }
                // Truncation demand for a product outside int32: every
                // consumer coerces through ToInt32 (directly or via
                // demanded Add/Sub links), so the wrapped i64 product IS
                // the observed value -- provided the spec-side chain stays
                // f64-exact. The +-2^47 bound is this node's 2^16-unit
                // claim in the walk's budget (see `trunc_demanded`), which
                // caps every demanded chain's spec value at 2^53; -0 is
                // unobservable through ToInt32. No result interval: the
                // wrapped value's range is not the op's.
                Some((lo, hi, _))
                    if lo >= -(1i64 << 47)
                        && hi <= (1i64 << 47)
                        && self.trunc_demanded(self.cur_pc) =>
                {
                    if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
                        crate::diag_line!(
                            "night: multrunc sid#{} pc {}",
                            self.source_id,
                            self.evid_pc(self.cur_pc)
                        );
                    }
                    let w = self.unop(Operator::I32WrapI64, prod, Type::I32);
                    self.stack.push(
                        Operand::plain(w, Repr::I32, prim_desc(PRIM_INT32))
                            .with_prov(a.prov.or(b.prov)),
                    );
                }
                _ => {
                    self.int_mul_result_or_ovf(
                        prod,
                        a64,
                        b64,
                        succ_pc,
                        riv,
                        true,
                        a.prov.or(b.prov),
                    );
                }
            }
            return Ok(());
        }
        // Exact-integer track: `*` only (the interval proves the product is
        // an in-domain integer and never -0, which is the case f64 mul would
        // have had to reproduce). `/` has no integer form.
        if kind == BINOP_MUL
            && opsem::iv_clean(riv).is_some()
            && i64_arith_operand_ok(&a)
            && i64_arith_operand_ok(&b)
        {
            self.emit_rely_census(census::RELY_IV_RUNG, a.prov.or(b.prov));
            if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
                crate::diag_line!(
                    "night: rungadm mul sid#{} pc {} track {:?}",
                    self.source_id,
                    self.evid_pc(self.cur_pc),
                    self.cur_track
                );
            }
            let ty = self.result_ty_iv(PRIM_INT32 | PRIM_DOUBLE, riv);
            let a64 = self.to_i64_exact(&a);
            let b64 = self.to_i64_exact(&b);
            let r = self.binop(Operator::I64Mul, a64, b64, Type::I64);
            self.stack.push(
                Operand::ranged(r, Repr::I64, ty, RangeBucket::I53)
                    .with_iv(riv)
                    .with_prov(a.prov.or(b.prov)),
            );
            return Ok(());
        }
        if is_numeric(&a.ty) && is_numeric(&b.ty) {
            self.emit_rely_census(census::RELY_ARITH_NUM, a.prov.or(b.prov));
            let ty = self.result_ty_iv(f64_result_prims(&a, &b), riv);
            let af = self.to_f64(&a);
            let bf = self.to_f64(&b);
            let r = self.binop(f64_op, af, bf, Type::F64);
            self.stack.push(
                Operand::plain(r, Repr::F64, ty)
                    .with_iv(riv)
                    .with_prov(a.prov.or(b.prov)),
            );
            return Ok(());
        }
        let ab = self.ladder_box(&a);
        let bb = self.ladder_box(&b);
        let na = self.number_tag_test(&a, ab);
        let nb = self.number_tag_test(&b, bb);
        let both_num = self.and_tests(na, nb);
        let num_blk = self.body.add_block();
        let slow_blk = self.body.add_block();
        self.cond_br_opt(both_num, num_blk, slow_blk);
        let (a4, b4) = (a.clone(), b.clone());
        self.side_arm(slow_blk, succ_pc, move |s| {
            s.emit_guard_census(census::ARITH_SLOW, s.cur_pc);
            let binop = s.helpers.binop;
            let r = s.emit_value_binop(binop, kind, &a, &b);
            s.bigint_result(r, PRIM_INT32 | PRIM_DOUBLE, riv, succ_pc)
        });
        self.cur = num_blk;
        self.refine_src(&a4, NUMERIC_SLOT);
        self.refine_src(&b4, NUMERIC_SLOT);
        let af = self.f64_of(&a4, ab);
        let bf = self.f64_of(&b4, bb);
        let r = self.binop(f64_op, af, bf, Type::F64);
        self.stack.push(
            Operand::plain(r, Repr::F64, prim_desc(PRIM_INT32 | PRIM_DOUBLE))
                .with_iv(riv)
                .with_prov(Prov::T_ARITH),
        );
        Ok(())
    }

    /// `Mod` (source: emit_arith's range-proof fmod form): the number arm is
    /// the leaf `night_runtime_fmod` (`js::NumberMod`, dividend-signed).
    pub(super) fn emit_mod_op(&mut self, succ_pc: Pc) -> Result<(), String> {
        self.emit_guard_census(census::ARITH_FAST, self.cur_pc);
        if self.outline_generic() {
            return self.emit_generic_binop_kind(BINOP_MOD);
        }
        let b = refine_by_repr(&self.pop()?);
        let a = refine_by_repr(&self.pop()?);
        // Exact-integer track: an interval at a `%` pc carries `iv_mod`'s own
        // preconditions (non-negative dividend, divisor excluding zero), so
        // `i64.rem_s` neither traps nor disagrees with JS's sign rule.
        // The rung admission IS `iv_mod`'s preconditions (non-negative
        // dividend, divisor excluding zero), proven from the ctx operand
        // intervals, so `i64.rem_s` neither traps nor disagrees with JS's
        // sign rule.
        let riv = opsem::iv_mod(op_iv(&a), op_iv(&b));
        if opsem::iv_clean(riv).is_some() && i64_arith_operand_ok(&a) && i64_arith_operand_ok(&b) {
            self.emit_rely_census(census::RELY_IV_RUNG, a.prov.or(b.prov));
            if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
                crate::diag_line!(
                    "night: rungadm mod sid#{} pc {} track {:?}",
                    self.source_id,
                    self.evid_pc(self.cur_pc),
                    self.cur_track
                );
            }
            let ty = self.result_ty_iv(PRIM_INT32 | PRIM_DOUBLE, riv);
            let a64 = self.to_i64_exact(&a);
            let b64 = self.to_i64_exact(&b);
            let r = self.binop(Operator::I64RemS, a64, b64, Type::I64);
            self.stack.push(
                Operand::ranged(r, Repr::I64, ty, RangeBucket::I53)
                    .with_iv(riv)
                    .with_prov(a.prov.or(b.prov)),
            );
            return Ok(());
        }
        if is_numeric(&a.ty) && is_numeric(&b.ty) {
            self.emit_rely_census(census::RELY_ARITH_NUM, a.prov.or(b.prov));
            let af = self.to_f64(&a);
            let bf = self.to_f64(&b);
            let fmod = self.helpers.fmod;
            let r = self.call_f64(fmod, &[af, bf]);
            self.stack.push(
                Operand::plain(r, Repr::F64, prim_desc(PRIM_INT32 | PRIM_DOUBLE))
                    .with_iv(riv)
                    .with_prov(a.prov.or(b.prov)),
            );
            return Ok(());
        }
        let ab = self.ladder_box(&a);
        let bb = self.ladder_box(&b);
        let na = self.number_tag_test(&a, ab);
        let nb = self.number_tag_test(&b, bb);
        let both_num = self.and_tests(na, nb);
        let num_blk = self.body.add_block();
        let slow_blk = self.body.add_block();
        self.cond_br_opt(both_num, num_blk, slow_blk);
        let (a4, b4) = (a.clone(), b.clone());
        self.side_arm(slow_blk, succ_pc, move |s| {
            s.emit_guard_census(census::ARITH_SLOW, s.cur_pc);
            let binop = s.helpers.binop;
            let r = s.emit_value_binop(binop, BINOP_MOD, &a, &b);
            s.bigint_result(r, PRIM_INT32 | PRIM_DOUBLE, riv, succ_pc)
        });
        self.cur = num_blk;
        self.refine_src(&a4, NUMERIC_SLOT);
        self.refine_src(&b4, NUMERIC_SLOT);
        let af = self.f64_of(&a4, ab);
        let bf = self.f64_of(&b4, bb);
        let fmod = self.helpers.fmod;
        let r = self.call_f64(fmod, &[af, bf]);
        self.stack.push(
            Operand::plain(r, Repr::F64, prim_desc(PRIM_INT32 | PRIM_DOUBLE))
                .with_iv(riv)
                .with_prov(Prov::T_ARITH),
        );
        Ok(())
    }

    /// The bitops with an int32 result (`&`/`|`/`^`/`<<`/`>>`): defined by
    /// ToInt32 on both operands (source: emit_arith + the W1 any-double
    /// to_int32_js form). Wasm shifts mask the count mod 32, matching JS.
    pub(super) fn emit_bitop(
        &mut self,
        wasm_op: Operator,
        kind: u32,
        succ_pc: Pc,
    ) -> Result<(), String> {
        self.emit_guard_census(census::ARITH_FAST, self.cur_pc);
        if self.outline_generic() {
            return self.emit_generic_binop_kind(kind);
        }
        let b = refine_by_repr(&self.pop()?);
        let a = refine_by_repr(&self.pop()?);
        let riv = match kind {
            BINOP_BITAND => opsem::iv_bitand(op_iv(&a), op_iv(&b)),
            BINOP_BITOR | BINOP_BITXOR => opsem::iv_bitorxor(op_iv(&a), op_iv(&b)),
            BINOP_LSH => opsem::iv_lsh(op_iv(&a), op_iv(&b)),
            _ => opsem::iv_rsh(op_iv(&a), op_iv(&b)),
        };
        if int32_wrap_operand_ok(&a) && int32_wrap_operand_ok(&b) {
            self.emit_rely_census(census::RELY_ARITH_I32, a.prov.or(b.prov));
            let ai = self.to_i32(&a);
            let bi = self.to_i32(&b);
            let r = self.binop(wasm_op, ai, bi, Type::I32);
            self.stack
                .push(Operand::plain(r, Repr::I32, prim_desc(PRIM_INT32)).with_iv(riv));
            return Ok(());
        }
        if is_numeric(&a.ty) && is_numeric(&b.ty) {
            self.emit_rely_census(census::RELY_ARITH_NUM, a.prov.or(b.prov));
            let af = self.to_f64(&a);
            let ai = self.to_int32_js(af);
            let bf = self.to_f64(&b);
            let bi = self.to_int32_js(bf);
            let r = self.binop(wasm_op, ai, bi, Type::I32);
            self.stack
                .push(Operand::plain(r, Repr::I32, prim_desc(PRIM_INT32)).with_iv(riv));
            return Ok(());
        }
        let ab = self.ladder_box(&a);
        let bb = self.ladder_box(&b);
        self.int32_chk_census("both_int32");
        let ta = self.int32_tag_test(&a, ab);
        let tb = self.int32_tag_test(&b, bb);
        let both = self.and_tests(ta, tb);
        let int_blk = self.body.add_block();
        let rest_blk = self.body.add_block();
        self.cond_br_opt(both, int_blk, rest_blk);
        self.cur = rest_blk;
        // A boolean operand (`(x >= y) & 1`, the comparison-to-int idiom)
        // coerces to its 0/1 payload, exactly the int32 wrap; no fact
        // refinement, since
        // the tag proved int32-or-boolean, not int32. An exact-int32
        // operand needs no test on this arm either.
        let ib_a = self.int32_or_bool_test(&a, ab);
        let ib_b = self.int32_or_bool_test(&b, bb);
        let both_ib = self.and_tests(ib_a, ib_b);
        let ib_blk = self.body.add_block();
        let rest2_blk = self.body.add_block();
        self.cond_br_opt(both_ib, ib_blk, rest2_blk);
        let (a5, b5) = (a.clone(), b.clone());
        self.side_arm_num(ib_blk, succ_pc, move |s| {
            let ai = s.int32_payload(&a5, ab);
            let bi = s.int32_payload(&b5, bb);
            let r = s.binop(wasm_op, ai, bi, Type::I32);
            Operand::plain(r, Repr::I32, prim_desc(PRIM_INT32)).with_iv(riv)
        });
        self.cur = rest2_blk;
        let na = self.number_tag_test(&a, ab);
        let nb = self.number_tag_test(&b, bb);
        let both_num = self.and_tests(na, nb);
        let num_blk = self.body.add_block();
        let slow_blk = self.body.add_block();
        self.cond_br_opt(both_num, num_blk, slow_blk);
        let (a2, b2) = (a.clone(), b.clone());
        self.side_arm_num(num_blk, succ_pc, move |s| {
            s.refine_src(&a2, NUMERIC_SLOT);
            s.refine_src(&b2, NUMERIC_SLOT);
            let af = s.f64_of(&a2, ab);
            let ai = s.to_int32_js(af);
            let bf = s.f64_of(&b2, bb);
            let bi = s.to_int32_js(bf);
            let r = s.binop(wasm_op, ai, bi, Type::I32);
            Operand::plain(r, Repr::I32, prim_desc(PRIM_INT32)).with_iv(riv)
        });
        self.side_arm(slow_blk, succ_pc, |s| {
            s.emit_guard_census(census::ARITH_SLOW, s.cur_pc);
            let binop = s.helpers.binop;
            let r = s.emit_value_binop(binop, kind, &a, &b);
            s.bigint_result(r, PRIM_INT32, None, succ_pc)
        });
        self.cur = int_blk;
        self.refine_src(&a, INT32_SLOT);
        self.refine_src(&b, INT32_SLOT);
        let ai = self.int32_payload(&a, ab);
        let bi = self.int32_payload(&b, bb);
        let r = self.binop(wasm_op, ai, bi, Type::I32);
        self.stack
            .push(Operand::plain(r, Repr::I32, prim_desc(PRIM_INT32)).with_iv(riv));
        Ok(())
    }

    /// `>>>` (source: emit_arith's Ursh forms): the u32 result rides
    /// `Repr::I64` in-domain (range I53). BigInt `>>>` throws, so the slow
    /// arm's success result is a number.
    pub(super) fn emit_ursh_op(&mut self, succ_pc: Pc) -> Result<(), String> {
        self.emit_guard_census(census::ARITH_FAST, self.cur_pc);
        if self.outline_generic() {
            return self.emit_generic_binop_kind(BINOP_URSH);
        }
        let b = refine_by_repr(&self.pop()?);
        let a = refine_by_repr(&self.pop()?);
        let num_ty = prim_desc(PRIM_INT32 | PRIM_DOUBLE);
        let riv = opsem::iv_ursh(op_iv(&a), op_iv(&b));
        if int32_wrap_operand_ok(&a) && int32_wrap_operand_ok(&b) {
            self.emit_rely_census(census::RELY_ARITH_I32, a.prov.or(b.prov));
            let ai = self.to_i32(&a);
            let bi = self.to_i32(&b);
            let r32 = self.binop(Operator::I32ShrU, ai, bi, Type::I32);
            let r = self.unop(Operator::I64ExtendI32U, r32, Type::I64);
            self.stack
                .push(Operand::ranged(r, Repr::I64, num_ty, RangeBucket::I53).with_iv(riv));
            return Ok(());
        }
        if is_numeric(&a.ty) && is_numeric(&b.ty) {
            self.emit_rely_census(census::RELY_ARITH_NUM, a.prov.or(b.prov));
            let af = self.to_f64(&a);
            let ai = self.to_int32_js(af);
            let bf = self.to_f64(&b);
            let bi = self.to_int32_js(bf);
            let r32 = self.binop(Operator::I32ShrU, ai, bi, Type::I32);
            let r = self.unop(Operator::I64ExtendI32U, r32, Type::I64);
            self.stack
                .push(Operand::ranged(r, Repr::I64, num_ty, RangeBucket::I53).with_iv(riv));
            return Ok(());
        }
        let ab = self.ladder_box(&a);
        let bb = self.ladder_box(&b);
        self.int32_chk_census("both_int32");
        let ta = self.int32_tag_test(&a, ab);
        let tb = self.int32_tag_test(&b, bb);
        let both = self.and_tests(ta, tb);
        let int_blk = self.body.add_block();
        let rest_blk = self.body.add_block();
        self.cond_br_opt(both, int_blk, rest_blk);
        self.cur = rest_blk;
        let na = self.number_tag_test(&a, ab);
        let nb = self.number_tag_test(&b, bb);
        let both_num = self.and_tests(na, nb);
        let num_blk = self.body.add_block();
        let slow_blk = self.body.add_block();
        self.cond_br_opt(both_num, num_blk, slow_blk);
        {
            let (a6, b6) = (a.clone(), b.clone());
            self.side_arm_num(num_blk, succ_pc, move |s| {
                let af = s.f64_of(&a6, ab);
                let ai = s.to_int32_js(af);
                let bf = s.f64_of(&b6, bb);
                let bi = s.to_int32_js(bf);
                let r32 = s.binop(Operator::I32ShrU, ai, bi, Type::I32);
                let r = s.unop(Operator::I64ExtendI32U, r32, Type::I64);
                Operand::ranged(r, Repr::I64, num_ty, RangeBucket::I53)
            });
        }
        let (a2, b2) = (a.clone(), b.clone());
        {
            self.side_arm(slow_blk, succ_pc, move |s| {
                s.emit_guard_census(census::ARITH_SLOW, s.cur_pc);
                let binop = s.helpers.binop;
                let r = s.emit_value_binop(binop, BINOP_URSH, &a, &b);
                // The slow arm's success value is a number (BigInt `>>>`
                // throws), so the ToUint32 interval holds here too.
                Operand::plain(r, Repr::Boxed, num_ty).with_iv(riv)
            });
        }
        self.cur = int_blk;
        self.refine_src(&a2, INT32_SLOT);
        self.refine_src(&b2, INT32_SLOT);
        let ai = self.int32_payload(&a2, ab);
        let bi = self.int32_payload(&b2, bb);
        let r32 = self.binop(Operator::I32ShrU, ai, bi, Type::I32);
        let r = self.unop(Operator::I64ExtendI32U, r32, Type::I64);
        self.stack
            .push(Operand::ranged(r, Repr::I64, num_ty, RangeBucket::I53).with_iv(riv));
        Ok(())
    }

    /// `Inc`/`Dec` (post-ToNumeric operand; may be BigInt). Source:
    /// emit_arith's int32_unop_addk generic arm + the addsub ladder.
    pub(super) fn emit_incdec_op(&mut self, is_inc: bool, succ_pc: Pc) -> Result<(), String> {
        self.emit_guard_census(census::ARITH_FAST, self.cur_pc);
        if self.outline_generic() {
            let kind = if is_inc { BINOP_INC } else { BINOP_DEC };
            let a = self.pop()?;
            let k_boxed = self.boxed_const((TAG_INT32 << 32) | 1);
            let k_op = Operand::plain(k_boxed, Repr::Boxed, prim_desc(PRIM_INT32));
            self.emit_guard_census(census::ARITH_SLOW, self.cur_pc);
            let binop = self.helpers.binop;
            let r = self.emit_value_binop(binop, kind, &a, &k_op);
            self.push_boxed(r, bottom_ty());
            return Ok(());
        }
        let a = refine_by_repr(&self.pop()?);
        let i64_op = if is_inc {
            Operator::I64Add
        } else {
            Operator::I64Sub
        };
        let f64_op = if is_inc {
            Operator::F64Add
        } else {
            Operator::F64Sub
        };
        let kind = if is_inc { BINOP_INC } else { BINOP_DEC };
        let riv = if is_inc {
            opsem::iv_add(op_iv(&a), Some((1, 1, false)))
        } else {
            opsem::iv_sub(op_iv(&a), Some((1, 1, false)))
        };
        if is_exact_int32(&a.ty) {
            self.emit_rely_census(census::RELY_ARITH_I32, a.prov);
            let a64 = self.to_i64_exact(&a);
            let one = self.boxed_const(1);
            let sum = self.binop(i64_op, a64, one, Type::I64);
            self.int_result_or_ovf(sum, succ_pc, riv, a.prov);
            return Ok(());
        }
        if opsem::iv_clean(riv).is_some() && i64_arith_operand_ok(&a) {
            self.emit_rely_census(census::RELY_IV_RUNG, a.prov);
            if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
                crate::diag_line!(
                    "night: rungadm incdec sid#{} pc {} track {:?}",
                    self.source_id,
                    self.evid_pc(self.cur_pc),
                    self.cur_track
                );
            }
            let ty = self.result_ty_iv(PRIM_INT32 | PRIM_DOUBLE, riv);
            let a64 = self.to_i64_exact(&a);
            let one = self.boxed_const(1);
            let r = self.binop(i64_op, a64, one, Type::I64);
            self.stack.push(
                Operand::ranged(r, Repr::I64, ty, RangeBucket::I53)
                    .with_iv(riv)
                    .with_prov(a.prov),
            );
            return Ok(());
        }
        if is_numeric(&a.ty) {
            self.emit_rely_census(census::RELY_ARITH_NUM, a.prov);
            let ty = self.result_ty_iv(PRIM_INT32 | PRIM_DOUBLE, riv);
            let af = self.to_f64(&a);
            let one = self.f64_const(1.0);
            let r = self.binop(f64_op, af, one, Type::F64);
            self.stack.push(
                Operand::plain(r, Repr::F64, ty)
                    .with_iv(riv)
                    .with_prov(a.prov),
            );
            return Ok(());
        }
        let ab = self.to_boxed(&a);
        let is_int = self.tag_eq(ab, TAG_INT32 as u32);
        let int_blk = self.body.add_block();
        let rest_blk = self.body.add_block();
        self.cond_br(is_int, int_blk, rest_blk);
        self.cur = rest_blk;
        let is_num = self.is_number_tag(ab);
        let num_blk = self.body.add_block();
        let slow_blk = self.body.add_block();
        self.cond_br(is_num, num_blk, slow_blk);
        let a2 = a.clone();
        self.side_arm_num_if_frac(num_blk, succ_pc, move |s| {
            s.refine_src(&a2, NUMERIC_SLOT);
            let af = s.unbox_number_f64(ab);
            let one = s.f64_const(1.0);
            let rf = s.binop(f64_op, af, one, Type::F64);
            let rb = s.box_f64_canonical(rf);
            Operand::plain(rb, Repr::Boxed, prim_desc(PRIM_INT32 | PRIM_DOUBLE))
                .with_iv(riv)
                .with_prov(Prov::T_ARITH)
        });
        let a3 = a.clone();
        self.side_arm(slow_blk, succ_pc, move |s| {
            let k_boxed = s.boxed_const((TAG_INT32 << 32) | 1);
            let k_op = Operand::plain(k_boxed, Repr::Boxed, prim_desc(PRIM_INT32));
            s.emit_guard_census(census::ARITH_SLOW, s.cur_pc);
            let binop = s.helpers.binop;
            let r = s.emit_value_binop(binop, kind, &a3, &k_op);
            s.bigint_result(r, PRIM_INT32 | PRIM_DOUBLE, riv, succ_pc)
        });
        self.cur = int_blk;
        self.refine_src(&a, INT32_SLOT);
        let ai = self.unop(Operator::I32WrapI64, ab, Type::I32);
        let a64 = self.unop(Operator::I64ExtendI32S, ai, Type::I64);
        let one = self.boxed_const(1);
        let sum = self.binop(i64_op, a64, one, Type::I64);
        let arm_riv = if is_inc {
            opsem::iv_add(opsem::IV_I32, Some((1, 1, false)))
        } else {
            opsem::iv_sub(opsem::IV_I32, Some((1, 1, false)))
        };
        self.int_result_or_ovf(sum, succ_pc, arm_riv, Prov::T_ARITH);
        Ok(())
    }

    /// `BitNot` (`~x` = `x ^ -1` after ToInt32).
    pub(super) fn emit_bitnot_op(&mut self, succ_pc: Pc) -> Result<(), String> {
        self.emit_guard_census(census::ARITH_FAST, self.cur_pc);
        if self.outline_generic() {
            let a = self.pop()?;
            let neg1_boxed = self.boxed_const((TAG_INT32 << 32) | 0xFFFF_FFFF);
            let neg1 = Operand::plain(neg1_boxed, Repr::Boxed, prim_desc(PRIM_INT32));
            self.emit_guard_census(census::ARITH_SLOW, self.cur_pc);
            let binop = self.helpers.binop;
            let r = self.emit_value_binop(binop, BINOP_BITNOT, &a, &neg1);
            self.push_boxed(r, bottom_ty());
            return Ok(());
        }
        let a = refine_by_repr(&self.pop()?);
        let riv = opsem::iv_bitnot(op_iv(&a));
        if int32_wrap_operand_ok(&a) {
            self.emit_rely_census(census::RELY_ARITH_I32, a.prov);
            let ai = self.to_i32(&a);
            let neg1 = self.i32_const(0xFFFF_FFFF);
            let r = self.binop(Operator::I32Xor, ai, neg1, Type::I32);
            self.stack
                .push(Operand::plain(r, Repr::I32, prim_desc(PRIM_INT32)).with_iv(riv));
            return Ok(());
        }
        if is_numeric(&a.ty) {
            self.emit_rely_census(census::RELY_ARITH_NUM, a.prov);
            let af = self.to_f64(&a);
            let ai = self.to_int32_js(af);
            let neg1 = self.i32_const(0xFFFF_FFFF);
            let r = self.binop(Operator::I32Xor, ai, neg1, Type::I32);
            self.stack
                .push(Operand::plain(r, Repr::I32, prim_desc(PRIM_INT32)).with_iv(riv));
            return Ok(());
        }
        let ab = self.to_boxed(&a);
        let is_num = self.is_number_tag(ab);
        let num_blk = self.body.add_block();
        let slow_blk = self.body.add_block();
        self.cond_br(is_num, num_blk, slow_blk);
        self.side_arm(slow_blk, succ_pc, |s| {
            let neg1_boxed = s.boxed_const((TAG_INT32 << 32) | 0xFFFF_FFFF);
            let neg1 = Operand::plain(neg1_boxed, Repr::Boxed, prim_desc(PRIM_INT32));
            s.emit_guard_census(census::ARITH_SLOW, s.cur_pc);
            let binop = s.helpers.binop;
            let r = s.emit_value_binop(binop, BINOP_BITNOT, &a, &neg1);
            s.bigint_result(r, PRIM_INT32, None, succ_pc)
        });
        self.cur = num_blk;
        self.refine_src(&a, NUMERIC_SLOT);
        let af = self.unbox_number_f64(ab);
        let ai = self.to_int32_js(af);
        let neg1 = self.i32_const(0xFFFF_FFFF);
        let r = self.binop(Operator::I32Xor, ai, neg1, Type::I32);
        self.push_known(r, Repr::I32, prim_desc(PRIM_INT32));
        Ok(())
    }

    /// `Neg` (source: emit_neg): IEEE f64 negation is exact JS negation on
    /// numbers (incl. -0/NaN/INT32_MIN).
    pub(super) fn emit_neg_op(&mut self, succ_pc: Pc) -> Result<(), String> {
        self.emit_guard_census(census::ARITH_FAST, self.cur_pc);
        if self.outline_generic() {
            let neg = self.helpers.neg;
            return self.emit_generic_unary(neg);
        }
        let a = refine_by_repr(&self.pop()?);
        let riv = opsem::iv_neg(op_iv(&a));
        if is_numeric(&a.ty) {
            self.emit_rely_census(census::RELY_ARITH_NUM, a.prov);
            let af = self.to_f64(&a);
            let r = self.unop(Operator::F64Neg, af, Type::F64);
            self.stack.push(
                Operand::plain(r, Repr::F64, prim_desc(PRIM_INT32 | PRIM_DOUBLE))
                    .with_iv(riv)
                    .with_prov(a.prov),
            );
            return Ok(());
        }
        let ab = self.to_boxed(&a);
        let is_num = self.is_number_tag(ab);
        let num_blk = self.body.add_block();
        let slow_blk = self.body.add_block();
        self.cond_br(is_num, num_blk, slow_blk);
        self.side_arm(slow_blk, succ_pc, |s| {
            let h = s.helpers.neg;
            let r = s.rt_call(h, true, |_, _| vec![ab]).unwrap();
            s.bigint_result(r, PRIM_INT32 | PRIM_DOUBLE, None, succ_pc)
        });
        self.cur = num_blk;
        self.refine_src(&a, NUMERIC_SLOT);
        let af = self.unbox_number_f64(ab);
        let r = self.unop(Operator::F64Neg, af, Type::F64);
        self.stack.push(
            Operand::plain(r, Repr::F64, prim_desc(PRIM_INT32 | PRIM_DOUBLE))
                .with_iv(riv)
                .with_prov(Prov::T_ARITH),
        );
        Ok(())
    }

    /// `ToNumeric`/`Pos` (source: emit_tonumeric_with): identity when the
    /// value is a number -- by ctx proof (no code at all) or by runtime tag
    /// (the fall-through arm refines). Only the coercion arm calls out.
    pub(super) fn emit_tonumeric_op(
        &mut self,
        is_tonumeric: bool,
        succ_pc: Pc,
    ) -> Result<(), String> {
        if self.outline_generic() {
            let h = if is_tonumeric {
                self.helpers.tonumeric
            } else {
                self.helpers.pos
            };
            return self.emit_generic_unary(h);
        }
        let a = refine_by_repr(&self.pop()?);
        if is_numeric(&a.ty) {
            self.emit_rely_census(census::RELY_ARITH_NUM, a.prov);
            self.stack.push(a);
            return Ok(());
        }
        let ab = self.to_boxed(&a);
        let is_num = self.is_number_tag(ab);
        let num_blk = self.body.add_block();
        let slow_blk = self.body.add_block();
        self.cond_br(is_num, num_blk, slow_blk);
        self.side_arm(slow_blk, succ_pc, |s| {
            let h = if is_tonumeric {
                s.helpers.tonumeric
            } else {
                s.helpers.pos
            };
            let r = s.rt_call(h, true, |_, _| vec![ab]).unwrap();
            if is_tonumeric {
                // ToNumeric yields a number or a bigint.
                s.bigint_result(r, PRIM_INT32 | PRIM_DOUBLE, None, succ_pc)
            } else {
                // ToNumber (`Pos`) throws on bigint.
                Operand::plain(r, Repr::Boxed, prim_desc(PRIM_INT32 | PRIM_DOUBLE))
            }
        });
        self.cur = num_blk;
        self.refine_src(&a, NUMERIC_SLOT);
        self.stack.push(
            Operand::plain(ab, Repr::Boxed, prim_desc(PRIM_INT32 | PRIM_DOUBLE))
                .with_prov(Prov::T_ARITH),
        );
        Ok(())
    }
}
