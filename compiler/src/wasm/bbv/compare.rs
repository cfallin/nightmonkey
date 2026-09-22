/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Equality and relational lowerings, plus the fully generic binop/unary
//! forms the gen-only rung falls back to.

use super::*;

impl<'a> Bbv<'a> {
    /// The fully generic forms (one helper call, no arms): the GEN-only
    /// retry lane re-derives them so a size-capped giant compiles exactly
    /// like the generic lane did.
    pub(super) fn emit_generic_binop_kind(&mut self, kind: u32) -> Result<(), String> {
        let b = self.pop()?;
        let a = self.pop()?;
        self.emit_guard_census(census::ARITH_SLOW, self.cur_pc);
        let binop = self.helpers.binop;
        let r = self.emit_value_binop(binop, kind, &a, &b);
        self.push_boxed(r, bottom_ty());
        Ok(())
    }

    pub(super) fn emit_generic_unary(&mut self, helper: Func) -> Result<(), String> {
        let a = self.pop()?;
        let ab = self.to_boxed(&a);
        let r = self.rt_call(helper, true, |_, _| vec![ab]).unwrap();
        self.push_boxed(r, bottom_ty());
        Ok(())
    }

    /// The equality ladder for the compare diamond's non-number edge
    /// (kinds 4-7; source `emit_tagguarded_compare`'s `kind >= 4` block).
    /// `from_blk` has both operands proven non-number by the diamond's tag
    /// tests. Peels both-boolean identity, then both-object identity, then
    /// (strict kinds) a string arm and a both-BigInt guard before the
    /// terminal raw-bits compare; the string residual (equal length, at
    /// least one non-atom) and both-BigInt fall to `slow_blk`. Every arm
    /// that decides the comparison joins one internal merge and continues
    /// at `succ_pc` as a per-arm continuation, exactly like the helper arm
    /// -- the in-version merge stays int/f64 only, so the diamond's
    /// numeric `refine_src` remains sound.
    ///
    /// There is deliberately no linear char-compare leaf here: it would be
    /// emitted only for a proven string operand, and the operands reaching
    /// this ladder are bottom-typed.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn emit_eq_ladder(
        &mut self,
        from_blk: Block,
        slow_blk: Block,
        merge: Block,
        ab: Value,
        bb: Value,
        kind: u32,
    ) {
        let negate = kind == CMP_NE || kind == CMP_STRICTNE;
        let strict = kind == CMP_STRICTEQ || kind == CMP_STRICTNE;

        self.cur = from_blk;
        if strict {
            // Strict needs no type peel at all. The diamond already routed
            // both-number away (a double can only be `===` to a number, so
            // no double survives here in a pair that could compare equal),
            // which leaves raw boxed bits exact for every remaining pair --
            // object and symbol identity, canonical boolean / null /
            // undefined payloads, and every mixed tag pair (unequal, and
            // its bits differ) -- except the two content-equality types,
            // where distinct pointers hold equal values. So the whole
            // ladder is: route both-String to the string arm, route
            // both-BigInt to the helper, compare bits. No boolean or object
            // peel is needed (those are subsumed), and no float test: the
            // f64 arm upstream IS that test.
            let bits_from = self.body.add_block();
            self.emit_string_eq_arm(bits_from, slow_blk, merge, ab, bb, negate);
            self.cur = bits_from;
            if self.bigint_free {
                // The module's own text cannot manufacture a BigInt, so
                // the pair cannot be both-BigInt and the bits are exact --
                // as long as no source has been compiled at runtime. One
                // load and one test buys the unconditional compare; once
                // the fuse is blown every surviving pair takes the helper,
                // which decides content equality for real.
                let intact = self.dyncode_fuse_intact();
                let bits_blk = self.body.add_block();
                self.cond_br(intact, bits_blk, slow_blk);
                self.cur = bits_blk;
                let eq = self.binop(Operator::I64Eq, ab, bb, Type::I32);
                let r = if negate {
                    self.unop(Operator::I32Eqz, eq, Type::I32)
                } else {
                    eq
                };
                let blk = self.cur;
                self.body.set_terminator(
                    blk,
                    Terminator::Br {
                        target: BlockTarget {
                            block: merge,
                            args: vec![r],
                        },
                    },
                );
            } else {
                self.emit_bits_identity_arm(slow_blk, merge, ab, bb, negate, TAG_BIGINT_HI, false);
            }
            return;
        }
        // Loose `==`/`!=` cannot use the bits residual (`1 == true` is true
        // with different bits), so it keeps the type peel: both-boolean and
        // both-object are pure identity, then the string arm, then the
        // nullish arm on the not-both-string edge. Only mixed coercing
        // pairs (number vs string/boolean/object) fall to the helper.
        let obj_from = self.body.add_block();
        self.emit_bits_identity_arm(obj_from, merge, ab, bb, negate, TAG_BOOLEAN as u32, true);
        self.cur = obj_from;
        let str_from = self.body.add_block();
        self.emit_bits_identity_arm(str_from, merge, ab, bb, negate, TAG_OBJECT as u32, true);
        self.cur = str_from;
        let nullish_from = self.body.add_block();
        self.emit_string_eq_arm(nullish_from, slow_blk, merge, ab, bb, negate);
        self.cur = nullish_from;
        self.emit_loose_nullish_arm(slow_blk, merge, ab, bb, negate);
    }

    /// Loose-equality nullish arm: null and undefined equal only each other
    /// and emu-undefined objects, so a pair with a nullish side decides
    /// inline -- `eq = (a nullish or a emu) and (b nullish or b emu)`,
    /// exactly the compile-time nullish-const lowering evaluated at
    /// runtime. A pair with no nullish side falls to `else_blk`. This is
    /// the tag family the peel was missing: an object compared loosely
    /// against a sometimes-null value (raytrace's `shape != exclude`) took
    /// the helper on every null.
    fn emit_loose_nullish_arm(
        &mut self,
        else_blk: Block,
        merge: Block,
        ab: Value,
        bb: Value,
        negate: bool,
    ) {
        let null_c = self.boxed_const(TAG_NULL << 32);
        let undef_c = self.boxed_const(TAG_UNDEFINED << 32);
        let a_null = self.binop(Operator::I64Eq, ab, null_c, Type::I32);
        let a_undef = self.binop(Operator::I64Eq, ab, undef_c, Type::I32);
        let a_nullish = self.binop(Operator::I32Or, a_null, a_undef, Type::I32);
        let b_null = self.binop(Operator::I64Eq, bb, null_c, Type::I32);
        let b_undef = self.binop(Operator::I64Eq, bb, undef_c, Type::I32);
        let b_nullish = self.binop(Operator::I32Or, b_null, b_undef, Type::I32);
        let either = self.binop(Operator::I32Or, a_nullish, b_nullish, Type::I32);
        let dec_blk = self.body.add_block();
        self.cond_br(either, dec_blk, else_blk);
        self.cur = dec_blk;
        let a_emu = self.emit_emu_undefined_gated(ab);
        let a_side = self.binop(Operator::I32Or, a_nullish, a_emu, Type::I32);
        let b_emu = self.emit_emu_undefined_gated(bb);
        let b_side = self.binop(Operator::I32Or, b_nullish, b_emu, Type::I32);
        let eq = self.binop(Operator::I32And, a_side, b_side, Type::I32);
        let res = if negate {
            self.unop(Operator::I32Eqz, eq, Type::I32)
        } else {
            eq
        };
        let blk = self.cur;
        self.body.set_terminator(
            blk,
            Terminator::Br {
                target: BlockTarget {
                    block: merge,
                    args: vec![res],
                },
            },
        );
    }

    /// The continuation shared by every compare arm that decided the result
    /// inline but is not the version's happy path: push the boolean and take
    /// a clean edge (no call ran) to `succ_pc` on the CURRENT track.
    ///
    /// This continuation keeps the track: every arm feeding it is
    /// user-code-free and produces the same boolean implication, so the
    /// identity concern behind the side-arm step does not apply; stepping
    /// here would cost every downstream lineage its Opt code for the sake
    /// of the happy path's post-compare NUMERIC refinement of the two
    /// source slots.
    pub(super) fn emit_cmp_side_continuation(
        &mut self,
        merge: Block,
        res: Value,
        succ_pc: Pc,
        bool_ty: &TypeDesc,
    ) {
        self.cur = merge;
        let saved_stack = self.stack.clone();
        let saved_track = self.cur_track;
        self.push_known(res, Repr::Bool, *bool_ty);
        let target = self.edge_to(succ_pc);
        self.body
            .set_terminator(self.cur, Terminator::Br { target });
        self.stack = saved_stack;
        self.cur_track = saved_track;
    }

    /// Inline boxed-bits identity arm (source `emit_bits_identity_arm`):
    /// both operands carrying `tag` compare exactly by raw bits for the
    /// equality kinds. `match_takes_identity` picks the polarity -- booleans
    /// and objects take the identity block on a match, while the terminal
    /// strict-bits arm instead diverts a both-BigInt match to `else_blk`
    /// (the helper) and compares bits on the non-match edge. Emits from
    /// `self.cur`; the arm's result joins `merge`.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn emit_bits_identity_arm(
        &mut self,
        else_blk: Block,
        merge: Block,
        ab: Value,
        bb: Value,
        negate: bool,
        tag: u32,
        match_takes_identity: bool,
    ) {
        let a_t = self.tag_eq(ab, tag);
        let b_t = self.tag_eq(bb, tag);
        let both = self.binop(Operator::I32And, a_t, b_t, Type::I32);
        let id_blk = self.body.add_block();
        let (if_true, if_false) = if match_takes_identity {
            (id_blk, else_blk)
        } else {
            (else_blk, id_blk)
        };
        self.cond_br(both, if_true, if_false);
        self.cur = id_blk;
        let eq = self.binop(Operator::I64Eq, ab, bb, Type::I32);
        let result = if negate {
            self.unop(Operator::I32Eqz, eq, Type::I32)
        } else {
            eq
        };
        self.body.set_terminator(
            id_blk,
            Terminator::Br {
                target: BlockTarget {
                    block: merge,
                    args: vec![result],
                },
            },
        );
    }

    /// Inline string-equality arm (source `emit_string_eq_arm`): decide
    /// `==`/`!=` by same-pointer, then length (ropes carry it -- no
    /// flatten), then both-atom (atoms are deduped, so two distinct
    /// same-length atoms are unequal). A not-both-string pair falls to
    /// `not_str_blk`; the both-string residual falls to `slow_blk`.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn emit_string_eq_arm(
        &mut self,
        not_str_blk: Block,
        slow_blk: Block,
        merge: Block,
        ab: Value,
        bb: Value,
        negate: bool,
    ) {
        let a_str = self.tag_eq(ab, TAG_STRING as u32);
        let b_str = self.tag_eq(bb, TAG_STRING as u32);
        let both_str = self.binop(Operator::I32And, a_str, b_str, Type::I32);
        let body = self.body.add_block();
        self.cond_br(both_str, body, not_str_blk);

        self.cur = body;
        let same = self.binop(Operator::I64Eq, ab, bb, Type::I32);
        let same_blk = self.body.add_block();
        let len_blk = self.body.add_block();
        self.cond_br(same, same_blk, len_blk);
        self.emit_str_eq_result(same_blk, merge, !negate);

        self.cur = len_blk;
        let ap = self.unop(Operator::I32WrapI64, ab, Type::I32);
        let bp = self.unop(Operator::I32WrapI64, bb, Type::I32);
        let al = self.load_i32(ap, STRING_LENGTH_OFFSET);
        self.eff(al, Eff::ReadBits(HeapKind::StringData));
        let bl = self.load_i32(bp, STRING_LENGTH_OFFSET);
        self.eff(bl, Eff::ReadBits(HeapKind::StringData));
        let len_eq = self.binop(Operator::I32Eq, al, bl, Type::I32);
        let atom_blk = self.body.add_block();
        let diff_blk = self.body.add_block();
        self.cond_br(len_eq, atom_blk, diff_blk);
        self.emit_str_eq_result(diff_blk, merge, negate);

        // Same length, distinct pointers: two atoms are deduped, so unequal.
        self.cur = atom_blk;
        let af = self.load_i32(ap, STRING_FLAGS_OFFSET);
        self.eff(af, Eff::ReadBits(HeapKind::StringData));
        let bf = self.load_i32(bp, STRING_FLAGS_OFFSET);
        self.eff(bf, Eff::ReadBits(HeapKind::StringData));
        let atom = self.i32_const(STRING_ATOM_BIT);
        let zero = self.i32_const(0);
        let a_at = self.binop(Operator::I32And, af, atom, Type::I32);
        let a_at = self.binop(Operator::I32Ne, a_at, zero, Type::I32);
        let b_at = self.binop(Operator::I32And, bf, atom, Type::I32);
        let b_at = self.binop(Operator::I32Ne, b_at, zero, Type::I32);
        let both_atom = self.binop(Operator::I32And, a_at, b_at, Type::I32);
        let atom_diff_blk = self.body.add_block();
        self.cond_br(both_atom, atom_diff_blk, slow_blk);
        self.emit_str_eq_result(atom_diff_blk, merge, negate);
    }

    /// A decided string comparison: join `merge` with the constant verdict.
    pub(super) fn emit_str_eq_result(&mut self, blk: Block, merge: Block, val: bool) {
        self.cur = blk;
        let c = self.i32_const(u32::from(val));
        self.body.set_terminator(
            blk,
            Terminator::Br {
                target: BlockTarget {
                    block: merge,
                    args: vec![c],
                },
            },
        );
    }

    /// Whether the eq-compare at `pc` has a `String` literal as its RHS,
    /// pushed by the immediately preceding op. A syntactic per-script scan,
    /// memoized: the literal's ctx fact is dropped at version boundaries
    /// (the operand arrives as a bare boxed value), but the VALUE arriving
    /// at the compare is the atom by bytecode adjacency regardless of
    /// version, so the proven-string admission may rest on it.
    fn compare_lit_rhs(&mut self, pc: Pc) -> bool {
        let pc = self.evid_pc(pc);
        let set = self.lit_rhs_cmp.entry(self.source_id).or_insert_with(|| {
            let mut set = rustc_hash::FxHashSet::default();
            let mut p = self.script.parser();
            let mut prev: Option<JSOp> = None;
            let mut at = Pc::new(0);
            while let Some(op) = p.next_op() {
                if p.advance(usize::try_from(op.len()).unwrap() - 1).is_none() {
                    break;
                }
                if matches!(op, JSOp::Eq | JSOp::Ne | JSOp::StrictEq | JSOp::StrictNe)
                    && prev == Some(JSOp::String)
                {
                    set.insert(at);
                }
                prev = Some(op);
                at += op.len();
            }
            set
        });
        set.contains(&pc)
    }

    /// Whether the `JumpIfTrue` at `pc` tests an `IsNoIter` result, i.e. is
    /// a for-in loop's exit test. Syntactic and memoized like
    /// `compare_lit_rhs`.
    pub(super) fn noiter_jump(&mut self, pc: Pc) -> bool {
        let pc = self.evid_pc(pc);
        let set = self.noiter_jumps.entry(self.source_id).or_insert_with(|| {
            let mut set = rustc_hash::FxHashSet::default();
            let mut p = self.script.parser();
            let mut prev: Option<JSOp> = None;
            let mut at = Pc::new(0);
            while let Some(op) = p.next_op() {
                if p.advance(usize::try_from(op.len()).unwrap() - 1).is_none() {
                    break;
                }
                if op == JSOp::JumpIfTrue && prev == Some(JSOp::IsNoIter) {
                    set.insert(at);
                }
                prev = Some(op);
                at += op.len();
            }
            set
        });
        set.contains(&pc)
    }

    /// A comparison (source: emit_compare + emit_tagguarded_compare). Every
    /// arm produces the same implication (a boolean), so theta would squash
    /// per-arm continuations anyway: the tag-tested form is an in-version
    /// deferred-spill diamond.
    pub(super) fn emit_compare_op(&mut self, kind: u32, succ_pc: Pc) -> Result<(), String> {
        if self.outline_generic() {
            let b = self.pop()?;
            let a = self.pop()?;
            let cmp = self.helpers.compare;
            let r_boxed = self.emit_value_binop(cmp, kind, &a, &b);
            let r = self.unop(Operator::I32WrapI64, r_boxed, Type::I32);
            self.push_known(r, Repr::Bool, prim_desc(PRIM_BOOLEAN));
            return Ok(());
        }
        let b = refine_by_repr(&self.pop()?);
        let a = refine_by_repr(&self.pop()?);
        let bool_ty = prim_desc(PRIM_BOOLEAN);
        if is_exact_int32(&a.ty) && is_exact_int32(&b.ty) {
            self.emit_rely_census(census::RELY_CMP, a.prov.or(b.prov));
            let av = self.to_i32(&a);
            let bv = self.to_i32(&b);
            let r = self.binop(i32_compare_op(kind), av, bv, Type::I32);
            self.push_known(r, Repr::Bool, bool_ty);
            return Ok(());
        }
        if (a.repr == Repr::I64 || b.repr == Repr::I64)
            && i64_arith_operand_ok(&a)
            && i64_arith_operand_ok(&b)
        {
            self.emit_rely_census(census::RELY_CMP, a.prov.or(b.prov));
            let av = self.to_i64_exact(&a);
            let bv = self.to_i64_exact(&b);
            let r = self.binop(i64_compare_op(kind), av, bv, Type::I32);
            self.push_known(r, Repr::Bool, bool_ty);
            return Ok(());
        }
        if is_numeric(&a.ty) && is_numeric(&b.ty) {
            self.emit_rely_census(census::RELY_CMP, a.prov.or(b.prov));
            let af = self.to_f64(&a);
            let bf = self.to_f64(&b);
            let r = self.binop(f64_compare_op(kind), af, bf, Type::I32);
            self.push_known(r, Repr::Bool, bool_ty);
            return Ok(());
        }
        if (kind == CMP_STRICTEQ || kind == CMP_STRICTNE) && strict_bits_eq_sound(&a.ty, &b.ty) {
            self.emit_rely_census(census::RELY_CMP, a.prov.or(b.prov));
            let ab = self.to_boxed(&a);
            let bb = self.to_boxed(&b);
            let eqop = if kind == CMP_STRICTEQ {
                Operator::I64Eq
            } else {
                Operator::I64Ne
            };
            let r = self.binop(eqop, ab, bb, Type::I32);
            self.push_known(r, Repr::Bool, bool_ty);
            return Ok(());
        }
        if (kind == CMP_EQ || kind == CMP_NE)
            && (is_nullish_const(&a.ty) || is_nullish_const(&b.ty))
        {
            self.emit_rely_census(census::RELY_CMP, a.prov.or(b.prov));
            let other = if is_nullish_const(&a.ty) { &b } else { &a };
            let other = other.clone();
            let ob = self.to_boxed(&other);
            let null_c = self.boxed_const(TAG_NULL << 32);
            let undef_c = self.boxed_const(TAG_UNDEFINED << 32);
            let is_null = self.binop(Operator::I64Eq, ob, null_c, Type::I32);
            let is_undef = self.binop(Operator::I64Eq, ob, undef_c, Type::I32);
            let mut nullish = self.binop(Operator::I32Or, is_null, is_undef, Type::I32);
            if !is_non_gc(&other.ty) && !is_nullish_const(&other.ty) {
                let emu = self.emit_emu_undefined_gated(ob);
                nullish = self.binop(Operator::I32Or, nullish, emu, Type::I32);
            }
            let r = if kind == CMP_EQ {
                nullish
            } else {
                self.unop(Operator::I32Eqz, nullish, Type::I32)
            };
            self.push_known(r, Repr::Bool, bool_ty);
            return Ok(());
        }
        // Proven-string equality (kinds 4-7): at least one operand
        // string-only for the strict kinds (a strict compare against a
        // non-string is simply unequal), both for the loose kinds (loose
        // against a non-string coerces). Every deciding arm is
        // user-code-free -- pointer identity, length reject, both-atom
        // reject, and the linear content compare (`str_chars_eq`, pure) --
        // so the whole op stays in-version on the current track: no side
        // continuation, no step. Only the rope residual (equal length, at
        // least one non-linear side) leaves through the compare helper's
        // arm continuation, exactly like the generic diamond's slow arm.
        // This is the form switch-on-string dispatch compiles to (a
        // scrutinee against atom-constant cases), where the stepped side
        // continuation was the dominant residency leak.
        {
            let str_a = is_string_only(&a.ty);
            let lit_b = self.compare_lit_rhs(self.cur_pc);
            let str_b = is_string_only(&b.ty) || (kind >= 4 && lit_b);
            let strict = kind == CMP_STRICTEQ || kind == CMP_STRICTNE;
            let negate = kind == CMP_NE || kind == CMP_STRICTNE;
            // Loose `x == "lit"` (CMP_EQ / CMP_NE): the literal is a proven
            // string, so a string-tagged `x` takes the same pure ladder; a
            // non-string `x` coerces (`1 == "1"`), which is the helper's
            // arm rather than "unequal". String dispatch against a literal
            // (e.g. pdfjs's `name == "FlateDecode"`) hits this form.
            let loose_lit = lit_b && !str_a && (kind == CMP_EQ || kind == CMP_NE);
            if loose_lit || (kind >= 4 && ((strict && (str_a || str_b)) || (str_a && str_b))) {
                let mut strp = Prov::NONE;
                if str_a {
                    strp = strp.or(a.prov);
                }
                if is_string_only(&b.ty) {
                    strp = strp.or(b.prov);
                }
                self.emit_rely_census(census::RELY_STRING, strp);
                // The deciding arms work on the string pointers; the boxed
                // forms are needed only to tag-test an unproven side and by
                // the slow arm, so a `StrPtr` operand is never re-boxed on
                // the fast path.
                let ap = self.to_ptr(&a);
                let bp = self.to_ptr(&b);
                let pre = self.diamond_begin();
                let d = self.diamond_merge(pre, Some(Type::I32));
                let slow_blk = self.body.add_block();
                let one = self.i32_const(1);
                let neq_res = self.i32_const(u32::from(negate));
                let eq_res = self.i32_const(u32::from(!negate));
                let br_res = |s: &mut Self, res: Value| {
                    let mut margs = d.vals.clone();
                    margs.push(res);
                    margs.push(one);
                    let blk = s.cur;
                    s.body.set_terminator(
                        blk,
                        Terminator::Br {
                            target: BlockTarget {
                                block: d.merge,
                                args: margs,
                            },
                        },
                    );
                };
                for (proven, o) in [(str_a, &a), (str_b || loose_lit, &b)] {
                    if !proven {
                        let v = self.to_boxed(o);
                        let is_s = self.tag_eq(v, TAG_STRING as u32);
                        let str_blk = self.body.add_block();
                        if loose_lit {
                            self.cond_br(is_s, str_blk, slow_blk);
                        } else {
                            let ne_blk = self.body.add_block();
                            self.cond_br(is_s, str_blk, ne_blk);
                            self.cur = ne_blk;
                            br_res(self, neq_res);
                        }
                        self.cur = str_blk;
                    }
                }
                let same = self.binop(Operator::I32Eq, ap, bp, Type::I32);
                let same_blk = self.body.add_block();
                let len_blk = self.body.add_block();
                self.cond_br(same, same_blk, len_blk);
                self.cur = same_blk;
                br_res(self, eq_res);

                self.cur = len_blk;
                let atom = self.i32_const(STRING_ATOM_BIT);
                // The literal side is an atom by construction (`String`
                // pushes one), so an atom on the other side that is not the
                // same pointer is unequal: one flag load decides the common
                // miss -- a `switch` on an iterated key -- before any
                // length is read, and the atom's own flags need no load.
                let lit_af = if lit_b {
                    let af = self.load_i32(ap, STRING_FLAGS_OFFSET);
                    self.eff(af, Eff::ReadBits(HeapKind::StringData));
                    let a_atom = self.binop(Operator::I32And, af, atom, Type::I32);
                    let atom_blk = self.body.add_block();
                    let len_blk2 = self.body.add_block();
                    self.cond_br(a_atom, atom_blk, len_blk2);
                    self.cur = atom_blk;
                    br_res(self, neq_res);
                    self.cur = len_blk2;
                    Some(af)
                } else {
                    None
                };
                let al = self.load_i32(ap, STRING_LENGTH_OFFSET);
                self.eff(al, Eff::ReadBits(HeapKind::StringData));
                let bl = self.load_i32(bp, STRING_LENGTH_OFFSET);
                self.eff(bl, Eff::ReadBits(HeapKind::StringData));
                let len_eq = self.binop(Operator::I32Eq, al, bl, Type::I32);
                let flags_blk = self.body.add_block();
                let diff_blk = self.body.add_block();
                self.cond_br(len_eq, flags_blk, diff_blk);
                self.cur = diff_blk;
                br_res(self, neq_res);

                self.cur = flags_blk;
                let fboth = match lit_af {
                    Some(af) => af,
                    None => {
                        let af = self.load_i32(ap, STRING_FLAGS_OFFSET);
                        self.eff(af, Eff::ReadBits(HeapKind::StringData));
                        let bf = self.load_i32(bp, STRING_FLAGS_OFFSET);
                        self.eff(bf, Eff::ReadBits(HeapKind::StringData));
                        let fboth = self.binop(Operator::I32And, af, bf, Type::I32);
                        let both_atom = self.binop(Operator::I32And, fboth, atom, Type::I32);
                        let atom_blk = self.body.add_block();
                        let lin_blk = self.body.add_block();
                        self.cond_br(both_atom, atom_blk, lin_blk);
                        self.cur = atom_blk;
                        br_res(self, neq_res);
                        self.cur = lin_blk;
                        fboth
                    }
                };
                let linear = self.i32_const(STRING_LINEAR_BIT);
                let both_lin = self.binop(Operator::I32And, fboth, linear, Type::I32);
                let chars_blk = self.body.add_block();
                self.cond_br(both_lin, chars_blk, slow_blk);
                self.cur = chars_blk;
                let r = self.call_i32(self.helpers.str_chars_eq, &[ap, bp]);
                let rr = if negate {
                    self.unop(Operator::I32Eqz, r, Type::I32)
                } else {
                    r
                };
                br_res(self, rr);

                // Rope residual (and the loose form's non-string side):
                // the generic diamond's slow arm. Not epoch-kept: loose
                // literal compares are hot and often non-string, so keeping
                // this residual costs more than it saves; it is never taken
                // where the names are linear strings that hit the ladder.
                self.cur = slow_blk;
                let arm_st = self.arm_state();
                let ab = self.to_boxed(&a);
                let bb = self.to_boxed(&b);
                let n = self.spill_all();
                let top = self.add_offset(self.vp, d.top_off);
                let kind_v = self.i32_const(kind);
                let cmp = self.helpers.compare;
                let ok = self.call_i32(cmp, &[self.cx, top, kind_v, ab, bb]);
                let res_boxed = self.load_i64(self.vp, d.top_off);
                let rs = self.unop(Operator::I32WrapI64, res_boxed, Type::I32);
                self.reload(n);
                self.branch_on_err(ok);
                self.push_known(rs, Repr::Bool, bool_ty);
                let target = self.dirty_edge_to(succ_pc);
                self.body
                    .set_terminator(self.cur, Terminator::Br { target });
                self.arm_restore(arm_st);

                self.diamond_join(&d);
                self.push_known(d.res_param.unwrap(), Repr::Bool, bool_ty);
                return Ok(());
            }
        }
        // Tag-guarded three-arm diamond: int32 / f64 / helper, deferred
        // spills (only the slow arm spills; source emit_tagguarded_compare).
        let ab = self.ladder_box(&a);
        let bb = self.ladder_box(&b);
        let pre = self.diamond_begin();
        let int_blk = self.body.add_block();
        let rest_blk = self.body.add_block();
        let f64_blk = self.body.add_block();
        let slow_blk = self.body.add_block();
        let d = self.diamond_merge(pre, Some(Type::I32));
        // Equality ladder (kinds 4-7; source emit_tagguarded_compare's
        // kind >= 4 block): both-boolean and both-object equality are pure
        // identity, and a strict pair that is neither number, boolean,
        // object, string nor BigInt compares exactly by raw boxed bits. Only
        // string residuals and both-BigInt reach the helper. Without this,
        // every object/symbol `===` calls the compare helper, which in a
        // symbol-comparing interpreter loop is millions of helper calls per
        // run.
        let eq_blk = if kind >= 4 {
            self.body.add_block()
        } else {
            slow_blk
        };
        // Every arm that decides inline but is not the happy path joins
        // here and takes one stepped-down continuation. Only the equality
        // kinds have such arms; the relational kinds keep the plain
        // int/f64/helper diamond.
        let side = if kind >= 4 {
            let m = self.body.add_block();
            let r = self.body.add_blockparam(m, Type::I32);
            Some((m, r))
        } else {
            None
        };
        let one = self.i32_const(1);

        self.int32_chk_census("both_int32");
        let ta = self.int32_tag_test(&a, ab);
        let tb = self.int32_tag_test(&b, bb);
        let both = self.and_tests(ta, tb);
        self.cond_br_opt(both, int_blk, rest_blk);
        self.cur = rest_blk;
        let na = self.number_tag_test(&a, ab);
        let nb = self.number_tag_test(&b, bb);
        let both_num = self.and_tests(na, nb);
        // Off the int32 fast path every arm below reads the boxes; an
        // exact operand's box is built here, where the int arm never runs.
        let ab = self.box_of(&a, ab);
        let bb = self.box_of(&b, bb);
        self.cond_br_opt(both_num, f64_blk, eq_blk);
        if kind >= 4 {
            self.emit_eq_ladder(eq_blk, slow_blk, side.unwrap().0, ab, bb, kind);
        }

        self.cur = int_blk;
        let ai = self.int32_payload(&a, Some(ab));
        let bi = self.int32_payload(&b, Some(bb));
        let ri = self.binop(i32_compare_op(kind), ai, bi, Type::I32);
        let mut margs = d.vals.clone();
        margs.push(ri);
        margs.push(one);
        self.body.set_terminator(
            int_blk,
            Terminator::Br {
                target: BlockTarget {
                    block: d.merge,
                    args: margs,
                },
            },
        );

        self.cur = f64_blk;
        let af = self.unbox_number_f64(ab);
        let bf = self.unbox_number_f64(bb);
        let rf = self.binop(f64_compare_op(kind), af, bf, Type::I32);
        let mut margs = d.vals.clone();
        margs.push(rf);
        margs.push(one);
        self.body.set_terminator(
            f64_blk,
            Terminator::Br {
                target: BlockTarget {
                    block: d.merge,
                    args: margs,
                },
            },
        );

        // Slow arm (arm continuation): the helper compare leaves the
        // version and continues at succ_pc -- same boolean implication as
        // the fast arms, but keeping the call out of the loop body is what
        // admits LICM on compare-conditioned loops.
        // Not epoch-kept: the int32/f64 arms
        // refine both operands' source slots, and a keep lineage restored
        // to the pre-op state joining succ_pc erases those facts for
        // every lineage there -- the loop's int32 facts, at compile time.
        self.cur = slow_blk;
        let arm_st = self.arm_state();
        let n = self.spill_all();
        let top = self.add_offset(self.vp, d.top_off);
        let kind_v = self.i32_const(kind);
        let cmp = self.helpers.compare;
        let ok = self.call_i32(cmp, &[self.cx, top, kind_v, ab, bb]);
        let res_boxed = self.load_i64(self.vp, d.top_off);
        let rs = self.unop(Operator::I32WrapI64, res_boxed, Type::I32);
        {
            self.reload(n);
            self.branch_on_err(ok);
            self.push_known(rs, Repr::Bool, bool_ty);
            let target = self.dirty_edge_to(succ_pc);
            self.body
                .set_terminator(self.cur, Terminator::Br { target });
            self.arm_restore(arm_st);
        }

        if let Some((m, r)) = side {
            self.emit_cmp_side_continuation(m, r, succ_pc, &bool_ty);
        }

        self.diamond_join(&d);
        // The in-version arms prove their tag family and the other arms left
        // the version, so the join's fact is the happy path's: both-object
        // under the object designation, else numeric (int pair / number
        // pair). Write it back to the source slots.
        self.refine_src(&a, NUMERIC_SLOT);
        self.refine_src(&b, NUMERIC_SLOT);
        self.push_known(d.res_param.unwrap(), Repr::Bool, bool_ty);
        Ok(())
    }
}
