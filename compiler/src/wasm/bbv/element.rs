/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Element lowerings: dense arrays, typed arrays, string indexing, and the
//! append arm.

use super::*;
use crate::opsem::TaKind;

/// In-module dense-append *check*: `night_elem_append_check(objptr,
/// elements, initlen, idx) -> (row << 32) | elemAddr`, 0 = no.
///
/// The out-of-bounds and hole tails of `SetElem` -- the capacity and
/// elements-flags checks, the shape-hashed append-row probe, the two cached
/// proto live-shape guards, the element store and the initializedLength /
/// Array-length bumps -- are the same eleven blocks at every store site,
/// and they are cold in practice. So they are emitted once and called.
///
/// Both entries into a fully-inline arm end up here: an append (`idx ==
/// initializedLength`) and the dense arm's in-bounds hole rejection, which
/// the helper re-derives rather than being told.
///
/// It proves the store is legal and hands back where to put it, but writes
/// nothing itself. That is deliberate: the stores carry per-site bookkeeping
/// the helper cannot do -- the receiver classification (`eff_store`'s
/// `recv_bit`, which is what keeps an own-`this` store from reading as
/// MUT_OTHER), the fact-driven store duty, and the barrier elision. So the
/// checks move and the stores stay, which also makes this a **pure leaf**:
/// reads only, no GC, no flags-word effect at all.
///
/// The returned word packs the append row beside the element address because
/// the caller's length bump needs `row[20]` (isArray) and one i64 result is
/// cheaper than a multi-value return to unpack.
pub fn build_elem_append_helper(
    m: &mut Module,
    mem: waffle::Memory,
    append_cache_base: u32,
    census: bool,
) -> Func {
    use crate::wasm::translate::RawEmit;
    use waffle::{FuncDecl, SignatureData};
    let sig = m.signatures.push(SignatureData {
        params: vec![Type::I32, Type::I32, Type::I32, Type::I32],
        returns: vec![Type::I64],
    });
    let mut e = RawEmit::new(m, sig, mem);
    let objptr = e.param(0);
    let elements = e.param(1);
    let initlen = e.param(2);
    let idx = e.param(3);

    let fail = e.body.add_block();
    let app1 = e.body.add_block();
    let hole_pre = e.body.add_block();
    let probe_blk = e.body.add_block();

    // Census builds return a distinct code per refusal
    // (`census::SETELEM_APPEND_WHY` buckets) instead of 0; the call site
    // tests `>= 8`. Production builds keep the single 0-returning block.
    let fail_code = |e: &mut RawEmit, code: u64| -> Block {
        if !census {
            return fail;
        }
        let saved = e.cur;
        let b = e.body.add_block();
        e.cur = b;
        let c = e.i64c(code);
        e.ret(vec![c]);
        e.cur = saved;
        b
    };

    let is_app = e.bin(Operator::I32Eq, idx, initlen, Type::I32);
    e.condbr(is_app, app1, hole_pre);

    e.cur = fail;
    let z = e.i64c(0);
    e.ret(vec![z]);

    // Hole overwrite: a store at idx < initializedLength whose slot holds the
    // hole. Add-like, so it takes the same row + proto proof as an append,
    // but bumps nothing.
    e.cur = hole_pre;
    let in_init = e.bin(Operator::I32LtU, idx, initlen, Type::I32);
    let hole1 = e.body.add_block();
    let f_beyond = fail_code(&mut e, 5);
    e.condbr(in_init, hole1, f_beyond);
    e.cur = hole1;
    let three = e.i32c(3);
    let hoff = e.bin(Operator::I32Shl, idx, three, Type::I32);
    let hole_addr = e.bin(Operator::I32Add, elements, hoff, Type::I32);
    let ma = e.marg(3, 0);
    let cur_slot = e.load(Operator::I64Load { memory: ma }, hole_addr, Type::I64);
    let sh = e.i64c(32);
    let hi64 = e.bin(Operator::I64ShrU, cur_slot, sh, Type::I64);
    let hi = e.un(Operator::I32WrapI64, hi64, Type::I32);
    let magic = e.i32c(TAG_MAGIC as u32);
    let is_hole = e.bin(Operator::I32Eq, hi, magic, Type::I32);
    let hole2 = e.body.add_block();
    let f_nonhole = fail_code(&mut e, 6);
    e.condbr(is_hole, hole2, f_nonhole);
    e.cur = hole2;
    let fb = e.i32c(ELEMENTS_FLAGS_BACK);
    let hflags_addr = e.bin(Operator::I32Sub, elements, fb, Type::I32);
    let hflags = e.ld32(hflags_addr, 0);
    let hmask = e.i32c(ELEMENTS_PUSH_BAIL_MASK);
    let hbits = e.bin(Operator::I32And, hflags, hmask, Type::I32);
    let hok = e.un(Operator::I32Eqz, hbits, Type::I32);
    let f_hflags = fail_code(&mut e, 2);
    e.condbr(hok, probe_blk, f_hflags);

    // Append: room in the capacity and no bail flag.
    e.cur = app1;
    let cb = e.i32c(ELEMENTS_CAPACITY_BACK);
    let cap_addr = e.bin(Operator::I32Sub, elements, cb, Type::I32);
    let cap = e.ld32(cap_addr, 0);
    let has_cap = e.bin(Operator::I32LtU, initlen, cap, Type::I32);
    let fb2 = e.i32c(ELEMENTS_FLAGS_BACK);
    let flags_addr = e.bin(Operator::I32Sub, elements, fb2, Type::I32);
    let flags = e.ld32(flags_addr, 0);
    let mask2 = e.i32c(ELEMENTS_PUSH_BAIL_MASK);
    let bits = e.bin(Operator::I32And, flags, mask2, Type::I32);
    let flags_ok = e.un(Operator::I32Eqz, bits, Type::I32);
    if census {
        // Split the compound test so the two causes report apart.
        let cap_ok_blk = e.body.add_block();
        let f_cap = fail_code(&mut e, 1);
        e.condbr(has_cap, cap_ok_blk, f_cap);
        e.cur = cap_ok_blk;
        let f_flags = fail_code(&mut e, 2);
        e.condbr(flags_ok, probe_blk, f_flags);
    } else {
        let pre_ok = e.bin(Operator::I32And, has_cap, flags_ok, Type::I32);
        e.condbr(pre_ok, probe_blk, fail);
    }

    // Row lookup: hash the shape word (the mega-table mix, no atom).
    e.cur = probe_blk;
    let shape = e.ld32(objptr, SHAPE_OFFSET);
    let three_s = e.i32c(3);
    let shr = e.bin(Operator::I32ShrU, shape, three_s, Type::I32);
    let k1 = e.i32c(2654435761);
    let h = e.bin(Operator::I32Mul, shr, k1, Type::I32);
    let mask = e.i32c(crate::wasm::translate::APPEND_CACHE_SIZE - 1);
    let ridx = e.bin(Operator::I32And, h, mask, Type::I32);
    let stride = e.i32c(crate::wasm::translate::APPEND_CACHE_ENTRY_BYTES);
    let roff = e.bin(Operator::I32Mul, ridx, stride, Type::I32);
    let base = e.i32c(append_cache_base);
    let row = e.bin(Operator::I32Add, base, roff, Type::I32);
    let row_shape = e.ld32(row, 0);
    let hit = e.bin(Operator::I32Eq, shape, row_shape, Type::I32);
    let pguard_blk = e.body.add_block();
    let f_probe = fail_code(&mut e, 3);
    e.condbr(hit, pguard_blk, f_probe);

    // Proto contents guarded through the cached protos' live shape words;
    // an empty pair (ptr 0) passes.
    e.cur = pguard_blk;
    let p0 = e.ld32(row, 4);
    let s0 = e.ld32(row, 8);
    let live0 = e.ld32(p0, SHAPE_OFFSET);
    let p0_empty = e.un(Operator::I32Eqz, p0, Type::I32);
    let m0 = e.bin(Operator::I32Eq, live0, s0, Type::I32);
    let ok0 = e.bin(Operator::I32Or, p0_empty, m0, Type::I32);
    let p1 = e.ld32(row, 12);
    let s1 = e.ld32(row, 16);
    let live1 = e.ld32(p1, SHAPE_OFFSET);
    let p1_empty = e.un(Operator::I32Eqz, p1, Type::I32);
    let m1 = e.bin(Operator::I32Eq, live1, s1, Type::I32);
    let ok1 = e.bin(Operator::I32Or, p1_empty, m1, Type::I32);
    let pok = e.bin(Operator::I32And, ok0, ok1, Type::I32);
    let store_blk = e.body.add_block();
    let f_proto = fail_code(&mut e, 4);
    e.condbr(pok, store_blk, f_proto);

    e.cur = store_blk;
    let t3 = e.i32c(3);
    let off = e.bin(Operator::I32Shl, idx, t3, Type::I32);
    let elem_addr = e.bin(Operator::I32Add, elements, off, Type::I32);
    let ea64 = e.un(Operator::I64ExtendI32U, elem_addr, Type::I64);
    let row64 = e.un(Operator::I64ExtendI32U, row, Type::I64);
    let s32 = e.i64c(32);
    let rhi = e.bin(Operator::I64Shl, row64, s32, Type::I64);
    let packed = e.bin(Operator::I64Or, rhi, ea64, Type::I64);
    e.ret(vec![packed]);

    m.funcs.push(FuncDecl::Body(
        sig,
        "night_elem_append_check".to_string(),
        e.body,
    ))
}

impl<'a> Bbv<'a> {
    /// Guard that `objptr` (a known JSObject*) is a NativeObject before any
    /// `slots_`/`elements_` dereference: a proxy or WasmGC object stores
    /// unrelated fields at those offsets. Branches to `fail` on a non-native
    /// receiver and leaves `self.cur` in the guarded continuation block.
    pub(super) fn emit_native_object_guard(&mut self, objptr: Value, fail: Block) {
        let shape = self.load_i32(objptr, SHAPE_OFFSET);
        self.eff(shape, Eff::Read(HeapKind::Shape));
        let imm = self.load_i32(shape, SHAPE_IMMUTABLE_FLAGS_OFFSET);
        self.eff(imm, Eff::ReadBits(HeapKind::Shape));
        let bit = self.i32_const(SHAPE_IS_NATIVE_BIT);
        let is_native = self.binop(Operator::I32And, imm, bit, Type::I32);
        let ok_blk = self.body.add_block();
        self.cond_br(is_native, ok_blk, fail);
        self.cur = ok_blk;
    }

    /// Instrument-only interposer naming which `SetElem` fast-diamond edge
    /// departed toward the generic helper (`census::SETELEM_WHY` buckets).
    /// Returns `tgt` itself when the census is off, so production codegen
    /// is untouched.
    fn setelem_why_blk(&mut self, tgt: Block, bucket: u32, pc: Pc) -> Block {
        if !self.guard_census_on() {
            return tgt;
        }
        let saved = self.cur;
        let b = self.body.add_block();
        self.cur = b;
        let kind = self.i32_const(census::SETELEM_WHY + bucket);
        self.emit_guard_census_dyn(kind, pc);
        self.body.set_terminator(
            b,
            Terminator::Br {
                target: BlockTarget {
                    block: tgt,
                    args: vec![],
                },
            },
        );
        self.cur = saved;
        b
    }

    /// Inline string `s[i]` arm of `emit_get_element`: linear latin1
    /// in-bounds char read boxed through the static-strings unit-atom table.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn emit_string_elem_arm(
        &mut self,
        from_blk: Block,
        slow_blk: Block,
        next_pc: Pc,
        recv_boxed: Value,
        recv_ptr: Value,
        key_boxed: Value,
        key_int: Value,
    ) {
        // from_blk: receiver not a (dense-qualifying) object. String + int32?
        self.cur = from_blk;
        let is_str = self.tag_eq(recv_boxed, TAG_STRING as u32);
        let both = self.binop(Operator::I32And, is_str, key_int, Type::I32);
        let str_blk = self.body.add_block();
        self.cond_br(both, str_blk, slow_blk);

        // str_blk: linear latin1 + in-bounds check.
        self.cur = str_blk;
        let strptr = recv_ptr;
        let flags = self.load_i32(strptr, STRING_FLAGS_OFFSET);
        self.eff(flags, Eff::ReadBits(HeapKind::StringData));
        let want = self.i32_const(STRING_LINEAR_BIT | STRING_LATIN1_CHARS_BIT);
        let masked = self.binop(Operator::I32And, flags, want, Type::I32);
        let lin_lat = self.binop(Operator::I32Eq, masked, want, Type::I32);
        let len = self.load_i32(strptr, STRING_LENGTH_OFFSET);
        self.eff(len, Eff::ReadBits(HeapKind::StringData));
        let idx = self.unop(Operator::I32WrapI64, key_boxed, Type::I32);
        let in_bounds = self.binop(Operator::I32LtU, idx, len, Type::I32);
        let ok_read = self.binop(Operator::I32And, lin_lat, in_bounds, Type::I32);
        let char_blk = self.body.add_block();
        self.cond_br(ok_read, char_blk, slow_blk);

        // char_blk: chars base (inline storage at +8, or the non-inline
        // pointer stored at +8 -- the speculative pointer load of an inline
        // string's first chars is dead, never dereferenced), byte load, unit
        // atom lookup, box as a string value.
        self.cur = char_blk;
        let inline_bit = self.i32_const(STRING_INLINE_CHARS_BIT);
        let is_inline = self.binop(Operator::I32And, flags, inline_bit, Type::I32);
        let noninline = self.load_i32(strptr, STRING_CHARS_OFFSET);
        self.eff(noninline, Eff::Read(HeapKind::StringData));
        let inline_addr = self.add_offset(strptr, STRING_CHARS_OFFSET);
        let chars = self.select(Type::I32, inline_addr, noninline, is_inline);
        let caddr = self.binop(Operator::I32Add, chars, idx, Type::I32);
        let c = self.load8_u(caddr, 0);
        self.eff(c, Eff::ReadBits(HeapKind::StringData));
        let tbl_slot = self.i32_const(self.helpers.static_strings_slot);
        let tbl = self.load_i32(tbl_slot, 0);
        self.eff(tbl, Eff::Read(HeapKind::EngineTable));
        let two = self.i32_const(2);
        let coff = self.binop(Operator::I32Shl, c, two, Type::I32);
        let entry_addr = self.binop(Operator::I32Add, tbl, coff, Type::I32);
        let atom = self.load_i32(entry_addr, 0);
        self.eff(atom, Eff::Read(HeapKind::EngineTable));
        // The unit atom is a proven string: continue at next_pc in the
        // StrPtr lineage, no boxing.
        let saved_stack = self.stack.clone();
        self.stack
            .push(Operand::plain(atom, Repr::StrPtr, prim_desc(PRIM_STRING)));
        let target = self.edge_to(next_pc);
        self.body
            .set_terminator(self.cur, Terminator::Br { target });
        self.stack = saved_stack;
    }

    /// Inline guarded-monomorphic typed-array read: clasp guard against the
    /// predicted fixed-length TA class, bounds check, kind-specific load. A
    /// clasp mismatch falls to `dense_blk`; OOB falls to `slow_blk`. The
    /// result type is proven by the element kind, so the arm pushes unboxed
    /// with no tag test and continues at `next_pc` in its typed lineage.
    /// Whether the object at `objptr` is a fixed-length typed array of
    /// `kind`: its clasp against the kind's class (the runtime's table).
    pub(super) fn ta_clasp_eq(&mut self, objptr: Value, kind: TaKind) -> Value {
        let shape = self.load_i32(objptr, SHAPE_OFFSET);
        self.eff(shape, Eff::Read(HeapKind::Shape));
        let base = self.load_i32(shape, SHAPE_BASESHAPE_OFFSET);
        self.eff(base, Eff::Read(HeapKind::Shape));
        let clasp = self.load_i32(base, BASESHAPE_CLASP_OFFSET);
        self.eff(clasp, Eff::Read(HeapKind::Shape));
        let cslot = self.i32_const(self.helpers.ta_class_base + 4 * (u32::from(kind.code()) - 1));
        let want = self.load_i32(cslot, 0);
        self.binop(Operator::I32Eq, clasp, want, Type::I32)
    }

    /// The clasp guard of a typed-array arm, or nothing when the receiver's
    /// fact already proves the kind (`SlotCtx::ta`): the arm's body block.
    /// A passed guard refines the receiver's source slot with the kind
    /// (`refine_ta_src`), test-once-per-lineage like the class guards; the
    /// caller brackets the arm with `arm_state`/`arm_restore`.
    fn ta_arm_guard(
        &mut self,
        from_blk: Block,
        dense_blk: Block,
        objptr: Value,
        kind: TaKind,
        recv: &Operand,
    ) -> Block {
        self.cur = from_blk;
        if recv.ta == Some(kind) {
            self.emit_rely_census(census::RELY_ELEM, recv.prov);
            return from_blk;
        }
        let is_ta = self.ta_clasp_eq(objptr, kind);
        let body = self.body.add_block();
        self.cond_br(is_ta, body, dense_blk);
        self.cur = body;
        self.refine_ta_src(recv, kind);
        body
    }

    /// The receiver's source slot takes the proven typed-array kind. A
    /// binding source takes it only as the ANALYSIS's claim for the
    /// binding (`gname_types`, the install rule of `install_gcell`): the
    /// guard validated exactly that prediction.
    fn refine_ta_src(&mut self, recv: &Operand, kind: TaKind) {
        // Every live operand sourced from the same slot IS the same value
        // (`clear_stale_src` drops the provenance when the slot is
        // reassigned): the `Dup`'d receiver of the store that follows a
        // read takes the kind too.
        if recv.src.is_some() {
            for o in &mut self.stack {
                if o.src == recv.src {
                    o.ta = Some(kind);
                }
            }
        }
        match recv.src {
            Some(SlotRef::GCell(bid)) => {
                let claimed = self
                    .ctx
                    .syn_gnames
                    .iter()
                    .find(|(_, &b)| b == bid)
                    .and_then(|(name, _)| self.ctx.facts.gname_types.get(name))
                    .is_some_and(|c| c.ta_kind() == Some(kind));
                if !claimed {
                    return;
                }
                let want = claim_slot_ctx(ClaimShape::Ta(kind));
                match self.gcells_ctx.iter_mut().find(|(b, _)| *b == bid) {
                    Some(e) => {
                        if let Some(m) = e.1.meet(want) {
                            e.1 = m;
                        }
                    }
                    None => {
                        self.gcells_ctx.push((bid, want));
                        self.gcells_ctx.sort_by_key(|(b, _)| *b);
                    }
                }
            }
            Some(_) => {
                let fact = SlotCtx {
                    ta: Some(kind),
                    prov: recv.prov.or(Prov::C_ELEM),
                    ..OBJ_ONLY_SLOT
                };
                self.refine_src(recv, fact);
            }
            None => {}
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn emit_ta_get_arm(
        &mut self,
        from_blk: Block,
        dense_blk: Block,
        slow_blk: Block,
        next_pc: Pc,
        objptr: Value,
        key_boxed: Value,
        kind: TaKind,
        recv: &Operand,
    ) {
        let st = self.arm_state();
        let body = self.ta_arm_guard(from_blk, dense_blk, objptr, kind, recv);

        // body: unsigned in-bounds check against the element count.
        self.cur = body;
        let idx = self.unop(Operator::I32WrapI64, key_boxed, Type::I32);
        let len = self.load_i32(objptr, TA_LENGTH_PAYLOAD_OFFSET);
        self.eff(len, Eff::ReadBits(HeapKind::ElementsHeader));
        let in_bounds = self.binop(Operator::I32LtU, idx, len, Type::I32);
        let load_blk = self.body.add_block();
        self.cond_br(in_bounds, load_blk, slow_blk);

        // load_blk: element address = data + (idx << shift); kind-specific load.
        self.cur = load_blk;
        let data = self.load_i32(objptr, TA_DATA_PAYLOAD_OFFSET);
        self.eff(data, Eff::Read(HeapKind::ElementsHeader));
        let shift = kind.log2_bytes();
        let addr = if shift == 0 {
            self.binop(Operator::I32Add, data, idx, Type::I32)
        } else {
            let s = self.i32_const(shift);
            let off = self.binop(Operator::I32Shl, idx, s, Type::I32);
            self.binop(Operator::I32Add, data, off, Type::I32)
        };
        let result = match kind {
            TaKind::Int8 => {
                let u = self.load8_u(addr, 0);
                let v = self.unop(Operator::I32Extend8S, u, Type::I32);
                Operand::plain(v, Repr::I32, prim_desc(PRIM_INT32))
            }
            TaKind::Uint8 | TaKind::Uint8Clamped => {
                let v = self.load8_u(addr, 0);
                Operand::plain(v, Repr::I32, prim_desc(PRIM_INT32))
            }
            TaKind::Int16 => {
                let u = self.load16_u(addr, 0);
                let v = self.unop(Operator::I32Extend16S, u, Type::I32);
                Operand::plain(v, Repr::I32, prim_desc(PRIM_INT32))
            }
            TaKind::Uint16 => {
                let v = self.load16_u(addr, 0);
                Operand::plain(v, Repr::I32, prim_desc(PRIM_INT32))
            }
            TaKind::Int32 => {
                let v = self.load_i32(addr, 0);
                Operand::plain(v, Repr::I32, prim_desc(PRIM_INT32))
            }
            TaKind::Float32 => {
                let f = self.load_f32(addr, 0);
                let d = self.unop(Operator::F64PromoteF32, f, Type::F64);
                let d = self.canon_nan_f64(d);
                Operand::plain(d, Repr::F64, prim_desc(PRIM_INT32 | PRIM_DOUBLE))
            }
            TaKind::Uint32 => {
                // Uint32: an integral value in [0, 2^32) -- the F64 carrier
                // is exact and the I53 bucket holds, so downstream integer
                // consumers cross versions in the raw-i64 repr.
                let v = self.load_i32(addr, 0);
                let f = self.unop(Operator::F64ConvertI32U, v, Type::F64);
                Operand::ranged(
                    f,
                    Repr::F64,
                    prim_desc(PRIM_INT32 | PRIM_DOUBLE),
                    RangeBucket::I53,
                )
            }
            TaKind::Float64 => {
                let d = self.load_f64(addr, 0);
                let d = self.canon_nan_f64(d);
                Operand::plain(d, Repr::F64, prim_desc(PRIM_INT32 | PRIM_DOUBLE))
            }
        };
        let result = match ta_kind_iv(kind) {
            Some(iv) => result.with_iv(Some(iv)),
            None => result,
        };
        let result = result.with_prov(Prov::C_ELEM);
        let saved_stack = self.stack.clone();
        self.stack.push(result);
        let target = self.edge_to(next_pc);
        self.body
            .set_terminator(self.cur, Terminator::Br { target });
        self.stack = saved_stack;
        self.arm_restore(st);
    }

    /// Inline guarded-monomorphic typed-array store: clasp guard, unsigned
    /// bounds check (a detached fixed-length TA has length 0), kind-specific
    /// store with conversion. The value dispatch uses the operand's static
    /// repr/type when available; a double stored to an integer kind must
    /// round-trip int32 exactly, else the generic helper's ToInt32
    /// wraparound covers it. No barrier: raw numeric data. Nothing on the
    /// fast path GCs.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn emit_ta_set_arm(
        &mut self,
        from_blk: Block,
        dense_blk: Block,
        slow_blk: Block,
        merge: Block,
        objptr: Value,
        key_boxed: Value,
        val: &Operand,
        val_boxed: Value,
        kind: TaKind,
        vals: &[Value],
        recv: &Operand,
    ) {
        let st = self.arm_state();
        let body = self.ta_arm_guard(from_blk, dense_blk, objptr, kind, recv);

        self.cur = body;
        let idx = self.unop(Operator::I32WrapI64, key_boxed, Type::I32);
        let len = self.load_i32(objptr, TA_LENGTH_PAYLOAD_OFFSET);
        self.eff(len, Eff::ReadBits(HeapKind::ElementsHeader));
        let in_bounds = self.binop(Operator::I32LtU, idx, len, Type::I32);
        let store_blk = self.body.add_block();
        self.cond_br(in_bounds, store_blk, slow_blk);

        self.cur = store_blk;
        let data = self.load_i32(objptr, TA_DATA_PAYLOAD_OFFSET);
        self.eff(data, Eff::Read(HeapKind::ElementsHeader));
        let shift = kind.log2_bytes();
        let addr = if shift == 0 {
            self.binop(Operator::I32Add, data, idx, Type::I32)
        } else {
            let s = self.i32_const(shift);
            let off = self.binop(Operator::I32Shl, idx, s, Type::I32);
            self.binop(Operator::I32Add, data, off, Type::I32)
        };

        let one = self.i32_const(1);
        let mut margs = vals.to_vec();
        margs.push(one);

        let static_int: Option<Value> = match val.repr {
            Repr::I32 | Repr::Bool => Some(val.val),
            Repr::Boxed if is_exact_int32(&val.ty) => {
                Some(self.unop(Operator::I32WrapI64, val_boxed, Type::I32))
            }
            _ => None,
        };
        if let Some(v) = static_int {
            self.emit_ta_store_int(addr, kind, v);
            self.body.set_terminator(
                self.cur,
                Terminator::Br {
                    target: BlockTarget {
                        block: merge,
                        args: margs,
                    },
                },
            );
            return;
        }
        if matches!(val.repr, Repr::F64) {
            self.emit_ta_store_f64(addr, kind, val.val, slow_blk, merge, margs);
            return;
        }

        // Boxed, statically mixed: dispatch on the nunbox tag.
        let int_blk = self.body.add_block();
        let chk_dbl = self.body.add_block();
        let dbl_blk = self.body.add_block();
        let is_int = self.tag_eq(val_boxed, TAG_INT32 as u32);
        self.cond_br(is_int, int_blk, chk_dbl);
        self.cur = chk_dbl;
        let is_dbl = self.is_double_tag(val_boxed);
        self.cond_br(is_dbl, dbl_blk, slow_blk);
        self.cur = int_blk;
        let v = self.unop(Operator::I32WrapI64, val_boxed, Type::I32);
        self.emit_ta_store_int(addr, kind, v);
        self.body.set_terminator(
            self.cur,
            Terminator::Br {
                target: BlockTarget {
                    block: merge,
                    args: margs.clone(),
                },
            },
        );
        self.cur = dbl_blk;
        let f = self.unop(Operator::F64ReinterpretI64, val_boxed, Type::F64);
        self.emit_ta_store_f64(addr, kind, f, slow_blk, merge, margs);
        self.arm_restore(st);
    }

    /// Kind-specific store of an unboxed int32 into a typed-array element at
    /// `addr` (no terminator; the caller branches). Integer kinds store the
    /// low bits (the ToInt32/ToUint32 wraparound); Uint8Clamped clamps to
    /// [0, 255]; the float kinds convert.
    pub(super) fn emit_ta_store_int(&mut self, addr: Value, kind: TaKind, v: Value) {
        let st = match kind {
            TaKind::Int8 | TaKind::Uint8 => self.store8(addr, 0, v),
            TaKind::Uint8Clamped => {
                let zero = self.i32_const(0);
                let cap = self.i32_const(255);
                let is_neg = self.binop(Operator::I32LtS, v, zero, Type::I32);
                let lo = self.select(Type::I32, zero, v, is_neg);
                let over = self.binop(Operator::I32GtS, lo, cap, Type::I32);
                let c = self.select(Type::I32, cap, lo, over);
                self.store8(addr, 0, c)
            }
            TaKind::Int16 | TaKind::Uint16 => self.store16(addr, 0, v),
            TaKind::Int32 | TaKind::Uint32 => self.store_i32(addr, 0, v),
            TaKind::Float32 => {
                let f = self.unop(Operator::F32ConvertI32S, v, Type::F32);
                self.store_f32(addr, 0, f)
            }
            TaKind::Float64 => {
                let d = self.unop(Operator::F64ConvertI32S, v, Type::F64);
                self.store_f64(addr, 0, d)
            }
        };
        self.tag_store(st, HeapKind::Elements);
    }

    /// Kind-specific store of an unboxed f64 into a typed-array element at
    /// `addr`. Integer kinds require an exact int32 round-trip (else
    /// `slow_blk`); Uint8Clamped clamps+rounds half-to-even (`f64.nearest`,
    /// NaN -> 0 via the saturating truncation) -- both defined for every
    /// double, no bail. Sets the terminator (success -> `merge` with `margs`).
    pub(super) fn emit_ta_store_f64(
        &mut self,
        addr: Value,
        kind: TaKind,
        f: Value,
        slow_blk: Block,
        merge: Block,
        margs: Vec<Value>,
    ) {
        match kind {
            TaKind::Int8
            | TaKind::Uint8
            | TaKind::Int16
            | TaKind::Uint16
            | TaKind::Int32
            | TaKind::Uint32 => {
                let i = self.unop(Operator::I32TruncSatF64S, f, Type::I32);
                let back = self.unop(Operator::F64ConvertI32S, i, Type::F64);
                let exact = self.binop(Operator::F64Eq, back, f, Type::I32);
                let ok_blk = self.body.add_block();
                self.cond_br(exact, ok_blk, slow_blk);
                self.cur = ok_blk;
                self.emit_ta_store_int(addr, kind, i);
            }
            TaKind::Uint8Clamped => {
                let zero = self.f64_const(0.0);
                let cap = self.f64_const(255.0);
                let lo = self.binop(Operator::F64Max, f, zero, Type::F64);
                let c = self.binop(Operator::F64Min, lo, cap, Type::F64);
                let r = self.unop(Operator::F64Nearest, c, Type::F64);
                let i = self.unop(Operator::I32TruncSatF64S, r, Type::I32);
                let st = self.store8(addr, 0, i);
                self.tag_store(st, HeapKind::Elements);
            }
            TaKind::Float32 => {
                let g = self.unop(Operator::F32DemoteF64, f, Type::F32);
                let st = self.store_f32(addr, 0, g);
                self.tag_store(st, HeapKind::Elements);
            }
            TaKind::Float64 => {
                let st = self.store_f64(addr, 0, f);
                self.tag_store(st, HeapKind::Elements);
            }
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

    /// `GetElem` fast arms: predicted-TA arm, dense in-bounds non-hole read,
    /// string `s[i]` arm, poly-TA probe, `arguments[i]` arm; only the miss
    /// calls the generic helper. The arms are ctx-independent hit/miss
    /// diamonds -- every arm carries the same implication (a boxed result),
    /// so the in-version merge is legal (theta-squash).
    pub(super) fn emit_get_element(&mut self, pc: Pc) -> Result<(), String> {
        if self.outline_generic() {
            // Arm-free generic early-out (the arm-free form) for the
            // MAX_BODY_VALUES retry.
            let key = self.pop()?;
            let recv = self.pop()?;
            let key_boxed = self.to_boxed(&key);
            let recv_boxed = self.to_boxed(&recv);
            let gete = self.helpers.get_element;
            let result = self
                .rt_call(gete, true, |_, _| vec![recv_boxed, key_boxed])
                .unwrap();
            self.push_boxed(result, self.def_type(pc, 0));
            return Ok(());
        }
        let key = self.pop()?;
        let recv = self.pop()?;
        let recv_ptr = self.to_ptr(&recv);
        let key_exact = is_exact_int32(&key.ty);
        let recv_only = is_object_only(&recv.ty);
        let ta_kind = self
            .ctx
            .facts
            .ta_elem_sites
            .get(&Site::new(self.source_id, self.evid_pc(pc)))
            .copied();
        let string_arm = !recv_only && may_be_string(&recv.ty);
        let mega_arm = recv.ty.outside && may_be_string(&key.ty);
        // The boxes are emitted in the entry block only where an arm the
        // entry dominates needs them; a proven int32 key rides the dense
        // arm raw, and the miss helper boxes its own arguments, so boxing
        // the index up front would only be an unbox/rebox round trip.
        let key_boxed = (!key_exact || ta_kind.is_some() || string_arm || mega_arm)
            .then(|| self.to_boxed(&key));
        let recv_boxed = (!recv_only || string_arm).then(|| self.to_boxed(&recv));

        // Deferred spills: the fast arms are pure, so only the slow
        // block spills (rooting; recv/key are helper args it roots itself).
        let (reprs, vals) = self.diamond_snapshot();
        let top_off = self.operand_base + 8 * u32::try_from(reprs.len()).unwrap();

        // Precondition: recv is an object and key is an int32 (each elided
        // when the ctx proves it, else a runtime nunbox tag test). The
        // dense loads below are reached only when this holds, so they
        // never dereference a non-object.
        let recv_obj = if recv_only {
            self.emit_rely_census(census::RELY_ELEM, recv.prov);
            None
        } else {
            Some(self.tag_eq(recv_boxed.unwrap(), TAG_OBJECT as u32))
        };
        let key_int = if key_exact {
            self.emit_rely_census(census::RELY_ELEM, key.prov);
            None
        } else {
            Some(self.tag_eq(key_boxed.unwrap(), TAG_INT32 as u32))
        };
        let pre = match (recv_obj, key_int) {
            (Some(a), Some(b)) => self.binop(Operator::I32And, a, b, Type::I32),
            (Some(a), None) | (None, Some(a)) => a,
            (None, None) => self.i32_const(1),
        };
        let recv_obj = match recv_obj {
            Some(v) => v,
            None => self.i32_const(1),
        };
        let key_int = match key_int {
            Some(v) => v,
            None => self.i32_const(1),
        };

        let load_blk = self.body.add_block();
        let read_blk = self.body.add_block();
        let slow_blk = self.body.add_block();
        let merge = self.body.add_block();
        let op_params = self.diamond_params(merge, &reprs);
        let res_param = self.body.add_blockparam(merge, Type::I64);
        let ok_param = self.body.add_blockparam(merge, Type::I32);

        // A non-object receiver with an int32 key routes through the inline
        // string s[i] arm before giving up; a non-int32 key goes straight
        // to the helper. A proven-object receiver kills the arm outright:
        // `outside` means the object world (the `recv_obj` elision above
        // already relies on that), so the arm is dead there -- and a dead
        // arm's exactly-`str` exit lineage would poison the consuming
        // version's ctx for whole loop bodies -- a `dbl|str` local forces
        // every chain add to the generic diamond. The helper still covers
        // actual strings.
        let not_dense_blk = if string_arm {
            self.body.add_block()
        } else {
            slow_blk
        };
        // Predicted typed-array read (likelier `ta_elem_sites` evidence):
        // guard the clasp against the predicted fixed-length TA class and
        // read inline. A clasp mismatch falls through to the dense
        // `load_blk`.
        let pre_true = if ta_kind.is_some() {
            self.body.add_block()
        } else {
            load_blk
        };
        let next_pc = pc + JSOp::GetElem.len();
        // String-keyed by-value mega arm (`obj[name]`, the for-in copy
        // shape): a pure-leaf probe of the mega-get table's elem key
        // namespace. A hit serves the read helper-free -- the value comes
        // back claim-free and the arm continues at next_pc in its own
        // lineage (the merge below refines the KEY to int32, which this
        // arm's population contradicts). Gated on the key not being a
        // proven int32 and the receiver reaching the object world, the
        // same join-poisoning discipline as the string-receiver arm.
        let mega_chk = if mega_arm {
            self.body.add_block()
        } else {
            not_dense_blk
        };
        self.cond_br(pre, pre_true, mega_chk);
        if mega_chk != not_dense_blk {
            self.cur = mega_chk;
            let mega_blk = self.body.add_block();
            self.cond_br(recv_obj, mega_blk, not_dense_blk);
            self.cur = mega_blk;
            let r = self.call_i64(self.helpers.elem_mega_get, &[recv_ptr, key_boxed.unwrap()]);
            let mega_miss = self.tag_eq(r, TAG_MAGIC as u32);
            let mega_hit_blk = self.body.add_block();
            self.cond_br(mega_miss, slow_blk, mega_hit_blk);
            self.cur = mega_hit_blk;
            let saved_stack = self.stack.clone();
            self.stack.push(Operand::plain(r, Repr::Boxed, bottom_ty()));
            let target = self.edge_to(next_pc);
            self.body
                .set_terminator(self.cur, Terminator::Br { target });
            self.stack = saved_stack;
        }
        if let Some(kind) = ta_kind {
            self.emit_ta_get_arm(
                pre_true,
                load_blk,
                slow_blk,
                next_pc,
                recv_ptr,
                key_boxed.unwrap(),
                kind,
                &recv,
            );
        }
        if not_dense_blk != slow_blk {
            self.emit_string_elem_arm(
                not_dense_blk,
                slow_blk,
                next_pc,
                recv_boxed.unwrap(),
                recv_ptr,
                key_boxed.unwrap(),
                key_int,
            );
        }

        // load_blk: recv is an object, key is an int32. Guard that it is a
        // NativeObject before `elements_` is dereferenced, then read
        // `elements_`, the dense `initializedLength` (12 bytes before
        // element[0]), and bounds-check the index (unsigned, so a negative
        // index fails too).
        self.cur = load_blk;
        let objptr = recv_ptr;
        self.emit_native_object_guard(objptr, slow_blk);
        let dense_blk = self.cur;
        let elements = self.load_i32(objptr, OBJ_ELEMENTS_OFFSET);
        self.eff(elements, Eff::Read(HeapKind::ElementsHeader));
        let initlen_addr = {
            let k = self.i32_const(ELEMENTS_INITLEN_BACK);
            self.binop(Operator::I32Sub, elements, k, Type::I32)
        };
        let initlen = self.load_i32(initlen_addr, 0);
        self.eff(initlen, Eff::ReadBits(HeapKind::ElementsHeader));
        let idx = if key_exact {
            self.int32_payload(&key, key_boxed)
        } else {
            self.unop(Operator::I32WrapI64, key_boxed.unwrap(), Type::I32)
        };
        let in_bounds = self.binop(Operator::I32LtU, idx, initlen, Type::I32);
        // An out-of-dense-bounds int-keyed object read (a typed array
        // always lands here: its dense initializedLength is 0) first tries
        // the shared polymorphic TA helper (pure leaf, magic bits = miss),
        // then the inline `arguments[i]` arm (gated on `needs_args_obj` so
        // scripts that never build an arguments object don't pay the clasp
        // loads), then the generic helper.
        let args_check = if !self.needs_args_obj {
            slow_blk
        } else {
            self.body.add_block()
        };
        let want_poly = self
            .ctx
            .facts
            .elem_poly_sites
            .contains(&Site::new(self.source_id, self.evid_pc(pc)));
        let oob_tgt = if want_poly {
            self.body.add_block()
        } else {
            args_check
        };
        self.body.set_terminator(
            dense_blk,
            Terminator::CondBr {
                cond: in_bounds,
                if_true: BlockTarget {
                    block: read_blk,
                    args: vec![],
                },
                if_false: BlockTarget {
                    block: oob_tgt,
                    args: vec![],
                },
            },
        );
        if want_poly {
            self.cur = oob_tgt;
            let ta_res = self.call_i64(self.helpers.ta_get_poly, &[objptr, idx]);
            let ta_miss = self.tag_eq(ta_res, TAG_MAGIC as u32);
            let one_ta = self.i32_const(1);
            let mut ta_args = vals.clone();
            ta_args.push(ta_res);
            ta_args.push(one_ta);
            self.body.set_terminator(
                oob_tgt,
                Terminator::CondBr {
                    cond: ta_miss,
                    if_true: BlockTarget {
                        block: args_check,
                        args: vec![],
                    },
                    if_false: BlockTarget {
                        block: merge,
                        args: ta_args,
                    },
                },
            );
        }

        // read_blk: in bounds. Load the element, then hole-check (any
        // magic-tagged dense slot is a hole, never a user value). Non-hole
        // -> fast merge; hole -> the generic helper.
        self.cur = read_blk;
        let elem_addr = {
            let three = self.i32_const(3);
            let off = self.binop(Operator::I32Shl, idx, three, Type::I32);
            self.binop(Operator::I32Add, elements, off, Type::I32)
        };
        let elem = self.load_i64(elem_addr, 0);
        self.eff(elem, Eff::Read(HeapKind::Elements));
        let is_hole = self.tag_eq(elem, TAG_MAGIC as u32);
        let one = self.i32_const(1);
        let mut fast_args = vals.clone();
        fast_args.push(elem);
        fast_args.push(one);
        self.body.set_terminator(
            read_blk,
            Terminator::CondBr {
                cond: is_hole,
                if_true: BlockTarget {
                    block: slow_blk,
                    args: vec![],
                },
                if_false: BlockTarget {
                    block: merge,
                    args: fast_args,
                },
            },
        );

        // args_check: an out-of-dense-bounds object read. If the receiver
        // is a (mapped or unmapped) arguments object, read
        // `data()->args[idx]` directly, mirroring
        // ArgumentsObject::element(i): bounds vs the packed initialLength
        // (fixed slot 0 >> 5), the ELEMENT_OVERRIDDEN_BIT (0x4) guard (any
        // deleted/redefined element -> helper), and the magic forward value
        // (an aliased mapped formal held in the CallObject) -> helper.
        // `data()` is DATA_SLOT (fixed slot 1) PrivateValue payload;
        // `offsetOfArgs` (engine constexpr, host slot +8) locates args[0].
        if args_check != slow_blk {
            self.cur = args_check;
            let shape = self.load_i32(recv_ptr, SHAPE_OFFSET);
            let base = self.load_i32(shape, SHAPE_BASESHAPE_OFFSET);
            self.eff(base, Eff::Read(HeapKind::Shape));
            let clasp = self.load_i32(base, BASESHAPE_CLASP_OFFSET);
            self.eff(clasp, Eff::Read(HeapKind::Shape));
            let acbase = self.i32_const(self.helpers.args_class_base);
            let mapped_class = self.load_i32(acbase, 0);
            let unmapped_class = self.load_i32(acbase, 4);
            let is_mapped = self.binop(Operator::I32Eq, clasp, mapped_class, Type::I32);
            let is_unmapped = self.binop(Operator::I32Eq, clasp, unmapped_class, Type::I32);
            let is_args = self.binop(Operator::I32Or, is_mapped, is_unmapped, Type::I32);
            let args_bounds = self.body.add_block();
            self.cond_br(is_args, args_bounds, slow_blk);

            self.cur = args_bounds;
            let packed = self.load_i32(recv_ptr, FIXED_SLOTS_BASE);
            let four = self.i32_const(4);
            let over = self.binop(Operator::I32And, packed, four, Type::I32);
            let over_zero = self.unop(Operator::I32Eqz, over, Type::I32);
            let five = self.i32_const(5);
            let arglen = self.binop(Operator::I32ShrU, packed, five, Type::I32);
            let in_arg = self.binop(Operator::I32LtU, idx, arglen, Type::I32);
            let valid = self.binop(Operator::I32And, in_arg, over_zero, Type::I32);
            let args_read = self.body.add_block();
            self.cond_br(valid, args_read, slow_blk);

            self.cur = args_read;
            let data = self.load_i32(recv_ptr, 24);
            let elems_off = self.load_i32(acbase, 8);
            let elems = self.binop(Operator::I32Add, data, elems_off, Type::I32);
            let three = self.i32_const(3);
            let off = self.binop(Operator::I32Shl, idx, three, Type::I32);
            let aelem_addr = self.binop(Operator::I32Add, elems, off, Type::I32);
            let aelem = self.load_i64(aelem_addr, 0);
            let is_magic = self.tag_eq(aelem, TAG_MAGIC as u32);
            let one2 = self.i32_const(1);
            let mut ok_args = vals.clone();
            ok_args.push(aelem);
            ok_args.push(one2);
            self.body.set_terminator(
                args_read,
                Terminator::CondBr {
                    cond: is_magic,
                    if_true: BlockTarget {
                        block: slow_blk,
                        args: vec![],
                    },
                    if_false: BlockTarget {
                        block: merge,
                        args: ok_args,
                    },
                },
            );
        }

        // slow_blk (arm continuation): spill (rooting), the generic
        // element get, reload, continue at next_pc under the weaker ctx --
        // the fast spine stays call-free (LICM depends on it).
        self.cur = slow_blk;
        // NOT epoch-kept: the merge refines the receiver (object) and the
        // key (int32) source slots; a keep lineage restored to the pre-op
        // state joining next_pc erases both for every lineage there.
        let arm_st = self.arm_state();
        let recv_boxed = match recv_boxed {
            Some(v) => v,
            None => self.to_boxed(&recv),
        };
        let key_boxed = match key_boxed {
            Some(v) => v,
            None => self.to_boxed(&key),
        };
        let n = self.spill_all();
        let top = self.add_offset(self.vp, top_off);
        let gete = self.helpers.get_element;
        let ok = self.call_i32(gete, &[self.cx, top, recv_boxed, key_boxed]);
        let slow_res = self.load_i64(self.vp, top_off);
        {
            self.reload(n);
            self.branch_on_err(ok);
            self.push_boxed(slow_res, bottom_ty());
            let target = self.dirty_edge_to(next_pc);
            self.body
                .set_terminator(self.cur, Terminator::Br { target });
            self.arm_restore(arm_st);
        }

        // merge: rebind operands, run the error handshake, then the
        // typed-load ladder on the result (dense/args/poly-TA arms carry
        // no type proof; likely_elems evidence orders the arms). Every
        // merge predecessor passed the object-receiver and int32-key
        // tests (the string arm and the slow arm left the version), so
        // both proofs write back to their source slots.
        self.cur = merge;
        self.diamond_rebind(&op_params);
        for (i, &r) in reprs.iter().enumerate() {
            self.stack[i].repr = r;
        }
        self.branch_on_err(ok_param);
        self.refine_src(&recv, OBJ_ONLY_SLOT);
        self.refine_src(&key, INT32_SLOT);
        let claim = self
            .ctx
            .likely_elems
            .get(&Site::new(self.source_id, self.evid_pc(pc)))
            .copied()
            .unwrap_or(Claim::NONE);
        // Array-stamp fold: every merge predecessor passed the
        // object-receiver test (the string and slow arms left the
        // version), so `recv_ptr` is a live object pointer here and the
        // stamp word can be read without another guard.
        let arr = self
            .ctx
            .array_elem_in
            .get(&Site::new(self.source_id, self.evid_pc(pc)))
            .filter(|a| a.mask == PRIM_INT32 && claim.prims().intersects(PRIM_INT32))
            .map(|a| ArrFold {
                recv_ptr,
                want_word: a.key.get() | CLASS_WORD_SHALLOW | CLASS_WORD_RANGES,
                range: a.range,
            });
        self.push_load_typed_arr(res_param, claim, next_pc, arr);
        Ok(())
    }

    /// `SetElem` fast arms: predicted-TA store, dense in-bounds overwrite
    /// (flags-masked; frozen/non-packed take the careful arm), the call-free
    /// append/hole-overwrite arm, poly-TA store probe; only the miss calls
    /// the generic helper. Leaves the value on the stack (def == use).
    pub(super) fn emit_set_element(&mut self, pc: Pc, strict: bool) -> Result<(), String> {
        if self.outline_generic() {
            // Arm-free generic early-out (the arm-free form) for the
            // MAX_BODY_VALUES retry.
            let val = self.pop()?;
            let key = self.pop()?;
            let recv = self.pop()?;
            let val_boxed = self.to_boxed(&val);
            let key_boxed = self.to_boxed(&key);
            let recv_boxed = self.to_boxed(&recv);
            self.push(val_boxed, Repr::Boxed, val.ty);
            let strict_v = self.i32_const(u32::from(strict));
            let sete = self.helpers.set_element;
            self.rt_call(sete, false, |_, _| {
                vec![recv_boxed, key_boxed, val_boxed, strict_v]
            });
            return Ok(());
        }
        let val = self.pop()?;
        let key = self.pop()?;
        let recv = self.pop()?;
        // An integral double stored under a write-site claim that admits
        // Double is boxed as the double it is: every read of that element
        // node already admits the tag, so the int32 canonicalisation (12
        // IR of trunc/convert/compare/select) proves nothing there. Only a
        // site whose node the analysis did not resolve keeps it.
        let site = Site::new(self.source_id, self.evid_pc(pc));
        let dbl_ok = val.repr == Repr::F64
            && !is_exact_int32(&val.ty)
            && self
                .ctx
                .facts
                .elem_write_sites
                .get(&site)
                .is_some_and(|m| m.prims().intersects(PRIM_DOUBLE));
        let val_boxed = if dbl_ok {
            self.unop(Operator::I64ReinterpretF64, val.val, Type::I64)
        } else {
            self.to_boxed(&val)
        };
        let recv_ptr = self.to_ptr(&recv);
        let recv_bit = self.store_recv_bit(&recv);
        let key_exact = is_exact_int32(&key.ty);
        let recv_only = is_object_only(&recv.ty);
        let ta_kind = self.ctx.facts.ta_elem_sites.get(&site).copied();
        let smega_arm = recv.ty.outside && may_be_string(&key.ty);
        // As on the get side: box in the entry block only for the arms it
        // dominates (tag tests, TA/mega arms, the element barrier); a
        // proven int32 key rides the dense arm raw.
        let key_boxed = (!key_exact || ta_kind.is_some() || smega_arm).then(|| self.to_boxed(&key));
        let recv_boxed =
            (!recv_only || smega_arm || !is_non_gc(&val.ty)).then(|| self.to_boxed(&recv));

        // SetElem leaves the value on the stack (def == use). Push it
        // before the diamond so the slow path roots it and the merge
        // rebinds it.
        self.push_ranged(val_boxed, Repr::Boxed, val.ty, val.range);

        // Deferred spills: the dense-store fast path never GCs (the
        // barrier is a leaf), so only the slow block spills and reloads.
        let (reprs, vals) = self.diamond_snapshot();
        let top_off = self.operand_base + 8 * u32::try_from(reprs.len()).unwrap();

        let recv_obj = if recv_only {
            self.emit_rely_census(census::RELY_ELEM, recv.prov);
            None
        } else {
            Some(self.tag_eq(recv_boxed.unwrap(), TAG_OBJECT as u32))
        };
        let key_int = if key_exact {
            self.emit_rely_census(census::RELY_ELEM, key.prov);
            None
        } else {
            Some(self.tag_eq(key_boxed.unwrap(), TAG_INT32 as u32))
        };
        let pre = match (recv_obj, key_int) {
            (Some(a), Some(b)) => self.binop(Operator::I32And, a, b, Type::I32),
            (Some(a), None) | (None, Some(a)) => a,
            (None, None) => self.i32_const(1),
        };
        let recv_obj = match recv_obj {
            Some(v) => v,
            None => self.i32_const(1),
        };

        let load_blk = self.body.add_block();
        let flags_blk = self.body.add_block();
        let store_blk = self.body.add_block();
        let slow_blk = self.body.add_block();
        let merge = self.body.add_block();
        let op_params = self.diamond_params(merge, &reprs);
        let ok_param = self.body.add_blockparam(merge, Type::I32);

        // Predicted typed-array store (likelier evidence, set side).
        let pre_true = if ta_kind.is_some() {
            self.body.add_block()
        } else {
            load_blk
        };
        let pre_fail = if self.guard_census_on() {
            let saved = self.cur;
            let b = self.body.add_block();
            self.cur = b;
            let k_key = self.i32_const(census::SETELEM_WHY + 1);
            let k_recv = self.i32_const(census::SETELEM_WHY);
            let kind = self.select(Type::I32, k_key, k_recv, recv_obj);
            self.emit_guard_census_dyn(kind, pc);
            self.body.set_terminator(
                b,
                Terminator::Br {
                    target: BlockTarget {
                        block: slow_blk,
                        args: vec![],
                    },
                },
            );
            self.cur = saved;
            b
        } else {
            slow_blk
        };
        // String-keyed by-value mega-set arm: probe the mega-set table's
        // elem key namespace (pure leaf); a hit is a validated plain-data
        // overwrite, so the site does the barriered store off the row and
        // continues at next_pc in its own lineage (the merge refines the
        // KEY to int32, which this population contradicts). The store owes
        // the full write-invalidation duty the C++ path pays engine-side.
        let smega_chk = if smega_arm {
            self.body.add_block()
        } else {
            pre_fail
        };
        self.cond_br(pre, pre_true, smega_chk);
        if smega_chk != pre_fail {
            self.cur = smega_chk;
            let smega_blk = self.body.add_block();
            self.cond_br(recv_obj, smega_blk, pre_fail);
            self.cur = smega_blk;
            let entry = self.call_i32(
                self.helpers.elem_mega_set_probe,
                &[recv_ptr, key_boxed.unwrap()],
            );
            let z = self.i32_const(0);
            let hit = self.binop(Operator::I32Ne, entry, z, Type::I32);
            let smega_store = self.body.add_block();
            self.cond_br(hit, smega_store, pre_fail);
            self.cur = smega_store;
            let m_slot_enc = self.load_i32(entry, MEGA_SET_SLOTENC);
            let m_slot_addr = self.emit_slot_addr(recv_ptr, m_slot_enc);
            self.emit_pre_write_barrier_addr(m_slot_addr);
            let st = self.store_i64(m_slot_addr, 0, val_boxed);
            self.eff_store(st, Eff::Write(HeapKind::Slot), recv_bit);
            let val_is_num = store_value_numeric(&val);
            let range_act = if self.ctx.layout_field_ranges_in.is_empty() {
                RangeAct::Nothing
            } else {
                // The written name is unknown at compile time, so any
                // range-claimed field could be the one hit.
                RangeAct::Clear
            };
            let (stamp_static, choke_dyn) =
                self.emit_store_choke(recv_ptr, val_boxed, val_is_num, recv_bit, None, range_act);
            if !is_non_gc(&val.ty) {
                let m_abs = self.load_i32(entry, MEGA_SET_ABSSLOT);
                self.emit_post_write_barrier(recv_boxed.unwrap(), m_abs, val_boxed);
            }
            let saved_flags = self.cur_flags;
            self.or_flags_const(recv_bit | stamp_static);
            if let Some(w) = choke_dyn {
                self.or_flags_word(w);
            }
            let next_pc = pc + JSOp::SetElem.len();
            let target = self.edge_to(next_pc);
            self.body
                .set_terminator(self.cur, Terminator::Br { target });
            self.cur_flags = saved_flags;
        }
        if let Some(kind) = ta_kind {
            let ta_slow = self.setelem_why_blk(slow_blk, 2, pc);
            self.emit_ta_set_arm(
                pre_true,
                load_blk,
                ta_slow,
                merge,
                recv_ptr,
                key_boxed.unwrap(),
                &val,
                val_boxed,
                kind,
                &vals,
                &recv,
            );
        }

        // load_blk: guard the receiver is a NativeObject (an unguarded
        // in-bounds hit would store into arbitrary memory), then read
        // `elements_` and the dense `initializedLength`; bounds-check the
        // index unsigned. Only an *in-bounds overwrite* takes the fast
        // path; append (idx == initializedLength) enters the inline append
        // arm, growth needs the generic helper's capacity/length
        // bookkeeping.
        self.cur = load_blk;
        let objptr = recv_ptr;
        let nonnative_slow = self.setelem_why_blk(slow_blk, 3, pc);
        self.emit_native_object_guard(objptr, nonnative_slow);
        let dense_blk = self.cur;
        let elements = self.load_i32(objptr, OBJ_ELEMENTS_OFFSET);
        self.eff(elements, Eff::Read(HeapKind::ElementsHeader));
        let initlen_addr = {
            let k = self.i32_const(ELEMENTS_INITLEN_BACK);
            self.binop(Operator::I32Sub, elements, k, Type::I32)
        };
        let initlen = self.load_i32(initlen_addr, 0);
        self.eff(initlen, Eff::ReadBits(HeapKind::ElementsHeader));
        let idx = if key_exact {
            self.int32_payload(&key, key_boxed)
        } else {
            self.unop(Operator::I32WrapI64, key_boxed.unwrap(), Type::I32)
        };
        let in_bounds = self.binop(Operator::I32LtU, idx, initlen, Type::I32);
        // Out-of-dense-bounds order: the inline dense-append arm (cache
        // probe, no call), then the shared polymorphic TA store helper
        // (pure leaf) on TA-possible sites, then the generic helper.
        let want_poly = self
            .ctx
            .facts
            .elem_poly_sites
            .contains(&Site::new(self.source_id, self.evid_pc(pc)));
        let poly_tgt = if want_poly {
            self.body.add_block()
        } else {
            slow_blk
        };
        let oob_tgt = self.body.add_block();
        self.body.set_terminator(
            dense_blk,
            Terminator::CondBr {
                cond: in_bounds,
                if_true: BlockTarget {
                    block: flags_blk,
                    args: vec![],
                },
                if_false: BlockTarget {
                    block: oob_tgt,
                    args: vec![],
                },
            },
        );
        self.cur = oob_tgt;
        let append_fail = self.setelem_why_blk(poly_tgt, 4, pc);
        let oob_recv_boxed = match recv_boxed {
            Some(v) => v,
            None => self.to_boxed(&recv),
        };
        let append_hole_tgt = self.emit_elem_append_arm(
            append_fail,
            merge,
            &vals,
            objptr,
            elements,
            initlen_addr,
            initlen,
            idx,
            oob_recv_boxed,
            &val,
            val_boxed,
            recv_bit,
            pc,
        );
        if want_poly {
            self.cur = poly_tgt;
            let ta_ok = self.call_i32(self.helpers.ta_set_poly, &[objptr, idx, val_boxed]);
            let poly_fail = self.setelem_why_blk(slow_blk, 5, pc);
            let mut ta_args = vals.clone();
            let one_ta = self.i32_const(1);
            ta_args.push(one_ta);
            self.body.set_terminator(
                poly_tgt,
                Terminator::CondBr {
                    cond: ta_ok,
                    if_true: BlockTarget {
                        block: merge,
                        args: ta_args,
                    },
                    if_false: BlockTarget {
                        block: poly_fail,
                        args: vec![],
                    },
                },
            );
        }

        // flags_blk: a frozen array's dense elements are non-writable, and
        // a NON_PACKED array's in-bounds slot may be a hole, whose
        // overwrite is a property add, not an overwrite. One masked test of
        // the already-loaded flags word admits the common packed unfrozen
        // array straight to the raw store; only a non-packed array pays the
        // careful arm's per-element hole check (a descending fill pattern
        // marks NON_PACKED permanently, so sending non-packed stores to the
        // generic helper outright is not acceptable).
        self.cur = flags_blk;
        let flags_addr = {
            let k = self.i32_const(ELEMENTS_FLAGS_BACK);
            self.binop(Operator::I32Sub, elements, k, Type::I32)
        };
        let flags = self.load_i32(flags_addr, 0);
        self.eff(flags, Eff::ReadBits(HeapKind::ElementsHeader));
        let elem_addr = {
            let three = self.i32_const(3);
            let off = self.binop(Operator::I32Shl, idx, three, Type::I32);
            self.binop(Operator::I32Add, elements, off, Type::I32)
        };
        let careful_bits = self.i32_const(ELEMENTS_FROZEN_FLAG | ELEMENTS_NON_PACKED_FLAG);
        let careful = self.binop(Operator::I32And, flags, careful_bits, Type::I32);
        let careful_blk = self.body.add_block();
        self.cond_br(careful, careful_blk, store_blk);
        self.cur = careful_blk;
        let frozen_bit = self.i32_const(ELEMENTS_FROZEN_FLAG);
        let frozen = self.binop(Operator::I32And, flags, frozen_bit, Type::I32);
        let hole_chk_blk = self.body.add_block();
        let frozen_slow = self.setelem_why_blk(slow_blk, 6, pc);
        self.cond_br(frozen, frozen_slow, hole_chk_blk);
        self.cur = hole_chk_blk;
        let old_elem = self.load_i64(elem_addr, 0);
        self.eff(old_elem, Eff::Read(HeapKind::Elements));
        let is_hole = self.tag_eq(old_elem, TAG_MAGIC as u32);
        // An in-bounds hole store re-enters the append arm's hole path
        // (row probe + live proto shapes prove add-safety; store, no
        // bumps) instead of the generic helper -- the descending-fill
        // band drains here.
        self.cond_br(is_hole, append_hole_tgt, store_blk);

        // store_blk: raw store of the boxed value into the dense slot, then
        // the element generational post-write barrier (its own inline
        // GC/nursery check + leaf call). No GC here -> no reload needed on
        // this path.
        self.cur = store_blk;
        let st = self.store_i64(elem_addr, 0, val_boxed);
        self.eff_store(st, Eff::Write(HeapKind::Elements), recv_bit);
        self.emit_elem_store_duty(objptr, &val);
        // Elide the element generational barrier when the ctx proves the
        // stored value holds no GC pointer.
        if !is_non_gc(&val.ty) {
            self.emit_post_write_barrier_elem(recv_boxed.unwrap(), idx, val_boxed);
        }
        let one = self.i32_const(1);
        let mut fast_args = vals.clone();
        fast_args.push(one);
        self.body.set_terminator(
            self.cur, // store_blk, or the barrier's continuation block
            Terminator::Br {
                target: BlockTarget {
                    block: merge,
                    args: fast_args,
                },
            },
        );

        // slow_blk (arm continuation): spill (rooting), the generic
        // element set (handles growth/frozen/proto setters/coercion),
        // reload, continue at next_pc under the weaker ctx.
        self.cur = slow_blk;
        let arm_st = self.arm_state();
        // Epoch-proven keep, gated to the string-key-possible sites (the
        // same gate as the mega arms): a for-in ADD lands the whole store
        // in the helper, but the C++ chokes bump the epoch only when a
        // REAL stamp demotes -- a fresh receiver's shape change moves no
        // stamp, so the keep arm rejoins Opt with the lineage's facts.
        // The gate is restricted to string-key-possible sites because an
        // ungated form degrades hot int-keyed sites through the pre-op
        // join.
        let keep = recv.ty.outside && may_be_string(&key.ty);
        let pre_e = if keep {
            Some(self.emit_epoch_read())
        } else {
            None
        };
        let pre_b = if keep { self.sample_bind_epoch() } else { None };
        let recv_boxed = match recv_boxed {
            Some(v) => v,
            None => self.to_boxed(&recv),
        };
        let key_boxed = match key_boxed {
            Some(v) => v,
            None => self.to_boxed(&key),
        };
        let n = self.spill_all();
        let top = self.add_offset(self.vp, top_off);
        let sete = self.helpers.set_element;
        let strict_v = self.i32_const(u32::from(strict));
        let ok = self.call_i32(
            sete,
            &[self.cx, top, recv_boxed, key_boxed, val_boxed, strict_v],
        );
        {
            let next_pc = pc + JSOp::SetElem.len();
            if let Some(pre_e) = pre_e {
                self.epoch_keep_tail(arm_st.clone(), pre_e, pre_b, ok, None, next_pc);
            }
            self.reload(n);
            self.branch_on_err(ok);
            let target = self.dirty_edge_to(next_pc);
            self.body
                .set_terminator(self.cur, Terminator::Br { target });
            self.arm_restore(arm_st);
        }

        // merge: rebind operands, run the error handshake; the value stays
        // on the stack (def == use). Every merge predecessor passed the
        // object-receiver and int32-key tests: write both proofs back.
        self.cur = merge;
        self.diamond_rebind(&op_params);
        for (i, &r) in reprs.iter().enumerate() {
            self.stack[i].repr = r;
        }
        self.branch_on_err(ok_param);
        // Per-lineage accounting: every arm that reaches this merge
        // stored (TA / dense / append / poly; the slow arm left dirty).
        self.or_flags_const(recv_bit);
        self.refine_src(&recv, OBJ_ONLY_SLOT);
        self.refine_src(&key, INT32_SLOT);
        Ok(())
    }

    /// The dense-append / hole-store arm: one direct call to
    /// `night_elem_append`, which holds the eleven blocks a fully-inline
    /// arm would need at every store site. These paths are cold in
    /// practice, so the call is rarely paid and the site keeps only what
    /// the helper cannot know: the fact-driven store duty and the barrier
    /// elision.
    ///
    /// Returns the block the dense arm's in-bounds hole rejection re-enters
    /// at; the helper re-derives the hole case rather than being told.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn emit_elem_append_arm(
        &mut self,
        fail_tgt: Block,
        merge: Block,
        vals: &[Value],
        objptr: Value,
        elements: Value,
        initlen_addr: Value,
        initlen: Value,
        idx: Value,
        recv_boxed: Value,
        val: &Operand,
        val_boxed: Value,
        recv_bit: u32,
        pc: Pc,
    ) -> Block {
        let entry = self.cur;
        let packed = self.call_i64(
            self.helpers.elem_append_check,
            &[objptr, elements, initlen, idx],
        );
        let store_blk = self.body.add_block();
        if self.guard_census_on() {
            // Census helper returns a refusal code (1..=6, all < 8; a real
            // element address is a heap pointer) -- tick it into the
            // SETELEM_APPEND_WHY buckets on the way out.
            let eight = self.boxed_const(8);
            let ok = self.binop(Operator::I64GeU, packed, eight, Type::I32);
            let saved = self.cur;
            let why_blk = self.body.add_block();
            self.cur = why_blk;
            let code = self.unop(Operator::I32WrapI64, packed, Type::I32);
            let base = self.i32_const(census::SETELEM_APPEND_WHY);
            let kind = self.binop(Operator::I32Add, base, code, Type::I32);
            self.emit_guard_census_dyn(kind, pc);
            self.body.set_terminator(
                why_blk,
                Terminator::Br {
                    target: BlockTarget {
                        block: fail_tgt,
                        args: vec![],
                    },
                },
            );
            self.cur = saved;
            self.cond_br(ok, store_blk, why_blk);
        } else {
            let zero64 = self.boxed_const(0);
            let ok = self.binop(Operator::I64Ne, packed, zero64, Type::I32);
            self.cond_br(ok, store_blk, fail_tgt);
        }

        self.cur = store_blk;
        let elem_addr = self.unop(Operator::I32WrapI64, packed, Type::I32);
        let sh32 = self.boxed_const(32);
        let row64 = self.binop(Operator::I64ShrU, packed, sh32, Type::I64);
        let row = self.unop(Operator::I32WrapI64, row64, Type::I32);
        let st = self.store_i64(elem_addr, 0, val_boxed);
        self.eff_store(st, Eff::Write(HeapKind::Elements), recv_bit);
        self.emit_elem_store_duty(objptr, val);
        // The bumps are append-only: a hole overwrite changes neither
        // initializedLength nor the Array length word.
        let is_app_st = self.binop(Operator::I32Eq, idx, initlen, Type::I32);
        let bump_blk = self.body.add_block();
        let app_done = self.body.add_block();
        self.cond_br(is_app_st, bump_blk, app_done);

        self.cur = bump_blk;
        let one_i = self.i32_const(1);
        let new_init = self.binop(Operator::I32Add, initlen, one_i, Type::I32);
        let st = self.store_i32(initlen_addr, 0, new_init);
        self.eff_store(st, Eff::Write(HeapKind::ElementsHeader), recv_bit);
        let len_addr = {
            let k = self.i32_const(ELEMENTS_LENGTH_BACK);
            self.binop(Operator::I32Sub, elements, k, Type::I32)
        };
        let len = self.load_i32(len_addr, 0);
        self.eff(len, Eff::ReadBits(HeapKind::ElementsHeader));
        let passes_len = self.binop(Operator::I32GeU, idx, len, Type::I32);
        // The elements `length` word is Array-only semantics; a plain
        // receiver's word stays untouched (row[20] = isArray, from prime).
        let is_arr = self.load_i32(row, 20);
        self.eff(is_arr, Eff::ReadBits(HeapKind::EngineTable));
        let bump = self.binop(Operator::I32And, passes_len, is_arr, Type::I32);
        let len_blk = self.body.add_block();
        self.cond_br(bump, len_blk, app_done);

        self.cur = len_blk;
        let new_len = self.binop(Operator::I32Add, idx, one_i, Type::I32);
        let st = self.store_i32(len_addr, 0, new_len);
        self.eff_store(st, Eff::Write(HeapKind::ElementsHeader), recv_bit);
        self.body.set_terminator(
            len_blk,
            Terminator::Br {
                target: BlockTarget {
                    block: app_done,
                    args: vec![],
                },
            },
        );

        self.cur = app_done;
        if !is_non_gc(&val.ty) {
            self.emit_post_write_barrier_elem(recv_boxed, idx, val_boxed);
        }
        let one_ok = self.i32_const(1);
        let mut fast_args = vals.to_vec();
        fast_args.push(one_ok);
        self.body.set_terminator(
            self.cur,
            Terminator::Br {
                target: BlockTarget {
                    block: merge,
                    args: fast_args,
                },
            },
        );
        entry
    }
}
