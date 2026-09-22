/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Property lowerings: slot access, the class-fact arms, accessors, and the
//! inline property caches.

use super::*;

/// In-module `night_ic_set_cold(shape, way_base, atom) -> i64`: the
/// fact-free SetProp site's COLD validation, emitted once per module and
/// reached by a direct call with the site's IC row pointer -- the
/// parameterized-helper discipline (`build_elem_append_helper` is the
/// precedent). It proves which cold route serves the store and hands the
/// caller where to look; the caller keeps the store itself, the choke,
/// the barriers and the flags word (per-site bookkeeping a shared helper
/// must not own). Pure leaf: reads only, no GC, no engine crossing.
///
/// Returns 0 = no cold route (fall to the miss helper);
///         2 = the add-transition row validated (old shape matched, slot
///             recorded, proto hops proven -- the caller re-derives the
///             row address from its own patched way base);
///         (1 << 32) | entry = the mega-set probe hit at `entry`.
///
/// Inlined, this validation -- the mega hash probe plus the transition
/// guards -- was the bulk of what made SetProp lower to a large number of
/// emitted instructions per site, a substantial share of a body's whole
/// IR.
pub fn build_ic_set_cold_helper(m: &mut Module, mem: waffle::Memory, mega_set_base: u32) -> Func {
    use crate::wasm::translate::RawEmit;
    use waffle::{FuncDecl, SignatureData};
    let sig = m.signatures.push(SignatureData {
        params: vec![Type::I32, Type::I32, Type::I32],
        returns: vec![Type::I64],
    });
    let mut e = RawEmit::new(m, sig, mem);
    let shape = e.param(0);
    let way_base = e.param(1);
    let atom_v = e.param(2);

    let miss = e.body.add_block();
    let poly_blk = e.body.add_block();
    let trans_blk = e.body.add_block();

    let cs = e.ld32(way_base, IC_SET_RECVSHAPE);
    let sentinel = e.i32c(IC_POLY_SENTINEL);
    let is_poly = e.bin(Operator::I32Eq, cs, sentinel, Type::I32);
    e.condbr(is_poly, poly_blk, trans_blk);

    e.cur = miss;
    let z = e.i64c(0);
    e.ret(vec![z]);

    // Mega-set probe (the hash mirrors `Bbv::emit_mega_probe`; the atom
    // half is a parameter here, one multiply on a cold path).
    e.cur = poly_blk;
    let three = e.i32c(3);
    let sh = e.bin(Operator::I32ShrU, shape, three, Type::I32);
    let k1 = e.i32c(2654435761);
    let h1 = e.bin(Operator::I32Mul, sh, k1, Type::I32);
    let k2c = e.i32c(0x9e37_79b9);
    let k2 = e.bin(Operator::I32Mul, atom_v, k2c, Type::I32);
    let h = e.bin(Operator::I32Xor, h1, k2, Type::I32);
    let mask = e.i32c(MEGA_SET_SIZE - 1);
    let idx = e.bin(Operator::I32And, h, mask, Type::I32);
    let stride = e.i32c(MEGA_SET_ENTRY_BYTES);
    let off = e.bin(Operator::I32Mul, idx, stride, Type::I32);
    let mbase = e.i32c(mega_set_base);
    let entry = e.bin(Operator::I32Add, mbase, off, Type::I32);
    let eshape = e.ld32(entry, MEGA_SHAPE);
    let eatom = e.ld32(entry, MEGA_ATOM);
    let m_shape = e.bin(Operator::I32Eq, eshape, shape, Type::I32);
    let m_atom = e.bin(Operator::I32Eq, eatom, atom_v, Type::I32);
    let m_hit = e.bin(Operator::I32And, m_shape, m_atom, Type::I32);
    let hit_blk = e.body.add_block();
    e.condbr(m_hit, hit_blk, miss);
    e.cur = hit_blk;
    let e64 = e.un(Operator::I64ExtendI32U, entry, Type::I64);
    let one32 = e.i64c(1 << 32);
    let packed = e.bin(Operator::I64Or, one32, e64, Type::I64);
    e.ret(vec![packed]);

    // Add-transition row validation (the inline replay arm's guards,
    // verbatim: old-shape match, recorded slot, IC_TRANS_INLINE_HOPS
    // proto rows against their live shape words, deeper rows empty).
    e.cur = trans_blk;
    let row = {
        let off = e.i32c(IC_TRANS_ROW_OFF);
        e.bin(Operator::I32Add, way_base, off, Type::I32)
    };
    let old_s = e.ld32(row, IC_TRANS_OLDSHAPE);
    let m_old = e.bin(Operator::I32Eq, old_s, shape, Type::I32);
    let g1 = e.body.add_block();
    e.condbr(m_old, g1, miss);
    e.cur = g1;
    let slot_off = e.ld32(row, IC_TRANS_SLOTOFF);
    let zero = e.i32c(0);
    let ok_slot = e.bin(Operator::I32Ne, slot_off, zero, Type::I32);
    let mut all = ok_slot;
    for n in 0..IC_TRANS_PROTO_HOPS {
        let pr = IC_TRANS_PROTO0 + IC_TRANS_PROTO_ROW_BYTES * n;
        let p = e.ld32(row, pr);
        let empty = e.un(Operator::I32Eqz, p, Type::I32);
        let ok = if n < IC_TRANS_INLINE_HOPS {
            let want = e.ld32(row, pr + 4);
            let live = e.ld32(p, SHAPE_OFFSET);
            let m_hop = e.bin(Operator::I32Eq, live, want, Type::I32);
            e.bin(Operator::I32Or, empty, m_hop, Type::I32)
        } else {
            empty
        };
        all = e.bin(Operator::I32And, all, ok, Type::I32);
    }
    let tr_hit = e.body.add_block();
    e.condbr(all, tr_hit, miss);
    e.cur = tr_hit;
    let two = e.i64c(2);
    e.ret(vec![two]);

    m.funcs
        .push(FuncDecl::Body(sig, "night_ic_set_cold".to_string(), e.body))
}

/// In-module by-value elem-mega probes for string-keyed element accesses
/// (`obj[name]` where the name is a runtime string: the for-in copy shape).
/// The rows live in the SAME mega get/set tables the property ICs use, in a
/// disjoint key namespace: the atom half holds `atomPtr | 1` -- a linmem
/// JSString* address, always even, so the forced low bit can never collide
/// with a property row's small-integer atomId (the C++ fill also refuses
/// the ambiguous range outright). Interning makes pointer equality the
/// exact key; a non-atom string never matches a row and takes the generic
/// helper, which is semantically its path anyway. Both are pure leaves --
/// no GC, no engine crossing -- so a hit costs a fact (the value comes back
/// claim-free), never the track.
///
///   night_elem_mega_get(objptr, keyBoxed) -> boxed value, magic bits = miss
///   night_elem_mega_set_probe(objptr, keyBoxed) -> set-row address, 0 = miss
///     (the SITE does the barriered store off the row, mirroring the
///      `night_ic_set_cold` division of labor)
pub fn build_elem_mega_helpers(
    m: &mut Module,
    mem: waffle::Memory,
    mega_get_base: u32,
    mega_set_base: u32,
) -> (Func, Func) {
    use crate::wasm::translate::{RawEmit, MEGA_GET_ENTRY_BYTES, MEGA_GET_SIZE};
    use waffle::{FuncDecl, SignatureData};
    const MEGA_GET_HOLDERPTR: u32 = 8;

    let get_sig = m.signatures.push(SignatureData {
        params: vec![Type::I32, Type::I64],
        returns: vec![Type::I64],
    });
    let elem_mega_get = {
        let mut e = RawEmit::new(m, get_sig, mem);
        let objptr = e.param(0);
        let key_boxed = e.param(1);
        let miss = e.body.add_block();
        let probe_blk = e.body.add_block();
        let is_str = e.tag_is(key_boxed, TAG_STRING);
        e.condbr(is_str, probe_blk, miss);
        e.cur = miss;
        let magic = e.i64c(TAG_MAGIC << 32);
        e.ret(vec![magic]);
        e.cur = probe_blk;
        let keyptr = e.un(Operator::I32WrapI64, key_boxed, Type::I32);
        let one = e.i32c(1);
        let ekey = e.bin(Operator::I32Or, keyptr, one, Type::I32);
        let shape = e.ld32(objptr, SHAPE_OFFSET);
        let three = e.i32c(3);
        let sh = e.bin(Operator::I32ShrU, shape, three, Type::I32);
        let k1 = e.i32c(2654435761);
        let h1 = e.bin(Operator::I32Mul, sh, k1, Type::I32);
        let k2c = e.i32c(0x9e37_79b9);
        let k2 = e.bin(Operator::I32Mul, ekey, k2c, Type::I32);
        let h = e.bin(Operator::I32Xor, h1, k2, Type::I32);
        let mask = e.i32c(MEGA_GET_SIZE - 1);
        let idx = e.bin(Operator::I32And, h, mask, Type::I32);
        let stride = e.i32c(MEGA_GET_ENTRY_BYTES);
        let off = e.bin(Operator::I32Mul, idx, stride, Type::I32);
        let mbase = e.i32c(mega_get_base);
        let entry = e.bin(Operator::I32Add, mbase, off, Type::I32);
        let eshape = e.ld32(entry, MEGA_SHAPE);
        let eatom = e.ld32(entry, MEGA_ATOM);
        let m_shape = e.bin(Operator::I32Eq, eshape, shape, Type::I32);
        let m_atom = e.bin(Operator::I32Eq, eatom, ekey, Type::I32);
        let m_hit = e.bin(Operator::I32And, m_shape, m_atom, Type::I32);
        let hit_blk = e.body.add_block();
        e.condbr(m_hit, hit_blk, miss);
        e.cur = hit_blk;
        let r = e.ic_hit_tail(objptr, entry, MEGA_GET_HOLDERPTR, miss);
        e.ret(vec![r]);
        m.funcs.push(FuncDecl::Body(
            get_sig,
            "night_elem_mega_get".to_string(),
            e.body,
        ))
    };

    let set_sig = m.signatures.push(SignatureData {
        params: vec![Type::I32, Type::I64],
        returns: vec![Type::I32],
    });
    let elem_mega_set_probe = {
        let mut e = RawEmit::new(m, set_sig, mem);
        let objptr = e.param(0);
        let key_boxed = e.param(1);
        let miss = e.body.add_block();
        let probe_blk = e.body.add_block();
        let is_str = e.tag_is(key_boxed, TAG_STRING);
        e.condbr(is_str, probe_blk, miss);
        e.cur = miss;
        let z = e.i32c(0);
        e.ret(vec![z]);
        e.cur = probe_blk;
        let keyptr = e.un(Operator::I32WrapI64, key_boxed, Type::I32);
        let one = e.i32c(1);
        let ekey = e.bin(Operator::I32Or, keyptr, one, Type::I32);
        let shape = e.ld32(objptr, SHAPE_OFFSET);
        let three = e.i32c(3);
        let sh = e.bin(Operator::I32ShrU, shape, three, Type::I32);
        let k1 = e.i32c(2654435761);
        let h1 = e.bin(Operator::I32Mul, sh, k1, Type::I32);
        let k2c = e.i32c(0x9e37_79b9);
        let k2 = e.bin(Operator::I32Mul, ekey, k2c, Type::I32);
        let h = e.bin(Operator::I32Xor, h1, k2, Type::I32);
        let mask = e.i32c(MEGA_SET_SIZE - 1);
        let idx = e.bin(Operator::I32And, h, mask, Type::I32);
        let stride = e.i32c(MEGA_SET_ENTRY_BYTES);
        let off = e.bin(Operator::I32Mul, idx, stride, Type::I32);
        let mbase = e.i32c(mega_set_base);
        let entry = e.bin(Operator::I32Add, mbase, off, Type::I32);
        let eshape = e.ld32(entry, MEGA_SHAPE);
        let eatom = e.ld32(entry, MEGA_ATOM);
        let m_shape = e.bin(Operator::I32Eq, eshape, shape, Type::I32);
        let m_atom = e.bin(Operator::I32Eq, eatom, ekey, Type::I32);
        let m_hit = e.bin(Operator::I32And, m_shape, m_atom, Type::I32);
        let hit_blk = e.body.add_block();
        e.condbr(m_hit, hit_blk, miss);
        e.cur = hit_blk;
        e.ret(vec![entry]);
        m.funcs.push(FuncDecl::Body(
            set_sig,
            "night_elem_mega_set_probe".to_string(),
            e.body,
        ))
    };

    (elem_mega_get, elem_mega_set_probe)
}

impl<'a> Bbv<'a> {
    // --- property ICs ----------------------------------------------------

    /// Branch a property-IC hit arm into the shared merge: the live operands,
    /// then whatever the arm produced, then the `ok = 1` flag, then -- when
    /// the site carries a per-arm accumulator -- this arm's own flags word,
    /// computed from the entry state so a sibling's saturation cannot leak in.
    fn ic_arm_br(
        &mut self,
        merge: Block,
        vals: &[Value],
        produced: &[Value],
        flags: Option<(FlagsAcc, Option<u32>, Option<Value>)>,
    ) {
        let mut margs = vals.to_vec();
        margs.extend_from_slice(produced);
        let one = self.i32_const(1);
        margs.push(one);
        if let Some((entry_flags, store_bit, dyn_word)) = flags {
            let restore = std::mem::replace(&mut self.cur_flags, entry_flags);
            if let Some(bit) = store_bit {
                self.or_flags_const(bit);
            }
            if let Some(w) = dyn_word {
                self.or_flags_word(w);
            }
            margs.push(self.materialize_flags());
            self.cur_flags = restore;
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

    pub(super) fn emit_slot_load(&mut self, obj: Value, slot_enc: Value) -> Value {
        let addr = self.emit_slot_addr(obj, slot_enc);
        let v = self.load_i64(addr, 0);
        self.eff(v, Eff::Read(HeapKind::Slot))
    }

    /// The slot address from a cache row's coordinate (`NightSlotEnc`: the
    /// byte offset from the base, bit 0 set when the base is the object's
    /// out-of-line `slots` vector). Two masks, the `slots` load, a select
    /// and an add.
    pub(super) fn emit_slot_addr(&mut self, obj: Value, slot_enc: Value) -> Value {
        let one = self.i32_const(1);
        let is_dynamic = self.binop(Operator::I32And, slot_enc, one, Type::I32);
        let mask = self.i32_const(!1);
        let off = self.binop(Operator::I32And, slot_enc, mask, Type::I32);
        self.emit_slot_addr_parts(obj, is_dynamic, off)
    }

    /// The slot address from a decoded coordinate: `is_dynamic` (0/1) and
    /// the byte offset from the base it selects.
    pub(super) fn emit_slot_addr_parts(
        &mut self,
        obj: Value,
        is_dynamic: Value,
        off: Value,
    ) -> Value {
        let slots_ptr = self.load_i32(obj, NATIVE_SLOTS_OFFSET);
        let slot_base = self.select(Type::I32, slots_ptr, obj, is_dynamic);
        self.binop(Operator::I32Add, slot_base, off, Type::I32)
    }

    /// Box a raw i32 as a nunbox Int32.
    pub(super) fn box_int32(&mut self, v: Value) -> Value {
        translate::box_int32(self, v)
    }

    /// Guard source 2 of the property lowerings (see DESIGN.md section 5.2):
    /// the per-site stamp-guarded fixed-slot read. No shape load, no cell,
    /// no generation stamp -- garbage never matches, because alloc paths
    /// zero the class word and stamps only ever write validated indices.
    ///
    /// The site carries a predicted layout key range `[k, k_hi]` and the
    /// fixed slot the field sits in. What has to be discharged before the
    /// baked slot offset may be used is: the receiver is an object, its
    /// stamped identity is in the range, and its SLOTS bit is set (identity
    /// alone does not license a positional read -- the bit's add-check
    /// history is what validates the offsets). How much of that is already
    /// proven by the lineage's ctx decides which of four shapes is emitted:
    ///
    /// ```text
    /// // cls fact in [k, k_hi] and cls_slots proven:
    ///     v = load  recv[16 + 8*slot]                  // no guard at all
    ///
    /// // cls fact in [k, k_hi], SLOTS not proven:
    ///     w = load32 recv[4]                           // the class word
    ///     if (w & WANT) == WANT { v = load recv[16 + 8*slot] }
    ///     else                  { side arm -> get IC, continue at next_pc }
    ///     // WANT = SLOTS, plus SHALLOW (and RANGES where the site has a
    ///     // range claim) when the numeric result wants a checkless load
    ///
    /// // no cls fact:
    ///     if !object(recv) goto miss                   // elided if obj-only
    ///     w = load32 recv[4]
    ///     hit = k == k_hi ? (w & (0xFFFF|SLOTS)) == (k|SLOTS)
    ///                     : (w & 0xFFFF) - k <=u (k_hi - k) && (w & SLOTS)
    ///     if hit  { v = load recv[16 + 8*slot] }
    ///     else    { miss: side arm -> get IC, continue at next_pc }
    /// ```
    ///
    /// The IC is the miss arm in every guarded shape, and it is the whole
    /// lowering when the site has no layout evidence at all -- see
    /// `emit_get_property` for the ladder that chooses between them.
    ///
    /// The result's type and representation come from the site's claim and
    /// from which stamp bits the guard proved:
    ///
    /// - numeric claim + proven SHALLOW: `push_typed_field` -- one int-tag
    ///   test, so the int arm carries an unboxed `I32` (plus the site's
    ///   interval where RANGES was in `WANT`) and the double arm an unboxed
    ///   `F64`. No other-type arm exists: SHALLOW is the proof there is
    ///   none.
    /// - numeric claim, SHALLOW not proven: `push_load_typed` -- the same
    ///   arms, but the mask is only arm-order evidence, so the ladder also
    ///   carries the other-type arm the guard leaves possible.
    /// - object claim (per-site read evidence, which the layout mask cannot
    ///   express): one `TAG_OBJECT` test, result object-only and `Boxed`.
    /// - no claim: `Boxed` with the bottom type.
    ///
    /// One record per site that would consume a durable class fact
    /// (`--dump-clsfact`). The fact-kill censuses report that a fact died;
    /// this reports whether anything wanted it. `have` names what the
    /// receiver actually carried:
    ///
    ///   none      -- no identity fact at all (killed, or never minted)
    ///   outside   -- an identity fact, but not inside this site's range
    ///   idonly    -- identity implied, SLOTS bit absent (guarded arm)
    ///   full      -- identity implied and SLOTS proven (checkless immediate)
    ///
    /// `src` is the receiver's slot provenance, which is what says whether a
    /// `kill_cls_facts` could ever have reached it: a fact on a durable slot
    /// (this / arg / local) survives across ops and is what a CallGc sweeps,
    /// while an operand with no slot never had a durable fact to lose.
    fn dump_cls_consumer(
        &self,
        pc: Pc,
        kind: &str,
        recv: &Operand,
        k: u32,
        k_hi: u32,
        cls_implied: bool,
    ) {
        if !self.opts.diagnostics.clsfact || self.mode != EmitMode::Code {
            return;
        }
        let have = if cls_implied && recv.cls_slots {
            "full"
        } else if cls_implied {
            "idonly"
        } else if recv.cls.is_some() {
            "outside"
        } else {
            "none"
        };
        let src = match recv.src {
            Some(SlotRef::This) => "this".to_string(),
            Some(SlotRef::Local(n)) => format!("local{n}"),
            Some(SlotRef::Arg(n)) => format!("arg{n}"),
            Some(SlotRef::GCell(n)) => format!("gcell{n}"),
            None => "stack".to_string(),
        };
        crate::diag_line!(
            "night: clsfact sid#{} pc {} lpc {} kind {kind} have {have} src {src} \
range {k}..{k_hi} track {:?} seg {} objonly {} recv v{}",
            self.source_id,
            self.evid_pc(pc),
            pc,
            self.cur_track,
            u32::from(self.cur_seg.is_some()),
            u32::from(is_object_only(&recv.ty)),
            recv.val.index(),
        );
    }

    /// Instrument-only interposer on a class-fact guard's not-an-object
    /// miss edge: tick bucket 0 and fall on into the real miss block.
    /// Returns `miss` itself when the census is off, so production codegen
    /// is untouched.
    fn guard_miss_tag_blk(&mut self, miss: Block, base: u32, pc: Pc) -> Block {
        if !self.guard_census_on() {
            return miss;
        }
        let saved = self.cur;
        let b = self.body.add_block();
        self.cur = b;
        // Deliberately the dyn form with a constant: the miss-why buckets
        // must not carry the track bump the other arms do, or bucket 0 would
        // land in another family's range.
        let kind = self.i32_const(base);
        self.emit_guard_census_dyn(kind, pc);
        self.body.set_terminator(
            b,
            Terminator::Br {
                target: BlockTarget {
                    block: miss,
                    args: vec![],
                },
            },
        );
        self.cur = saved;
        b
    }

    /// Instrument-only interposer on a class-fact guard's identity miss
    /// edge. Reads the bucket straight off the receiver's own class word
    /// `w`, which is the only place the answer lives: 1 = never stamped,
    /// 2 = the prediction named the wrong class, 3 = the right class with
    /// SLOTS clear, 4 = unreachable. Returns `miss` when the census is off.
    #[allow(clippy::too_many_arguments)]
    fn guard_miss_why_blk(
        &mut self,
        miss: Block,
        base: u32,
        w: Value,
        objptr: Value,
        k: u32,
        k_hi: u32,
        pc: Pc,
    ) -> Block {
        if !self.guard_census_on() {
            return miss;
        }
        let saved = self.cur;
        let b = self.body.add_block();
        self.cur = b;
        let m16 = self.i32_const(0xFFFF);
        let idx = self.binop(Operator::I32And, w, m16, Type::I32);
        let unstamped = self.unop(Operator::I32Eqz, idx, Type::I32);
        let kv = self.i32_const(k);
        let d = self.binop(Operator::I32Sub, idx, kv, Type::I32);
        let span = self.i32_const(k_hi - k);
        let in_range = self.binop(Operator::I32LeU, d, span, Type::I32);
        let sm = self.i32_const(CLASS_WORD_SLOTS);
        let sb = self.binop(Operator::I32And, w, sm, Type::I32);
        let z = self.i32_const(0);
        let slots = self.binop(Operator::I32Ne, sb, z, Type::I32);
        // in_range ? (slots ? 4 : 3) : 2, then 1 if the word is bare.
        let four = self.i32_const(4);
        let three = self.i32_const(3);
        let two = self.i32_const(2);
        let one = self.i32_const(1);
        let ok = self.select(Type::I32, four, three, slots);
        let inr = self.select(Type::I32, ok, two, in_range);
        let bucket = self.select(Type::I32, one, inr, unstamped);
        let basev = self.i32_const(base);
        let kind = self.binop(Operator::I32Add, basev, bucket, Type::I32);
        self.emit_guard_census_dyn(kind, pc);
        // Second tick, keyed on the RECEIVER rather than the site: the
        // number of distinct ids says whether the misses come from a
        // handful of long-lived objects or from fresh allocations.
        let rk = self.i32_const(if base == census::GET_MISS_WHY {
            census::GET_MISS_RECV
        } else {
            census::SET_MISS_RECV
        });
        self.emit_guard_census_dyn_id(rk, objptr);
        let ik = self.i32_const(if base == census::GET_MISS_WHY {
            census::GET_MISS_IDX
        } else {
            census::SET_MISS_IDX
        });
        self.emit_guard_census_dyn_id(ik, w);
        self.body.set_terminator(
            b,
            Terminator::Br {
                target: BlockTarget {
                    block: miss,
                    args: vec![],
                },
            },
        );
        self.cur = saved;
        b
    }

    /// Audit disciplines that keep "stamp implies plain data" true: only the
    /// site's evidenced name/slot is served (`PropSiteIn` slots come from
    /// validated rows); the identity compare is exact on the full idx half;
    /// and no proto-chain claim is implied anywhere.
    ///
    /// Per-op BBV: the arms carry different implications, so they are
    /// continuations -- the hit arm falls through refined (the driver's
    /// auto-continuation), the miss arm re-runs the property IC and
    /// continues at `next_pc` under the weaker result ctx via `side_arm`.
    pub(super) fn emit_class_fact_get(
        &mut self,
        pc: Pc,
        ps: &PropSiteIn,
        atom_id: u32,
    ) -> Result<(), String> {
        let k = ps.layout_id + 1;
        let k_hi = ps.hi_layout_id + 1;
        debug_assert!(k_hi <= crate::ids::LayoutKey::LIMIT);
        let next_pc = pc + JSOp::GetProp.len();
        let recv = self.pop()?;
        let recv_boxed = self.to_boxed(&recv);
        let recv_ptr = self.to_ptr(&recv);
        let typed = ps
            .claim
            .prims()
            .is_nonempty_subset_of(PRIM_INT32 | PRIM_DOUBLE);
        // The layout mask is the store-conformance claim and is numeric by
        // construction, so an object-valued field carries none and the
        // result would land as bottom. The per-site read evidence has an
        // object-only tier the layout mask cannot express; consult it for
        // the result typing only. One TAG_OBJECT test buys obj-only, which
        // is what lets a downstream receiver-tag test elide and kills the
        // dead string/number arms a bottom result keeps alive.
        let obj_claim = !typed && self.field_claim(pc).is_object();

        // A durable class fact contained in the site's range makes the
        // identity guard (and the object tag test) redundant, but the slot
        // immediate always demands the SLOTS bit: identity alone no longer
        // licenses a positional read -- the bit's add-check history is what
        // validates the baked offsets. A SLOTS-clear receiver falls to the
        // per-site IC, correct for any object of the right identity.
        let cls_implied = recv
            .cls
            .is_some_and(|(lo, hi)| u32::from(lo) >= k && u32::from(hi) <= k_hi);
        self.dump_cls_consumer(pc, "get", &recv, k, k_hi, cls_implied);
        if cls_implied && recv.cls_slots {
            // Proven-SLOTS receiver: the immediate is licensed with no
            // word load and no fork at all (value stores cannot clear the
            // bit -- the chokes are TYPES-only). This is what packs the
            // hot chain back together: re-test forks fragment a hot loop
            // into more, shorter contiguous runs and cost real instruction
            // cache, and machine block layout is not ours to fix
            // downstream.
            self.emit_guard_census(census::GET_L1A, pc);
            self.emit_rely_census(census::RELY_PROP_CLS, recv.prov);
            let boxed = self.load_i64(recv_ptr, FIXED_SLOTS_BASE + 8 * ps.slot);
            self.eff(boxed, Eff::Read(HeapKind::Slot));
            if typed && recv.cls_shallow {
                self.push_typed_field(boxed, ps.claim, None, next_pc);
            } else if typed {
                self.push_load_typed(boxed, ps.claim, next_pc, Prov::C_FIELD);
            } else if obj_claim {
                self.push_load_typed(boxed, Claim::OBJECT, next_pc, Prov::C_FIELD);
            } else {
                self.push_boxed(boxed, bottom_ty());
            }
            return Ok(());
        }
        if cls_implied {
            self.emit_rely_census(census::RELY_PROP_CLS, recv.prov);
            let w = self.load_i32(recv_ptr, OBJ_CLASS_IDX_OFFSET);
            self.eff(w, Eff::ReadBits(HeapKind::ClassWord));
            if typed && !recv.cls_shallow && ps.shallow_possible {
                // Two-bit dispatch, folded: SLOTS+TYPES -> checkless typed
                // immediate (fall-through); anything else -> the per-site
                // IC side arm. A SLOTS-only receiver could take a boxed
                // immediate instead, but a third arm per typed site
                // measurably bloats the hot unit and costs instruction
                // cache; the IC serves that small population correctly.
                // Three bits where the site has a range to consume: the
                // fold is the same and/compare against a wider immediate,
                // so the claim rides in free. Sites without a range keep
                // the two-bit test, which is what stops a cleared RANGES
                // from pushing unrelated receivers to the IC arm.
                let want = CLASS_WORD_SHALLOW
                    | CLASS_WORD_SLOTS
                    | if ps.range.is_some() {
                        CLASS_WORD_RANGES
                    } else {
                        0
                    };
                let bm = self.i32_const(want);
                let t = self.binop(Operator::I32And, w, bm, Type::I32);
                let both = self.binop(Operator::I32Eq, t, bm, Type::I32);
                let fast_blk = self.body.add_block();
                let ic_blk = self.body.add_block();
                self.cond_br(both, fast_blk, ic_blk);
                let recv2 = recv.clone();
                self.side_arm(ic_blk, next_pc, move |s| {
                    s.emit_guard_census(census::GET_L1B_MISS, pc);
                    s.emit_get_prop_ic_inline(&recv2, recv_boxed, atom_id, None);
                    s.stack.pop().expect("IC pushes its result")
                });
                self.cur = fast_blk;
                self.emit_guard_census(census::GET_L1B_HIT, pc);
                // The passed dispatch proved SHALLOW and SLOTS: durable
                // for the lineage (SLOTS survives value stores; both die
                // at CallGc, SLOTS also at inline set-IC emissions).
                self.refine_src(
                    &recv,
                    SlotCtx {
                        prims: Prims::EMPTY,
                        outside: true,
                        range: RangeBucket::Top,
                        cls: recv.cls,
                        cls_shallow: true,
                        cls_slots: true,
                        ta: None,
                        likely_cls: None,
                        src: None,
                        iv: None,
                        iv_grow: 0,
                        prov: recv.prov.or(Prov::C_FIELD),
                    },
                );
                let boxed = self.load_i64(recv_ptr, FIXED_SLOTS_BASE + 8 * ps.slot);
                self.eff(boxed, Eff::Read(HeapKind::Slot));
                let seed = ps.range;
                self.push_typed_field(boxed, ps.claim, seed, next_pc);
            } else {
                // SLOTS-guarded immediate (untyped, or TYPES proven by the
                // live fact). The miss arm keeps the full inline IC. A tiny
                // generic-helper arm in its place shrinks the hot unit
                // without moving the score, and loses outright wherever the
                // SLOTS-clear population is itself read-hot.
                let sm = self.i32_const(CLASS_WORD_SLOTS);
                let sb = self.binop(Operator::I32And, w, sm, Type::I32);
                let z = self.i32_const(0);
                let slots_ok = self.binop(Operator::I32Ne, sb, z, Type::I32);
                let hit_blk = self.body.add_block();
                let ic_blk = self.body.add_block();
                self.cond_br(slots_ok, hit_blk, ic_blk);
                let recv2 = recv.clone();
                self.side_arm(ic_blk, next_pc, move |s| {
                    s.emit_guard_census(census::GET_L1C_MISS, pc);
                    s.emit_get_prop_ic_inline(&recv2, recv_boxed, atom_id, None);
                    s.stack.pop().expect("IC pushes its result")
                });
                self.cur = hit_blk;
                self.emit_guard_census(census::GET_L1C_HIT, pc);
                // The passed bit test proved SLOTS: durable for the
                // lineage (survives value stores; dies at CallGc and
                // inline set-IC emissions).
                self.refine_src(
                    &recv,
                    SlotCtx {
                        prims: Prims::EMPTY,
                        outside: true,
                        range: RangeBucket::Top,
                        cls: recv.cls,
                        cls_shallow: false,
                        cls_slots: true,
                        ta: None,
                        likely_cls: None,
                        src: None,
                        iv: None,
                        iv_grow: 0,
                        prov: recv.prov.or(Prov::C_FIELD),
                    },
                );
                let boxed = self.load_i64(recv_ptr, FIXED_SLOTS_BASE + 8 * ps.slot);
                self.eff(boxed, Eff::Read(HeapKind::Slot));
                if typed && recv.cls_shallow {
                    self.push_typed_field(boxed, ps.claim, None, next_pc);
                } else if typed {
                    self.push_load_typed(boxed, ps.claim, next_pc, Prov::C_FIELD);
                } else if obj_claim {
                    self.push_load_typed(boxed, Claim::OBJECT, next_pc, Prov::C_FIELD);
                } else {
                    self.push_boxed(boxed, bottom_ty());
                }
            }
            return Ok(());
        }

        let miss_blk = self.body.add_block();
        // Precondition: an object receiver (elided under an object-only
        // ctx claim).
        if !is_object_only(&recv.ty) {
            let is_obj = self.tag_eq(recv_boxed, TAG_OBJECT as u32);
            let chk_blk = self.body.add_block();
            let tagfail = self.guard_miss_tag_blk(miss_blk, census::GET_MISS_WHY, pc);
            self.cond_br(is_obj, chk_blk, tagfail);
            self.cur = chk_blk;
        } else {
            self.emit_rely_census(census::RELY_PROP_OBJ, recv.prov);
        }
        // Identity fused with SLOTS: one load+and+cmp, the same cost as an
        // identity test alone, and a miss means exactly "the immediate arm
        // does not apply" (identity misses and SLOTS-clear receivers both
        // belong on the IC route).
        //
        // This arm must not require SHALLOW (or RANGES), the way the
        // durable-fact arm does to make the typed load checkless and
        // deliver its interval: a real population of receivers here
        // carries proven identity with SHALLOW cleared by the engine
        // choke, and requiring it would send them to GEN instead of a
        // passed guard plus one tag test. A SLOTS-only receiver with a
        // numeric value in the field is a live population this arm must
        // keep serving.
        let fold_bits = 0;
        let w = self.load_i32(recv_ptr, OBJ_CLASS_IDX_OFFSET);
        self.eff(w, Eff::ReadBits(HeapKind::ClassWord));
        // A keep arm guarded by the full word (identity|SLOTS|SHALLOW|RANGES)
        // delivering the field's interval, with the SLOTS-only guard as
        // the fall-through, buys nothing: both arms continue at the same
        // pc, whose ONE prediction is the meet, so the interval dies at
        // the join and the ranged store downstream keeps its choke. An
        // interval only one arm proves needs its own lineage, a version
        // split, not an arm.
        let eq = if k == k_hi {
            let m = self.i32_const(0xFFFF | CLASS_WORD_SLOTS | fold_bits);
            let t = self.binop(Operator::I32And, w, m, Type::I32);
            let kv = self.i32_const(k | CLASS_WORD_SLOTS | fold_bits);
            self.binop(Operator::I32Eq, t, kv, Type::I32)
        } else {
            let m16 = self.i32_const(0xFFFF);
            let idx = self.binop(Operator::I32And, w, m16, Type::I32);
            let kv = self.i32_const(k);
            let d = self.binop(Operator::I32Sub, idx, kv, Type::I32);
            let span = self.i32_const(k_hi - k);
            let in_range = self.binop(Operator::I32LeU, d, span, Type::I32);
            let sm = self.i32_const(CLASS_WORD_SLOTS | fold_bits);
            let sb = self.binop(Operator::I32And, w, sm, Type::I32);
            let slots_ok = self.binop(Operator::I32Eq, sb, sm, Type::I32);
            self.binop(Operator::I32And, in_range, slots_ok, Type::I32)
        };
        let hit_blk = self.body.add_block();
        let attr_blk =
            self.guard_miss_why_blk(miss_blk, census::GET_MISS_WHY, w, recv_ptr, k, k_hi, pc);
        self.cond_br(eq, hit_blk, attr_blk);

        // Miss arm: the property IC (it manages its own spills), continuing at
        // next_pc with the generic boxed result. It STEPS (side_arm): the
        // IC-hit lineage joining the fall-through's version at next_pc
        // would cost the fall-through its class fact for the rest of the
        // body, on every site, whether or not the miss ever runs.
        let recv2 = recv.clone();
        self.side_arm(miss_blk, next_pc, move |s| {
            s.emit_guard_census(census::GET_L1D_MISS, pc);
            s.emit_get_prop_ic_inline(&recv2, recv_boxed, atom_id, None);
            s.stack.pop().expect("IC pushes its result")
        });

        // Hit arm (fall-through): pure fixed-slot load. The passed guard
        // proves an object whose class idx is in the site's range: write
        // the durable fact back to the source slot (killed at
        // CallGc). The fused guard also proved SLOTS, but that is not a
        // durable fact -- later immediates re-test the bit themselves.
        self.cur = hit_blk;
        self.emit_guard_census(census::GET_L1D_HIT, pc);
        self.refine_src(
            &recv,
            SlotCtx {
                prims: Prims::EMPTY,
                outside: true,
                range: RangeBucket::Top,
                cls: Some((u16::try_from(k).unwrap(), u16::try_from(k_hi).unwrap())),
                cls_shallow: false,
                cls_slots: true,
                ta: None,
                likely_cls: None,
                src: None,
                iv: None,
                iv_grow: 0,
                prov: recv.prov.or(Prov::C_FIELD),
            },
        );
        let boxed = self.load_i64(recv_ptr, FIXED_SLOTS_BASE + 8 * ps.slot);
        self.eff(boxed, Eff::Read(HeapKind::Slot));
        if typed {
            // Identity+SLOTS only: the mask is arm-order evidence, and the
            // ladder carries the other-type arm the guard leaves possible.
            self.push_load_typed(boxed, ps.claim, next_pc, Prov::C_FIELD);
        } else {
            self.push_boxed(boxed, bottom_ty());
        }
        Ok(())
    }

    /// The typed-field result push under a proven-shallow word (a passed
    /// fullword/SHALLOW guard or a live proven-shallow fact): the field is
    /// number-proven, so no other-type arm exists. An int32-only mask is
    /// arm-order evidence, discharged by one int-tag test -- the int arm
    /// falls through exact-i32 (range I32 by construction), the double arm
    /// continues proven-F64 (reinterpret is exact: number and not int32
    /// means a double encoding). A mixed mask takes the tag-select f64
    /// unbox.
    ///
    /// `range` is the site's range claim, non-None only where the fold
    /// above also proved the RANGES bit. It rides out on the int arm's
    /// operand as an interval, which is the whole point of the dimension:
    /// downstream arithmetic elides its overflow ladders against it
    /// without a single check at this load.
    pub(super) fn push_typed_field(
        &mut self,
        boxed: Value,
        claim: Claim,
        range: Option<ValueRange>,
        next_pc: Pc,
    ) {
        let prims = claim.prims();
        if prims == PRIM_INT32 {
            let is_int = self.tag_eq(boxed, TAG_INT32 as u32);
            let int_blk = self.body.add_block();
            let dbl_blk = self.body.add_block();
            self.cond_br(is_int, int_blk, dbl_blk);
            self.side_arm(dbl_blk, next_pc, |s| {
                let f = s.unop(Operator::F64ReinterpretI64, boxed, Type::F64);
                Operand::plain(f, Repr::F64, prim_desc(PRIM_DOUBLE)).with_prov(Prov::C_FIELD)
            });
            self.cur = int_blk;
            let w = self.unop(Operator::I32WrapI64, boxed, Type::I32);
            let o = Operand::plain(w, Repr::I32, prim_desc(PRIM_INT32)).with_prov(Prov::C_FIELD);
            self.stack.push(match range {
                Some(r) => o.with_iv(opsem::iv_ok(r.lo, r.hi, false)),
                None => o,
            });
        } else if prims != PRIM_DOUBLE {
            // Mixed mask under the init-mask discipline: the checkless
            // numeric unbox below yields an F64 carrier with a mixed fact
            // -- which forfeits the exact-int32 facts the int32
            // arithmetic track needs. The typed-load ladder keeps the int
            // arm first and exactness intact; shallowness still saved the
            // class-word guard above.
            self.push_load_typed(boxed, claim, next_pc, Prov::C_FIELD);
        } else {
            let f = self.unbox_number_f64(boxed);
            let o = Operand::plain(f, Repr::F64, prim_desc(PRIM_INT32 | PRIM_DOUBLE))
                .with_prov(Prov::C_FIELD);
            self.stack.push(o);
        }
    }

    /// `GetProp`. The ladder, in the order the emitter tries it:
    ///
    /// ```text
    /// if the site (or the name) is known to hit an accessor
    ///     -> emit_accessor_prop        // getter call behind its own cell
    /// else if the site has layout evidence, or the receiver's live class
    ///         fact supplies one for this name
    ///     -> emit_class_fact_get       // stamp-guarded fixed-slot read,
    ///                                  // get IC on the miss arm
    /// else if the name is `length`
    ///     -> string / dense-array / arguments header loads, in one
    ///        diamond; the miss arm is emit_get_prop_ic_inline nested
    ///        in-version (so it merges rather than leaving)
    /// else if the name is `charCodeAt`/`charAt` and the engine fuse holds
    ///     -> the char-op arm, which elides the method lookup entirely
    /// else
    ///     -> emit_get_prop_ic_inline   // the site's own IC, standalone
    /// ```
    ///
    /// `gen_only` bodies skip the first two: the accessor call and the
    /// class-fact arm both leave the version through `side_arm`, and GEN-only
    /// exists to keep a near-cap body at one version per pc. The `length` and
    /// char-op arms are in-version diamonds, so they stay.
    /// Attach the site's advisory value class (`field_cls_sites`) to the
    /// just-pushed property result on the fall-through lineage -- the
    /// "likely this class, unchecked" ctx fact. Costs nothing here; the
    /// first use that needs the identity guards it (`layout_site_for`'s
    /// advisory tier). Never overrides a proven fact.
    pub(super) fn attach_likely_cls(&mut self, pc: Pc) {
        if self.gen_only {
            return;
        }
        let site = Site::new(self.source_id, self.evid_pc(pc));
        let Some(&(lo, hi)) = self.ctx.facts.field_cls_sites.get(&site) else {
            return;
        };
        let (Ok(lo), Ok(hi)) = (u16::try_from(lo.get()), u16::try_from(hi.get())) else {
            return;
        };
        if let Some(o) = self.stack.last_mut() {
            if o.cls.is_none() && o.likely_cls.is_none() && o.ty.outside {
                o.likely_cls = Some((lo, hi));
            }
        }
    }

    /// Which of the get-property forms a site took. Nothing else says
    /// this, and the forms differ in what they do to the operand stack, so
    /// a fact that dies inside one of them cannot be attributed without it.
    fn prop_form(&mut self, pc: Pc, form: &'static str) {
        self.op_form = Some(form);
        if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
            crate::diag_line!(
                "night: propform sid#{} pc {} form {form} track {:?}",
                self.source_id,
                self.evid_pc(pc),
                self.cur_track,
            );
        }
    }

    pub(super) fn emit_get_property(&mut self, pc: Pc, name: NameId) -> Result<(), String> {
        if !self.outline_generic() {
            let acc_hit = matches!(
                self.ctx
                    .facts
                    .accessor_sites
                    .get(&Site::new(self.source_id, Pc::new(self.evid_pc(pc).get()))),
                Some(&(_, 0))
            ) || self.ctx.facts.accessor_names.contains(&name);
            if acc_hit {
                let atom_id = self.atoms.intern(name);
                self.prop_form(pc, "accessor");
                return self.emit_accessor_prop(pc, atom_id, false);
            }
            let site = self
                .ctx
                .prop_sites_in
                .get(&Site::new(self.source_id, self.evid_pc(pc)))
                .cloned()
                .or_else(|| {
                    let recv = self.stack.last()?;
                    self.layout_site_for(recv, name)
                });
            if let Some(ps) = site {
                let atom_id = self.atoms.intern(name);
                self.prop_form(pc, "clsfact");
                return self.emit_class_fact_get(pc, &ps, atom_id);
            }
            if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
                let recv = self.stack.last().cloned();
                crate::diag_line!(
                    "night: bbv getprop-nosite sid#{} pc {} in_table {} recv_cls {:?} likely {:?} outside {:?} track {:?}",
                    self.source_id,
                    self.evid_pc(pc),
                    self.ctx.prop_sites_in.contains_key(&Site::new(self.source_id, self.evid_pc(pc))),
                    recv.as_ref().map(|o| o.cls),
                    recv.as_ref().map(|o| o.likely_cls),
                    recv.as_ref().map(|o| o.ty.outside),
                    self.cur_track,
                );
            }
        }
        if name == self.atoms.well_known.length && !self.outline_generic() {
            self.prop_form(pc, "length-diamond");
            let recv = self.pop()?;
            let recv_boxed = self.to_boxed(&recv);
            let recv_ptr = self.to_ptr(&recv);
            let (reprs, vals) = self.diamond_snapshot();
            let slow_blk = self.body.add_block();
            let merge = self.body.add_block();
            let op_params = self.diamond_params(merge, &reprs);
            let res_param = self.body.add_blockparam(merge, Type::I64);
            // The nested property IC below threads a per-arm flags word out of
            // its merge; this outer diamond must thread it through its
            // merge too, or the fast arms' paths would reference a value
            // they never dominate.
            let outer_fp = self
                .flags_threading()
                .then(|| self.body.add_blockparam(merge, Type::I32));

            // String receiver: len always boxes Int32 (< 2^30).
            let str_blk = self.body.add_block();
            let chk_obj = self.body.add_block();
            let is_str = self.tag_eq(recv_boxed, TAG_STRING as u32);
            self.cond_br(is_str, str_blk, chk_obj);
            self.cur = str_blk;
            let strptr = recv_ptr;
            let slen = self.load_i32(strptr, STRING_LENGTH_OFFSET);
            self.eff(slen, Eff::ReadBits(HeapKind::StringData));
            let sboxed = self.box_int32(slen);
            let mut sargs = vals.clone();
            sargs.push(sboxed);
            if outer_fp.is_some() {
                sargs.push(self.materialize_flags());
            }
            self.body.set_terminator(
                self.cur,
                Terminator::Br {
                    target: BlockTarget {
                        block: merge,
                        args: sargs,
                    },
                },
            );

            // Array receiver: clasp identity + ObjectElements length word.
            self.cur = chk_obj;
            let is_obj = self.tag_eq(recv_boxed, TAG_OBJECT as u32);
            let obj_blk = self.body.add_block();
            self.cond_br(is_obj, obj_blk, slow_blk);
            self.cur = obj_blk;
            let objptr = recv_ptr;
            let shape = self.load_i32(objptr, SHAPE_OFFSET);
            self.eff(shape, Eff::Read(HeapKind::Shape));
            let base = self.load_i32(shape, SHAPE_BASESHAPE_OFFSET);
            self.eff(base, Eff::Read(HeapKind::Shape));
            let clasp = self.load_i32(base, BASESHAPE_CLASP_OFFSET);
            self.eff(clasp, Eff::Read(HeapKind::Shape));
            let aslot = self.i32_const(self.helpers.array_class_slot);
            let arr_class = self.load_i32(aslot, 0);
            let is_arr = self.binop(Operator::I32Eq, clasp, arr_class, Type::I32);
            let arr_blk = self.body.add_block();
            let chk_args = self.body.add_block();
            self.cond_br(is_arr, arr_blk, chk_args);
            self.cur = arr_blk;
            let elements = self.load_i32(objptr, OBJ_ELEMENTS_OFFSET);
            self.eff(elements, Eff::Read(HeapKind::ElementsHeader));
            let four = self.i32_const(4);
            let len_addr = self.binop(Operator::I32Sub, elements, four, Type::I32);
            let alen = self.load_i32(len_addr, 0);
            let zero = self.i32_const(0);
            let in_range = self.binop(Operator::I32GeS, alen, zero, Type::I32);
            let fit_blk = self.body.add_block();
            self.cond_br(in_range, fit_blk, slow_blk);
            self.cur = fit_blk;
            let aboxed = self.box_int32(alen);
            let mut aargs = vals.clone();
            aargs.push(aboxed);
            if outer_fp.is_some() {
                aargs.push(self.materialize_flags());
            }
            self.body.set_terminator(
                self.cur,
                Terminator::Br {
                    target: BlockTarget {
                        block: merge,
                        args: aargs,
                    },
                },
            );

            // Arguments receiver: packed length in fixed slot 0 unless
            // overridden.
            self.cur = chk_args;
            let acbase = self.i32_const(self.helpers.args_class_base);
            let mapped_class = self.load_i32(acbase, 0);
            let unmapped_class = self.load_i32(acbase, 4);
            let is_mapped = self.binop(Operator::I32Eq, clasp, mapped_class, Type::I32);
            let is_unmapped = self.binop(Operator::I32Eq, clasp, unmapped_class, Type::I32);
            let is_args = self.binop(Operator::I32Or, is_mapped, is_unmapped, Type::I32);
            let args_blk = self.body.add_block();
            self.cond_br(is_args, args_blk, slow_blk);
            self.cur = args_blk;
            let packed = self.load_i32(objptr, FIXED_SLOTS_BASE);
            let one = self.i32_const(1);
            let overridden = self.binop(Operator::I32And, packed, one, Type::I32);
            let argc_blk = self.body.add_block();
            self.cond_br(overridden, slow_blk, argc_blk);
            self.cur = argc_blk;
            let five = self.i32_const(5);
            let argc = self.binop(Operator::I32ShrU, packed, five, Type::I32);
            let argc_boxed = self.box_int32(argc);
            let mut gargs = vals.clone();
            gargs.push(argc_boxed);
            if outer_fp.is_some() {
                gargs.push(self.materialize_flags());
            }
            self.body.set_terminator(
                self.cur,
                Terminator::Br {
                    target: BlockTarget {
                        block: merge,
                        args: gargs,
                    },
                },
            );

            // Slow arm: the property IC as a side continuation. Merging it
            // back in-version would put its miss helper's track step on
            // every path through the merge, leaving an array `.length`
            // read in a loop on Dirty every iteration even though the fast
            // arm ran every time.
            let atom_id = self.atoms.intern(name);
            let recv2 = Operand::plain(recv_boxed, Repr::Boxed, bottom_ty());
            let next_pc = pc + JSOp::GetProp.len();
            let mask = self.field_claim(pc);
            self.side_arm_keep(slow_blk, next_pc, move |s| {
                s.emit_get_prop_ic_inline(&recv2, recv_boxed, atom_id, Some((next_pc.get(), mask)));
                s.stack.pop().expect("IC pushes its result")
            });
            self.cur = merge;
            self.diamond_rebind(&op_params);
            for (i, &rr) in reprs.iter().enumerate() {
                self.stack[i].repr = rr;
            }
            if let Some(fp) = outer_fp {
                self.cur_flags = FlagsAcc::Dyn(fp, 0);
            }
            self.push_boxed(res_param, bottom_ty());
            return Ok(());
        }
        // String char-op method read: fuse-intact + string receiver ->
        // the startup-cached original native's bits, lookup elided.
        let is_ccat_name = name == self.atoms.well_known.char_code_at;
        let is_cat_name = name == self.atoms.well_known.char_at;
        if is_ccat_name || is_cat_name {
            let recv_ty = self.stack.last().map(|o| o.ty).unwrap_or_else(bottom_ty);
            if !is_object_only(&recv_ty) {
                let cell_addr = if is_ccat_name {
                    self.helpers.str_ccat_cell
                } else {
                    self.helpers.str_cat_cell
                };
                let recv = self.pop()?;
                let recv_boxed = self.to_boxed(&recv);
                let (reprs, vals) = self.diamond_snapshot();
                let slow_blk = self.body.add_block();
                let merge = self.body.add_block();
                let op_params = self.diamond_params(merge, &reprs);
                let res_param = self.body.add_blockparam(merge, Type::I64);
                let outer_fp = self
                    .flags_threading()
                    .then(|| self.body.add_blockparam(merge, Type::I32));

                let is_str = self.tag_eq(recv_boxed, TAG_STRING as u32);
                let addr_slot = self.i32_const(self.helpers.str_fuse_addr_slot);
                let fuse_addr = self.load_i32(addr_slot, 0);
                let fuse_word = self.load_i32(fuse_addr, 0);
                let intact = self.unop(Operator::I32Eqz, fuse_word, Type::I32);
                let cell = self.i32_const(cell_addr);
                let bits = self.load_i64(cell, 0);
                let zero64 = self.boxed_const(0);
                let armed = self.binop(Operator::I64Ne, bits, zero64, Type::I32);
                let fi = self.binop(Operator::I32And, is_str, intact, Type::I32);
                let all = self.binop(Operator::I32And, fi, armed, Type::I32);
                let mut hit_args = vals.clone();
                hit_args.push(bits);
                if outer_fp.is_some() {
                    hit_args.push(self.materialize_flags());
                }
                self.body.set_terminator(
                    self.cur,
                    Terminator::CondBr {
                        cond: all,
                        if_true: BlockTarget {
                            block: merge,
                            args: hit_args,
                        },
                        if_false: BlockTarget {
                            block: slow_blk,
                            args: vec![],
                        },
                    },
                );
                // The method-lookup slow arm as a side continuation (the
                // `length` diamond's rule: merging it back joined the IC
                // miss helper's stepped state into the fused arm's path).
                let atom_id = self.atoms.intern(name);
                let recv2 = Operand::plain(recv_boxed, Repr::Boxed, bottom_ty());
                let next_pc = pc + JSOp::GetProp.len();
                let mask = self.field_claim(pc);
                self.side_arm_keep(slow_blk, next_pc, move |s| {
                    s.emit_get_prop_ic_inline(
                        &recv2,
                        recv_boxed,
                        atom_id,
                        Some((next_pc.get(), mask)),
                    );
                    s.stack.pop().expect("IC pushes its result")
                });
                self.cur = merge;
                self.diamond_rebind(&op_params);
                for (i, &rr) in reprs.iter().enumerate() {
                    self.stack[i].repr = rr;
                }
                if let Some(fp) = outer_fp {
                    self.cur_flags = FlagsAcc::Dyn(fp, 0);
                }
                self.push_boxed(res_param, bottom_ty());
                return Ok(());
            }
        }
        self.prop_form(pc, "ic-inline");
        let recv = self.pop()?;
        let recv_boxed = self.to_boxed(&recv);
        let atom_id = self.atoms.intern(name);
        let next_pc = pc + JSOp::GetProp.len();
        let mask = self.field_claim(pc);
        self.emit_get_prop_ic_inline(&recv, recv_boxed, atom_id, Some((next_pc.get(), mask)));
        Ok(())
    }

    /// The per-site likely value mask of a property read (`field_sites`,
    /// merged into `likely_elems` at plumbing time -- one op per pc).
    /// Absent = no numeric claim at this site, which is a claim of its own:
    /// the typed-load ladder then emits NO tag test at all.
    pub(super) fn field_claim(&self, pc: Pc) -> Claim {
        self.ctx
            .likely_elems
            .get(&Site::new(self.source_id, self.evid_pc(pc)))
            .copied()
            .unwrap_or(Claim::NONE)
    }

    /// The accessor-call arm at a likelier-classified accessor property
    /// site: probe the global (shape, atom^kind) accessor cache (primed
    /// by the generic get/set miss helpers, GC-zeroed), verify the
    /// receiver shape, the atom/kind, and the holder's live shape (an
    /// accessor redefinition reshapes the holder), then run the accessor
    /// as an ordinary call -- `emit_call_generic` re-classifies the cached
    /// callee and its likely-direct arm guards funcidx against the
    /// predicted target, so a mispredicted or repurposed entry only costs
    /// the fallback, never correctness. The probe miss rides a side arm
    /// through the ordinary property IC (the pre-arm status quo).
    pub(super) fn emit_accessor_prop(
        &mut self,
        pc: Pc,
        atom_id: u32,
        is_set: bool,
    ) -> Result<(), String> {
        use super::translate::{
            ACCESSOR_ATOM_KIND, ACCESSOR_CACHE_ENTRY_BYTES, ACCESSOR_CACHE_SIZE, ACCESSOR_CALLEE,
            ACCESSOR_HOLDER_PTR, ACCESSOR_HOLDER_SHAPE, ACCESSOR_RECV_SHAPE,
        };
        let next_pc = pc + self.cur_op.expect("accessor site has an op").len();
        let val = if is_set { Some(self.pop()?) } else { None };
        let recv = self.pop()?;
        let recv_boxed = self.to_boxed(&recv);
        let val_boxed = val.as_ref().map(|v| self.to_boxed(v));
        if is_set && !val.as_ref().is_some_and(store_value_numeric) {
            self.kill_shallow_facts();
        }
        let miss_blk = self.body.add_block();
        if !is_object_only(&recv.ty) {
            let is_obj = self.tag_eq(recv_boxed, TAG_OBJECT as u32);
            let chk = self.body.add_block();
            self.cond_br(is_obj, chk, miss_blk);
            self.cur = chk;
        } else {
            self.emit_rely_census(census::RELY_PROP_OBJ, recv.prov);
        }
        let objptr = self.to_ptr(&recv);
        let shape = self.load_i32(objptr, SHAPE_OFFSET);
        self.eff(shape, Eff::Read(HeapKind::Shape));
        let ak = (atom_id << 1) | u32::from(is_set);
        let three = self.i32_const(3);
        let sh = self.binop(Operator::I32ShrU, shape, three, Type::I32);
        let k1 = self.i32_const(2654435761);
        let h1 = self.binop(Operator::I32Mul, sh, k1, Type::I32);
        let k2 = self.i32_const(ak.wrapping_mul(0x9e37_79b9));
        let h = self.binop(Operator::I32Xor, h1, k2, Type::I32);
        let mask = self.i32_const(ACCESSOR_CACHE_SIZE - 1);
        let idx = self.binop(Operator::I32And, h, mask, Type::I32);
        let stride = self.i32_const(ACCESSOR_CACHE_ENTRY_BYTES);
        let off = self.binop(Operator::I32Mul, idx, stride, Type::I32);
        let base = self.i32_const(self.helpers.accessor_cache_base);
        let entry = self.binop(Operator::I32Add, base, off, Type::I32);
        let e_shape = self.load_i32(entry, ACCESSOR_RECV_SHAPE);
        self.eff(e_shape, Eff::Read(HeapKind::EngineTable));
        let e_ak = self.load_i32(entry, ACCESSOR_ATOM_KIND);
        let m1 = self.binop(Operator::I32Eq, e_shape, shape, Type::I32);
        let akv = self.i32_const(ak);
        let m2 = self.binop(Operator::I32Eq, e_ak, akv, Type::I32);
        let m12 = self.binop(Operator::I32And, m1, m2, Type::I32);
        let hold_blk = self.body.add_block();
        self.cond_br(m12, hold_blk, miss_blk);
        // A matched entry is primed (a live shape word is never 0), so the
        // holder pointer is non-null and its shape load is safe here.
        self.cur = hold_blk;
        let hp = self.load_i32(entry, ACCESSOR_HOLDER_PTR);
        let hs = self.load_i32(entry, ACCESSOR_HOLDER_SHAPE);
        let live = self.load_i32(hp, SHAPE_OFFSET);
        self.eff(live, Eff::Read(HeapKind::Shape));
        let m3 = self.binop(Operator::I32Eq, live, hs, Type::I32);
        let call_blk = self.body.add_block();
        self.cond_br(m3, call_blk, miss_blk);
        {
            let recv2 = recv.clone();
            let vinfo = val.as_ref().map(|v| (v.ty, v.range));
            let val_is_num = val.as_ref().is_some_and(store_value_numeric);
            let elide_barrier = val.as_ref().is_some_and(|v| is_non_gc(&v.ty));
            let range_act = val.as_ref().map_or(RangeAct::Nothing, |v| {
                let name = self.atoms.emitted_name(atom_id);
                self.store_range_act(&recv, name, v)
            });
            if val.is_none() {
                // GET miss: a plain-data receiver behind a name that is
                // accessor-classified elsewhere in the bundle takes this
                // arm on EVERY read (the cell never matches it), so it
                // keeps the track with the standalone-IC form -- hits and
                // clean misses rejoin, only the real miss helper leaves as
                // its own Dirty lineage (the `length` lowering's rule).
                let mask = self.field_claim(pc);
                self.side_arm_keep(miss_blk, next_pc, move |s| {
                    s.emit_get_prop_ic_inline(
                        &recv2,
                        recv_boxed,
                        atom_id,
                        Some((next_pc.get(), mask)),
                    );
                    s.stack.pop().expect("the get result stays on the stack")
                });
            } else {
                self.side_arm(miss_blk, next_pc, move |s| {
                    if let (Some(vb), Some((vty, vrange))) = (val_boxed, vinfo) {
                        s.push_ranged(vb, Repr::Boxed, vty, vrange);
                        s.emit_set_prop_ic_inline(
                            &recv2,
                            recv_boxed,
                            vb,
                            elide_barrier,
                            val_is_num,
                            atom_id,
                            None,
                            true,
                            None,
                            range_act,
                        );
                        s.stack.pop().expect("the stored value stays on the stack")
                    } else {
                        s.emit_get_prop_ic_inline(&recv2, recv_boxed, atom_id, None);
                        s.stack.pop().expect("the get result stays on the stack")
                    }
                });
            }
        }
        self.cur = call_blk;
        let callee_bits = self.load_i64(entry, ACCESSOR_CALLEE);
        self.eff(callee_bits, Eff::Read(HeapKind::EngineTable));
        self.push_boxed(callee_bits, bottom_ty());
        self.stack.push(recv);
        if let Some(v) = val.clone() {
            self.stack.push(v);
        }
        let argc: u16 = u16::from(is_set);
        // Setter calls fork on effects like every other call: `set_result`
        // makes every continuation -- the merge and the clean/keep arms --
        // deliver the STORED VALUE (off its reloaded spill slot, GC-safe)
        // as the op result, without which setter continuations would be
        // fork-free and therefore unconditionally Dirty, even when the
        // setter provably kept stamps intact.
        self.emit_call_generic_to(pc, argc, usize::from(argc) + 2, true, None, is_set)?;
        Ok(())
    }

    /// GetProp IC: N-way guarded slot read inline (mono way + mega-get
    /// probe), only a miss calling `night_runtime_get_prop_ic_miss`.
    /// `slow_cont`: arm-continuation mode (arms with different
    /// implications are continuations). Some((next_pc, mask))
    /// sends the miss through spill/call/reload and on to next_pc's weaker
    /// version -- the loop's fast spine stays call-free, which is what
    /// admits LICM -- and orders the result's typed-load ladder by the
    /// site's likely value mask. None keeps the in-version merge (nested
    /// tail uses).
    /// The per-site property get IC: guard source 3, and the miss arm of
    /// every guard source above it.
    ///
    /// A way chain, two inline arms and a call. Everything past the holder
    /// tail is the same code at every fact-free site, so it lives once in
    /// `night_ic_get` (`translate::build_ic_get_helper`) rather than at each
    /// of the tens of thousands of them. What stays inline stays because a
    /// profile said so, not because it is cheap to emit: see
    /// `emit_get_ic_inline_arms`.
    ///
    /// ```text
    /// if !object(recv) goto probe                  // elided if obj-only
    /// shape = load32 recv[0]
    /// if shape == way0.recvShape goto hit(way0)    // one compare per way
    /// ...
    /// if shape == wayN.recvShape goto hit(wayN)
    /// goto probe
    /// hit(way):
    /// if way.ownOff != 0 { v = load recv[way.ownOff]; goto merge }
    /// base = way.holderPtr == 0 ? recv : way.holderPtr   // holder tail
    /// if load32 base[0] != way.holderShape goto probe
    /// v = slot_load(base, way.slotEnc); goto merge
    ///
    /// probe: v = night_ic_get(recv, atom, way)     // the ways again, then
    ///        if v != magic goto merge              //   the mega hash + tail
    ///
    /// slow: v = get_prop_ic_miss(cx, top, recv, atom, cache)
    /// ```
    ///
    /// `slow_cont` decides what the slow arm is. `Some((next_pc, mask))`
    /// makes this a standalone site: the miss leaves the version as a
    /// second-chance continuation at `next_pc`, the merge proves an object
    /// receiver back into the source slot, and the result takes the
    /// typed-load ladder for `mask`. `None` makes it a nested tail under an
    /// outer diamond: the miss merges back in-version and the result is
    /// boxed and untyped.
    ///
    /// The miss helper is a full may-GC call (it can run an arbitrary
    /// getter), so a nested site threads its own flags word out of the merge
    /// -- otherwise its saturated accumulator would leak onto the pure hit
    /// paths and every accessor called in a loop would read as a heap writer.
    pub(super) fn emit_get_prop_ic_inline(
        &mut self,
        recv: &Operand,
        recv_boxed: Value,
        atom_id: u32,
        slow_cont: Option<(u32, Claim)>,
    ) {
        // `Code`-only allocation (see emit_instanceof's cell note).
        let cache_idx = if self.mode == EmitMode::Code {
            self.atoms.next_prop_cache()
        } else {
            0
        };
        let atom_v = self.i32_const(atom_id);
        let cache_v = self.i32_const(cache_idx);

        let (reprs, vals) = self.diamond_snapshot();
        let top_off = self.operand_base + 8 * u32::try_from(reprs.len()).unwrap();

        let slow_blk = self.body.add_block();
        let merge = self.body.add_block();
        let op_params = self.diamond_params(merge, &reprs);
        let res_param = self.body.add_blockparam(merge, Type::I64);
        let ok_param = self.body.add_blockparam(merge, Type::I32);
        // The set-IC None-case rule, get side: the miss helper is
        // a full CallGc (it may run an arbitrary getter), and its leaked
        // saturated accumulator is path-shared -- without a per-arm flags
        // param every nested-tail get site turns the body's returned word
        // into all on the pure hit paths too, so a plain accessor called in
        // a loop reads as a heap writer every iteration.
        let entry_flags = self.cur_flags;
        // With `slow_cont` the miss helper's second chance leaves as its
        // own lineage and never reaches this merge, so the param is safe in
        // both shapes (and necessary: without it the fall-through would
        // have to claim every arm's worst static word, FLAG_STAMPS
        // included).
        let merge_flags_param = self
            .flags_threading()
            .then(|| self.body.add_blockparam(merge, Type::I32));

        // Split by measurement, not by taste. Everything past the
        // monomorphic fixed-slot arm -- the holder tail, the poly sentinel,
        // the mega hash and its duplicate hit tail -- is the same code at
        // every fact-free site and rarely executed, so it lives in
        // `night_ic_get`, emitted once per module and reached by a direct
        // call. The mono arm stays inline: it is the mono arm's population
        // that really does need an inline fast path, the case the default
        // backs off from.
        // `night_ic_get` re-tests the tag and the way, which is dead work on
        // a path that only runs when an inline arm already failed.
        //
        // On the GEN rung there are no inline arms at all: a body that fell
        // to GEN has no facts to speculate on and is there because it was
        // too big to refine, so it is exactly the body that should pay one
        // call instead of a guard ladder per site.
        let way_base = self.i32_const(IC_WAY_ADDR_PLACEHOLDER);
        self.prop_ic_patches
            .push((way_base, cache_idx * INLINE_IC_STRIDE));
        // Out-lining the mono arm and holder tail for every site (they
        // already live in `night_ic_get`) loses even with class-fact and
        // claims coverage in: the inline mono fast path is load-bearing
        // regardless of how much the fact-free population shrinks, and
        // the icache savings do not buy it back even on icache-bound
        // benchmarks.
        let probe_blk = if self.outline_generic() {
            self.cur
        } else {
            let probe_blk = self.body.add_block();
            self.emit_get_ic_inline_arms(
                recv,
                recv_boxed,
                way_base,
                cache_idx * INLINE_IC_STRIDE,
                probe_blk,
                merge,
                &vals,
                merge_flags_param,
                entry_flags,
            );
            probe_blk
        };

        self.cur = probe_blk;
        self.emit_guard_census(census::GET_IC_PROBE, self.cur_pc);
        let res = self.call_i64(self.helpers.ic_get_poly, &[recv_boxed, atom_v, way_base]);
        let is_miss = self.tag_eq(res, TAG_MAGIC as u32);
        let mut hit_args = vals.clone();
        hit_args.push(res);
        let one = self.i32_const(1);
        hit_args.push(one);
        if merge_flags_param.is_some() {
            hit_args.push(self.materialize_flags());
        }
        self.body.set_terminator(
            self.cur,
            Terminator::CondBr {
                cond: is_miss,
                if_true: BlockTarget {
                    block: slow_blk,
                    args: vec![],
                },
                if_false: BlockTarget {
                    block: merge,
                    args: hit_args,
                },
            },
        );

        self.cur = slow_blk;
        self.emit_guard_census(census::GET_IC_MISS, self.cur_pc);

        let arm_st = self.arm_state();
        let n = self.spill_all();
        let top = self.add_offset(self.vp, top_off);
        let getmiss = self.helpers.get_prop_ic_miss;
        let ok = self.call_i32(getmiss, &[self.cx, top, recv_boxed, atom_v, cache_v]);
        let slow_res = self.load_i64(self.vp, top_off);
        match slow_cont {
            Some((next_pc, _)) => {
                self.branch_on_err(ok);
                self.miss_second_chance(ok, n, Pc::new(next_pc), arm_st, |s| {
                    s.push_boxed(slow_res, bottom_ty());
                });
            }
            None => {
                let mut margs = self.diamond_slow_args(&reprs);
                margs.push(slow_res);
                margs.push(ok);
                if merge_flags_param.is_some() {
                    // The miss helper is a full CallGc: the leaked
                    // saturated state is this arm's honest word.
                    margs.push(self.materialize_flags());
                }
                self.body.set_terminator(
                    slow_blk,
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
        if let Some(fp) = merge_flags_param {
            self.cur_flags = FlagsAcc::Dyn(fp, 0);
        }
        // Standalone site (the slow arm already left as a continuation):
        // every merge predecessor passed the object-receiver test, so the
        // proof writes back; then the typed-load test on the hit-arm
        // result, ordered by the site's `field_sites` mask -- a site with
        // no numeric claim emits no test (the hard-coded int32 default
        // this replaced was wrong most of the time).
        // Nested tail uses (slow_cont None) merge the generic helper back
        // in-version: no proof, boxed result.
        match slow_cont {
            Some((next_pc, mask)) => {
                self.refine_src(recv, OBJ_ONLY_SLOT);
                self.push_load_typed(res_param, mask, Pc::new(next_pc), Prov::C_FIELD)
            }
            None => self.push_boxed(res_param, bottom_ty()),
        }
    }

    /// The inline arms of a fact-free property read: the object tag test,
    /// the way chain (one shape compare per way, `INLINE_IC_WAYS` of them),
    /// and the hit block every way shares -- the matched way's address is
    /// its block parameter -- holding the own-fixed-slot fast arm and the
    /// holder tail. Every other arm lives in `night_ic_get`; these are here
    /// because measurement said so (out-of-lining either the mono arm or
    /// the holder tail costs real throughput on prototype-method-heavy
    /// code).
    /// Falls through to `probe_blk` on every miss.
    #[allow(clippy::too_many_arguments)]
    fn emit_get_ic_inline_arms(
        &mut self,
        recv: &Operand,
        recv_boxed: Value,
        way_base: Value,
        way_off: u32,
        probe_blk: Block,
        merge: Block,
        vals: &[Value],
        merge_flags_param: Option<Value>,
        entry_flags: FlagsAcc,
    ) {
        let recv_obj = if is_object_only(&recv.ty) {
            self.emit_rely_census(census::RELY_PROP_OBJ, recv.prov);
            self.i32_const(1)
        } else {
            self.tag_eq(recv_boxed, TAG_OBJECT as u32)
        };
        let chain = self.body.add_block();
        self.cond_br(recv_obj, chain, probe_blk);
        self.cur = chain;
        let objptr = self.to_ptr(recv);
        let shape = self.load_i32(objptr, SHAPE_OFFSET);
        self.eff(shape, Eff::Read(HeapKind::Shape));
        let hit_blk = self.body.add_block();
        let way = self.body.add_blockparam(hit_blk, Type::I32);
        let census_on = self.opts.instrument.guards && self.mode == EmitMode::Code;
        let chain_end = if census_on {
            self.body.add_block()
        } else {
            probe_blk
        };
        for w in 0..INLINE_IC_WAYS {
            let wb = if w == 0 {
                way_base
            } else {
                let v = self.i32_const(IC_WAY_ADDR_PLACEHOLDER);
                self.prop_ic_patches
                    .push((v, way_off + w * INLINE_IC_WAY_BYTES));
                v
            };
            let wshape = self.load_i32(wb, IC_WAY_RECVSHAPE);
            self.eff(wshape, Eff::Read(HeapKind::EngineTable));
            let m = self.binop(Operator::I32Eq, shape, wshape, Type::I32);
            let next = if w + 1 < INLINE_IC_WAYS {
                self.body.add_block()
            } else {
                chain_end
            };
            self.body.set_terminator(
                self.cur,
                Terminator::CondBr {
                    cond: m,
                    if_true: BlockTarget {
                        block: hit_blk,
                        args: vec![wb],
                    },
                    if_false: BlockTarget {
                        block: next,
                        args: vec![],
                    },
                },
            );
            self.cur = next;
        }
        if census_on {
            let k = self.i32_const(census::GET_IC_PROBE_SHAPE);
            let site = self.i32_const((self.evid_pc(self.cur_pc).get() & 0xffff) << 16);
            let three = self.i32_const(3);
            let sh3 = self.binop(Operator::I32ShrU, shape, three, Type::I32);
            let m16 = self.i32_const(0xffff);
            let shk = self.binop(Operator::I32And, sh3, m16, Type::I32);
            let id = self.binop(Operator::I32Or, site, shk, Type::I32);
            self.emit_guard_census_dyn_id(k, id);
            let kf = self.i32_const(census::GET_IC_PROBE_SHAPE_FLAGS);
            let sflags = self.load_i32(shape, SHAPE_IMMUTABLE_FLAGS_OFFSET);
            self.emit_guard_census_dyn_id(kf, sflags);
            self.body.set_terminator(
                self.cur,
                Terminator::Br {
                    target: BlockTarget {
                        block: probe_blk,
                        args: vec![],
                    },
                },
            );
        }

        self.cur = hit_blk;
        // Fast way: the pre-decoded own fixed-slot byte offset.
        let moff = self.load_i32(way, IC_WAY_MONO_OFF);
        let zero = self.i32_const(0);
        let is_fast = self.binop(Operator::I32Ne, moff, zero, Type::I32);
        let fastw_blk = self.body.add_block();
        let tail_blk = self.body.add_block();
        self.cond_br(is_fast, fastw_blk, tail_blk);
        self.cur = fastw_blk;
        self.emit_guard_census(census::GET_IC_W0, self.cur_pc);
        let addr = self.binop(Operator::I32Add, objptr, moff, Type::I32);
        let result = self.load_i64(addr, 0);
        let flags = merge_flags_param.map(|_| (entry_flags, None, None));
        self.ic_arm_br(merge, vals, &[result], flags);

        // Holder tail: the way's cached holder and its shape. This is hot
        // (a prototype method read takes this arm), so it stays inline
        // even though it is the same code at every site; the mega copy
        // lives once in `night_ic_get` with the rest of the poly path.
        self.cur = tail_blk;
        let hp = self.load_i32(way, IC_WAY_HOLDERPTR);
        let chs = self.load_i32(way, IC_WAY_HOLDERPTR + 4);
        let slot_enc = self.load_i32(way, IC_WAY_HOLDERPTR + 8);
        let zero = self.i32_const(0);
        let hp_is_own = self.binop(Operator::I32Eq, hp, zero, Type::I32);
        let base = self.select(Type::I32, objptr, hp, hp_is_own);
        let live_hs = self.load_i32(base, SHAPE_OFFSET);
        let m_holder = self.binop(Operator::I32Eq, live_hs, chs, Type::I32);
        let load_blk = self.body.add_block();
        self.cond_br(m_holder, load_blk, probe_blk);
        self.cur = load_blk;
        self.emit_guard_census(census::GET_IC_W1, self.cur_pc);
        let result = self.emit_slot_load(base, slot_enc);
        let flags = merge_flags_param.map(|_| (entry_flags, None, None));
        self.ic_arm_br(merge, vals, &[result], flags);
    }

    /// The set mirror of `emit_class_fact_get`: guarding fullword on the
    /// receiver's class is enough to reach raw slots with known types, and
    /// nothing about it is specific to `this`.
    /// One class-idx guard over the site's predicted layout turns the store
    /// into a bare fixed-slot write, and the passed guard is written back to
    /// the source slot as a durable `cls` fact -- so a live fact inside the
    /// site's range drops the guard entirely and later reads of the same
    /// lineage take the get arm checkless. Miss arm: the property set IC.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn emit_class_fact_set(
        &mut self,
        ps: &PropSiteIn,
        atom_id: u32,
        recv: &Operand,
        val: &Operand,
        recv_boxed: Value,
        val_boxed: Value,
        elide_barrier: bool,
        val_is_num: bool,
        next_pc: Pc,
        site_claim: Option<Claim>,
        range_act: RangeAct,
    ) {
        let k = ps.layout_id + 1;
        let k_hi = ps.hi_layout_id + 1;
        if !val_is_num {
            self.kill_shallow_facts();
        }
        let recv_ptr = self.to_ptr(recv);
        let cls_implied = recv
            .cls
            .is_some_and(|(lo, hi)| u32::from(lo) >= k && u32::from(hi) <= k_hi);
        self.dump_cls_consumer(self.cur_pc, "set", recv, k, k_hi, cls_implied);
        // Proven-SLOTS receiver: the store immediate is licensed with no
        // guard and no miss arm (the get side's checkless twin).
        if cls_implied {
            self.emit_rely_census(census::RELY_PROP_CLS, recv.prov);
        } else if is_object_only(&recv.ty) {
            self.emit_rely_census(census::RELY_PROP_OBJ, recv.prov);
        }
        if !(cls_implied && recv.cls_slots) {
            let miss_blk = self.body.add_block();
            if !cls_implied && !is_object_only(&recv.ty) {
                let is_obj = self.tag_eq(recv_boxed, TAG_OBJECT as u32);
                let chk_blk = self.body.add_block();
                let spc = self.cur_pc;
                let tagfail = self.guard_miss_tag_blk(miss_blk, census::SET_MISS_WHY, spc);
                self.cond_br(is_obj, chk_blk, tagfail);
                self.cur = chk_blk;
            }
            // The slot-immediate store demands the SLOTS bit on top of
            // identity (fused into one compare when identity is guarded;
            // a bare bit test when the fact already implies identity). A
            // miss means the immediate does not apply -- the set IC serves
            // the store either way.
            let w = self.load_i32(recv_ptr, OBJ_CLASS_IDX_OFFSET);
            self.eff(w, Eff::ReadBits(HeapKind::ClassWord));
            let eq = if cls_implied {
                let sm = self.i32_const(CLASS_WORD_SLOTS);
                let sb = self.binop(Operator::I32And, w, sm, Type::I32);
                let z = self.i32_const(0);
                self.binop(Operator::I32Ne, sb, z, Type::I32)
            } else if k == k_hi {
                let m = self.i32_const(0xFFFF | CLASS_WORD_SLOTS);
                let t = self.binop(Operator::I32And, w, m, Type::I32);
                let kv = self.i32_const(k | CLASS_WORD_SLOTS);
                self.binop(Operator::I32Eq, t, kv, Type::I32)
            } else {
                let m16 = self.i32_const(0xFFFF);
                let idx = self.binop(Operator::I32And, w, m16, Type::I32);
                let kv = self.i32_const(k);
                let d = self.binop(Operator::I32Sub, idx, kv, Type::I32);
                let span = self.i32_const(k_hi - k);
                let in_range = self.binop(Operator::I32LeU, d, span, Type::I32);
                let sm = self.i32_const(CLASS_WORD_SLOTS);
                let sb = self.binop(Operator::I32And, w, sm, Type::I32);
                let z = self.i32_const(0);
                let slots_ok = self.binop(Operator::I32Ne, sb, z, Type::I32);
                self.binop(Operator::I32And, in_range, slots_ok, Type::I32)
            };
            let hit_blk = self.body.add_block();
            let spc = self.cur_pc;
            let attr_blk =
                self.guard_miss_why_blk(miss_blk, census::SET_MISS_WHY, w, recv_ptr, k, k_hi, spc);
            self.cond_br(eq, hit_blk, attr_blk);

            let recv2 = recv.clone();
            let vty = val.ty;
            let vrange = val.range;
            // A layout fast arm precedes this: the arm takes the hot
            // overwrites, so the transition arm here is bloat -- except in
            // stamping-ctor / init-delegate bodies, whose `this.field = v`
            // adds always land on this tail during construction (the
            // fused guard cannot match an unstamped receiver): without the
            // arm every ctor add pays the miss helper, and an allocating
            // benchmark runs millions of them.
            let init_add = self.ctx.stamp_ctors_in.contains_key(&self.source_id)
                || self
                    .ctx
                    .this_layouts_in
                    .get(&self.source_id)
                    .is_some_and(|li| li.init_home);
            let mpc = self.cur_pc;
            self.side_arm(miss_blk, next_pc, move |s| {
                s.emit_guard_census(census::SET_L1_MISS, mpc);
                s.push_ranged(val_boxed, Repr::Boxed, vty, vrange);
                s.emit_set_prop_ic_inline(
                    &recv2,
                    recv_boxed,
                    val_boxed,
                    elide_barrier,
                    val_is_num,
                    atom_id,
                    None,
                    init_add,
                    site_claim,
                    range_act,
                );
                s.stack.pop().expect("the stored value stays on the stack")
            });

            self.cur = hit_blk;
            // The passed guard proved SLOTS either way (fused with
            // identity, or the bare bit under a live identity fact).
            let cls = if cls_implied {
                recv.cls
            } else {
                Some((u16::try_from(k).unwrap(), u16::try_from(k_hi).unwrap()))
            };
            self.refine_src(
                recv,
                SlotCtx {
                    prims: Prims::EMPTY,
                    outside: true,
                    range: RangeBucket::Top,
                    cls,
                    cls_shallow: false,
                    cls_slots: true,
                    ta: None,
                    likely_cls: None,
                    src: None,
                    iv: None,
                    iv_grow: 0,
                    prov: recv.prov.or(Prov::C_FIELD),
                },
            );
        }
        if cls_implied && recv.cls_slots {
            self.emit_guard_census(census::SET_L1A, self.cur_pc);
        } else {
            self.emit_guard_census(census::SET_L1_HIT, self.cur_pc);
        }
        let off = FIXED_SLOTS_BASE + 8 * ps.slot;
        let slot_addr = self.add_offset(recv_ptr, off);
        self.emit_pre_write_barrier_addr(slot_addr);
        let recv_bit = self.store_recv_bit(recv);
        let st = self.store_i64(recv_ptr, off, val_boxed);
        self.eff_store(st, Eff::Write(HeapKind::Slot), recv_bit);
        // On this arm the receiver's class is proven and `ps` is its row,
        // so the field's own claim is the store's duty: an unmasked
        // (object) field owes nothing, a masked one owes the conform
        // check. Without it every non-ctor object store would take the
        // generic choke, which clears SHALLOW on any non-number value --
        // so a `this.link = node` store would demote every typed field of
        // the receiver, and the SHALLOW-checkless read forms would never
        // fire. The miss arm keeps the site claim as given: there the
        // receiver's class is unknown.
        // The claim is the LAYOUT's mask for this exact class -- the tier
        // SHALLOW certifies and the ctor init masks come from -- never a
        // site row's, and never for a group range, whose meet could be
        // unmasked where a member's own row is not.
        let arm_claim = site_claim.or_else(|| {
            if k != k_hi {
                return None;
            }
            let name = self.atoms.emitted_name(atom_id);
            self.ctx
                .layout_field_masks_in
                .get(&StampKey::new(k))
                .map(|m| m.get(&name).copied().unwrap_or(Claim::NONE))
        });
        let (_, choke_dyn) = self.emit_store_choke(
            recv_ptr, val_boxed, val_is_num, recv_bit, arm_claim, range_act,
        );
        if !elide_barrier {
            let slot_v = self.i32_const(ps.slot);
            self.emit_post_write_barrier(recv_boxed, slot_v, val_boxed);
        }
        // Per-lineage accounting: the fall-through stored; the choke's
        // runtime word says whether it also demoted a stamp.
        self.or_flags_const(recv_bit);
        if let Some(w) = choke_dyn {
            self.or_flags_word(w);
        }
        self.push_ranged(val_boxed, Repr::Boxed, val.ty, val.range);
    }

    /// SetProp IC: mono own-slot store (barriered), mega-set probe, and the
    /// add-transition replay arm; only a miss calling
    /// `night_runtime_set_prop_ic_miss`.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn emit_set_prop_ic_inline(
        &mut self,
        recv: &Operand,
        recv_boxed: Value,
        val_boxed: Value,
        elide_barrier: bool,
        val_is_num: bool,
        atom_id: u32,
        slow_cont: Option<u32>,
        allow_trans: bool,
        site_claim: Option<Claim>,
        range_act: RangeAct,
    ) {
        // A non-number inline store may clear any aliased object's
        // valid-types flags -- proven-shallow facts die here (number
        // stores violate no claim, facts survive).
        if !val_is_num {
            self.kill_shallow_facts();
        }
        // Two-bit family: the transition replay's add check may clear an
        // aliased object's SLOTS bit -- proven-SLOTS facts die on every
        // set-IC emission.
        self.kill_slots_facts();
        // Arm-free outlined form (Dirty only; the gen-only rung keeps its
        // historical inline-IC shape): the slow arm alone. The helper's
        // effect classification carries the kills and flags.
        if self.outline_generic() && !self.gen_only {
            let cache_idx = if self.mode == EmitMode::Code {
                self.atoms.next_prop_cache()
            } else {
                0
            };
            let atom_v = self.i32_const(atom_id);
            let cache_v = self.i32_const(cache_idx);
            let strict = matches!(self.cur_op, Some(JSOp::StrictSetProp));
            let strict_v = self.i32_const(u32::from(strict));
            self.emit_guard_census(census::SET_IC_MISS, self.cur_pc);
            let setmiss = self.helpers.set_prop_ic_miss;
            self.rt_call(setmiss, false, |_, _| {
                vec![recv_boxed, atom_v, val_boxed, cache_v, strict_v]
            });
            return;
        }
        let recv_bit = self.store_recv_bit(recv);
        let add_check = if allow_trans {
            self.ctor_add_check(recv, self.atoms.emitted_name(atom_id))
        } else {
            AddCheck::Runtime(Vec::new())
        };
        // `Code`-only allocation (see emit_instanceof's cell note).
        let cache_idx = if self.mode == EmitMode::Code {
            self.atoms.next_prop_cache()
        } else {
            0
        };
        let atom_v = self.i32_const(atom_id);
        let cache_v = self.i32_const(cache_idx);

        let (reprs, vals) = self.diamond_snapshot();
        let top_off = self.operand_base + 8 * u32::try_from(reprs.len()).unwrap();

        let slow_blk = self.body.add_block();
        let merge = self.body.add_block();
        let op_params = self.diamond_params(merge, &reprs);
        let store_bit = recv_bit;
        // None-case (in-arm) merges carry the accumulator as a param: the
        // helper sub-arm's saturation must not leak into the inline arms'
        // paths -- a ctor's `this.x = v` adds land on this tail during
        // construction (the steady path), and a leaked all here turns the
        // body's returned word from MUT_THIS into all, killing every
        // construct-fork consumer downstream (the kind-38=0 census).
        let entry_flags = self.cur_flags;
        // With `slow_cont` the miss helper's second chance leaves as its
        // own lineage and never reaches this merge, so the param is safe in
        // both shapes (and necessary: without it the fall-through would
        // have to claim every arm's worst static word, FLAG_STAMPS
        // included).
        // The proto-proof cell this store may spend and re-mint: the root
        // body's own `this` only (see `proto_on`). Any other receiver's
        // replay may reshape a proto of `this`, so it kills the cell.
        let own_this = self.cur_seg.is_none() && self.store_recv_is_this(recv);
        let cell = if allow_trans { self.proto_cell() } else { None };
        let ok_param = self.body.add_blockparam(merge, Type::I32);
        let merge_flags_param = self
            .flags_threading()
            .then(|| self.body.add_blockparam(merge, Type::I32));

        let recv_obj = if is_object_only(&recv.ty) {
            self.emit_rely_census(census::RELY_PROP_OBJ, recv.prov);
            self.i32_const(1)
        } else {
            self.tag_eq(recv_boxed, TAG_OBJECT as u32)
        };
        let way0 = self.body.add_block();
        self.cond_br(recv_obj, way0, slow_blk);

        self.cur = way0;
        let objptr = self.to_ptr(recv);
        let shape = self.load_i32(objptr, SHAPE_OFFSET);
        self.eff(shape, Eff::Read(HeapKind::Shape));
        let way_addr_off = cache_idx * INLINE_IC_STRIDE;
        let way_base = self.i32_const(IC_WAY_ADDR_PLACEHOLDER);
        self.prop_ic_patches.push((way_base, way_addr_off));
        let store_blk = self.body.add_block();
        // `allow_trans` false = a layout fast arm already covers this site,
        // so the way0 miss goes straight to the slow path: the add
        // transition replay (its poly probe, its four proto live-shape
        // guards and its shape-word swap) is pure code bloat behind an arm
        // that already took the hot overwrites. Emitting the transition arm
        // at every set site instead is most of what makes SetProp lower to
        // half again as many blocks and values as it needs.
        let trans_blk = if allow_trans {
            self.body.add_block()
        } else {
            slow_blk
        };
        let addarm_blk = allow_trans.then(|| self.body.add_block());
        let row = allow_trans.then(|| {
            let row = self.i32_const(IC_WAY_ADDR_PLACEHOLDER);
            self.prop_ic_patches
                .push((row, way_addr_off + IC_TRANS_ROW_OFF));
            row
        });
        // A static add site (`this.f = v` on the predicted field of a
        // stamping ctor): the receiver is the fresh object with the
        // PRE-add shape, so way 0 -- a filled slot -- never matches and the
        // transition row is the steady arm. Test its old shape first; the
        // way test and the sentinel dispatch follow only on a miss.
        let trans_first = allow_trans && matches!(add_check, AddCheck::Predicted(_));
        let trans_guard_blk = if trans_first {
            let old_s = self.load_i32(row.unwrap(), IC_TRANS_OLDSHAPE);
            let m_old = self.binop(Operator::I32Eq, old_s, shape, Type::I32);
            let way_blk = self.body.add_block();
            self.cond_br(m_old, addarm_blk.unwrap(), way_blk);
            self.cur = way_blk;
            addarm_blk
        } else {
            allow_trans.then(|| self.body.add_block())
        };
        let cs = self.load_i32(way_base, IC_SET_RECVSHAPE);
        self.eff(cs, Eff::Read(HeapKind::EngineTable));
        let hit = self.binop(Operator::I32Eq, shape, cs, Type::I32);
        let slot_enc = self.load_i32(way_base, IC_SET_SLOTENC);
        let abs_slot = self.load_i32(way_base, IC_SET_ABSSLOT);
        self.cond_br(hit, store_blk, trans_blk);

        if allow_trans {
            let row = row.unwrap();
            let addarm_blk = addarm_blk.unwrap();
            let trans_guard_blk = trans_guard_blk.unwrap();
            // Way0 missed: dispatch on the sentinel. The MEGA probe lives
            // in `night_ic_set_cold` (one call with the site's IC row --
            // the parameterized-helper discipline; mega stores run flat
            // under it). The ADD-TRANSITION validation stays INLINE: it is
            // the ctor-init steady path, executed heavily enough that
            // out-lining it costs real throughput -- the same hot-arm law
            // as the get side.
            self.cur = trans_blk;
            let sentinel = self.i32_const(IC_POLY_SENTINEL);
            let m_poly = self.binop(Operator::I32Eq, cs, sentinel, Type::I32);
            let mega_blk = self.body.add_block();
            // Under `trans_first` the row already missed on this path.
            let not_poly = if trans_first { slow_blk } else { addarm_blk };
            self.cond_br(m_poly, mega_blk, not_poly);
            self.cur = mega_blk;
            let cold = self.call_i64(self.helpers.ic_set_cold, &[shape, way_base, atom_v]);
            let z64 = self.boxed_const(0);
            let is_cold_miss = self.binop(Operator::I64Eq, cold, z64, Type::I32);
            let mega_store_blk = self.body.add_block();
            self.cond_br(is_cold_miss, slow_blk, mega_store_blk);
            // Mega-set hit: the helper hands back the table entry.
            self.cur = mega_store_blk;
            self.emit_guard_census(census::SET_IC_MEGA, self.cur_pc);
            let entry = self.unop(Operator::I32WrapI64, cold, Type::I32);
            let m_slot_enc = self.load_i32(entry, MEGA_SET_SLOTENC);
            let m_slot_addr = self.emit_slot_addr(objptr, m_slot_enc);
            self.emit_pre_write_barrier_addr(m_slot_addr);
            let st = self.store_i64(m_slot_addr, 0, val_boxed);
            self.tag_store(st, HeapKind::Slot);
            let (_, choke_dyn) = self.emit_store_choke(
                objptr, val_boxed, val_is_num, recv_bit, site_claim, range_act,
            );
            if !elide_barrier {
                let m_abs = self.load_i32(entry, MEGA_SET_ABSSLOT);
                self.emit_post_write_barrier(recv_boxed, m_abs, val_boxed);
            }
            let flags = merge_flags_param.map(|_| (entry_flags, Some(store_bit), choke_dyn));
            self.ic_arm_br(merge, &vals, &[], flags);
            // Add-transition replay: cached pre-add shape + proto
            // live-shape guards -> fresh-slot init store + shape-word
            // swap. INLINE by measurement, twice (see the arm comment
            // above): this is the ctor-init steady path.
            if !trans_first {
                self.cur = addarm_blk;
                let old_s = self.load_i32(row, IC_TRANS_OLDSHAPE);
                let m_old = self.binop(Operator::I32Eq, old_s, shape, Type::I32);
                self.cond_br(m_old, trans_guard_blk, slow_blk);
            }
            self.cur = trans_guard_blk;
            let slot_off = self.load_i32(row, IC_TRANS_SLOTOFF);
            let zero = self.i32_const(0);
            let ok_slot = self.binop(Operator::I32Ne, slot_off, zero, Type::I32);
            let proto_row = |n: u32| IC_TRANS_PROTO0 + IC_TRANS_PROTO_ROW_BYTES * n;
            // The row's recorded proto shapes: the words the replay
            // validates against the live chain, and the proof it mints.
            let wants: Vec<Value> = (0..IC_TRANS_INLINE_HOPS)
                .map(|n| self.load_i32(row, proto_row(n) + 4))
                .collect();
            let replay_blk = self.body.add_block();
            // Proof spent: the cell holds this `this` and the same two
            // shape words, validated live by an earlier replay in this
            // activation with nothing since that could reshape a proto
            // (the kills zero the cell). Equal words mean the chain this
            // row was recorded against is the live one, deeper rows
            // included (`proto_on`).
            let spend = own_this.then_some(cell).flatten();
            if let Some(cell) = spend {
                let c_recv = self.load_i32(cell, PROTO_CELL_RECV);
                self.eff(c_recv, Eff::Read(HeapKind::EngineTable));
                let same_recv = self.binop(Operator::I32Eq, c_recv, objptr, Type::I32);
                let mut same = vec![same_recv];
                for (n, &w) in wants.iter().enumerate() {
                    let cw = self.load_i32(cell, PROTO_CELL_SHAPE0 + 4 * n as u32);
                    self.eff(cw, Eff::Read(HeapKind::EngineTable));
                    same.push(self.binop(Operator::I32Eq, cw, w, Type::I32));
                }
                let m = self.and_all(&same).unwrap();
                let m = self.binop(Operator::I32And, m, ok_slot, Type::I32);
                let validate_blk = self.body.add_block();
                let proven_blk = self.body.add_block();
                self.cond_br(m, proven_blk, validate_blk);
                self.cur = proven_blk;
                self.emit_guard_census(census::SET_IC_TRANS_PROVEN, self.cur_pc);
                self.body.set_terminator(
                    self.cur,
                    Terminator::Br {
                        target: BlockTarget {
                            block: replay_blk,
                            args: vec![],
                        },
                    },
                );
                self.cur = validate_blk;
            }
            // The row records `IC_TRANS_PROTO_HOPS` hops and all of them
            // must be accounted for here, or the replay would trust an
            // unchecked chain. The first `IC_TRANS_INLINE_HOPS` are
            // validated against their live shape word; the rest are
            // discharged by requiring them empty, so a row deeper than
            // that falls to the helper, which replays against every hop.
            let validated: Vec<Value> = (0..IC_TRANS_INLINE_HOPS)
                .map(|n| {
                    let p = self.load_i32(row, proto_row(n));
                    let want = wants[n as usize];
                    let live = self.load_i32(p, SHAPE_OFFSET);
                    self.eff(live, Eff::Read(HeapKind::Shape));
                    let empty = self.unop(Operator::I32Eqz, p, Type::I32);
                    let m = self.binop(Operator::I32Eq, live, want, Type::I32);
                    self.binop(Operator::I32Or, empty, m, Type::I32)
                })
                .collect();
            let deep: Vec<Value> = (IC_TRANS_INLINE_HOPS..IC_TRANS_PROTO_HOPS)
                .map(|n| self.load_i32(row, proto_row(n)))
                .collect();
            let deep_empty: Vec<Value> = deep
                .into_iter()
                .map(|p| self.unop(Operator::I32Eqz, p, Type::I32))
                .collect();
            let g_validated = self.and_all(&validated);
            let g_deep = self.and_all(&deep_empty);
            let g_protos = match (g_validated, g_deep) {
                (Some(a), Some(b)) => Some(self.binop(Operator::I32And, a, b, Type::I32)),
                (a, b) => a.or(b),
            };
            let all = match g_protos {
                Some(g) => self.binop(Operator::I32And, g, ok_slot, Type::I32),
                None => ok_slot,
            };
            // Validated on the root `this`: mint the proof for the body's
            // later replays. Any other receiver's replay reshapes an
            // object that may be a proto of `this`: kill instead.
            match (spend, cell) {
                (Some(cell), _) => {
                    let mint_blk = self.body.add_block();
                    self.cond_br(all, mint_blk, slow_blk);
                    self.cur = mint_blk;
                    let st = self.store_i32(cell, PROTO_CELL_RECV, objptr);
                    self.effects.insert(st, Eff::Write(HeapKind::EngineTable));
                    for (n, &w) in wants.iter().enumerate() {
                        let st = self.store_i32(cell, PROTO_CELL_SHAPE0 + 4 * n as u32, w);
                        self.effects.insert(st, Eff::Write(HeapKind::EngineTable));
                    }
                    self.body.set_terminator(
                        self.cur,
                        Terminator::Br {
                            target: BlockTarget {
                                block: replay_blk,
                                args: vec![],
                            },
                        },
                    );
                }
                (None, Some(_)) => {
                    self.cond_br(all, replay_blk, slow_blk);
                    self.cur = replay_blk;
                    self.kill_proto_cell();
                }
                (None, None) => {
                    self.cond_br(all, replay_blk, slow_blk);
                }
            }
            self.cur = replay_blk;
            self.emit_guard_census(census::SET_IC_TRANS, self.cur_pc);
            let slot_addr = self.binop(Operator::I32Add, objptr, slot_off, Type::I32);
            let st = self.store_i64(slot_addr, 0, val_boxed);
            self.tag_store(st, HeapKind::Slot);
            let (_, choke_dyn) = self.emit_store_choke(
                objptr, val_boxed, val_is_num, recv_bit, site_claim, range_act,
            );
            let new_s = self.load_i32(row, IC_TRANS_NEWSHAPE);
            let sw = self.store_i32(objptr, SHAPE_OFFSET, new_s);
            self.tag_store(sw, HeapKind::Shape);
            // The add-check's runtime word: FLAG_STAMPS iff it clears a
            // non-fresh receiver's SLOTS bit.
            let add_sel = self.emit_add_slots_check(objptr, slot_off, add_check);
            let add_sel = if recv_bit != 0 { add_sel } else { None };
            let arm_dyn = self.or_opt_words(choke_dyn, add_sel);
            if !elide_barrier {
                let t_abs_slot = self.load_i32(row, IC_TRANS_ABSSLOT);
                self.emit_post_write_barrier(recv_boxed, t_abs_slot, val_boxed);
            }
            let flags = merge_flags_param.map(|_| (entry_flags, Some(store_bit), arm_dyn));
            self.ic_arm_br(merge, &vals, &[], flags);
        }

        // Mono hit: barriered own-slot store.
        self.cur = store_blk;
        self.emit_guard_census(census::SET_IC_W0, self.cur_pc);
        let slot_addr = self.emit_slot_addr(objptr, slot_enc);
        self.emit_pre_write_barrier_addr(slot_addr);
        let st = self.store_i64(slot_addr, 0, val_boxed);
        self.eff_store(st, Eff::Write(HeapKind::Slot), recv_bit);
        let (_, choke_dyn) = self.emit_store_choke(
            objptr, val_boxed, val_is_num, recv_bit, site_claim, range_act,
        );
        if !elide_barrier {
            self.emit_post_write_barrier(recv_boxed, abs_slot, val_boxed);
        }
        let flags = merge_flags_param.map(|_| (entry_flags, Some(store_bit), choke_dyn));
        self.ic_arm_br(merge, &vals, &[], flags);
        self.cur = slow_blk;
        self.emit_guard_census(census::SET_IC_MISS, self.cur_pc);

        let arm_st = self.arm_state();
        let n = self.spill_all();
        let top = self.add_offset(self.vp, top_off);
        let setmiss = self.helpers.set_prop_ic_miss;
        let strict = matches!(self.cur_op, Some(JSOp::StrictSetProp));
        let strict_v = self.i32_const(u32::from(strict));
        let ok = self.call_i32(
            setmiss,
            &[
                self.cx, top, recv_boxed, atom_v, val_boxed, cache_v, strict_v,
            ],
        );
        match slow_cont {
            Some(next_pc) => {
                // Arm continuation, with the second-chance fork: a store
                // served by an existing slot OR by a cached add-transition
                // replay ran no user code and could not GC, so it rejoins the
                // fall-through's lineage. The clean edge still stored, so its
                // restored accumulator ORs the classified bit -- otherwise
                // the accumulator would under-report the write.
                self.branch_on_err(ok);
                // The helper-served store may run the C++ choke or a cached
                // add replay: its restored word carries the same static
                // stamp-break union as the inline arms.
                let sc_bits = store_bit | if recv_bit != 0 { FLAG_STAMPS } else { 0 };
                self.miss_second_chance_w(ok, n, Pc::new(next_pc), arm_st, sc_bits, |_| {});
            }
            None => {
                let mut margs = self.diamond_slow_args(&reprs);
                margs.push(ok);
                if merge_flags_param.is_some() {
                    // The miss helper is a full CallGc: the leaked
                    // saturated state is this arm's honest word.
                    margs.push(self.materialize_flags());
                }
                self.body.set_terminator(
                    slow_blk,
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
        // Per-lineage accounting: with the param the arms carried
        // their own classified words; without it every merge predecessor
        // stored (mono / mega / transition replay -- the second-chance
        // edges left the version).
        if let Some(fp) = merge_flags_param {
            self.cur_flags = FlagsAcc::Dyn(fp, 0);
        } else {
            self.or_flags_const(store_bit);
        }
    }
}
