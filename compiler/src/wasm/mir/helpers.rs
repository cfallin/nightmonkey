//! Out-of-line runtime helpers the MIR and baseline tiers call: in-module
//! functions built once per module, for checks that are the same at every
//! site (the callee classify chain, the dense-append check, the megamorphic
//! property/element probes, the IC set cold path).

use super::abi::*;
use crate::wasm::translate::*;
use waffle::{Block, Func, Module, Operator, Type};

/// In-module generic callee classify: `night_call_classify(calleeBoxed,
/// cellAddr, trashAddr) -> (funcidx, script, isNative)`, funcidx 0 = not a
/// dispatchable AOT function.
///
/// The chain below -- function-clasp validation through shape and baseShape,
/// the BaseScript flag, the class-constructor kind test, the nightFuncIndex
/// load and the cell fill -- is byte-for-byte the same work at every call
/// site; only the cell address varies, and that is a parameter. So it is
/// emitted once and called. What stays inline at the site is the per-site
/// cell probe (`emit_inline_classify`), which is the steady state at nearly
/// every site and the reason the cell exists at all.
///
/// `cellAddr` 0 means the site declined a cell: the probe is skipped and
/// nothing is filled.
///
/// A Leaf that writes engine bookkeeping only (the cell row) -- no GC, no
/// user code, no user-visible heap. It lives here rather than in `translate`
/// so it sits next to the inline probe it has to agree with, and reads the
/// same layout constants.
pub fn build_call_classify_helper(m: &mut Module, mem: waffle::Memory, fn_class_slot: u32) -> Func {
    use crate::wasm::translate::RawEmit;
    use waffle::{FuncDecl, SignatureData};
    let sig = m.signatures.push(SignatureData {
        params: vec![Type::I64, Type::I32, Type::I32],
        returns: vec![Type::I32, Type::I32, Type::I32],
    });
    let mut e = RawEmit::new(m, sig, mem);
    let callee_boxed = e.param(0);
    let cell_addr = e.param(1);
    let trash = e.param(2);

    let fail = e.body.add_block();
    let native = e.body.add_block();
    let c1 = e.body.add_block();

    let shift = e.i64c(32);
    let hi64 = e.bin(Operator::I64ShrU, callee_boxed, shift, Type::I64);
    let hi = e.un(Operator::I32WrapI64, hi64, Type::I32);
    let objtag = e.i32c(TAG_OBJECT as u32);
    let is_obj = e.bin(Operator::I32Eq, hi, objtag, Type::I32);
    e.condbr(is_obj, c1, fail);

    // Each arm materializes its own constants: a const is an instruction in
    // the block that made it, and these blocks do not dominate each other.
    e.cur = fail;
    let fz = e.i32c(0);
    e.ret(vec![fz, fz, fz]);
    e.cur = native;
    let nz = e.i32c(0);
    let no = e.i32c(1);
    e.ret(vec![nz, nz, no]);

    e.cur = c1;
    let ptr = e.un(Operator::I32WrapI64, callee_boxed, Type::I32);
    let shape = e.ld32(ptr, SHAPE_OFFSET);
    let base = e.ld32(shape, SHAPE_BASESHAPE_OFFSET);
    let clasp = e.ld32(base, BASESHAPE_CLASP_OFFSET);
    let slot = e.i32c(fn_class_slot);
    let fn_class = e.ld32(slot, 0);
    let ext_class = e.ld32(slot, 4);
    let is_fn = e.bin(Operator::I32Eq, clasp, fn_class, Type::I32);
    let is_ext = e.bin(Operator::I32Eq, clasp, ext_class, Type::I32);
    let is_function = e.bin(Operator::I32Or, is_fn, is_ext, Type::I32);
    let c2 = e.body.add_block();
    e.condbr(is_function, c2, fail);

    e.cur = c2;
    let memarg = e.marg(3, 0);
    let flags_addr = {
        let k = e.i32c(FUNC_FLAGS_SLOT_OFFSET);
        e.bin(Operator::I32Add, ptr, k, Type::I32)
    };
    let slot0 = e.load(Operator::I64Load { memory: memarg }, flags_addr, Type::I64);
    let raw = e.un(Operator::I32WrapI64, slot0, Type::I32);
    let bs_bit = e.i32c(FUNCTION_FLAGS_BASESCRIPT);
    let has_bs = e.bin(Operator::I32And, raw, bs_bit, Type::I32);
    let bs_blk = e.body.add_block();
    e.condbr(has_bs, bs_blk, native);

    e.cur = bs_blk;
    let kind_mask = e.i32c(FUNCTION_KIND_MASK);
    let kind = e.bin(Operator::I32And, raw, kind_mask, Type::I32);
    let class_k = e.i32c(FUNCTION_KIND_CLASS_CTOR);
    let is_class = e.bin(Operator::I32Eq, kind, class_k, Type::I32);
    let c3 = e.body.add_block();
    e.condbr(is_class, fail, c3);

    e.cur = c3;
    let script = e.ld32(ptr, FUNC_SCRIPT_SLOT_OFFSET);
    let idx = e.ld32(script, BASESCRIPT_NIGHTFUNCINDEX_OFFSET);

    // Cell fill, same state machine as the inline version: an empty row
    // learns this callee, a populated row that missed is poisoned with the
    // sentinel so a polymorphic site stops paying the write-back churn. A
    // nursery callee's store is diverted to the shared trash row rather than
    // branched around.
    let has_cell = e.body.add_block();
    let done = e.body.add_block();
    e.condbr(cell_addr, has_cell, done);
    e.cur = has_cell;
    let cached = e.load(Operator::I64Load { memory: memarg }, cell_addr, Type::I64);
    let zero64 = e.i64c(0);
    let was_empty = e.bin(Operator::I64Eq, cached, zero64, Type::I32);
    let fill_blk = e.body.add_block();
    let sent_blk = e.body.add_block();
    e.condbr(was_empty, fill_blk, sent_blk);

    e.cur = fill_blk;
    let mask = e.i32c(NOT_CHUNK_MASK);
    let chunk = e.bin(Operator::I32And, ptr, mask, Type::I32);
    let sb = e.ld32(chunk, CHUNK_STORE_BUFFER_OFFSET);
    let dst = e.sel(Type::I32, trash, cell_addr, sb);
    e.store(Operator::I64Store { memory: memarg }, dst, callee_boxed);
    let fa = {
        let k = e.i32c(CALL_CELL_FUNCIDX);
        e.bin(Operator::I32Add, dst, k, Type::I32)
    };
    let st32 = e.marg(2, 0);
    e.store(Operator::I32Store { memory: st32 }, fa, idx);
    let sa = {
        let k = e.i32c(CALL_CELL_SCRIPT);
        e.bin(Operator::I32Add, dst, k, Type::I32)
    };
    e.store(Operator::I32Store { memory: st32 }, sa, script);
    let z0 = e.i32c(0);
    e.ret(vec![idx, script, z0]);

    e.cur = sent_blk;
    let one64 = e.i64c(1);
    e.store(Operator::I64Store { memory: memarg }, cell_addr, one64);
    let z1 = e.i32c(0);
    e.ret(vec![idx, script, z1]);

    e.cur = done;
    let z2 = e.i32c(0);
    e.ret(vec![idx, script, z2]);

    m.funcs.push(FuncDecl::Body(
        sig,
        "night_call_classify".to_string(),
        e.body,
    ))
}

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

    // Mega-set probe (the hash mirrors NightRuntime.cpp's `MegaSet`; the atom
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
        e.ic_hit_tail(objptr, entry, MEGA_GET_HOLDERPTR, miss);
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

