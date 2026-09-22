/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! The effect taxonomy: One classification of every emission form,
//! consulted by both the plan (interval admission, split placement) and the
//! emission (arm selection, census).
//!
//! The property of interest is unknown-SIDE-effect-free (USEF): code that
//! cannot invoke arbitrary other JavaScript or an opaque runtime path.
//! Pure/leaf/alloc forms are all USEF; Unknown is not.
//!
//! The main consumer is loop-invariant code motion, which runs on every
//! compiled body: `bbv::run_script` calls `bbv::licm::licm` on the emitted
//! IR once `assert_reducible` confirms the CFG is reducible, with no switch
//! to turn it off. It is not decoration -- it lifts thousands of
//! loop-invariant loads out of hot loops on real programs, and the
//! reducibility check has not refused a body in practice. The `HeapKind`
//! vocabulary below is what makes that safe: a hoist candidate moves only
//! when the loop's write summary cannot touch the kind it reads.

use super::translate::Helpers;
use rustc_hash::FxHashMap as HashMap;
use waffle::Func;

/// The abstract-location vocabulary for LICM's loop write summaries:
/// Kind-level disambiguation: split a kind finer only with evidence of a
/// real read/write conflict inside it.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum HeapKind {
    /// Guarded engine-table rows at constant addresses (gname slot rows,
    /// IC ways, append rows, call cells, layout guard cells, startup-
    /// immutable class/atom tables): every consumer re-verifies against
    /// live object state in-loop, and rows are rewritten only by each
    /// site's own resolve/miss helper, so a stale row read can only miss
    /// (re-resolve) or coincide with a still-valid mapping -- never yield
    /// a wrong value. This is what makes them hoistable even across
    /// may-GC arms (their const addresses cannot be relocated), and why
    /// EngineTable writes in a loop never block EngineTable reads.
    EngineTable,
    /// Fuse words and value cells (gname literal fuses, gGlobalVals,
    /// intrinsic/strlit cells): the cell IS the soundness guard, and a
    /// mid-loop call can blow it -- never hoistable across calls.
    FuseCell,
    /// Object shape word loads.
    Shape,
    /// The likely-class word (stamps write it).
    ClassWord,
    /// ObjectElements header words (initializedLength/flags/capacity/
    /// length; the append arm writes them).
    ElementsHeader,
    /// Dense element data and typed-array element data (one kind: an
    /// element store may alias an element read; kind-level suffices).
    Elements,
    /// Fixed/dynamic property slots (object, env, global, args-object).
    Slot,
    /// String header/char data (immutable post-creation, but flags can
    /// change: linearization).
    StringData,
    /// The nursery bump cursor + chunk metadata (pos/end words). Written
    /// by every inline allocation; changes each iteration of an
    /// allocating loop, so its reads must never hoist over its writes.
    AllocCursor,
    /// Stores into memory claimed from the nursery bump within this body
    /// (fresh-object header/shape/class/slots/elements stamps, fresh
    /// string fills). Without a GC the cursor only moves up, so fresh
    /// bytes are disjoint from every address that existed at loop entry:
    /// a Fresh write can never invalidate an invariant load, and no read
    /// is ever tagged Fresh. Exists so alloc fast paths need not poison
    /// the summary as Unknown.
    Fresh,
    /// Anything untagged.
    Unknown,
}

impl HeapKind {
    pub const fn bit(self) -> u16 {
        1u16 << (self as u16)
    }

    pub const ALL: [HeapKind; 11] = [
        HeapKind::EngineTable,
        HeapKind::FuseCell,
        HeapKind::Shape,
        HeapKind::ClassWord,
        HeapKind::ElementsHeader,
        HeapKind::Elements,
        HeapKind::Slot,
        HeapKind::StringData,
        HeapKind::AllocCursor,
        HeapKind::Fresh,
        HeapKind::Unknown,
    ];
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum EffectClass {
    /// Wasm ops, register/frame traffic, validated-fence loads, class-word
    /// tests, tag tests; helpers that only read engine state.
    Pure,
    /// Helpers that provably run no user code and no GC (math helpers,
    /// barrier appends, slot stores, generator state copies).
    Leaf,
    /// May GC, never runs user code (literal allocation, env objects,
    /// throw paths). Kills GC-pointer carriers only; numeric carriers and
    /// class facts survive (GC never mutates a class word).
    ///
    /// **This contract is not fully honoured.** `note_call_eff` and
    /// `outline_generic`, the only two readers of this enum, collapse
    /// `Alloc` into `Unknown` unless `quiet`, so a non-quiet `Alloc` gets
    /// the full fact kill. Honouring it means separating what a generic
    /// "CallGc" conflates: a GC invalidates SSA-cached raw pointers and
    /// nothing else -- it moves no JS-level value and mutates no class
    /// word -- while an arbitrary mutation invalidates heap facts. Keep
    /// the classification accurate regardless: a reader may rely on it
    /// directly.
    Alloc,
    /// Can reach user code (helper fallbacks, IC misses, ToPrimitive
    /// coercions, proto getters/setters, unresolved calls).
    Unknown,
}

/// Everything the emitter needs to know about one runtime helper, in one
/// record. The properties are not independent -- `quiet` is meaningful only
/// on `Alloc`, `user_heap_writes` and `leaf_writes` only on `Leaf` -- and a
/// wrong combination is a miscompile: a helper wrongly called quiet lets the
/// emitter keep context facts across a write to pre-existing heap. One row
/// per helper is what makes the combination checkable (see the test below).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct HelperMeta {
    pub effect: EffectClass,
    /// `Alloc` only: may GC but provably writes NO pre-existing user-visible
    /// heap -- fresh allocations (the result and its innards), throw/check
    /// paths, and literal fills whose receiver is by op semantics the literal
    /// under construction. A GC invalidates raw pointers only; every
    /// compile-time fact is a property of the value and moves with the
    /// object. So a quiet alloc neither steps the track, nor kills ctx facts,
    /// nor saturates the flags word -- it only sweeps raw-pointer carriers
    /// (the frame slot, which the GC updates in place, is the truth).
    ///
    /// Deliberately not quiet: init_glexical (writes the pre-existing global
    /// lexical env); mutate_proto (proto write observable through the chain);
    /// the env push/freshen/recreate family (replaces live environments); the
    /// generator/async family (gen state is heap the caller can observe).
    /// Unknown-class helpers keep the full conservative treatment: they can
    /// run arbitrary user code -- `optimize_spread_call` is one of those
    /// (iterator protocol reach), not an `Alloc`.
    pub quiet: bool,
    /// `Leaf` only: writes user-visible heap state (object slots, env/args-
    /// object slots, global data slots, typed-array data, iterator state) --
    /// the writes that can falsify a caller's kept facts across a
    /// clean-flagged return. Guard-cell/cache/barrier writers are engine
    /// bookkeeping and stay out. The bytecode scan cannot see a spliced
    /// callee's leaf writes, so emission records them instead.
    pub user_heap_writes: bool,
    /// `Leaf` only: the `HeapKind::bit` mask the helper can write, folded
    /// into LICM's loop write summary in place of a blanket has-leaf
    /// restriction. Audited against the runtime implementations:
    /// - barrier/mark helpers append to the store buffer / mark stack only,
    ///   engine state no Read kind can address, so their mask is empty;
    /// - `set_global` also blows binding fuses and warms the gGlobalSlots row;
    /// - resolve_global_slot* rewrite their own row (stale-tolerant contract);
    /// - validate_this_layout publishes into the layout guard cell;
    /// - math_unary/math_pow/fmod, strlit_verify (debug crash-only),
    ///   gen_closing (cx pending-exception word) and bind_var (reads + a
    ///   frame out-slot) write no addressable heap;
    /// - iterator/generator state helpers get {Slot, Elements} conservatively.
    /// A non-Leaf row keeps the poisoning `Unknown` mask, so a new Leaf whose
    /// mask was forgotten degrades LICM instead of breaking it.
    pub leaf_writes: u16,
}

impl HelperMeta {
    /// Unlisted funcs (compiled bodies, stubs, call_indirect): a scripted
    /// callee runs arbitrary JS.
    pub const UNLISTED: HelperMeta = unknown();
}

const fn meta(
    effect: EffectClass,
    quiet: bool,
    user_heap_writes: bool,
    leaf_writes: u16,
) -> HelperMeta {
    HelperMeta {
        effect,
        quiet,
        user_heap_writes,
        leaf_writes,
    }
}

/// The mask a non-Leaf row carries: reading it as a write summary poisons.
const POISON: u16 = HeapKind::Unknown.bit();

const fn pure() -> HelperMeta {
    meta(EffectClass::Pure, false, false, POISON)
}
/// A Leaf writing only engine bookkeeping.
const fn leaf(writes: u16) -> HelperMeta {
    meta(EffectClass::Leaf, false, false, writes)
}
/// A Leaf writing user-visible heap.
const fn leaf_user(writes: u16) -> HelperMeta {
    meta(EffectClass::Leaf, false, true, writes)
}
const fn alloc() -> HelperMeta {
    meta(EffectClass::Alloc, false, false, POISON)
}
const fn quiet_alloc() -> HelperMeta {
    meta(EffectClass::Alloc, true, false, POISON)
}
const fn unknown() -> HelperMeta {
    meta(EffectClass::Unknown, false, false, POISON)
}

/// One helper: how to find its `Func` in `Helpers`, its census name, and its
/// metadata. Soundness bias where a runtime doc contract is ambiguous:
/// between Leaf and Alloc pick Alloc (a missed GC would skip a boxed-carrier
/// revive); between Alloc and Unknown pick Unknown.
type Row = (fn(&Helpers) -> Func, &'static str, HelperMeta);

fn helper_rows() -> Vec<Row> {
    use HeapKind::*;
    let slot_elems = Slot.bit() | Elements.bit();
    vec![
        // read-only / infallible predicates and loads
        (|h| h.callee_night_target, "callee_night_target", pure()),
        (|h| h.ta_get_poly, "ta_get_poly", pure()),
        (|h| h.ic_get_poly, "ic_get_poly", pure()),
        (|h| h.ic_set_cold, "ic_set_cold", pure()),
        (|h| h.elem_mega_get, "elem_mega_get", pure()),
        (|h| h.elem_mega_set_probe, "elem_mega_set_probe", pure()),
        (|h| h.elem_append_check, "elem_append_check", pure()),
        (|h| h.str_chars_eq, "str_chars_eq", pure()),
        (|h| h.get_mapped_arg, "get_mapped_arg", pure()),
        (|h| h.to_boolean, "to_boolean", pure()),
        (|h| h.typeof_, "typeof", pure()),
        (|h| h.typeof_eq, "typeof_eq", pure()),
        (|h| h.constant_strict_eq, "constant_strict_eq", pure()),
        (|h| h.get_aliased, "get_aliased", pure()),
        (|h| h.global_this, "global_this", pure()),
        (|h| h.object, "object", pure()),
        (|h| h.symbol, "symbol", pure()),
        (|h| h.optimize_get_iterator, "optimize_get_iterator", pure()),
        (|h| h.no_extra_indexed, "no_extra_indexed", pure()),
        (|h| h.gen_is_closing, "gen_is_closing", pure()),
        (|h| h.super_base, "super_base", pure()),
        (|h| h.super_fun, "super_fun", pure()),
        // engine-state writes without GC or user code
        (
            |h| h.call_classify,
            "call_classify",
            leaf(EngineTable.bit()),
        ),
        (|h| h.ta_set_poly, "ta_set_poly", leaf_user(Elements.bit())),
        (|h| h.strlit_verify, "strlit_verify", leaf(0)),
        (
            |h| h.set_mapped_arg,
            "set_mapped_arg",
            leaf_user(slot_elems),
        ),
        (
            |h| h.validate_this_layout,
            "validate_this_layout",
            leaf(EngineTable.bit()),
        ),
        (|h| h.set_aliased, "set_aliased", leaf_user(Slot.bit())),
        (|h| h.gen_suspend, "gen_suspend", leaf_user(slot_elems)),
        (|h| h.gen_restore, "gen_restore", leaf_user(slot_elems)),
        (|h| h.gen_closing, "gen_closing", leaf_user(0)),
        (|h| h.more_iter, "more_iter", leaf_user(slot_elems)),
        (|h| h.end_iter, "end_iter", leaf_user(slot_elems)),
        (|h| h.post_write_barrier, "post_write_barrier", leaf(0)),
        (|h| h.pre_write_barrier, "pre_write_barrier", leaf(0)),
        (
            |h| h.post_write_barrier_elem,
            "post_write_barrier_elem",
            leaf(0),
        ),
        (
            |h| h.resolve_global_slot,
            "resolve_global_slot",
            leaf(EngineTable.bit()),
        ),
        (
            |h| h.resolve_global_slot_guarded,
            "resolve_global_slot_guarded",
            leaf(EngineTable.bit()),
        ),
        (
            |h| h.set_global,
            "set_global",
            leaf_user(Slot.bit() | FuseCell.bit() | EngineTable.bit()),
        ),
        (
            |h| h.binding_written,
            "binding_written",
            leaf(FuseCell.bit()),
        ),
        (
            |h| h.binding_value,
            "binding_value",
            leaf(FuseCell.bit() | EngineTable.bit()),
        ),
        (|h| h.math_unary, "math_unary", leaf(0)),
        (|h| h.math_pow, "math_pow", leaf(0)),
        (|h| h.fmod, "fmod", leaf(0)),
        (
            |h| h.init_home_object,
            "init_home_object",
            leaf_user(Slot.bit()),
        ),
        (|h| h.bind_var, "bind_var", leaf_user(0)),
        // may GC, no user code (allocation, throw paths)
        (|h| h.string, "string", quiet_alloc()),
        (|h| h.new_object, "new_object", quiet_alloc()),
        (|h| h.new_array, "new_array", quiet_alloc()),
        (|h| h.init_prop, "init_prop", quiet_alloc()),
        (|h| h.init_elem, "init_elem", quiet_alloc()),
        (|h| h.init_prop_getset, "init_prop_getset", quiet_alloc()),
        (|h| h.new_private_name, "new_private_name", quiet_alloc()),
        (|h| h.lambda, "lambda", quiet_alloc()),
        (|h| h.fun_with_proto, "fun_with_proto", quiet_alloc()),
        (|h| h.obj_with_proto, "obj_with_proto", quiet_alloc()),
        (|h| h.mutate_proto, "mutate_proto", alloc()),
        (|h| h.regexp, "regexp", quiet_alloc()),
        (|h| h.rest, "rest", quiet_alloc()),
        (|h| h.arguments_, "arguments", quiet_alloc()),
        (|h| h.arguments_env, "arguments_env", quiet_alloc()),
        // A fresh CallObject over the callee's environment (or the existing
        // env head, no allocation at all): nothing pre-existing is written.
        // A stepping alloc here would put every closure-bearing body on
        // the Dirty track from pc 0.
        (|h| h.env_setup, "env_setup", quiet_alloc()),
        (|h| h.push_lexical_env, "push_lexical_env", alloc()),
        (|h| h.push_class_body_env, "push_class_body_env", alloc()),
        (|h| h.freshen_lexical_env, "freshen_lexical_env", alloc()),
        (|h| h.recreate_lexical_env, "recreate_lexical_env", alloc()),
        (|h| h.push_var_env, "push_var_env", alloc()),
        (|h| h.enter_with, "enter_with", alloc()),
        (|h| h.init_glexical, "init_glexical", alloc()),
        (
            |h| h.box_nonstrict_this,
            "box_nonstrict_this",
            quiet_alloc(),
        ),
        (|h| h.create_this, "create_this", quiet_alloc()),
        (|h| h.create_generator, "create_generator", alloc()),
        (|h| h.gen_check_resume, "gen_check_resume", alloc()),
        (|h| h.gen_final, "gen_final", alloc()),
        (|h| h.async_reject, "async_reject", alloc()),
        (|h| h.to_async_iter, "to_async_iter", alloc()),
        // `Unknown`, not `alloc()`: the iterator protocol it consults can
        // run a user-defined `Symbol.iterator`, and `Alloc` claims never to
        // run user code. Both readers currently collapse non-quiet `Alloc`
        // into `Unknown`, so a wrong row here would only surface once
        // `Alloc`'s contract is fully honoured; keep it accurate.
        (
            |h| h.optimize_spread_call,
            "optimize_spread_call",
            unknown(),
        ),
        (|h| h.exception, "exception", quiet_alloc()),
        (|h| h.throw, "throw", quiet_alloc()),
        (|h| h.throw_with_stack, "throw_with_stack", quiet_alloc()),
        (
            |h| h.get_exception_for_finally,
            "get_exception_for_finally",
            quiet_alloc(),
        ),
        (|h| h.throw_msg, "throw_msg", quiet_alloc()),
        (|h| h.throw_set_const, "throw_set_const", quiet_alloc()),
        (
            |h| h.check_obj_coercible,
            "check_obj_coercible",
            quiet_alloc(),
        ),
        (
            |h| h.check_class_heritage,
            "check_class_heritage",
            quiet_alloc(),
        ),
        (|h| h.check_is_obj, "check_is_obj", quiet_alloc()),
        (|h| h.check_this, "check_this", quiet_alloc()),
        (|h| h.check_this_reinit, "check_this_reinit", quiet_alloc()),
        (|h| h.check_return, "check_return", quiet_alloc()),
        (|h| h.check_lexical, "check_lexical", quiet_alloc()),
        (|h| h.set_fun_name, "set_fun_name", quiet_alloc()),
        // can reach user code: the default class, listed for the census name
        (|h| h.direct_call_stub, "direct_call", unknown()),
        (|h| h.add, "add", unknown()),
        (|h| h.concat, "concat", quiet_alloc()),
        (|h| h.call, "call", unknown()),
        (|h| h.call_iter, "call_iter", unknown()),
        (|h| h.native_dispatch, "native_dispatch", unknown()),
        (|h| h.apply_fwd, "apply_fwd", unknown()),
        (|h| h.construct, "construct", unknown()),
        (|h| h.get_property, "get_property", unknown()),
        (|h| h.set_property, "set_property", unknown()),
        (|h| h.get_prop_ic_miss, "get_prop_ic_miss", unknown()),
        (|h| h.set_prop_ic_miss, "set_prop_ic_miss", unknown()),
        (|h| h.get_gname, "get_gname", unknown()),
        (|h| h.get_element, "get_element", unknown()),
        (|h| h.set_element, "set_element", unknown()),
        (|h| h.binop, "binop", unknown()),
        (|h| h.compare, "compare", unknown()),
        (|h| h.tonumeric, "tonumeric", unknown()),
        (|h| h.pos, "pos", unknown()),
        (|h| h.neg, "neg", unknown()),
        (|h| h.instanceof_, "instanceof", unknown()),
        (|h| h.del_prop, "del_prop", unknown()),
        (|h| h.tostring, "tostring", unknown()),
        (|h| h.pow, "pow", unknown()),
        // `GlobalObject::getIntrinsicValue`: a slot read off the intrinsics
        // holder, or on first use the clone of the self-hosted function
        // into it -- engine-owned heap, no user code. `unknown()` here
        // would put every self-hosted body on the Dirty track at its
        // first intrinsic read.
        (
            |h| h.get_intrinsic_cell,
            "get_intrinsic_cell",
            quiet_alloc(),
        ),
        (|h| h.get_intrinsic, "get_intrinsic", unknown()),
        (|h| h.get_name, "get_name", unknown()),
        (|h| h.bind_name, "bind_name", unknown()),
        (|h| h.get_bound_name, "get_bound_name", unknown()),
        (
            |h| h.bind_unqualified_name,
            "bind_unqualified_name",
            unknown(),
        ),
        (
            |h| h.bind_unqualified_gname,
            "bind_unqualified_gname",
            unknown(),
        ),
        (|h| h.set_name, "set_name", unknown()),
        (|h| h.del_name, "del_name", unknown()),
        (|h| h.in_, "in", unknown()),
        (|h| h.has_own, "has_own", unknown()),
        (|h| h.to_property_key, "to_property_key", unknown()),
        (|h| h.del_elem, "del_elem", unknown()),
        (|h| h.iter_, "iter", unknown()),
        (|h| h.close_iter, "close_iter", unknown()),
        (
            |h| h.close_iter_for_exception,
            "close_iter_for_exception",
            unknown(),
        ),
        (|h| h.spread_call, "spread_call", unknown()),
        (|h| h.get_prop_super, "get_prop_super", unknown()),
        (|h| h.get_elem_super, "get_elem_super", unknown()),
        (|h| h.set_prop_super, "set_prop_super", unknown()),
        (|h| h.set_elem_super, "set_elem_super", unknown()),
        (|h| h.init_elem_getset, "init_elem_getset", unknown()),
        (|h| h.check_private_field, "check_private_field", unknown()),
        (|h| h.implicit_this, "implicit_this", unknown()),
        (
            |h| h.global_decl_instantiation,
            "global_decl_instantiation",
            unknown(),
        ),
        (|h| h.builtin_object, "builtin_object", unknown()),
        (|h| h.async_await, "async_await", unknown()),
        (|h| h.async_resolve, "async_resolve", unknown()),
        (|h| h.can_skip_await, "can_skip_await", unknown()),
        (|h| h.maybe_extract_await, "maybe_extract_await", unknown()),
    ]
}

/// The per-compile lookup: one row per helper, hashed once instead of a
/// linear scan per helper call. First row wins, matching the table order.
pub fn helper_meta_map(h: &Helpers) -> HashMap<Func, HelperMeta> {
    let mut m: HashMap<Func, HelperMeta> = HashMap::default();
    for (get, _, meta) in helper_rows() {
        m.entry(get(h)).or_insert(meta);
    }
    m
}

/// The helper's field name, for census output. Unlisted = a scripted call
/// (compiled body / stub / call_indirect). Diagnostics only, so the linear
/// scan is fine.
pub fn helper_name(h: &Helpers, f: Func) -> &'static str {
    for (get, name, _) in helper_rows() {
        if get(h) == f {
            return name;
        }
    }
    "scripted/other"
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The properties in a row must agree with each other. Nothing at runtime
    /// can notice a wrong combination -- it just silently licenses keeping a
    /// fact the helper falsified -- so it is checked here.
    #[test]
    fn helper_rows_are_consistent() {
        let rows = helper_rows();
        assert!(rows.len() > 100, "helper table lost rows");
        for (_, name, m) in rows {
            let leafy = m.effect == EffectClass::Leaf;
            assert!(
                !m.quiet || m.effect == EffectClass::Alloc,
                "{name}: quiet is an Alloc-only claim"
            );
            assert!(
                !m.user_heap_writes || leafy,
                "{name}: user_heap_writes is a Leaf-only claim"
            );
            assert_eq!(
                leafy,
                m.leaf_writes & POISON == 0,
                "{name}: exactly the Leaf rows carry a write mask"
            );
        }
    }
}
