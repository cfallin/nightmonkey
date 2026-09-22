/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// The C ABI exposed by the AOT runtime library (js/src/night/runtime/). This is
// the only SpiderMonkey surface that AOT-generated Wasm code calls directly: a
// flat, POD-only C ABI (no C++ types cross the boundary). See
// js/src/night/docs/DESIGN.md section 8.1 for the full design.

#ifndef night_runtime_NightRuntime_h
#define night_runtime_NightRuntime_h

#include <stdint.h>

// Forward-declares JSContext with the correct public-API visibility (a bare
// `struct JSContext;` here would be the first declaration and pick up the
// global hidden-visibility pragma, clashing with the engine's JS_PUBLIC_API
// declaration). Only C++ engine TUs include this header; the generated Wasm
// references the exports by name.
#include "js/TypeDecls.h"

// On Wasm, mark every ABI entry point with an export_name so wasm-ld keeps it
// (the linker DCEs unreferenced functions otherwise) and exposes it under a
// stable name. No-op on native builds (used for unit-testing the helpers).
#ifdef __wasm__
#  define NIGHT_RUNTIME_EXPORT(name) __attribute__((export_name(#name), used))
#else
#  define NIGHT_RUNTIME_EXPORT(name)
#endif

// Boxed JS::Value crosses the ABI as a raw uint64_t (its raw bits); object and
// context pointers cross as wasm32 pointers. No C++ types appear here.
//
// "Can throw" helpers follow the err-flag convention: they
// return `true` on success and `false` when an exception is pending in
// cx->pendingException, writing any result through an out-param.

extern "C" {

// Every may-GC helper takes `top` (the GC scan limit) as its second
// parameter: it installs it on `cx->nightStackTop` on entry, rather than
// through a separate set-top round-trip, and `top` doubles as the
// scratch out-slot -- a helper with a boxed result writes it to
// `*(uint64_t*)top` (the slot sits at the scan boundary, excluded from the
// rooted region). The leaf helpers (to_boolean, get_aliased/set_aliased,
// get_exception_for_finally) take no `top`: they neither GC nor throw.

// Generic property get/set by atom id (the property-IC fallback path).
NIGHT_RUNTIME_EXPORT(night_runtime_get_property)
bool night_runtime_get_property(JSContext* cx, uint32_t top, uint64_t recv,
                                uint32_t atomId);
NIGHT_RUNTIME_EXPORT(night_runtime_set_property)
bool night_runtime_set_property(JSContext* cx, uint32_t top, uint64_t recv,
                                uint32_t atomId, uint64_t val, uint32_t strict);

// Property inline cache by atom id + per-site cache index. The hit
// path is emitted inline in the compiled body (a shape/generation/holder guard
// + slot load/store, no call); only a miss calls these helpers, which do the
// generic by-id access and populate the linear-memory inline cache.
// Inline GetProp IC miss helper: the compiled body emits the hit path
// (shape/generation/holder guards + slot load) inline and calls this only on a
// miss, which does the generic by-id get and populates the linear-memory inline
// cache way for `cacheIdx`. Writes the boxed result to the out-slot `*top`.
// Returns a BITSET, not a bool: bit 0 = ok (0 means an exception is pending),
// bit 1 = CLEAN, meaning the miss was served without running user code,
// allocating, GCing or changing any shape. A clean miss cannot have
// invalidated the caller's facts, so the compiled body rejoins its
// happy-path lineage instead of continuing dirty.
NIGHT_RUNTIME_EXPORT(night_runtime_get_prop_ic_miss)
uint32_t night_runtime_get_prop_ic_miss(JSContext* cx, uint32_t top,
                                        uint64_t recv, uint32_t atomId,
                                        uint32_t cacheIdx);
// Inline SetProp IC miss helper: the body emits the hit path (shape+gen
// guard
// + barriered slot store) inline and calls this only on a miss (generic by-id
// set
// + populate the linear-memory inline cache way for `cacheIdx`).
// Same bitset contract as the get side. CLEAN here covers the existing-slot
// store AND the cached add-transition replay: `NightTryAddPropTransition` is
// shape compares plus `growSlotsPure` (which asserts
// `AutoUnsafeCallWithABI`, so it cannot GC) plus `setShape` + `initSlot`, and
// none of that runs user code, moves anything, or touches the class-idx word
// the caller's `cls` facts name. The RESHAPE is invisible to the caller: it
// guards shapes by re-loading them, never by remembering them.
NIGHT_RUNTIME_EXPORT(night_runtime_set_prop_ic_miss)
uint32_t night_runtime_set_prop_ic_miss(JSContext* cx, uint32_t top,
                                        uint64_t recv, uint32_t atomId,
                                        uint64_t val, uint32_t cacheIdx,
                                        uint32_t strict);

// Static fixed-slot store post-write (generational) barrier slow path. The
// driver inlines the raw `store_i64` and the is-GC-thing/is-nursery check, and
// calls this only when `valBits` is a GC thing in the nursery, to record the
// (owner, slot) edge in the nursery store buffer (`HeapSlot::post`). A leaf (no
// GC, no throw, no `cx`/`top`): a store-buffer append never moves objects, so
// the caller needs no rooting handshake. The pre-write (incremental) barrier is
// unnecessary -- the reactor disables incremental GC. Reads are a raw load (no
// helper, no barrier); writes are a raw store + this rare barrier call.
NIGHT_RUNTIME_EXPORT(night_runtime_post_write_barrier)
void night_runtime_post_write_barrier(uint64_t ownerBits, uint32_t slot,
                                      uint64_t valBits);

// Element variant of the post-write barrier, behind the inlined dense `SetElem`
// store. Like `night_runtime_post_write_barrier` but records the
// `HeapSlot::Element` store-buffer edge; `index` is the logical dense index
// (the helper converts it to the unshifted store-buffer index from the owner).
// A leaf -- no rooting.
NIGHT_RUNTIME_EXPORT(night_runtime_post_write_barrier_elem)
void night_runtime_post_write_barrier_elem(uint64_t ownerBits, uint32_t index,
                                           uint64_t valBits);

// Static fixed-slot store pre-write (incremental-marking / snapshot-at-the-
// beginning) barrier slow path. The driver inlines the raw `store_i64` AND the
// gate -- it reads the zone's `needsIncrementalBarrier` flag inline and calls
// this (with the old slot value) only during active incremental marking, to
// mark the overwritten value. A leaf (marking is non-moving), so no rooting
// handshake.
NIGHT_RUNTIME_EXPORT(night_runtime_pre_write_barrier)
void night_runtime_pre_write_barrier(uint64_t valBits);

// Leaf Math helpers behind the inline Math.* callee-identity arms, for the
// functions with no wasm opcode. `kind`: 0 = sin, 1 = cos (routed to the same
// fdlibm/native impl the engine's Math object uses); pow is `js::ecmaPow`.
// Leaves (no GC, no throw, no cx).
NIGHT_RUNTIME_EXPORT(night_runtime_math_unary)
double night_runtime_math_unary(uint32_t kind, double x);

NIGHT_RUNTIME_EXPORT(night_runtime_math_pow)
double night_runtime_math_pow(double x, double y);

// JS `%` on two numbers (`js::NumberMod`), for range-proven-numeric Mod
// sites whose pure form has no wasm opcode. Leaf (no GC, no throw, no cx).
NIGHT_RUNTIME_EXPORT(night_runtime_fmod)
double night_runtime_fmod(double x, double y);

// Read a global binding by atom id (resolves like the interpreter's GetGName).
// `forTypeof` selects the non-throwing TypeOf-mode lookup (a `GetGName` feeding
// a `typeof` yields "undefined" for an undeclared name instead of throwing).
NIGHT_RUNTIME_EXPORT(night_runtime_get_gname)
bool night_runtime_get_gname(JSContext* cx, uint32_t top, uint32_t atomId,
                             uint32_t forTypeof);

// Global binding resolution. `night_runtime_resolve_global_slot` is the
// cold resolve-once path behind the inlined `GetGName`: on first access the
// binding's `gGlobalSlots` entry is 0 (unresolved), so the inline code calls
// this, which `lookupPure`s the pre-interned binding name on the global object
// (non-allocating, never GCs), writes the encoded entry (`bit0` resolved,
// `bit1` is-dynamic-slot, `bits[31:2]` slot index) into
// `gGlobalSlots[bindingId]`, and returns it. A leaf -- no `top`, no rooting
// handshake.
NIGHT_RUNTIME_EXPORT(night_runtime_resolve_global_slot)
uint32_t night_runtime_resolve_global_slot(JSContext* cx, uint32_t bindingId);

// GUARDED variant for syntactically-collected (no-TI) bindings: unlike the
// TI-proven resolve above, the name may be anything a `GetGName` can mention,
// so resolution can fail. Caches (and returns) the encoded entry ONLY when the
// name is an own plain data slot of the global object NOT shadowed by a global
// lexical binding; also caches the global's shape word, which the inline read
// guards against (any global-object reshape -- delete, redefine-as-accessor --
// invalidates). Returns 0 ("not cacheable"): the caller falls back to the
// generic char-based `night_runtime_get_gname`. A leaf (lookupPure, no
// allocation).
NIGHT_RUNTIME_EXPORT(night_runtime_resolve_global_slot_guarded)
uint32_t night_runtime_resolve_global_slot_guarded(JSContext* cx,
                                                   uint32_t bindingId);

// Inlined `SetGName` for a resolved global-object binding: store `valBits`
// into the binding's slot with the engine's `setSlot` write barriers (a store +
// barriers never move objects, so a leaf -- no rooting handshake). Also warms
// the `gGlobalSlots` cache so a following inline read avoids the cold resolve.
NIGHT_RUNTIME_EXPORT(night_runtime_set_global)
void night_runtime_set_global(JSContext* cx, uint32_t bindingId,
                              uint64_t valBits);
// The inline `SetGName` store unarmed the binding's value-fuse cell (its
// value changed): re-arm it from the stored value. A leaf.
NIGHT_RUNTIME_EXPORT(night_runtime_binding_written)
void night_runtime_binding_written(uint32_t bindingId);
// The binding's current value for a compiled re-proof of a carried
// per-binding value fact: the armed cell's bits, else the guarded resolve
// (refilling the gGlobalSlots row and re-arming the cell) and the slot it
// names; a name that is no longer an own plain data slot of the global
// yields a magic Value. A leaf (lookupPure + slot read).
NIGHT_RUNTIME_EXPORT(night_runtime_binding_value)
uint64_t night_runtime_binding_value(JSContext* cx, uint32_t bindingId);

// Direct construct: create the `this` object for a specialized `new` (the
// callee is a single resolved scripted constructor, direct-called inline).
// A sized site (`nSlots != 0xFFFFFFFF`) gets an empty object with fixed slots
// for every predicted layout field (delegate-assigned included); else the
// ordinary `CreateThis(callee, newTarget)` the interpreter would build.
// Writes the boxed object to the out-slot. May GC (allocates).
NIGHT_RUNTIME_EXPORT(night_runtime_create_this)
bool night_runtime_create_this(JSContext* cx, uint32_t top, uint64_t calleeBits,
                               uint64_t newTargetBits, uint32_t nSlots,
                               uint32_t cellAddr, uint32_t stampWord);

// Generic element get/set by key value.
NIGHT_RUNTIME_EXPORT(night_runtime_get_element)
bool night_runtime_get_element(JSContext* cx, uint32_t top, uint64_t recv,
                               uint64_t key);
NIGHT_RUNTIME_EXPORT(night_runtime_set_element)
bool night_runtime_set_element(JSContext* cx, uint32_t top, uint64_t recv,
                               uint64_t key, uint64_t val, uint32_t strict);

// Generic binary arithmetic/bitop and comparison by `kind`.
NIGHT_RUNTIME_EXPORT(night_runtime_binop)
bool night_runtime_binop(JSContext* cx, uint32_t top, uint32_t kind, uint64_t a,
                         uint64_t b);
NIGHT_RUNTIME_EXPORT(night_runtime_compare)
bool night_runtime_compare(JSContext* cx, uint32_t top, uint32_t kind,
                           uint64_t a, uint64_t b);

// String constant from atom id; ToNumeric coercion.
NIGHT_RUNTIME_EXPORT(night_runtime_string)
bool night_runtime_string(JSContext* cx, uint32_t top, uint32_t atomId);

// Self-hosted intrinsic value by atom-table name (JSOp::GetIntrinsic); may
// lazily clone the intrinsic from the self-hosting zone (GC/throw).
NIGHT_RUNTIME_EXPORT(night_runtime_get_intrinsic)
bool night_runtime_get_intrinsic(JSContext* cx, uint32_t top, uint32_t atomId);

// Validate an inline-materialized string literal (debug compiles only).
NIGHT_RUNTIME_EXPORT(night_runtime_strlit_verify)
bool night_runtime_strlit_verify(JSContext* cx, uint32_t strPtr,
                                 uint32_t atomId);

// Track census (diagnostic builds only): count one occurrence of (kind, id).
// The compiler emits these calls only under its `--census` switch, so a
// production module never contains one. Counts are dumped to stderr at exit.
NIGHT_RUNTIME_EXPORT(night_runtime_census)
int32_t night_runtime_census(uint32_t kind, uint32_t id);

// Leaf char-equality of two LINEAR same-length strings (inline compare arm).
NIGHT_RUNTIME_EXPORT(night_runtime_str_chars_eq)
int32_t night_runtime_str_chars_eq(uint32_t a, uint32_t b);
NIGHT_RUNTIME_EXPORT(night_runtime_tonumeric)
bool night_runtime_tonumeric(JSContext* cx, uint32_t top, uint64_t a);

// `Pos` (`+x`) slow path: ToNumber (unlike ToNumeric, throws on BigInt).
// Boxed number to the out-slot. May GC (valueOf).
NIGHT_RUNTIME_EXPORT(night_runtime_pos)
bool night_runtime_pos(JSContext* cx, uint32_t top, uint64_t a);

// `Neg` (`-x`) slow path: NegOperation (ToNumeric + negate). Boxed result to
// the out-slot. May GC (valueOf).
NIGHT_RUNTIME_EXPORT(night_runtime_neg)
bool night_runtime_neg(JSContext* cx, uint32_t top, uint64_t a);

// `l instanceof r`: the full operator (proto walk / Symbol.hasInstance).
// Boxed boolean to the out-slot; throws on a primitive/non-callable rhs.
NIGHT_RUNTIME_EXPORT(night_runtime_instanceof)
bool night_runtime_instanceof(JSContext* cx, uint32_t top, uint64_t l,
                              uint64_t r, uint32_t cellAddr);

// `delete val.name` (strict by flag): boxed boolean to the out-slot; strict
// mode throws on a non-configurable property. May GC.
NIGHT_RUNTIME_EXPORT(night_runtime_del_prop)
bool night_runtime_del_prop(JSContext* cx, uint32_t top, uint64_t val,
                            uint32_t atomId, uint32_t strict);

// For-in: `Iter` builds the PropertyIteratorObject (boxed object to the
// out-slot; may GC/throw); `MoreIter` returns the next property name or
// the NO_ITER magic (leaf); `EndIter` closes the iterator (leaf).
NIGHT_RUNTIME_EXPORT(night_runtime_iter)
bool night_runtime_iter(JSContext* cx, uint32_t top, uint64_t val);
NIGHT_RUNTIME_EXPORT(night_runtime_more_iter)
uint64_t night_runtime_more_iter(JSContext* cx, uint64_t iter);
NIGHT_RUNTIME_EXPORT(night_runtime_end_iter)
void night_runtime_end_iter(JSContext* cx, uint64_t iter);

// Destructuring try-note unwind: when an exception unwinds through a
// destructuring pattern, close its iterator unless it is already done.
// `done` is `sp[-1]` (asserted non-magic), `iter` is `sp[-2]`. Uses
// IteratorCloseForException (CompletionKind::Throw), which preserves the
// already-pending exception across a well-behaved `return()`. A caller has a
// pending exception here (we are unwinding), so no result is reported: on
// success the original exception is restored, on a throwing `return()` the new
// exception is left pending -- either way the caller propagates it.
NIGHT_RUNTIME_EXPORT(night_runtime_close_iter_for_exception)
void night_runtime_close_iter_for_exception(JSContext* cx, uint32_t top,
                                            uint64_t done, uint64_t iter);

// `Symbol code`: push the well-known symbol named by the `SymbolCode` byte
// (leaf: runtime-pinned tenured value).
NIGHT_RUNTIME_EXPORT(night_runtime_symbol)
uint64_t night_runtime_symbol(JSContext* cx, uint32_t code);

// `OptimizeGetIterator`: pure predicate -- true when `v` is an array with the
// default iteration protocol (leaf: no GC/throw).
NIGHT_RUNTIME_EXPORT(night_runtime_optimize_get_iterator)
uint32_t night_runtime_optimize_get_iterator(JSContext* cx, uint64_t v);

// `CloseIter kind`: IteratorClose on `iter` with the given CompletionKind byte.
// May run a user `return` method (GC/throw).
NIGHT_RUNTIME_EXPORT(night_runtime_close_iter)
bool night_runtime_close_iter(JSContext* cx, uint32_t top, uint64_t iter,
                              uint32_t kind);

// `ToAsyncIter`: wrap the sync iterator `iter` (+ its `next` method) in an
// async-from-sync iterator; boxed object to the out-slot. May GC.
NIGHT_RUNTIME_EXPORT(night_runtime_to_async_iter)
bool night_runtime_to_async_iter(JSContext* cx, uint32_t top, uint64_t iter,
                                 uint64_t nextMethod);

// `SpreadCall`/`SpreadNew`: call/construct `callee` spreading the packed array
// `arr` as actual args (`constructing` selects the form + `newTarget`). Result
// to the out-slot. May GC/throw.
NIGHT_RUNTIME_EXPORT(night_runtime_spread_call)
bool night_runtime_spread_call(JSContext* cx, uint32_t top, uint64_t calleeBits,
                               uint64_t thisvBits, uint64_t arrBits,
                               uint64_t newTargetBits, uint32_t constructing);

// `OptimizeSpreadCall`: forward-array-or-undefined for a spread argument `v`
// to the out-slot. May GC.
NIGHT_RUNTIME_EXPORT(night_runtime_optimize_spread_call)
bool night_runtime_optimize_spread_call(JSContext* cx, uint32_t top,
                                        uint64_t v);

// `Arguments`: build the (strict-contract: unmapped) arguments object from
// the AOT frame at `sp` (`[callee, this, args...]`, argc actuals). Boxed
// object to the out-slot. May GC (allocates).
NIGHT_RUNTIME_EXPORT(night_runtime_arguments)
bool night_runtime_arguments(JSContext* cx, uint32_t top, uint32_t sp,
                             uint32_t argc);

// Like `night_runtime_arguments` but passes the activation's environment head
// `env` (its CallObject) as the scope chain, so a mapped args object over a
// script that closes over formals forwards `arguments[i]` to the CallObject
// slot.
NIGHT_RUNTIME_EXPORT(night_runtime_arguments_env)
bool night_runtime_arguments_env(JSContext* cx, uint32_t top, uint32_t sp,
                                 uint32_t argc, uint64_t env);

// `Rest` (JSOp::Rest): build the rest array from the actual args beyond the
// formal count. `nformal` = callee.nargs() - 1 (the rest binding counts in
// nargs); the actuals live in the frame at `sp`. May GC (allocates). Boxed
// array to the out-slot.
NIGHT_RUNTIME_EXPORT(night_runtime_rest)
bool night_runtime_rest(JSContext* cx, uint32_t top, uint32_t sp, uint32_t argc,
                        uint32_t nformal);

// `ImplicitThis` (JSOp::ImplicitThis): compute the implicit `this` binding for
// an unqualified name call from the environment object `env` (undefined in
// ordinary scopes; the with-object for a with-scope). Infallible. Boxed result
// to the out-slot.
NIGHT_RUNTIME_EXPORT(night_runtime_implicit_this)
bool night_runtime_implicit_this(JSContext* cx, uint32_t top, uint64_t env);

// `CheckThisReinit` (JSOp::CheckThisReinit): throw a ReferenceError if `v` is
// NOT the uninitialized-lexical magic (i.e. `super()` already ran), else a
// no-op. Returns false on the throwing path.
NIGHT_RUNTIME_EXPORT(night_runtime_check_this_reinit)
bool night_runtime_check_this_reinit(JSContext* cx, uint32_t top, uint64_t v);

// `CheckReturn` (JSOp::CheckReturn, derived ctor): given `thisv` (sp[-1]) and
// the frame's return value `rval`, produce the checked return value to the
// out-slot: an object `rval` -> `rval`; undefined `rval` -> `thisv` (throwing
// if `thisv` is uninitialized); else the bad-derived-return TypeError.
NIGHT_RUNTIME_EXPORT(night_runtime_check_return)
bool night_runtime_check_return(JSContext* cx, uint32_t top, uint64_t thisv,
                                uint64_t rval);

// `ObjWithProto` (JSOp::ObjWithProto): `Object.create(proto)` for an object
// literal `{__proto__: proto, ...}`. `proto` must be object-or-null (else a
// TypeError). May GC. Boxed object to the out-slot.
NIGHT_RUNTIME_EXPORT(night_runtime_obj_with_proto)
bool night_runtime_obj_with_proto(JSContext* cx, uint32_t top, uint64_t proto);

// `FunWithProto` (JSOp::FunWithProto): clone the function template
// `script->getFunction(funcIndex)` with the explicit prototype `proto` and the
// enclosing environment `env` (class heritage). May GC. Boxed fn to the
// out-slot.
NIGHT_RUNTIME_EXPORT(night_runtime_fun_with_proto)
bool night_runtime_fun_with_proto(JSContext* cx, uint32_t top, uint64_t env,
                                  uint64_t proto, uint32_t script,
                                  uint32_t funcIndex);

// `SetFunName` (JSOp::SetFunName): set the inferred `name` on the anonymous
// function `fun` under the FunctionPrefixKind byte `prefixKind`. May GC/throw.
// Leaves `fun` on the stack (no out-slot).
NIGHT_RUNTIME_EXPORT(night_runtime_set_fun_name)
bool night_runtime_set_fun_name(JSContext* cx, uint32_t top, uint64_t fun,
                                uint64_t name, uint32_t prefixKind);

// `1` iff neither `obj` nor anything on its prototype chain may have extra
// indexed properties (js::ObjectMayHaveExtraIndexedProperties): the inline
// dense-append (Array.prototype.push) arm's proto guard. Leaf (pure walk).
NIGHT_RUNTIME_EXPORT(night_runtime_no_extra_indexed)
int32_t night_runtime_no_extra_indexed(uint32_t obj);

// Peek-only generator-closing check (the pending magic is NOT cleared):
// the catch-pad closing split. Leaf.
NIGHT_RUNTIME_EXPORT(night_runtime_gen_is_closing)
int32_t night_runtime_gen_is_closing(JSContext* cx);

// `key in obj` (JSOp::In): boxed boolean to the out-slot; throws when `obj`
// is not an object. May GC (proxy hooks).
NIGHT_RUNTIME_EXPORT(night_runtime_in)
bool night_runtime_in(JSContext* cx, uint32_t top, uint64_t id, uint64_t obj);

// `HasOwn` (Object.hasOwn / #in): boxed boolean to the out-slot. May GC.
NIGHT_RUNTIME_EXPORT(night_runtime_has_own)
bool night_runtime_has_own(JSContext* cx, uint32_t top, uint64_t id,
                           uint64_t val);

// `ToPropertyKey`: the coerced key (string/symbol/int) to the out-slot. May
// GC (toString/valueOf).
NIGHT_RUNTIME_EXPORT(night_runtime_to_property_key)
bool night_runtime_to_property_key(JSContext* cx, uint32_t top, uint64_t val);

// `MutateProto`: object-literal `__proto__: expr`. Sets obj's prototype when
// `proto` is object-or-null (else no-op). May GC. Leaves obj on the stack.
NIGHT_RUNTIME_EXPORT(night_runtime_mutate_proto)
bool night_runtime_mutate_proto(JSContext* cx, uint32_t top, uint64_t obj,
                                uint64_t proto);

// Super-property ops. `InitHomeObject` stores the method [[HomeObject]] in a
// function extended slot; `SuperBase`/`SuperFun` read the home-object proto /
// the derived-ctor proto; the get/set-super ops do a property access on a
// distinct `superBase` object with an explicit `receiver`. All may GC/throw
// except InitHomeObject/SuperBase/SuperFun (pure slot/proto reads).
NIGHT_RUNTIME_EXPORT(night_runtime_init_home_object)
bool night_runtime_init_home_object(JSContext* cx, uint32_t top,
                                    uint64_t fnBits, uint64_t homeBits);
NIGHT_RUNTIME_EXPORT(night_runtime_super_base)
bool night_runtime_super_base(JSContext* cx, uint32_t top, uint64_t calleeBits);
NIGHT_RUNTIME_EXPORT(night_runtime_super_fun)
bool night_runtime_super_fun(JSContext* cx, uint32_t top, uint64_t calleeBits);
NIGHT_RUNTIME_EXPORT(night_runtime_get_prop_super)
bool night_runtime_get_prop_super(JSContext* cx, uint32_t top,
                                  uint64_t recvBits, uint64_t lvalBits,
                                  uint32_t atomId);
NIGHT_RUNTIME_EXPORT(night_runtime_get_elem_super)
bool night_runtime_get_elem_super(JSContext* cx, uint32_t top,
                                  uint64_t recvBits, uint64_t keyBits,
                                  uint64_t lvalBits);
NIGHT_RUNTIME_EXPORT(night_runtime_set_prop_super)
bool night_runtime_set_prop_super(JSContext* cx, uint32_t top,
                                  uint64_t recvBits, uint64_t lvalBits,
                                  uint32_t atomId, uint64_t valBits,
                                  uint32_t strict);
NIGHT_RUNTIME_EXPORT(night_runtime_set_elem_super)
bool night_runtime_set_elem_super(JSContext* cx, uint32_t top,
                                  uint64_t recvBits, uint64_t keyBits,
                                  uint64_t lvalBits, uint64_t valBits,
                                  uint32_t strict);

// `ToString`: template-literal / explicit string coercion (calls user
// toString/valueOf; may GC/throw). Writes ToString(v) to the out-slot.
NIGHT_RUNTIME_EXPORT(night_runtime_tostring)
bool night_runtime_tostring(JSContext* cx, uint32_t top, uint64_t v);

// `Pow` (`**`): generic numeric/bigint exponentiation to the out-slot. May
// GC/throw (ToNumeric coercion of the operands).
NIGHT_RUNTIME_EXPORT(night_runtime_pow)
bool night_runtime_pow(JSContext* cx, uint32_t top, uint64_t a, uint64_t b);

// `CheckObjCoercible`: throw a TypeError if `v` is null/undefined (else no-op).
NIGHT_RUNTIME_EXPORT(night_runtime_check_obj_coercible)
bool night_runtime_check_obj_coercible(JSContext* cx, uint32_t top, uint64_t v);

// `CheckClassHeritage`: throw if the `extends` operand is not a constructor or
// null (else no-op).
NIGHT_RUNTIME_EXPORT(night_runtime_check_class_heritage)
bool night_runtime_check_class_heritage(JSContext* cx, uint32_t top,
                                        uint64_t v);

// `Generator`: create this frame's generator object; result to the out-slot.
NIGHT_RUNTIME_EXPORT(night_runtime_create_generator)
bool night_runtime_create_generator(JSContext* cx, uint32_t top,
                                    uint64_t callee, uint64_t env);

// Generator suspend: save locals + spilled live operands into the
// generator's stack storage; mark suspended at resume index `k`. Leaf.
NIGHT_RUNTIME_EXPORT(night_runtime_gen_suspend)
int32_t night_runtime_gen_suspend(JSContext* cx, uint64_t gen, uint32_t k,
                                  uint32_t localsPtr, uint32_t nlocals,
                                  uint32_t opsPtr, uint32_t nops, uint64_t env);

// Generator resume restore: copy saved state back into the frame; mark
// running. Returns the restored operand count. Leaf.
NIGHT_RUNTIME_EXPORT(night_runtime_gen_restore)
int32_t night_runtime_gen_restore(JSContext* cx, uint64_t gen,
                                  uint32_t localsPtr, uint32_t nlocals,
                                  uint32_t envPtr, uint32_t opsPtr);

// `CheckResumeKind` non-Next kinds: always raises (Throw: val; Return:
// stages val in the frame's rval slot + raises the closing magic).
NIGHT_RUNTIME_EXPORT(night_runtime_gen_check_resume)
bool night_runtime_gen_check_resume(JSContext* cx, uint32_t top, uint64_t gen,
                                    uint64_t val, uint32_t kind,
                                    uint32_t rvalAddr);

// Generator error-epilogue closing check: clear + report a pending
// JS_GENERATOR_CLOSING magic. Leaf.
NIGHT_RUNTIME_EXPORT(night_runtime_gen_closing)
int32_t night_runtime_gen_closing(JSContext* cx);

// `FinalYieldRval`: close the completed generator.
NIGHT_RUNTIME_EXPORT(night_runtime_gen_final)
bool night_runtime_gen_final(JSContext* cx, uint32_t top, uint64_t gen);

// Async-function ops: await continuation registration, result-promise
// settle, and the skip-await fast-path checks. Results to the out-slot.
NIGHT_RUNTIME_EXPORT(night_runtime_async_await)
bool night_runtime_async_await(JSContext* cx, uint32_t top, uint64_t gen,
                               uint64_t val);
NIGHT_RUNTIME_EXPORT(night_runtime_async_resolve)
bool night_runtime_async_resolve(JSContext* cx, uint32_t top, uint64_t gen,
                                 uint64_t val);
NIGHT_RUNTIME_EXPORT(night_runtime_async_reject)
bool night_runtime_async_reject(JSContext* cx, uint32_t top, uint64_t gen,
                                uint64_t reason, uint64_t stack);
NIGHT_RUNTIME_EXPORT(night_runtime_can_skip_await)
bool night_runtime_can_skip_await(JSContext* cx, uint32_t top, uint64_t val);
NIGHT_RUNTIME_EXPORT(night_runtime_maybe_extract_await)
bool night_runtime_maybe_extract_await(JSContext* cx, uint32_t top,
                                       uint64_t val, uint32_t canSkip);

// `CheckIsObj`: throw a TypeError (per CheckIsObjectKind byte) if `v` is not an
// object (else no-op).
NIGHT_RUNTIME_EXPORT(night_runtime_check_is_obj)
bool night_runtime_check_is_obj(JSContext* cx, uint32_t top, uint64_t v,
                                uint32_t kind);

// `CheckThis`: throw a ReferenceError if `this` is uninitialized (else no-op).
NIGHT_RUNTIME_EXPORT(night_runtime_check_this)
bool night_runtime_check_this(JSContext* cx, uint32_t top, uint64_t v);

// `CheckLexical`/`CheckAliasedLexical`: throw a TDZ ReferenceError if `v` is
// the uninitialized-lexical magic value (else no-op). `pcOffset` locates the op
// for the binding-name message.
NIGHT_RUNTIME_EXPORT(night_runtime_check_lexical)
bool night_runtime_check_lexical(JSContext* cx, uint32_t top, uint64_t v,
                                 uint32_t script, uint32_t pcOffset);

// `ThrowSetConst`: unconditionally throw the const-reassignment TypeError.
NIGHT_RUNTIME_EXPORT(night_runtime_throw_set_const)
void night_runtime_throw_set_const(JSContext* cx, uint32_t top, uint32_t script,
                                   uint32_t pcOffset);

// `PushLexicalEnv`: create a BlockLexicalEnvironmentObject for the scope at
// `pcOffset` over env head `env`; writes the new env to the out-slot. May GC.
NIGHT_RUNTIME_EXPORT(night_runtime_push_lexical_env)
bool night_runtime_push_lexical_env(JSContext* cx, uint32_t top, uint64_t env,
                                    uint32_t script, uint32_t pcOffset);

// `PushClassBodyEnv`: like night_runtime_push_lexical_env but a ClassBody
// lexical env.
NIGHT_RUNTIME_EXPORT(night_runtime_push_class_body_env)
bool night_runtime_push_class_body_env(JSContext* cx, uint32_t top,
                                       uint64_t env, uint32_t script,
                                       uint32_t pcOffset);

// `FreshenLexicalEnv`: clone the current innermost block lexical env (copies
// binding values) to the out-slot. May GC.
NIGHT_RUNTIME_EXPORT(night_runtime_freshen_lexical_env)
bool night_runtime_freshen_lexical_env(JSContext* cx, uint32_t top,
                                       uint64_t env);

// `RecreateLexicalEnv`: recreate the current innermost block lexical env
// (bindings reset to TDZ) to the out-slot. May GC.
NIGHT_RUNTIME_EXPORT(night_runtime_recreate_lexical_env)
bool night_runtime_recreate_lexical_env(JSContext* cx, uint32_t top,
                                        uint64_t env);

// `InitGLexical`: initialize the global lexical binding named at `pcOffset`
// with `val` (clears the TDZ). Leaves `val` on the stack (out-slot untouched).
// May not GC.
NIGHT_RUNTIME_EXPORT(night_runtime_init_glexical)
bool night_runtime_init_glexical(JSContext* cx, uint32_t top, uint64_t val,
                                 uint32_t script, uint32_t pcOffset);

// `GetName`: scope-chain read of `atomId` over env head `env` (the `with`/
// dynamic-scope general path). `forTypeof` selects the non-throwing lookup.
// Result to the out-slot. May GC/throw.
NIGHT_RUNTIME_EXPORT(night_runtime_get_name)
bool night_runtime_get_name(JSContext* cx, uint32_t top, uint64_t env,
                            uint32_t atomId, uint32_t forTypeof);

// `BindName`: push the environment object a subsequent `SetName` assigns into
// (scope-chain binding resolution with a global default). To the out-slot.
NIGHT_RUNTIME_EXPORT(night_runtime_bind_name)
bool night_runtime_bind_name(JSContext* cx, uint32_t top, uint64_t env,
                             uint32_t atomId);

// `GetBoundName`: read `atomId` from the already-bound environment `env`
// (pairs with `BindName` for compound assignments). To the out-slot. May GC.
NIGHT_RUNTIME_EXPORT(night_runtime_get_bound_name)
bool night_runtime_get_bound_name(JSContext* cx, uint32_t top, uint64_t env,
                                  uint32_t atomId);

// `BindUnqualifiedName`: binding resolution for a `name =` store over env head
// `env` (adds to the global object if undeclared). To the out-slot.
NIGHT_RUNTIME_EXPORT(night_runtime_bind_unqualified_name)
bool night_runtime_bind_unqualified_name(JSContext* cx, uint32_t top,
                                         uint64_t env, uint32_t atomId);

// `BindVar`: the var environment object for the env head `env`. To the
// out-slot. May not GC.
NIGHT_RUNTIME_EXPORT(night_runtime_bind_var)
bool night_runtime_bind_var(JSContext* cx, uint32_t top, uint64_t env);

// `DelName`: `delete name` over env head `env` -> boolean to the out-slot.
NIGHT_RUNTIME_EXPORT(night_runtime_del_name)
bool night_runtime_del_name(JSContext* cx, uint32_t top, uint64_t env,
                            uint32_t atomId);

// `PushVarEnv`: create a VarEnvironmentObject for the scope at `pcOffset` over
// env head `env`; writes the new env to the out-slot. May GC.
NIGHT_RUNTIME_EXPORT(night_runtime_push_var_env)
bool night_runtime_push_var_env(JSContext* cx, uint32_t top, uint64_t env,
                                uint32_t script, uint32_t pcOffset);

// `EnterWith`: create a WithEnvironmentObject wrapping `val` for the WithScope
// at `pcOffset` over env head `env`; writes the new env to the out-slot. May
// GC/throw (ToObject on a primitive).
NIGHT_RUNTIME_EXPORT(night_runtime_enter_with)
bool night_runtime_enter_with(JSContext* cx, uint32_t top, uint64_t env,
                              uint64_t val, uint32_t script, uint32_t pcOffset);

// `ThrowMsg`: unconditionally throw the error named by the ThrowMsgKind byte.
NIGHT_RUNTIME_EXPORT(night_runtime_throw_msg)
void night_runtime_throw_msg(JSContext* cx, uint32_t top, uint32_t kind);

// `BuiltinObject`: the builtin object named by the BuiltinObjectKind byte to
// the out-slot. May GC.
NIGHT_RUNTIME_EXPORT(night_runtime_builtin_object)
bool night_runtime_builtin_object(JSContext* cx, uint32_t top, uint32_t kind);
NIGHT_RUNTIME_EXPORT(night_runtime_builtin_object_cell)
bool night_runtime_builtin_object_cell(JSContext* cx, uint32_t top,
                                       uint32_t kind, uint32_t cellAddr);

// `DelElem`/`StrictDelElem`: boxed boolean to the out-slot; strict throws on
// a non-configurable element. May GC.
NIGHT_RUNTIME_EXPORT(night_runtime_del_elem)
bool night_runtime_del_elem(JSContext* cx, uint32_t top, uint64_t val,
                            uint64_t key, uint32_t strict);

// `GlobalThis`: the global lexical `this` object to the out-slot. Leaf.
NIGHT_RUNTIME_EXPORT(night_runtime_global_this)
bool night_runtime_global_this(JSContext* cx, uint32_t top);
NIGHT_RUNTIME_EXPORT(night_runtime_box_nonstrict_this)
bool night_runtime_box_nonstrict_this(JSContext* cx, uint32_t top,
                                      uint64_t thisv);
NIGHT_RUNTIME_EXPORT(night_runtime_get_mapped_arg)
uint64_t night_runtime_get_mapped_arg(uint64_t objBits, uint32_t i);
NIGHT_RUNTIME_EXPORT(night_runtime_set_mapped_arg)
void night_runtime_set_mapped_arg(uint64_t objBits, uint32_t i, uint64_t val);
NIGHT_RUNTIME_EXPORT(night_runtime_validate_this_layout)
void night_runtime_validate_this_layout(uint64_t thisBits, uint32_t layoutId);

// `RegExp`: clone the regexp literal `gcthing[index]` of `script`. May GC.
NIGHT_RUNTIME_EXPORT(night_runtime_regexp)
bool night_runtime_regexp(JSContext* cx, uint32_t top, void* script,
                          uint32_t index);

// `InitPropGetter`/`InitPropSetter` (+Hidden forms): define the accessor
// `atomId` on `obj` with callable `fn`. `kind` bit0 = setter, bit1 = hidden
// (non-enumerable). May GC.
NIGHT_RUNTIME_EXPORT(night_runtime_init_prop_getset)
bool night_runtime_init_prop_getset(JSContext* cx, uint32_t top, uint64_t obj,
                                    uint32_t atomId, uint64_t fn,
                                    uint32_t kind);

// JS ToBoolean: a pure structural test on the value (never runs user code,
// allocates, or throws). Returns 1 for truthy, 0 for falsy.
NIGHT_RUNTIME_EXPORT(night_runtime_to_boolean)
int32_t night_runtime_to_boolean(JSContext* cx, uint64_t a);

// `typeof a`: returns the type string (a runtime-pinned common atom), boxed.
// Leaf: no GC, no throw.
NIGHT_RUNTIME_EXPORT(night_runtime_typeof)
uint64_t night_runtime_typeof(JSContext* cx, uint64_t a);
// Fused `typeof a CMP "type"` (`TypeofEq`): `operand` is the TypeofEqOperand
// byte (low bits = JSType, 0x80 = `!==`). Infallible leaf; returns 0/1.
NIGHT_RUNTIME_EXPORT(night_runtime_typeof_eq)
int32_t night_runtime_typeof_eq(JSContext* cx, uint64_t a, uint32_t operand);
// Strict-equality of `a` against an immediate constant (`StrictConstantEq`;
// `operand` is the ConstantCompareOperand uint16). Infallible leaf; returns 0/1
// (the `Ne` form is the translator negating this).
NIGHT_RUNTIME_EXPORT(night_runtime_constant_strict_eq)
int32_t night_runtime_constant_strict_eq(JSContext* cx, uint64_t a,
                                         uint32_t operand);

// `BindUnqualifiedGName atomId`: push the binding object for a global-name
// assignment (the global object for an undeclared name). May GC/throw.
NIGHT_RUNTIME_EXPORT(night_runtime_bind_unqualified_gname)
bool night_runtime_bind_unqualified_gname(JSContext* cx, uint32_t top,
                                          uint32_t atomId);
// `SetGName`/`SetName` (+ strict forms) `atomId`: assign `val` to the name on
// the binding object `env`; `strict` picks strict-mode error semantics. May
// GC/throw.
NIGHT_RUNTIME_EXPORT(night_runtime_set_name)
bool night_runtime_set_name(JSContext* cx, uint32_t top, uint64_t env,
                            uint32_t atomId, uint64_t val, uint32_t strict);

// Object/array literal construction.
// `night_runtime_new_object` creates an empty `{}`; `night_runtime_new_array`
// an array of `length` holes; the `init_*` helpers define own data properties
// on the literal under construction (`attrs` is an INIT_ATTR_* kind, see
// translate.rs). `cell` is the site's inline-alloc cell (0 = none): the helper
// fills it from the object it allocates so the compiled site can bump-allocate
// inline next time.
NIGHT_RUNTIME_EXPORT(night_runtime_new_object)
bool night_runtime_new_object(JSContext* cx, uint32_t top, uint32_t cell);
NIGHT_RUNTIME_EXPORT(night_runtime_new_array)
bool night_runtime_new_array(JSContext* cx, uint32_t top, uint32_t length,
                             uint32_t cell);
NIGHT_RUNTIME_EXPORT(night_runtime_init_prop)
bool night_runtime_init_prop(JSContext* cx, uint32_t top, uint64_t obj,
                             uint32_t atomId, uint64_t val, uint32_t attrs,
                             uint32_t cacheIdx);
NIGHT_RUNTIME_EXPORT(night_runtime_init_elem)
bool night_runtime_init_elem(JSContext* cx, uint32_t top, uint64_t obj,
                             uint64_t key, uint64_t val, uint32_t attrs);

// `InitElemGetter`/`InitElemSetter` (+Hidden forms): define the accessor with a
// computed key `key` on `obj` with callable `fn`. `kind` bit0 = setter, bit1 =
// hidden (non-enumerable, class bodies). May GC/throw (ToPropertyKey).
NIGHT_RUNTIME_EXPORT(night_runtime_init_elem_getset)
bool night_runtime_init_elem_getset(JSContext* cx, uint32_t top, uint64_t obj,
                                    uint64_t key, uint64_t fn, uint32_t kind);

// `CheckPrivateField`: private-field brand/presence check. `obj`/`key` are the
// receiver and the private-name symbol; `cond`/`kind` are the ThrowCondition
// and ThrowMsgKind immediate bytes. Writes the presence bool to the out-slot;
// may throw per the ThrowCondition. May GC.
NIGHT_RUNTIME_EXPORT(night_runtime_check_private_field)
bool night_runtime_check_private_field(JSContext* cx, uint32_t top,
                                       uint64_t obj, uint64_t key,
                                       uint32_t cond, uint32_t kind);

// `NewPrivateName atomId`: create a fresh private-name symbol whose description
// is the atom `atomId` (a `#x` class member). Writes the boxed symbol to the
// out-slot. May GC.
NIGHT_RUNTIME_EXPORT(night_runtime_new_private_name)
bool night_runtime_new_private_name(JSContext* cx, uint32_t top,
                                    uint32_t atomId);

// Closure support. `night_runtime_env_setup` builds the
// function's environment head from its compiled-body frame at `sp` (an empty
// CallObject over `callee->environment()`, or that environment itself), boxed
// into the out-slot. `night_runtime_get_aliased`/`night_runtime_set_aliased`
// read/write an environment slot after walking `hops` enclosing links (leaf: no
// GC/throw). `night_runtime_lambda` clones the function template
// `script->getFunction(funcIndex)` capturing `env`. `night_runtime_env_setup`
// takes the body's own `script` (compiled-body ABI 5th arg) so it returns the
// global lexical environment for a global script (spec 2b).
NIGHT_RUNTIME_EXPORT(night_runtime_env_setup)
bool night_runtime_env_setup(JSContext* cx, uint32_t top, uint32_t sp,
                             uint32_t script);

// Top-level (global) script support (spec 2c / Object).
// `night_runtime_global_decl_ instantiation` runs the global script's pc-0 op
// (instantiate hoisted global function/var declarations onto the global; may
// GC). `night_runtime_object` pushes a precompiled run-once object
// `script->getObject(idx)` (leaf: no GC/throw).
NIGHT_RUNTIME_EXPORT(night_runtime_global_decl_instantiation)
bool night_runtime_global_decl_instantiation(JSContext* cx, uint32_t top,
                                             uint32_t script,
                                             uint32_t gcthingIndex);
NIGHT_RUNTIME_EXPORT(night_runtime_object)
uint64_t night_runtime_object(JSContext* cx, uint32_t script,
                              uint32_t gcthingIndex);
NIGHT_RUNTIME_EXPORT(night_runtime_get_aliased)
uint64_t night_runtime_get_aliased(JSContext* cx, uint64_t env, uint32_t hops,
                                   uint32_t slot);
NIGHT_RUNTIME_EXPORT(night_runtime_set_aliased)
void night_runtime_set_aliased(JSContext* cx, uint64_t env, uint32_t hops,
                               uint32_t slot, uint64_t val);
NIGHT_RUNTIME_EXPORT(night_runtime_lambda)
bool night_runtime_lambda(JSContext* cx, uint32_t top, uint64_t env,
                          uint32_t script, uint32_t funcIndex);

// Exceptions. `night_runtime_exception` gets and clears the
// pending exception (the `Exception` op), boxed into the out-slot (false on
// interrupt). `night_runtime_throw` sets `val` as the pending exception with a
// captured stack (the `Throw` op).
NIGHT_RUNTIME_EXPORT(night_runtime_exception)
bool night_runtime_exception(JSContext* cx, uint32_t top);
NIGHT_RUNTIME_EXPORT(night_runtime_throw)
void night_runtime_throw(JSContext* cx, uint32_t top, uint64_t val);
// `ThrowWithStack` (finally re-raise): re-throw `val` with the saved `stack`.
NIGHT_RUNTIME_EXPORT(night_runtime_throw_with_stack)
void night_runtime_throw_with_stack(JSContext* cx, uint32_t top, uint64_t val,
                                    uint64_t stack);
// A finally's exceptional entry: read+clear the pending exception value/stack.
// A leaf (no GC), so no `top`. Returns false when NO exception is pending
// (an uncatchable error, e.g. termination): the finally body must not run.
NIGHT_RUNTIME_EXPORT(night_runtime_get_exception_for_finally)
bool night_runtime_get_exception_for_finally(JSContext* cx, uint64_t* excOut,
                                             uint64_t* stackOut);

// Generic binary add.
NIGHT_RUNTIME_EXPORT(night_runtime_add)
bool night_runtime_add(JSContext* cx, uint32_t top, uint64_t a, uint64_t b);

NIGHT_RUNTIME_EXPORT(night_runtime_concat)
bool night_runtime_concat(JSContext* cx, uint32_t top, uint64_t a, uint64_t b);

// Call-site specialization: classify the runtime callee `calleeBits`
// (a boxed Value). Returns `(JSScript* << 32) | nightFuncIndex` (non-zero low
// half) when it is an interpreted JSFunction with a compiled AOT body, so the
// caller can dispatch via `call_indirect`; returns 0 for native / not-compiled
// callees (fall back to `night_runtime_call`). Leaf: no GC, no allocation.
NIGHT_RUNTIME_EXPORT(night_runtime_callee_night_target)
uint64_t night_runtime_callee_night_target(uint64_t calleeBits);

// Generic call: invoke the callee in the frame at `sp` with `argc` args
// Writes the return value to the out-slot at `top`.
NIGHT_RUNTIME_EXPORT(night_runtime_call)
bool night_runtime_call(JSContext* cx, uint32_t top, uint32_t sp,
                        uint32_t argc);

// `night_runtime_call` for a `CallIter`/`CallContentIter` site: a primitive
// callee reports the iterable (the frame's `this`) as not iterable, the way
// the interpreter does, instead of the callee as not a function.
NIGHT_RUNTIME_EXPORT(night_runtime_call_iter)
bool night_runtime_call_iter(JSContext* cx, uint32_t top, uint32_t sp,
                             uint32_t argc);

// Lean native dispatch: the callee in the frame at `sp` was already proved a
// pristine builtin native by a callee-identity cell (String.prototype
// direct-dispatch arms), so skip night_runtime_call's classify/apply/rope
// machinery -- recursion check, AutoRealm, `fun->native()(cx, argc, frame)`,
// result to the out-slot at `top`. Falls back correctly only for a genuine
// native callee.
NIGHT_RUNTIME_EXPORT(night_runtime_native_dispatch)
bool night_runtime_native_dispatch(JSContext* cx, uint32_t top, uint32_t sp,
                                   uint32_t argc);

// Compile-time apply-forward: a recognized
// `T.apply(thisArg, arguments)` super-call whose `arguments` is only forwarded.
// Enters T's compiled AOT body directly with the caller's live actuals (at
// `callerSp[2..2+callerArgc]`), no arguments object; faithfully reconstructs
// the call on the cold fallback. Result boxed to the out-slot at `top`.
NIGHT_RUNTIME_EXPORT(night_runtime_apply_fwd)
bool night_runtime_apply_fwd(JSContext* cx, uint32_t top, uint64_t applyFnBits,
                             uint64_t targetBits, uint64_t thisBits,
                             uint32_t callerSp, uint32_t callerArgc);

// Generic construct (`new`): the frame at `sp` is
// [callee, this_placeholder, arg0..arg_{argc-1}, newTarget]; build the object
// via JS::Construct and write it to the out-slot at `top`.
// `nSlots` is the construct site's predicted fixed-slot count (the resolved
// ctor's full layout row length, so `this` is born with room for every
// predicted field), or `0xFFFFFFFF` for the default this-creation.
NIGHT_RUNTIME_EXPORT(night_runtime_construct)
bool night_runtime_construct(JSContext* cx, uint32_t top, uint32_t sp,
                             uint32_t argc, uint32_t nSlots,
                             uint32_t stampWord);

// Host print of a single boxed Value (one of the allowlisted opaque globals).
NIGHT_RUNTIME_EXPORT(night_runtime_print)
void night_runtime_print(JSContext* cx, uint64_t val);

// Miss arm of the inline intrinsic value-cell read (GetIntrinsic): resolve
// the intrinsic by pre-interned atom id, write the boxed result to the
// out-slot, and arm the 8-byte cell at `cellAddr` when the value is safe to
// cache (tenured GC thing, or a primitive with nonzero raw bits). The cell
// region is zeroed on major GC.
NIGHT_RUNTIME_EXPORT(night_runtime_get_intrinsic_cell)
bool night_runtime_get_intrinsic_cell(JSContext* cx, uint32_t top,
                                      uint32_t atomId, uint32_t cellAddr);

// Case-insensitive backreference compare for AOT regex matchers (two-byte
// subjects only): wraps irregexp's CaseInsensitiveCompare{NonUnicode,Unicode}.
// Leaf (no GC, no throw). Returns 1 on match.
NIGHT_RUNTIME_EXPORT(night_runtime_regex_ci_compare)
int32_t night_runtime_regex_ci_compare(uint32_t a_ptr, uint32_t b_ptr,
                                       uint32_t byte_len, uint32_t unicode);

}  // extern "C"

#endif  // night_runtime_NightRuntime_h
