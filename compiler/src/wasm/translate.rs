//! AOT Wasm codegen: the opcode-translation engine.
//!
//! Abstract-interprets a script's bytecode into a waffle SSA `FunctionBody`
//! honoring the JS-to-JS ABI (`(cx, sp, argc, retval_out, script,
//! new_target) -> err`),
//! rooting, and operand-location tracking. It emits the **generic-helper**
//! forms for property access and calls, plus guarded dynamic fast paths driven
//! by the intraprocedural prepass and the likely-facts hints.
//!
//! Each op has one `(Block, AbstractState)` entry and one exit.
//!
//! Selection is **capability-gated** (`is_supported`): a script is compiled
//! iff every op it contains is translatable; otherwise it is left interpreted
//! (`nightFuncIndex = 0`). A script is never partially compiled -- that would be
//! a miscompile, not a fallback.

use waffle::{
    Block, BlockTarget, Func, FuncDecl, FunctionBody, Memory, MemoryArg, Module, Operator,
    Signature, SignatureData, Table, Terminator, Type, Value, ValueDef,
};

use crate::bytecode::{JSOp, OpcodeVisitor, Script};
use crate::options::Options;
use crate::source::{ScopeData, Source, SourceObject};
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

/// Resolved runtime-helper function indices in the merged module + the shared
/// memory, threaded into the translator so it can emit calls to the runtime
/// helper ABI.
#[derive(Clone, Copy)]
pub struct Helpers {
    pub mem: Memory,
    /// The shared JS-to-JS compiled-body ABI signature `(cx, sp, argc,
    /// retval_out, script,
    /// new_target i64) -> err`. Every compiled body has this type, and a
    /// specialized call site `call_indirect`s through it.
    pub night_abi_sig: Signature,
    /// The shared `__indirect_function_table` (C function-pointer table). The
    /// appended bodies live here; a specialized call dispatches through it with
    /// the callee's `nightFuncIndex`.
    pub indirect_table: Table,
    /// `night_runtime_callee_night_target(callee) -> i64` (leaf): classify a call target;
    /// non-zero packs `(JSScript* << 32) | nightFuncIndex` for a `call_indirect`,
    /// zero means fall back to the generic helper.
    pub callee_night_target: Func,
    /// An inert `night_abi_sig` function used as the initial target of a Direct
    /// call's emitted `call` instruction. After placement the caller rewrites the
    /// `function_index` to the resolved callee (and the constant-folded guard to
    /// take the direct arm); a callee that turned out uncompiled leaves the call
    /// pointing here in the dead (folded-out) arm, so it is never executed. It
    /// must exist with the right signature so the dead arm still validates.
    pub direct_call_stub: Func,
    /// The WIDENED ABI for compiled-to-compiled direct calls (call-round
    /// part 2): same params, multivalue returns `(err, eff)` where `eff`
    /// is the effect-provenance flag (1 = this invocation provably ran no
    /// GC and no heap mutation, so the caller's facts survive; 0 = assume
    /// everything). BBV-lane bodies carry this signature; the C-visible
    /// funcref table holds per-script `night_abi_sig` adapters that call
    /// the body and drop `eff`, so runtime entries and `call_indirect`
    /// never see multivalue.
    pub night_abi_sig2: Signature,
    /// Inert `night_abi_sig2` stub: the initial target of a BBV direct
    /// call, rewritten at placement exactly as `direct_call_stub`.
    pub direct_call_stub2: Func,
    /// `night_runtime_add(cx, a, b, out) -> ok` (generic JS `+`).
    pub add: Func,
    /// `night_runtime_concat(cx, top, a, b) -> ok`: string concat for a
    /// pair the compiled arm proved both-string. Quiet alloc -- no user
    /// code, no pre-existing-heap writes.
    pub concat: Func,
    /// `night_runtime_call(cx, sp, argc, out) -> ok` (generic call).
    pub call: Func,
    /// `night_runtime_call` for a `CallIter`/`CallContentIter` site: a
    /// primitive callee reports the iterable as not iterable.
    pub call_iter: Func,
    /// `night_runtime_native_dispatch(cx, top, sp, argc) -> ok`: lean native invoke
    /// for a callee already proved (by identity cell) a pristine builtin --
    /// recursion check + AutoRealm + `fun->native()`, no classify/apply/rope
    /// machinery. Used by the String.prototype direct-dispatch arms (Part B).
    pub native_dispatch: Func,
    /// `night_runtime_apply_fwd(cx, top, applyFn, target, this, callerSp, callerArgc)
    /// -> ok`: compile-time apply-forward for `T.apply(this,arguments)`.
    pub apply_fwd: Func,
    /// `night_runtime_construct(cx, sp, argc, out) -> ok` (generic `new`; the frame is
    /// `[callee, this_placeholder, arg0..arg_{argc-1}, newTarget]`).
    pub construct: Func,
    /// `night_runtime_get_property(cx, recv, atomId, out) -> ok`: the generic
    /// property get helper.
    pub get_property: Func,
    /// `night_runtime_set_property(cx, recv, atomId, val) -> ok`: the generic
    /// property set helper.
    pub set_property: Func,
    /// `night_runtime_get_prop_ic_miss(cx, top, recv, atomId, cacheIdx) -> ok`
    /// (the property-IC miss helper): the
    /// miss helper behind the inline GetProp hit path. The compiled body emits
    /// the shape/generation/holder guards + slot load inline and calls this only
    /// on a miss (generic get + populate the linear-memory inline cache way).
    pub get_prop_ic_miss: Func,
    /// `night_runtime_set_prop_ic_miss(cx, top, recv, atomId, val, cacheIdx) ->
    /// ok` (the property-IC miss helper):
    /// the miss helper behind the inline SetProp hit path. The body emits the
    /// shape+gen guard + barriered slot store inline and calls this only on a miss
    /// (generic set + populate the linear-memory inline cache way).
    pub set_prop_ic_miss: Func,
    /// `night_runtime_get_gname(cx, atomId, out) -> ok` (global-name read).
    pub get_gname: Func,
    /// `night_runtime_get_element(cx, recv, key, out) -> ok` (element read).
    pub get_element: Func,
    /// `night_runtime_set_element(cx, recv, key, val) -> ok` (element write).
    pub set_element: Func,
    /// In-module `night_ta_get(objptr, idx) -> boxed` (magic bits = miss):
    /// polymorphic typed-array element read for sites with no (or a wrong)
    /// compile-time kind prediction. Pure leaf (no GC, no engine crossing).
    pub ta_get_poly: Func,
    /// In-module `night_ta_set(objptr, idx, val) -> stored?` (0 = miss): the
    /// store-side twin of `ta_get_poly`. Pure leaf.
    pub ta_set_poly: Func,
    /// In-module `night_ic_get(recvBoxed, atomId, wayBase) -> boxed` (magic
    /// bits = miss): the generic property-get IC probe, emitted once and
    /// called from every fact-free read site. Pure leaf.
    pub ic_get_poly: Func,
    /// In-module `night_ic_set_cold(shape, way_base, atom) -> packed`:
    /// the fact-free SetProp cold validation (mega probe + transition
    /// guards), once per module (see `build_ic_set_cold_helper`).
    pub ic_set_cold: Func,
    /// In-module `night_elem_mega_get(objptr, keyBoxed) -> boxed` (magic
    /// bits = miss): by-value string-keyed element read through the mega-get
    /// table's elem key namespace. Pure leaf.
    pub elem_mega_get: Func,
    /// In-module `night_elem_mega_set_probe(objptr, keyBoxed) -> entry`
    /// (0 = miss): the write-side probe; the site does the barriered store
    /// off the returned row. Pure leaf.
    pub elem_mega_set_probe: Func,
    /// `night_runtime_census(kind, id) -> 0`: the dynamic per-site counter
    /// behind `Instrumentation::census`. `None` when the shell predates the
    /// helper -- a snapshot taken from an older build still compiles, it just
    /// cannot be instrumented.
    pub census: Option<Func>,
    /// In-module `night_call_classify(calleeBoxed, cellAddr, trashAddr) ->
    /// (funcidx, script, isNative)`: the generic callee classify behind every
    /// call site's inline cell probe. Leaf; writes the cell row only.
    pub call_classify: Func,
    /// In-module `night_elem_append_check(objptr, elements, initlen, idx) ->
    /// (row << 32) | elemAddr` (0 = no): proves a dense append or hole store
    /// is legal and returns where to put it. Pure leaf; the stores stay at
    /// the site, which is what keeps their receiver classification.
    pub elem_append_check: Func,
    /// `night_runtime_binop(cx, kind, a, b, out) -> ok` (generic Sub/Mul/Div/Mod/bitops).
    pub binop: Func,
    /// `night_runtime_compare(cx, kind, a, b, out) -> ok` (generic compares -> boolean).
    pub compare: Func,
    /// `night_runtime_string(cx, atomId, out) -> ok` (string constant from atom table).
    pub string: Func,
    /// `night_runtime_get_intrinsic_cell(cx, top, atomId, cellAddr) -> ok`: resolve a
    /// self-hosted intrinsic by name and populate the per-intrinsic value
    /// cell (tenured values only; the region is zeroed on major GC). The
    /// slow arm behind the inline armed-cell read.
    pub get_intrinsic_cell: Func,
    /// `night_runtime_get_intrinsic(cx, atomId, out) -> ok` (self-hosted intrinsic
    /// value by name; may lazily clone from the self-hosting zone).
    pub get_intrinsic: Func,
    /// `night_runtime_strlit_verify(cx, strPtr, atomId)` (leaf; debug only):
    /// crash if the inline-materialized string mismatches the atom table
    /// entry.
    pub strlit_verify: Func,
    /// `night_runtime_str_chars_eq(aPtr, bPtr) -> 0/1` (pure leaf): char equality of
    /// two linear same-length strings (the inline compare arm's residual).
    pub str_chars_eq: Func,
    /// `night_runtime_tonumeric(cx, a, out) -> ok` (ToNumeric coercion).
    pub tonumeric: Func,
    /// `night_runtime_pos(cx, top, a) -> ok` (ToNumber; unlike ToNumeric, throws on
    /// BigInt) -- the `Pos` slow path.
    pub pos: Func,
    /// `night_runtime_neg(cx, top, a) -> ok` (`NegOperation`: ToNumeric + negate) --
    /// the `Neg` non-number slow path.
    pub neg: Func,
    /// `night_runtime_instanceof(cx, top, l, r) -> ok` (the full `instanceof`
    /// operator incl. Symbol.hasInstance; boxed boolean out).
    pub instanceof_: Func,
    /// `night_runtime_del_prop(cx, top, val, atomId, strict) -> ok`
    /// (`delete obj.name`; boxed boolean out; strict throws on
    /// non-configurable).
    pub del_prop: Func,
    /// `night_runtime_mutate_proto(cx, top, obj i64, proto i64) -> ok`: object-literal
    /// `__proto__: expr` (`JSOp::MutateProto`); sets `obj`'s prototype to
    /// `proto` when `proto` is object-or-null, else a no-op. Leaves `obj`.
    pub mutate_proto: Func,
    /// `night_runtime_init_home_object(cx, top, fn i64, homeObj i64) -> ok`:
    /// `JSOp::InitHomeObject`; stores `homeObj` as `fn`'s `[[HomeObject]]`. Leaves
    /// `fn`.
    pub init_home_object: Func,
    /// `night_runtime_super_base(cx, top, callee i64) -> ok`: `JSOp::SuperBase`; writes
    /// the callee method's home-object `[[Prototype]]` (object-or-null).
    pub super_base: Func,
    /// `night_runtime_super_fun(cx, top, callee i64) -> ok`: `JSOp::SuperFun`; writes the
    /// derived-ctor `[[Prototype]]` (object-or-null). Unreachable for now.
    pub super_fun: Func,
    /// `night_runtime_get_prop_super(cx, top, recv i64, superBase i64, atomId i32) -> ok`:
    /// `JSOp::GetPropSuper`; GetProperty(superBase, name) with `recv` receiver.
    pub get_prop_super: Func,
    /// `night_runtime_get_elem_super(cx, top, recv i64, key i64, superBase i64) -> ok`:
    /// `JSOp::GetElemSuper`; computed-key variant.
    pub get_elem_super: Func,
    /// `night_runtime_set_prop_super(cx, top, recv i64, superBase i64, atomId i32, val
    /// i64, strict i32) -> ok`: `JSOp::SetPropSuper`/`StrictSetPropSuper`; writes
    /// `val` back to the out-slot.
    pub set_prop_super: Func,
    /// `night_runtime_set_elem_super(cx, top, recv i64, key i64, superBase i64, val i64,
    /// strict i32) -> ok`: `JSOp::SetElemSuper`/`StrictSetElemSuper`.
    pub set_elem_super: Func,
    /// `night_runtime_tostring(cx, top, v i64) -> ok`: `JSOp::ToString` (template-literal
    /// coercion); writes `ToString(v)` to the out-slot. May GC/throw.
    pub tostring: Func,
    /// `night_runtime_pow(cx, top, a i64, b i64) -> ok`: `JSOp::Pow` (`**`); generic
    /// numeric/bigint exponentiation to the out-slot. May GC/throw.
    pub pow: Func,
    /// `night_runtime_check_obj_coercible(cx, top, v i64) -> ok`: `JSOp::CheckObjCoercible`
    /// -- throws a TypeError if `v` is null/undefined, else leaves it.
    pub check_obj_coercible: Func,
    /// `night_runtime_check_class_heritage(cx, top, v i64) -> ok`:
    /// `JSOp::CheckClassHeritage` -- throws if `v` is not a constructor or null.
    pub check_class_heritage: Func,
    /// `night_runtime_create_generator(cx, top, callee i64, env i64) -> ok`:
    /// `JSOp::Generator` -- create the GeneratorObject for this frame
    /// (callee/env/subtype). May GC; result to the out-slot.
    pub create_generator: Func,
    /// `night_runtime_gen_suspend(cx, gen i64, k i32, locals_ptr i32, nlocals i32,
    /// ops_ptr i32, nops i32, env i64) -> i32`: save the frame's locals +
    /// live operands into the generator's stack storage and mark it
    /// suspended at resume index `k`. Leaf (in-capacity dense writes; no GC).
    pub gen_suspend: Func,
    /// `night_runtime_gen_restore(cx, gen i64, locals_ptr i32, nlocals i32,
    /// env_ptr i32, ops_ptr i32) -> i32`: copy the generator's saved state
    /// back into the frame (locals, operands, env head), mark it running.
    /// Leaf (no GC); returns the restored operand count (unused).
    pub gen_restore: Func,
    /// `night_runtime_gen_check_resume(cx, top, gen i64, val i64, kind i32,
    /// rval_addr i32) -> ok`: non-Next resume kinds; always raises -- Throw:
    /// pending exception = val; Return: stages val in the frame's rval slot
    /// and raises the JS_GENERATOR_CLOSING magic (finallys run; the
    /// generator error epilogue converts it into a normal return).
    pub gen_check_resume: Func,
    /// `night_runtime_gen_closing(cx) -> i32`: if the pending exception is the
    /// JS_GENERATOR_CLOSING magic, clear it and return 1 (the error
    /// epilogue then returns the rval register normally); else 0. Leaf.
    pub gen_closing: Func,
    /// `night_runtime_gen_final(cx, top, gen i64) -> ok`: `JSOp::FinalYieldRval` --
    /// close the completed generator (the interpreter's finalSuspend).
    pub gen_final: Func,
    /// `night_runtime_async_await(cx, top, gen i64, val i64) -> ok`:
    /// `JSOp::AsyncAwait` -- register the await continuation; the promise
    /// the initial call returns goes to the out-slot.
    pub async_await: Func,
    /// `night_runtime_async_resolve(cx, top, gen i64, val i64) -> ok`:
    /// `JSOp::AsyncResolve` -- fulfill the result promise (to the out-slot).
    pub async_resolve: Func,
    /// `night_runtime_async_reject(cx, top, gen i64, reason i64, stack i64) -> ok`:
    /// `JSOp::AsyncReject` -- reject the result promise (to the out-slot).
    pub async_reject: Func,
    /// `night_runtime_can_skip_await(cx, top, val i64) -> ok`: `JSOp::CanSkipAwait`
    /// -- boolean to the out-slot.
    pub can_skip_await: Func,
    /// `night_runtime_maybe_extract_await(cx, top, val i64, canSkip i32) -> ok`:
    /// `JSOp::MaybeExtractAwaitValue` -- the (maybe-)extracted value to the
    /// out-slot.
    pub maybe_extract_await: Func,
    /// `night_runtime_check_is_obj(cx, top, v i64, kind i32) -> ok`: `JSOp::CheckIsObj`
    /// -- throws a TypeError if `v` is not an object, else leaves it.
    pub check_is_obj: Func,
    /// `night_runtime_check_this(cx, top, v i64) -> ok`: `JSOp::CheckThis` -- throws a
    /// ReferenceError if `this` is the uninitialized-lexical magic, else leaves it.
    pub check_this: Func,
    /// `night_runtime_check_lexical(cx, top, v i64, script i32, pc i32) -> ok`:
    /// `JSOp::CheckLexical`/`CheckAliasedLexical` -- throws a TDZ ReferenceError
    /// if `v` is the uninitialized-lexical magic, else leaves it.
    pub check_lexical: Func,
    /// `night_runtime_throw_set_const(cx, top, script i32, pc i32)`: `JSOp::ThrowSetConst`
    /// -- unconditionally throws the const-reassignment TypeError.
    pub throw_set_const: Func,
    /// `night_runtime_push_lexical_env(cx, top, env i64, script i32, pc i32) -> ok`:
    /// `JSOp::PushLexicalEnv` -- creates a block lexical env for the scope at
    /// `pc` over `env`, writing the new env to the out-slot.
    pub push_lexical_env: Func,
    /// `night_runtime_push_class_body_env(cx, top, env i64, script i32, pc i32) -> ok`:
    /// `JSOp::PushClassBodyEnv` -- like `push_lexical_env` but a class-body env.
    pub push_class_body_env: Func,
    /// `night_runtime_freshen_lexical_env(cx, top, env i64) -> ok`:
    /// `JSOp::FreshenLexicalEnv` -- clones the current block lexical env.
    pub freshen_lexical_env: Func,
    /// `night_runtime_recreate_lexical_env(cx, top, env i64) -> ok`:
    /// `JSOp::RecreateLexicalEnv` -- recreates the current block lexical env.
    pub recreate_lexical_env: Func,
    /// `night_runtime_init_glexical(cx, top, val i64, script i32, pc i32) -> ok`:
    /// `JSOp::InitGLexical` -- initializes the global lexical binding named at
    /// `pc` with `val` (clears the TDZ); leaves `val` on the stack.
    pub init_glexical: Func,
    /// `night_runtime_get_name(cx, top, env i64, atomId i32, forTypeof i32) -> ok`:
    /// `JSOp::GetName` -- scope-chain name read over the env head.
    pub get_name: Func,
    /// `night_runtime_bind_name(cx, top, env i64, atomId i32) -> ok`: `JSOp::BindName`
    /// -- push the env a subsequent `SetName` assigns into.
    pub bind_name: Func,
    /// `night_runtime_get_bound_name(cx, top, env i64, atomId i32) -> ok`:
    /// `JSOp::GetBoundName` -- read the name from an already-bound env.
    pub get_bound_name: Func,
    /// `night_runtime_bind_unqualified_name(cx, top, env i64, atomId i32) -> ok`:
    /// `JSOp::BindUnqualifiedName` -- binding resolution for a `name =` store.
    pub bind_unqualified_name: Func,
    /// `night_runtime_bind_var(cx, top, env i64) -> ok`: `JSOp::BindVar` -- the var
    /// environment object for the env head.
    pub bind_var: Func,
    /// `night_runtime_del_name(cx, top, env i64, atomId i32) -> ok`: `JSOp::DelName` --
    /// `delete name` (unqualified) -> boolean.
    pub del_name: Func,
    /// `night_runtime_push_var_env(cx, top, env i64, script i32, pc i32) -> ok`:
    /// `JSOp::PushVarEnv` -- push a VarEnvironmentObject onto the env chain.
    pub push_var_env: Func,
    /// `night_runtime_enter_with(cx, top, env i64, val i64, script i32, pc i32) -> ok`:
    /// `JSOp::EnterWith` -- push a WithEnvironmentObject wrapping `val`.
    pub enter_with: Func,
    /// `night_runtime_throw_msg(cx, top, kind i32)`: `JSOp::ThrowMsg` -- unconditionally
    /// throws the error named by the ThrowMsgKind byte.
    pub throw_msg: Func,
    /// `night_runtime_builtin_object(cx, top, kind i32) -> ok`: `JSOp::BuiltinObject` --
    /// the builtin object named by the BuiltinObjectKind byte to the out-slot.
    pub builtin_object: Func,
    pub builtin_object_cell: Func,
    /// `night_runtime_arguments(cx, top, sp, argc) -> ok`: build the (unmapped)
    /// arguments object from the frame at `sp`.
    pub arguments_: Func,
    /// `night_runtime_arguments_env(cx, top, sp, argc, env i64) -> ok`: build the
    /// arguments object passing the activation's environment head as the scope
    /// chain, so a mapped args object whose formals are closed over forwards
    /// `arguments[i]` to the CallObject slot (see `MaybeForwardToCallObject`).
    /// Used in the prologue of a mapped script that also closes over bindings.
    pub arguments_env: Func,
    /// `night_runtime_box_nonstrict_this(cx, top, this) -> ok`: the sloppy
    /// `FunctionThis` slow arm -- null/undefined -> the global `this`,
    /// primitives -> wrapper objects (boxed object out). May GC/throw.
    pub box_nonstrict_this: Func,
    /// `night_runtime_get_mapped_arg(argsobj, i) -> value`: mapped-arguments formal
    /// read through the args object (the canonical location once created).
    /// Infallible leaf.
    pub get_mapped_arg: Func,
    /// `night_runtime_set_mapped_arg(argsobj, i, value)`: mapped-arguments formal
    /// write through the args object (runs the GCPtr barriers). Leaf.
    pub set_mapped_arg: Func,
    /// `night_runtime_validate_this_layout(this, layout_id)`: check every predicted
    /// (field, fixed slot) of the layout against the live object's shape and
    /// publish the shape word (or the invalid sentinel) into the layout's
    /// guard cell. Leaf (lookupPure; no GC, no throw).
    pub validate_this_layout: Func,
    /// `night_runtime_in(cx, top, id, obj) -> ok` (`key in obj`; boxed boolean out).
    pub in_: Func,
    /// `night_runtime_has_own(cx, top, id, val) -> ok` (boxed boolean out).
    pub has_own: Func,
    /// `night_runtime_to_property_key(cx, top, val) -> ok` (coerced key out).
    pub to_property_key: Func,
    /// `night_runtime_del_elem(cx, top, val, key, strict) -> ok` (boxed boolean out).
    pub del_elem: Func,
    /// `night_runtime_global_this(cx, top) -> ok` (the global lexical this out).
    pub global_this: Func,
    /// `night_runtime_regexp(cx, top, script, index) -> ok` (cloned regexp out).
    pub regexp: Func,
    /// `night_runtime_init_prop_getset(cx, top, obj, atomId, fn, kind) -> ok`:
    /// object-literal accessor definition (kind bit0=setter, bit1=hidden).
    pub init_prop_getset: Func,
    /// `night_runtime_to_boolean(cx, a) -> i32` (JS ToBoolean; a pure structural test --
    /// never runs user code, allocates, or throws, so no rooting/err handshake).
    pub to_boolean: Func,
    /// `night_runtime_typeof(cx, a) -> u64` (boxed string): the `typeof` operator. The
    /// result is a runtime-pinned common atom, so this is a leaf (no GC/throw).
    pub typeof_: Func,
    /// `night_runtime_typeof_eq(cx, a, operand) -> i32` (0/1): the fused
    /// `typeof a CMP "type"` (`TypeofEq`); infallible leaf.
    pub typeof_eq: Func,
    /// `night_runtime_constant_strict_eq(cx, a, operand) -> i32` (0/1): strict-equality of
    /// `a` against an immediate constant (`StrictConstantEq`/`Ne`); infallible
    /// leaf. The `Ne` form negates the result in the translator.
    pub constant_strict_eq: Func,
    /// `night_runtime_bind_unqualified_gname(cx, top, atomId) -> ok`: push the binding
    /// object for a global-name assignment (`BindUnqualifiedGName`). May GC/throw.
    pub bind_unqualified_gname: Func,
    /// `night_runtime_set_name(cx, top, env, atomId, val, strict) -> ok`: assign `val` to
    /// `name` on the binding object `env` (`SetGName`/`SetName` + strict forms).
    /// May GC/throw.
    pub set_name: Func,
    /// `night_runtime_new_object(cx, out) -> ok` (empty `{}` plain object literal).
    pub new_object: Func,
    /// `night_runtime_new_array(cx, length, out) -> ok` (array literal of given length).
    pub new_array: Func,
    /// `night_runtime_init_prop(cx, obj, atomId, val, attrs) -> ok` (define own data
    /// property on an object/array literal under construction).
    pub init_prop: Func,
    /// `night_runtime_init_elem(cx, obj, key, val, attrs) -> ok` (define own indexed data
    /// property on an object/array literal under construction).
    pub init_elem: Func,
    /// `night_runtime_init_elem_getset(cx, top, obj, key, fn, kind) -> ok`: object-literal
    /// accessor with a computed key (`InitElemGetter`/`Setter` + Hidden forms;
    /// kind bit0=setter, bit1=hidden). May GC/throw (ToPropertyKey).
    pub init_elem_getset: Func,
    /// `night_runtime_check_private_field(cx, top, obj, key, cond, kind) -> bool`: private
    /// brand/presence check (`CheckPrivateField`); throws per the ThrowCondition.
    pub check_private_field: Func,
    /// `night_runtime_new_private_name(cx, top, atomId) -> symbol`: create a private-name
    /// symbol for a `#x` class member (`NewPrivateName`). May GC.
    pub new_private_name: Func,
    /// `night_runtime_env_setup(cx, sp, out) -> ok` (the environment
    /// prologue): build the function's
    /// environment head -- its CallObject (over `callee->environment()`) when the
    /// callee `needsCallObject`, else `callee->environment()` itself -- and write
    /// it boxed to `*out`. May GC (allocates the CallObject).
    pub env_setup: Func,
    /// `night_runtime_get_aliased(cx, env, hops, slot) -> u64` (boxed value): walk `hops`
    /// enclosing links from `env`, read environment slot `slot`. Leaf (no GC/throw).
    pub get_aliased: Func,
    /// `night_runtime_set_aliased(cx, env, hops, slot, val)`: walk `hops`, write the slot.
    /// Leaf (no GC/throw).
    pub set_aliased: Func,
    /// `night_runtime_lambda(cx, env, script, func_index, out) -> ok`: clone the function
    /// template `script->getFunction(func_index)` capturing `env`. May GC.
    pub lambda: Func,
    /// `night_runtime_exception(cx, out) -> ok`: get and clear the pending
    /// exception (the `Exception` op). May fail (interrupt) -> err edge.
    pub exception: Func,
    /// `night_runtime_throw(cx, val)`: set `val` as the pending exception with a
    /// captured stack (the `Throw` op). May GC.
    pub throw: Func,
    /// `night_runtime_throw_with_stack(cx, val, stack)`: re-throw `val` with the
    /// saved exception `stack` (the `ThrowWithStack` op, finally re-raise).
    pub throw_with_stack: Func,
    /// `night_runtime_get_exception_for_finally(cx, exc_out, stack_out)`: get the
    /// pending exception value + stack and clear it, for a finally's exceptional
    /// entry (which pushes `[exception, exceptionStack, true]`).
    pub get_exception_for_finally: Func,
    /// `night_runtime_global_decl_instantiation(cx, top, script, gcthingIndex) -> ok`:
    /// instantiate the hoisted global `function`/`var` declarations onto the
    /// global (the `GlobalOrEvalDeclInstantiation` op, pc 0 of a global script).
    /// May GC (creates bindings); no operand-stack effect.
    pub global_decl_instantiation: Func,
    /// `night_runtime_iter(cx, top, val) -> ok` (for-in): build the property iterator
    /// (boxed object to the out-slot). May GC/throw.
    pub iter_: Func,
    /// `night_runtime_more_iter(cx, iter) -> u64`: the next property name, or the
    /// NO_ITER magic when exhausted. Leaf.
    pub more_iter: Func,
    /// `night_runtime_end_iter(cx, iter)`: close the iterator (leaf; also called on
    /// exception unwind through a ForIn try-note range).
    pub end_iter: Func,
    /// `night_runtime_close_iter_for_exception(cx, top, done i64, iter i64)`: exception
    /// unwind through a `Destructuring` try-note -- close the destructuring
    /// iterator unless `done` is truthy, via IteratorCloseForException (which
    /// preserves the pending exception). May GC/throw (runs `return()`).
    pub close_iter_for_exception: Func,
    /// `night_runtime_symbol(cx, code i32) -> i64` (leaf): push the well-known symbol
    /// named by the `SymbolCode` byte (`JSOp::Symbol`, e.g. `@@iterator`).
    pub symbol: Func,
    /// `night_runtime_optimize_get_iterator(cx, v i64) -> i32` (leaf): the
    /// `OptimizeGetIterator` predicate -- `v` is an array with the default
    /// iteration protocol (for-of/destructuring fast-path gate).
    pub optimize_get_iterator: Func,
    /// `night_runtime_close_iter(cx, top, iter i64, kind i32) -> ok`: `JSOp::CloseIter`
    /// -- IteratorClose on `iter` with the CompletionKind byte. May GC/throw.
    pub close_iter: Func,
    /// `night_runtime_to_async_iter(cx, top, iter i64, next i64) -> ok`:
    /// `JSOp::ToAsyncIter` -- async-from-sync iterator wrapper to the out-slot.
    pub to_async_iter: Func,
    /// `night_runtime_spread_call(cx, top, callee i64, this i64, arr i64, newTarget i64,
    /// constructing i32) -> ok`: `JSOp::SpreadCall`/`SpreadNew` -- call/construct
    /// `callee` spreading the packed array `arr`; result to the out-slot.
    pub spread_call: Func,
    /// `night_runtime_optimize_spread_call(cx, top, v i64) -> ok`:
    /// `JSOp::OptimizeSpreadCall` -- forward-array-or-undefined to the out-slot.
    pub optimize_spread_call: Func,
    /// `night_runtime_object(cx, script, gcthingIndex) -> u64` (boxed object): push the
    /// precompiled object `script->getObject(gcthingIndex)` (the `Object` op, a
    /// run-once frozen object literal). Leaf: a load of an already-rooted GC
    /// pointer (no GC/throw).
    pub object: Func,
    /// `night_runtime_post_write_barrier(ownerBits, slot, valBits)` (leaf): the
    /// generational post-write barrier slow path for an inlined static fixed-slot
    /// store. The translator inlines the raw `store_i64` and the is-GC-thing/
    /// is-nursery check, calling this only when a nursery pointer is stored (to
    /// record the (owner, slot) store-buffer edge -- `HeapSlot::post`). A
    /// store-buffer append never moves objects, so no rooting/err handshake.
    /// The pre-write (incremental-marking) barrier is separate:
    /// `pre_write_barrier` below.
    pub post_write_barrier: Func,
    /// `night_runtime_pre_write_barrier(valBits)` (leaf): the pre-write (incremental-
    /// marking / sab) barrier slow path. The translator inlines the gate -- it
    /// reads the zone's `needsIncrementalBarrier` flag (`cx->zone()->...`) inline
    /// and, only when set (active incremental marking), reads the old slot value
    /// and calls this to mark it (before the store overwrites it). Marking is
    /// non-moving, so no rooting/err handshake.
    pub pre_write_barrier: Func,
    /// `night_runtime_post_write_barrier_elem(ownerBits, index, valBits)` (leaf): the
    /// generational post-write barrier for an inlined dense-element store. Like
    /// `post_write_barrier` but records the **element** store-buffer edge
    /// (`HeapSlot::Element`) -- a different edge than the slot one. The driver
    /// inlines the raw element `store_i64` and the is-GC-thing/is-nursery check,
    /// calling this only on a nursery-pointer store. The helper converts the
    /// logical `index` to the unshifted store-buffer index from the owner (so a
    /// post-`.shift()` array records the right edge). No rooting/err handshake.
    pub post_write_barrier_elem: Func,
    /// `night_runtime_resolve_global_slot(cx, bindingId) -> u32` (leaf): the cold
    /// resolve-once path for a global binding. On first access the inline read
    /// finds the binding's `gGlobalSlots` entry unresolved (0) and calls this,
    /// which `lookupPure`s the pre-interned binding name on the global object
    /// (non-allocating, never GCs) and writes back + returns the encoded entry
    /// (v2: `bit0` resolved, `bit1` is-dynamic-slot, `bit2` writable,
    /// `bits[31:3]` slot index).
    pub resolve_global_slot: Func,
    /// `night_runtime_resolve_global_slot_guarded(cx, bindingId) -> u32` (leaf): the
    /// no-TI variant -- caches `[entry, globalShape]` only for an own plain
    /// data slot of the global object (not lexically shadowed); returns 0
    /// ("not cacheable"), sending the site to the char-based helper.
    pub resolve_global_slot_guarded: Func,
    /// `night_runtime_set_global(cx, bindingId, valBits)` (leaf): assign a
    /// global-object binding by its resolved slot (shared `gGlobalSlots`), with
    /// the generational/incremental write barriers (`NativeObject::setSlot`).
    /// Leaf: the slot store + barriers never move objects.
    pub set_global: Func,
    /// `night_runtime_binding_value(cx, bindingId) -> i64` (leaf): the
    /// binding's current value bits for a compiled re-proof of a carried
    /// per-binding value fact (armed cell, else guarded resolve + slot);
    /// a magic Value when the name is no longer an own plain data slot.
    pub binding_value: Func,
    /// `night_runtime_binding_written(bindingId)` (leaf): the inline
    /// `SetGName` store unarmed the binding's value-fuse cell; re-arm it.
    pub binding_written: Func,
    /// Linear-memory base address of the `gGlobalSlots` region (one `u32`
    /// per binding id; zero = unresolved). The inline `GetGName` reads
    /// `i32.load(global_slots_base + 4 * binding_id)`.
    pub global_slots_base: u32,
    /// Linear-memory base of the inline property-IC region. A GetProp IC
    /// site `cacheIdx` reads way `w` at `prop_ic_base + cacheIdx*INLINE_IC_STRIDE
    /// + w*INLINE_IC_WAY_BYTES` (fields: recvShape, ownFixedOff, holderPtr,
    /// holderShape, slotEnc). Written by the miss helper; zero == empty way.
    pub prop_ic_base: u32,
    /// Linear-memory address of the single `u32` inline-IC generation
    /// counter (bumped by the reactor's major-GC callback). The inline guard
    /// compares it against each way's cached generation.
    pub prop_ic_gen_base: u32,
    /// Static per-layout add-check bound table base (the retired guard
    /// cells' region, stride 8): word 0 of each entry holds the byte-offset
    /// bound `FIXED_SLOTS_BASE + 8 * maxExtPrefixLen` the unknown-receiver
    /// add arms compare assigned slot offsets against (0 = unfilled ->
    /// conservative clear). Filled by the runtime at install from the
    /// layout blob.
    pub this_cells_base: u32,
    /// Observed-slot layout table base: one row per layout id (stride 40:
    /// u32 published-count + 16 x u16 observed slots), published write-once
    /// by the runtime validator. In observed-slot mode the layout arms read
    /// each field's slot from here instead of assuming index == slot.
    pub this_slots_base: u32,
    /// Linear-memory base of the global megamorphic get table
    /// (`MEGA_GET_SIZE` direct-mapped entries of `MEGA_GET_ENTRY_BYTES`,
    /// keyed by hash(receiver shape, atomId); GC-zeroed). Poly GetProp sites
    /// (mono way holds the sentinel) probe it inline.
    pub mega_get_base: u32,
    /// The set-side megamorphic table (`MEGA_SET_SIZE` x
    /// `MEGA_SET_ENTRY_BYTES`, same hash; GC-zeroed). Poly SetProp sites
    /// probe it inline (barriered own-slot store on hit).
    pub mega_set_base: u32,
    /// The dense-append cache region (`APPEND_CACHE_SIZE` x
    /// `APPEND_CACHE_ENTRY_BYTES`, shape-hashed; GC-zeroed). The SetElem
    /// append arm probes it inline; the generic set-element helper primes.
    pub append_cache_base: u32,
    /// The accessor-call cache (`ACCESSOR_CACHE_SIZE` x
    /// `ACCESSOR_CACHE_ENTRY_BYTES`, (shape, atom^kind)-hashed;
    /// GC-zeroed). Accessor-classified property sites probe it inline;
    /// the generic get/set miss helpers prime it.
    pub accessor_cache_base: u32,
    /// Linear-memory address of the `u32` AOT-stack limit (one past the
    /// region), published by `night_runtime_run_main`. The specialized-call guard
    /// compares the callee frame top (+ headroom) against it and takes the
    /// generic-helper arm when the region would overflow -- `EnterNight` there
    /// bounds-checks and falls back to the interpreter gracefully.
    pub night_stack_limit_base: u32,
    /// Linear-memory address of the startup-written pair `[&js::FunctionClass,
    /// &js::ExtendedFunctionClass]` (two u32 slots), for the inline callee
    /// classify's `is<JSFunction>` clasp compares.
    pub fn_class_slot: u32,
    /// Linear-memory address of the startup-written StaticStrings unit-string
    /// table base (JSString* per latin1 char < 128), for the inline string
    /// element fast path.
    pub static_strings_slot: u32,
    pub atom_table_slot: u32,
    /// Linear-memory address of the startup-written u32 pair holding the
    /// addresses of the nursery's `position_` and `currentEnd_` words (the
    /// same pair the JIT's bumpPointerAllocate uses). Zero == nursery
    /// allocation disabled (the alloc cells then never fill, so the inline
    /// arm never runs).
    pub nursery_pos_slot: u32,
    pub nursery_end_slot: u32,
    /// Linear-memory addresses of the u64 cells holding the boxed bits of the
    /// original String.prototype.charCodeAt / charAt (0 = unarmed; the GC
    /// callback re-arms after moves). The generic-call fallback compares the
    /// runtime callee against them to enter the inline char-access arm --
    /// callee identity subsumes a proto fuse: a monkeypatched prototype hands
    /// the site a different callee value and the guard self-misses.
    pub str_ccat_cell: u32,
    pub str_cat_cell: u32,
    /// As above for the original String.fromCharCode (static method; the
    /// inline arm serves codes < 256 from the static unit-string table).
    pub str_fcc_cell: u32,
    /// Linear-memory slot holding the address of the engine's
    /// OptimizeStringCharOpsFuse guard word (Watchtower pops it on any
    /// mutation of the char-op methods -- set, defineProperty, delete).
    /// Guard: load slot, load word, == 0 means intact. The reactor points
    /// the slot at a permanently-popped word when the fuse is unavailable.
    pub str_fuse_addr_slot: u32,
    /// Linear-memory slot holding the address of the runtime's
    /// HasSeenObjectEmulateUndefinedFuse guard word (popped when the first
    /// shape of an emulates-undefined class is created). While the word is
    /// 0 the loose-eq nullish and truthiness arms skip the per-operand
    /// clasp walk.
    pub dda_fuse_addr_slot: u32,
    /// Linear-memory address of the dynamic-code fuse word itself (night-owned,
    /// zero-init; `0` == no script has been compiled from source text since
    /// startup). Unlike the two slots above it holds no address indirection --
    /// one load, one compare -- because the engine has no such word to point
    /// at: the C++ runtime blows this one from `EvalKernel` and the `Function`
    /// constructor. The BigInt-freedom claims read it, since source the static
    /// scan never saw can mint a BigInt.
    pub dyncode_fuse_word: u32,
    /// Linear-memory slot holding &js::ArrayObject::class_ (startup-written;
    /// the inline array-length arm's clasp identity compare).
    pub array_class_slot: u32,
    /// Base of the two startup-written arguments class pointers
    /// (`[mapped @0, unmapped @4]`); the inline `arguments.length` arm's
    /// clasp identity guard.
    pub args_class_base: u32,
    /// Base of the string-literal inline-materialization block (32 bytes):
    /// `[emptyString u32 @0]` (startup-written permanent atom, never zeroed),
    /// then the thin `[hdrWord @4, flagsWord @8, totalSize @12]` and fat
    /// `[hdrWord @16, flagsWord @20, totalSize @24]` replay triples the slow
    /// helper fills from its first nursery inline allocation of each kind
    /// (zeroed on major GC like the alloc cells). The JSOp::String inline
    /// path bump-allocates a fresh nursery inline Latin1 string from them.
    pub strlit_slot: u32,
    /// Base of the builtin callee-identity cells (u64 boxed bits of the
    /// pristine builtin each, 0 = unarmed, GC re-armed; BC_* indexes).
    pub builtin_cells_base: u32,
    /// Base of the startup-written Math native-pointer slots (`MN_*`).
    pub math_natives_base: u32,
    /// Base of the typed-array clasp table: 9 startup-written `u32` class
    /// pointers (fixed-length TA class for element kind 1..=9 at index
    /// kind-1). The inline typed-array read arm's clasp identity guard.
    pub ta_class_base: u32,
    /// `night_runtime_math_unary(kind, x) -> f64` (leaf): kind 0 = sin, 1 = cos,
    /// routed to the engine's own impl (fdlibm/native per realm config).
    pub math_unary: Func,
    /// `night_runtime_math_pow(x, y) -> f64` (leaf): `js::ecmaPow`.
    pub math_pow: Func,
    /// `night_runtime_fmod(x, y) -> f64` (leaf): `js::NumberMod`, the pure
    /// form of `%` at range-proven-numeric sites (no wasm f64 modulo).
    pub fmod: Func,
    /// Base of the per-binding value-fuse cells
    /// (`[bits u64][fuseWord u32][pad]`, 16 bytes each), right after the
    /// gGlobalSlots rows; GC-zeroed
    /// with them). fuseWord 1 == the bits are the binding's current value
    /// (armed at resolve, blown by the compiled global write paths).
    pub global_vals_base: u32,
    /// `night_runtime_create_this(cx, top, calleeBits, newTargetBits, nSlots) -> ok`
    /// (direct construct): create the `this` object for a specialized `new`
    /// (empty sized allocation for a resolved layout ctor, else ordinary `CreateThis`).
    /// May GC.
    pub create_this: Func,
    /// `night_runtime_rest(cx, top, sp i32, argc i32, nformal i32) -> ok`: `JSOp::Rest`
    /// -- build the rest array from the actuals beyond the formal count. Boxed
    /// array to the out-slot. May GC.
    pub rest: Func,
    /// `night_runtime_implicit_this(cx, top, env i64) -> ok`: `JSOp::ImplicitThis` --
    /// the implicit `this` for an unqualified name call from the env object.
    pub implicit_this: Func,
    /// `night_runtime_check_this_reinit(cx, top, v i64) -> ok`: `JSOp::CheckThisReinit`
    /// -- throw if `v` is not the uninitialized-lexical magic, else a no-op.
    pub check_this_reinit: Func,
    /// `night_runtime_check_return(cx, top, thisv i64, rval i64) -> ok`:
    /// `JSOp::CheckReturn` (derived ctor) -- checked return value to the
    /// out-slot (object rval -> rval; undefined -> thisv; else throws).
    pub check_return: Func,
    /// `night_runtime_obj_with_proto(cx, top, proto i64) -> ok`: `JSOp::ObjWithProto`
    /// -- `Object.create(proto)` for an object literal with `__proto__`.
    pub obj_with_proto: Func,
    /// `night_runtime_fun_with_proto(cx, top, env i64, proto i64, script i32,
    /// funcIndex i32) -> ok`: `JSOp::FunWithProto` -- clone the function
    /// template with an explicit proto (class heritage). Boxed fn to out-slot.
    pub fun_with_proto: Func,
    /// `night_runtime_no_extra_indexed(obj i32) -> i32` (leaf): `1` iff neither `obj`
    /// nor its prototype chain may have extra indexed properties -- the inline
    /// dense-append (push) arm's proto guard.
    pub no_extra_indexed: Func,
    /// `night_runtime_gen_is_closing(cx) -> i32` (leaf): peek-only generator-closing
    /// check (the pending magic is not cleared) for the catch-pad split.
    pub gen_is_closing: Func,
    /// `night_runtime_set_fun_name(cx, top, fun i64, name i64, prefixKind i32) -> ok`:
    /// `JSOp::SetFunName` -- set the inferred name on an anonymous function.
    /// Leaves `fun` on the stack (no out-slot).
    pub set_fun_name: Func,
    // Baseline-tier helpers (docs/BASELINE.md §6).
    /// `(cx, top, script, gcthingIndex) -> ok`; the BigInt literal.
    pub bigint: Func,
    /// `(cx, top, env i64) -> ok`.
    pub non_syntactic_global_this: Func,
    /// `(cx, top, script, pcOffset, val i64) -> ok`.
    pub set_intrinsic: Func,
    /// Leaf `(cx, env i64, hops) -> callee i64`.
    pub env_callee: Func,
    /// `(cx, top, sp, argc, env i64, script, pcOffset) -> ok`: direct eval
    /// when the callee is `eval`, else an ordinary call.
    pub eval: Func,
    /// `(cx, top, callee, this, arr, env i64, script, pcOffset) -> ok`.
    pub spread_eval: Func,
    /// `(cx, top, script, specifier i64, options i64) -> ok`.
    pub dynamic_import: Func,
    /// `(cx, top, script) -> ok`.
    pub import_meta: Func,
    /// `(cx, top, env i64, script, pcOffset) -> ok`.
    pub get_import: Func,
    /// `(cx, top, env i64, val, method, needsClosure, hint) -> ok`.
    pub add_disposable: Func,
    /// `(cx, top, env i64) -> ok`.
    pub take_dispose_capability: Func,
    /// `(cx, top, error i64, suppressed i64) -> ok`.
    pub create_suppressed_error: Func,
    /// `(cx, top, gen i64, val i64, kind i64) -> ok`: `JSOp::Resume`.
    pub resume: Func,
}

/// A monotonically-incrementing dense-index allocator: `next()` claims the next
/// index (post-increment) and `count()` reports how many have been claimed
/// (which sizes the corresponding linear-memory region).
#[derive(Default)]
struct DenseCounter {
    next: u32,
}

impl DenseCounter {
    fn next(&mut self) -> u32 {
        let idx = self.next;
        self.next += 1;
        idx
    }

    fn count(&self) -> u32 {
        self.next
    }
}

/// The names an emitter recognizes by identity, so the test is an integer
/// compare rather than a UTF-16 comparison at every op that could be one.
#[derive(Default)]
pub struct WellKnownNames {
    pub length: NameId,
    pub char_code_at: NameId,
    pub char_at: NameId,
}

/// Property-name atom table built during translation: the names compiled
/// bodies actually reference, each assigned a dense `atomId`. The merge
/// embeds them; the runtime interns each to a `JSAtom*` at startup and the
/// generic property helpers index by `atomId`.
///
/// The `atomId` is a *serialization index*, not an identity -- it exists so
/// the embedded table is dense and so the emitted immediates are small. The
/// identity is the [`NameId`], and this table owns the compilation's one
/// [`Names`] (handed over from `LikelyFacts`) rather than keeping a second
/// copy of the strings: `intern` maps an already-interned `NameId` to the
/// next dense slot.
pub struct AtomTable {
    /// The compilation's string table, moved here for the translation phase.
    /// Codegen can still intern: it reaches names in scripts the analysis
    /// skipped.
    pub names: Names,
    /// `NameId -> atomId`, and its inverse in assignment order.
    atom_of: HashMap<NameId, u32>,
    emitted: Vec<NameId>,
    /// The names the lowerings test for by identity, interned once.
    pub well_known: WellKnownNames,
    /// Running count of allocated property-IC cache slots: each
    /// specialized GetProp/SetProp site claims the next dense index, baked into
    /// the body as the offset of its way block in the `gPropIC` linear-memory
    /// region (sized by this count). Shared across all scripts in the module
    /// (threaded with the atom table).
    prop_cache_count: DenseCounter,
    /// Running count of per-site callee value cells: each inline-classify site
    /// claims the next dense index into the call-cell region (16-byte rows
    /// `[callee_bits i64][funcidx u32][script u32]`). The region's base is only
    /// known post-translation (it sits after the prop-IC ways), so sites bake a
    /// placeholder address const that mod.rs patches (`call_cell_patches`).
    call_cell_count: DenseCounter,
    /// Running count of inline-alloc site cells (object/array literals): each
    /// site claims the next dense index into the alloc-cell region (32-byte
    /// rows filled by the slow-path helper from the first allocated object).
    /// The base is only known post-translation; sites bake placeholder consts
    /// mod.rs patches (`alloc_cell_patches`).
    alloc_cell_count: DenseCounter,
    /// Running count of per-site instanceof cells: each `Instanceof` site claims
    /// the next dense index into the iof-cell region (16-byte rows
    /// `[funShape u32][gen u32][protoSlotEnc u32][pad]`, populated by the miss
    /// helper). Base known post-translation; sites bake placeholder consts
    /// mod.rs patches (`iof_cell_patches`).
    iof_cell_count: DenseCounter,
    /// Running count of per-site construct-`this` cells (40-byte rows; alloc
    /// fields + a constructor-shape/prototype guard, populated by the miss
    /// helper). Base known post-translation; sites bake placeholder consts
    /// mod.rs patches (`construct_cell_patches`).
    construct_cell_count: DenseCounter,
    /// Latin1 bytes of the string literals the inline JSOp::String path
    /// copies from (one padded entry per distinct eligible atom; thin
    /// entries padded to 8 bytes, fat to 24, so the copy can use whole-word
    /// loads). Embedded as a data segment; sites bake placeholder consts
    /// mod.rs patches with the blob base (`strlit_patches`).
    strlit_blob: Vec<u8>,
    /// Per-intrinsic value cells (8-byte rows holding the boxed Value bits;
    /// 0 == unresolved), deduped by atom -- every GetIntrinsic site of the
    /// same name shares one cell. Base known post-translation; sites bake
    /// placeholder consts mod.rs patches (`intrinsic_cell_patches`).
    intrinsic_cells: HashMap<u32, u32>,
}

impl AtomTable {
    /// Take the compilation's string table over for the translation phase.
    ///
    /// The only constructor: the well-known ids have to be interned into
    /// *this* table, so a default-constructed one would answer every
    /// well-known test with id 0.
    pub fn new(mut names: Names) -> AtomTable {
        let well_known = WellKnownNames {
            length: names.intern_str("length"),
            char_code_at: names.intern_str("charCodeAt"),
            char_at: names.intern_str("charAt"),
        };
        AtomTable {
            names,
            well_known,
            atom_of: HashMap::default(),
            emitted: Vec::new(),
            prop_cache_count: DenseCounter::default(),
            call_cell_count: DenseCounter::default(),
            alloc_cell_count: DenseCounter::default(),
            iof_cell_count: DenseCounter::default(),
            construct_cell_count: DenseCounter::default(),
            strlit_blob: Vec::new(),
            intrinsic_cells: HashMap::default(),
        }
    }

    /// The dense `atomId` for a name, assigning the next one on first use.
    /// Emission order, so the embedded table holds only what compiled bodies
    /// reference.
    pub fn intern(&mut self, name: NameId) -> u32 {
        if let Some(&id) = self.atom_of.get(&name) {
            return id;
        }
        let id = u32::try_from(self.emitted.len()).unwrap();
        self.atom_of.insert(name, id);
        self.emitted.push(name);
        id
    }

    /// Intern by code units: the path for a name the string table has not
    /// seen (a script the analysis skipped).
    pub fn intern_chars(&mut self, chars: &[u16]) -> u32 {
        let name = self.names.intern(chars);
        self.intern(name)
    }

    /// The `NameId` behind an atom id.
    pub(crate) fn emitted_name(&self, id: u32) -> NameId {
        self.emitted[id as usize]
    }

    /// The emitted names, in `atomId` order -- what the module embeds.
    pub fn emitted_names(&self) -> impl Iterator<Item = &JsString> {
        self.emitted.iter().map(|&n| self.names.get(n))
    }

    /// How many names compiled bodies referenced.
    pub fn emitted_len(&self) -> usize {
        self.emitted.len()
    }

    /// Claim the next property-IC cache index.
    pub(crate) fn next_prop_cache(&mut self) -> u32 {
        self.prop_cache_count.next()
    }

    /// Total property-IC cache slots allocated across the module (sizes the
    /// property-IC
    /// inline-cache linear-memory region).
    pub fn prop_cache_count(&self) -> u32 {
        self.prop_cache_count.count()
    }

    /// Claim the next callee value-cell index.
    pub(crate) fn next_call_cell(&mut self) -> u32 {
        self.call_cell_count.next()
    }

    /// Total callee value cells allocated across the module (sizes the
    /// call-cell linear-memory region; 16 bytes per cell).
    pub fn call_cell_count(&self) -> u32 {
        self.call_cell_count.count()
    }

    /// Claim the next inline-alloc cell index.
    pub(crate) fn next_alloc_cell(&mut self) -> u32 {
        self.alloc_cell_count.next()
    }

    /// Total inline-alloc cells allocated across the module (sizes the
    /// alloc-cell linear-memory region; 32 bytes per cell).
    pub fn alloc_cell_count(&self) -> u32 {
        self.alloc_cell_count.count()
    }

    /// Claim the next instanceof cell index.
    pub(crate) fn next_iof_cell(&mut self) -> u32 {
        self.iof_cell_count.next()
    }

    /// Total instanceof cells allocated across the module (sizes the iof-cell
    /// linear-memory region; 16 bytes per cell).
    pub fn iof_cell_count(&self) -> u32 {
        self.iof_cell_count.count()
    }

    /// Claim the next construct-`this` cell index.
    pub(crate) fn next_construct_cell(&mut self) -> u32 {
        self.construct_cell_count.next()
    }

    /// Total construct-`this` cells allocated across the module (sizes the
    /// construct-cell linear-memory region; 40 bytes per cell).
    pub fn construct_cell_count(&self) -> u32 {
        self.construct_cell_count.count()
    }

    /// The value cell shared by every GetIntrinsic site reading `atom_id`
    /// (row index into the intrinsic-cell region).
    pub(crate) fn intrinsic_cell(&mut self, atom_id: u32) -> u32 {
        let next = u32::try_from(self.intrinsic_cells.len()).unwrap();
        *self.intrinsic_cells.entry(atom_id).or_insert(next)
    }

    /// The value cell shared by every `BuiltinObject` site of `kind`: the
    /// same region (and compacting-GC purge) as the intrinsic cells, keyed
    /// above the atom-id space.
    pub(crate) fn builtin_object_cell(&mut self, kind: u32) -> u32 {
        self.intrinsic_cell(0x8000_0000 | kind)
    }

    /// Total intrinsic value cells (sizes the region; 8 bytes per cell).
    pub fn intrinsic_cell_count(&self) -> u32 {
        u32::try_from(self.intrinsic_cells.len()).unwrap()
    }

    /// The accumulated Latin1 literal blob (a data segment in the merge).
    pub fn strlit_blob(&self) -> &[u8] {
        &self.strlit_blob
    }
}

/// Callee value-cell row size and field offsets (must match NightRuntime.cpp's
/// zeroing region math): `[callee_bits i64 @0][funcidx u32 @8][script u32 @12]`.
pub const CALL_CELL_BYTES: u32 = 16;

// The native-route arm is cheaper than a cell (two blocks, no stores), so it
// tolerates mid-size bodies (generated functions that call natives in loops);
// only the truly giant ones skip it.
pub const NATIVE_ROUTE_SCRIPT_MAX_BYTECODE: usize = 64 * 1024;

/// Inline-alloc cell row size and field offsets (must match NightRuntime.cpp's fill
/// helpers and zeroing region math). Object-literal rows: `[shape u32 @0]
/// [totalSize u32 @4][slotsWord u32 @8][elementsWord u32 @12][headerWord u32
/// @16]`. Array-literal rows reuse: `@12 = elements offset from the object`,
/// plus `[elemFlags u32 @20][capacity u32 @24][length u32 @28]`. `shape == 0`
/// means empty (helper not yet run / GC-zeroed); the helper fills the row by
/// copying words from the first object it allocates at the site.
pub use crate::region_shape::ALLOC_CELL_BYTES;

/// Instanceof cell row size and field offsets (must match NightRuntime.cpp's populate
/// + region math): `[funShape u32 @0][gen u32 @4][protoSlotEnc u32 @8][pad]`.
/// `funShape == 0` means empty. The miss helper (`night_runtime_instanceof`) populates
/// it when rhs is a function with the default @@hasInstance and its `.prototype`
/// is an own data slot; the inline hit guards funShape + the live generation
/// (`prop_ic_gen_base`), then reads the live `.prototype` slot and walks lhs's
/// prototype chain. Staleness is handled by the gen stamp (no GC zeroing).
pub const IOF_CELL_BYTES: u32 = 16;

/// Inline construct-`this` cell (must match NightRuntime.cpp populate + region math).
/// The first five u32 mirror an alloc cell exactly
/// (`[shape@0, total@4, slotsWord@8, elementsWord@12, headerWord@16]`) so
/// `NightFillAllocCellObject`
/// fills them unchanged from the freshly-created empty `this`; the constructor
/// guard fields follow: `[ctorShape@20, gen@24, protoPtr@28, protoSlotEnc@32]`.
/// A `new C()` whose `this` is an empty PlainObject nursery-bumps inline (same
/// machinery as an object literal), guarded by C's shape + generation + a live
/// re-read of C's `.prototype` (a reassignment is a slot write, no shape change,
/// so the cached this-shape would otherwise go stale). `shape == 0` means empty.
pub use crate::region_shape::CONSTRUCT_CELL_BYTES;

/// Strlit block field offsets off `helpers.strlit_slot` (mirrored in
/// NightRuntime.cpp's arming/fill/zeroing): emptyString @0, thin/fat replay triples.
pub use crate::region_shape::STRLIT_BLOCK_BYTES;

/// Intrinsic value-cell row size (a boxed Value; 0 == unresolved) and the
/// placeholder mod.rs patches to `intrinsic_cells_base + 8 * row`.
pub const INTRINSIC_CELL_BYTES: u32 = 8;

// nunbox32 value tags (the runtime is wasm32 => JS_NUNBOX32). A boxed
// `JS::Value` is `(tag << 32) | payload`; doubles are stored as their raw
// IEEE bits (the tag space is NaN-space). Carried from prior phases / Value.h.
pub(super) const TAG_CLEAR: u32 = 0xFFFF_FF80;
pub(super) const TAG_INT32: u64 = 0xFFFF_FF81;
pub(super) const TAG_BOOLEAN: u64 = 0xFFFF_FF82;
pub(super) const TAG_UNDEFINED: u64 = 0xFFFF_FF83;
pub(super) const TAG_NULL: u64 = 0xFFFF_FF84;
pub(super) const TAG_MAGIC: u64 = 0xFFFF_FF85;
pub(super) const TAG_STRING: u64 = 0xFFFF_FF86;
pub(super) const TAG_SYMBOL: u64 = 0xFFFF_FF87;
pub(super) const TAG_BIGINT_HI: u32 = 0xFFFF_FF89;
// `JSVAL_TAG_OBJECT` (= `JSVAL_TAG_CLEAR | JSVAL_TYPE_OBJECT` = 0xFFFFFF80|0x0c),
// Value.h:200-212. On NUNBOX32 the low 32 bits of a boxed object Value are the
// `JSObject*` directly (Value::toObjectOrNull, Value.h:945), so the object
// pointer is `i32.wrap_i64(value)`.
pub(super) const TAG_OBJECT: u64 = 0xFFFF_FF8C;

/// A JavaScript value the compiler knows at compile time, together with the
/// boxed `JS::Value` bit pattern the runtime will see.
///
/// The boxing rule is the engine's, not ours, so it belongs next to the tag
/// constants rather than at each place that needs a literal: a Number boxes
/// as `Int32` exactly when it is an exact int32 and not negative zero, and
/// as its raw IEEE bits otherwise. Anywhere that spells the tags out again
/// is a second copy of that rule, and the two can drift.
#[derive(Clone, Copy, PartialEq, Debug)]
pub(super) enum ConstValue {
    Number(f64),
    Boolean(bool),
    Null,
    Undefined,
}

impl ConstValue {
    pub(super) fn boxed_bits(self) -> u64 {
        match self {
            ConstValue::Number(f) => {
                let i = f as i32;
                if f64::from(i) == f && !(f == 0.0 && f.is_sign_negative()) {
                    (TAG_INT32 << 32) | u64::from(i as u32)
                } else {
                    f.to_bits()
                }
            }
            ConstValue::Boolean(b) => (TAG_BOOLEAN << 32) | u64::from(b),
            ConstValue::Null => TAG_NULL << 32,
            ConstValue::Undefined => TAG_UNDEFINED << 32,
        }
    }
}

// MagicValue payloads (the low half of a TAG_MAGIC value).
pub(super) const MAGIC_ELEMENTS_HOLE: u64 = 0;
pub(super) const MAGIC_NO_ITER_VALUE: u64 = 1;
pub(super) const MAGIC_IS_CONSTRUCTING: u64 = 5;
pub(super) const MAGIC_UNINITIALIZED_LEXICAL: u64 = 10;
/// `JS_GENERATOR_CLOSING`: staged by the interpreter's Resume hook in the
/// frame `this` slot to mark a re-entry, and raised as a pending exception
/// by a forced `.return()` so the enclosing finallys run (see
/// `bbv/generator.rs` and runtime/NightGenerator.cpp).
pub(super) const MAGIC_GENERATOR_CLOSING: u64 = 2;

// Fixed-slot object layout on wasm32 (JS_NUNBOX32). Consumed by the static
// slot-access path; the reactor `static_assert`s these against the engine
// (runtime/NightInlineHeap.cpp) so a layout change is a build error, not a
// silent miscompile.
//   sizeof(NativeObject) = shape_(4) + externalWord_(4) + slots_(4)
//   + elements_(4) = 16  (NativeObject.h:614-620, shadow/Object.h:34-52)
// First inline fixed slot at this offset; getFixedSlotOffset(i) =
// sizeof(NativeObject) + i*sizeof(Value)  (NativeObject.h:1751).
pub(crate) const FIXED_SLOTS_BASE: u32 = 16;
// pop additionally bails on MAYBE_IN_ITERATION (0x100): removing an element
// under an active for-in needs SuppressDeletedProperty.
pub const ELEMENTS_POP_BAIL_MASK: u32 = 0x172;
// Dense-append cache (the SetElem append arm): a direct-mapped
// shape-keyed table in linear memory. Row: [shape, protoPtr0, protoShape0,
// protoPtr1, protoShape1, isArray, pad, pad] (8 x u32). A row is primed by
// the generic set-element helper after a successful engine-side dense
// append/overwrite on a validated receiver (shared shape, Array or
// hook-free class, tenured <=2-hop proto chain to null, no indexed
// properties anywhere); the inline arm's hit re-checks the protos' live
// shape words. GC: the whole region is zeroed on major GC (shapes/protos
// can move); protos are tenured-only so minor GCs cannot invalidate.
pub use crate::region_shape::{
    APPEND_CACHE_ROWS as APPEND_CACHE_SIZE, APPEND_CACHE_ROW_BYTES as APPEND_CACHE_ENTRY_BYTES,
};
// Accessor-call cache ((shape, atom ^ kind)-hashed, GC-zeroed; mirrors the
// C++ kAccessorCache* constants; the base rides its own region-table
// slot, ABI v5). Entry: [callee_bits u64 @0, recvShape @8, atomKind @12
// (atomId << 1 | kind), holderPtr @16, holderShape @20, pad @24..32]. A
// zero recvShape marks the entry empty.
pub use crate::region_shape::{
    ACCESSOR_ATOM_KIND_OFF as ACCESSOR_ATOM_KIND, ACCESSOR_CACHE_ROWS as ACCESSOR_CACHE_SIZE,
    ACCESSOR_CACHE_ROW_BYTES as ACCESSOR_CACHE_ENTRY_BYTES, ACCESSOR_CALLEE_OFF as ACCESSOR_CALLEE,
    ACCESSOR_HOLDER_PTR_OFF as ACCESSOR_HOLDER_PTR,
    ACCESSOR_HOLDER_SHAPE_OFF as ACCESSOR_HOLDER_SHAPE,
    ACCESSOR_RECV_SHAPE_OFF as ACCESSOR_RECV_SHAPE,
};
// Builtin callee-identity cell indexes (u64 cells at helpers.builtin_cells_base
// + 8*BC_*; the reactor arms/re-arms them in the same order).
pub const BC_ARR_PUSH: u32 = 0;
pub const BC_ARR_POP: u32 = 1;
pub const BC_MATH_SQRT: u32 = 2;
pub const BC_MATH_ABS: u32 = 3;
pub const BC_MATH_FLOOR: u32 = 4;
pub const BC_MATH_MIN: u32 = 5;
pub const BC_MATH_MAX: u32 = 6;
pub const BC_MATH_SIN: u32 = 7;
pub const BC_MATH_COS: u32 = 8;
pub const BC_MATH_POW: u32 = 9;
pub const BC_PARSE_INT: u32 = 10;
pub const BC_MATH_CLZ32: u32 = 11;
pub const BC_MATH_IMUL: u32 = 12;
// String.prototype direct-dispatch identity cells (Part B): callee-identity
// against the pristine native, receiver-is-string guard, then invoke the
// native in place (night_runtime_native_dispatch) -- no classify/apply/rope machinery.
/// Startup-written Math native-pointer slots (4 bytes each; 0 = unavailable):
/// the math arms compare a classified-native callee's JSNative (JSFunction
/// slot 1 low word) against these. Pointer identity is clone-proof -- the
/// Math.max property and the std_Math_max self-hosting intrinsic are
/// different JSFunction objects wrapping the same native, so the old
/// value-identity cells missed every self-hosted call site.
pub use crate::region_shape::MATH_NATIVE_SLOTS;
pub const MN_MAX: u32 = 0;
pub const MN_MIN: u32 = 1;
pub const MN_POW: u32 = 2;
pub const MN_SQRT: u32 = 3;
pub const MN_ABS: u32 = 4;
pub const MN_FLOOR: u32 = 5;
pub const MN_CEIL: u32 = 6;
pub const MN_TRUNC: u32 = 7;
pub const MN_FROUND: u32 = 8;
pub const MN_IMUL: u32 = 9;
pub const MN_CLZ32: u32 = 10;
pub const MN_SIN: u32 = 11;
pub const MN_COS: u32 = 12;

pub const BC_STR_INDEXOF: u32 = 13;
pub const BC_STR_LASTINDEXOF: u32 = 14;
pub const BC_STR_SLICE: u32 = 15;
pub const BC_STR_SUBSTRING: u32 = 16;
pub const BC_STR_TOLOWERCASE: u32 = 17;
pub const BC_STR_TOUPPERCASE: u32 = 18;
pub const BC_STR_TRIM: u32 = 19;
pub const BC_STR_STARTSWITH: u32 = 20;
pub const BC_STR_ENDSWITH: u32 = 21;
pub const BC_STR_INCLUDES: u32 = 22;
/// The pristine Array constructor (construct-site identity: the compiled
/// `new Array()` bump arm; runtime NightRuntime.cpp arms it at startup).
pub const BC_ARRAY_CTOR: u32 = 23;
/// `Function.prototype.apply`. The apply-forward fast arm calls the resolved
/// target directly, which is only correct if the `.apply` the site reached is
/// the pristine one; this is the helper's `native() == js::fun_apply` test as
/// a value-identity compare.
pub const BC_FUN_APPLY: u32 = 24;
/// `Function.prototype.call` and `Object.prototype.hasOwnProperty`: the
/// `hasOwnProperty.call(o, k)` arm guards both by value identity.
pub const BC_FUN_CALL: u32 = 25;
pub const BC_OBJ_HASOWN: u32 = 26;
pub use crate::region_shape::BUILTIN_CELL_COUNT as BC_COUNT;
const SHAPE_BASESHAPE_OFFSET: u32 = 0; // Shape::offsetOfBaseShape (header word)
const BASESHAPE_CLASP_OFFSET: u32 = 0; // BaseShape::offsetOfClasp (header word)
                                       // Typed-array reserved-slot payload offsets (wasm32, JS_NUNBOX32): fixed slots
                                       // at 16 + i*8, PrivateValue payload in the low 32 bits. LENGTH_SLOT=1 (element
                                       // count), DATA_SLOT=3 (element data pointer, inline or out-of-line).
const TA_LENGTH_PAYLOAD_OFFSET: u32 = 16 + 8;
const TA_DATA_PAYLOAD_OFFSET: u32 = 16 + 8 * 3;

// Inline property-IC hit path. `shape_` is the first field of every JSObject
// (offset 0); the reactor `static_assert`s `offsetof(JS::shadow::Object, shape)
// == 0`. The per-site inline cache (in the reserved `gPropIC` linear-memory
// region) is one monomorphic way of five `u32` fields in this order:
// [recvShape, gen, holderPtr, holderShape, slotEnc] -- polymorphism is served
// by the poly sentinel plus the mega tables, not by extra ways. The way
// count, way size and stride are shared with NightRuntime.cpp through
// runtime/NightRegionShape.h -- see `crate::region_shape`.
const SHAPE_OFFSET: u32 = 0;
use crate::region_shape::{INLINE_IC_WAYS, INLINE_IC_WAY_BYTES};
/// Per-site add-transition row appended after the way (size shared through
/// NightRegionShape.h): [oldShape, newShape, slotOff (fixed-slot byte offset; 0 =
/// dynamic slot -> helper), absSlot, protoPtr0, protoShape0, protoPtr1,
/// protoShape1]. Written by the set-miss helper's populate; the inline set
/// arm replays the add (fresh fixed-slot store + shape word swap) when the
/// receiver shape matches oldShape and the cached proto shape words are
/// live. Adds on >2-hop proto chains never fill the row -- the helper's
/// global (shape, atom) set-add table serves them (growing the row to 4 hops
/// would widen the stride and cost dcache).
/// GC-zeroed with the rest of the region; also zeroed at minor-GC end when a
/// row cached a nursery proto.
const IC_TRANS_ROW_OFF: u32 = INLINE_IC_WAYS * INLINE_IC_WAY_BYTES;
pub use crate::region_shape::INLINE_IC_STRIDE;
use crate::region_shape::INLINE_IC_TRANS_BYTES as IC_TRANS_ROW_BYTES;
const _: () = assert!(INLINE_IC_STRIDE == IC_TRANS_ROW_OFF + IC_TRANS_ROW_BYTES);
// Global megamorphic get table: MEGA_GET_SIZE direct-mapped entries of
// [shape, atomId, holderPtr, holderShape, slotEnc, pad] (shape shared through
// NightRegionShape.h); the hash is mirrored by NightRuntime.cpp's
// MegaGetSlot. GC-zeroed.
pub use crate::region_shape::{MEGA_GET_ENTRY_BYTES, MEGA_GET_SIZE};

// Global megamorphic set table: direct-mapped linmem entries the inline
// poly-set probe reads (same hash as mega-get); the miss helper fills them.
// [shape @0, atomId @4, slotEnc @8, absSlot @12]; zero = empty; GC-zeroed.
pub use crate::region_shape::{MEGA_SET_ENTRY_BYTES, MEGA_SET_SIZE};

// Primitive-type bits (declaration order in `PrimType`); the canonical
// definitions live in the op-semantics vocabulary.
pub(crate) use crate::facts::{CallForm, Claim, LikelyFacts};
pub(crate) use crate::ids::{ArgIndex, JsString, NameId, Names, Pc, ScriptId, Site, StampKey};
pub(crate) use crate::opsem::{
    Prims, TaKind, ValueRange, PRIM_BIGINT, PRIM_BOOLEAN, PRIM_DOUBLE, PRIM_INT32, PRIM_NULL,
    PRIM_STRING, PRIM_SYMBOL, PRIM_UNDEFINED,
};

/// Likely this-layout input for one method script (from the likely-facts
/// analysis via the
/// merge): the guard cell address, the layout id (indexing the reactor's
/// parsed table), and the ordered field names (position == predicted fixed
/// slot).
pub struct ThisLayoutIn {
    pub cell_addr: u32,
    pub layout_id: u32,
    /// Highest layout id of the predictor group when this is a range home
    /// (contiguous ctor-class ids); == layout_id for an exact ctor home.
    pub hi_layout_id: u32,
    pub fields: Vec<NameId>,
    /// Per-field likely value claims, parallel to `fields`.
    pub masks: Vec<Claim>,
    /// Per-field likely value RANGES, parallel to `fields` (None = no
    /// claim; only ever set where `masks` also claims).
    pub ranges: Vec<Option<ValueRange>>,
    /// The script is a this-forwarded init delegate (its layout-field
    /// stores are instance inits: the layout-set slow tail carries the
    /// add-transition arm so construction preserves the sentinel).
    pub init_home: bool,
}

#[derive(Clone, Copy)]
pub struct PropSiteIn {
    pub cell_addr: u32,
    pub slot: u32,
    pub layout_id: u32,
    /// Highest layout id of the predictor group (range fact); ==
    /// layout_id for an exact ctor-class fact.
    pub hi_layout_id: u32,
    /// The field's likely value mask (PRIM_* bits; 0 = no claim).
    pub claim: Claim,
    /// The field's likely value range (None = no claim). Consumed
    /// checklessly behind the RANGES stamp bit, so it seeds the pushed
    /// operand's interval directly.
    pub range: Option<ValueRange>,
    /// Whether a receiver of the site's layouts can carry the SHALLOW bit
    /// at all: the allocation seeds it only for a layout with masked
    /// fields, and a prefix-stamped object (a two-phase or post-fill
    /// row) keeps it only if its prefix layout seeded it. A site whose
    /// receivers never carry it takes the SLOTS-guarded load with a tag
    /// test instead of the two-bit dispatch, which would miss every time.
    pub shallow_possible: bool,
}

/// Per-layout-ctor stamp input: at each return of the ctor's compiled body,
/// if `this` is an object whose live shape equals the layout's validated
/// shape (same `[shape, gen]` cell the method prologues use; primed via
/// `validate_this_layout` when cold), store the likely-class index
/// `layout_id + 1` into the object's class-idx word.
#[derive(Clone)]
pub struct StampCtorIn {
    pub cell_addr: u32,
    pub layout_id: u32,
    /// The ctor's own layout field names + masks (for the checked init
    /// stores that keep the CONSTRUCTING sentinel alive).
    pub fields: Vec<NameId>,
    pub masks: Vec<Claim>,
    /// Per-field likely value RANGES, parallel to `fields`: the checked
    /// init stores maintain these alongside the masks.
    pub ranges: Vec<Option<ValueRange>>,
    /// Layout ids whose field lists are proper nonempty prefixes of this
    /// layout's: the receivers a delegate-exit restamp may advance (their
    /// validity-bit history covers this clump).
    pub prefix_keys: Vec<u32>,
    /// Byte-offset add-check bound: FIXED_SLOTS_BASE + 8 * the longest
    /// prefix length over every layout extending this one (self included).
    /// An unpredicted add at an assigned offset below this bound could sit
    /// inside a clump member's guarded prefix and must clear SLOTS.
    pub ext_bound: u32,
}

/// Outcome of trying to translate one script.
pub enum Outcome {
    /// Translated successfully: the built body and its signature, ready to be
    /// appended into the module and placed in the funcref table by the caller.
    Compiled {
        sig: Signature,
        body: FunctionBody,
        /// Likely-callee placeholders: `(expected I32Const, Call value,
        /// callee_source_id)`. Post-placement the caller patches the const to
        /// the callee's funcref-table index (the runtime guard compares the
        /// classified funcidx against it) and the `Call` to the callee body;
        /// an uncompiled callee leaves the const at `u32::MAX` (arm dead).
        likely_patches: Vec<(Value, Value, u32)>,
        /// Fuse-guarded direct-call placeholders: `(enabled I32Const,
        /// Call value, binding_id, callee_source_id)`. Post-placement the
        /// caller patches the `Call` to the callee body and the const to 1,
        /// and records binding_id -> callee table index for the reactor's
        /// arm-time validation; an uncompiled callee (or a binding predicted
        /// with conflicting callees) leaves the const at 0 (arm dead).
        fuse_call_patches: Vec<FuseCallPatch>,
        /// Callee value-cell address placeholders: `(addr I32Const, row)`.
        /// Post-translation (once the prop-IC region size fixes the cell
        /// region's base) mod.rs patches each const to
        /// `call_cells_base + CALL_CELL_BYTES * row`. Row 0 is the shared
        /// trash row (nursery-callee stores divert there via `select` instead
        /// of branching around the store); a site's cell is row `idx + 1`.
        call_cell_patches: Vec<(Value, u32)>,
        /// Inline-alloc cell address placeholders: `(addr I32Const, row)`;
        /// mod.rs patches each const to `alloc_cells_base +
        /// ALLOC_CELL_BYTES * row` once the region base is known.
        alloc_cell_patches: Vec<(Value, u32)>,
        /// Instanceof cell address placeholders: `(addr I32Const, row)`; mod.rs
        /// patches each const to `iof_cells_base + IOF_CELL_BYTES * row`. A
        /// site's cell is row `idx + 1` (row 0 reserved so a missed patch is
        /// obvious); the placeholder-only 0 rows never occur (no trash row).
        iof_cell_patches: Vec<(Value, u32)>,
        /// Construct-`this` cell address placeholders: `(addr I32Const, row)`;
        /// mod.rs patches each const to `construct_cells_base +
        /// CONSTRUCT_CELL_BYTES * row` (row `idx + 1`).
        construct_cell_patches: Vec<(Value, u32)>,
        /// String-literal blob address placeholders: `(addr I32Const,
        /// blob offset)`; mod.rs patches each const to `strlit_blob_base +
        /// offset` once the blob segment is placed.
        strlit_patches: Vec<(Value, u32)>,
        /// Intrinsic value-cell address placeholders: `(addr I32Const, row)`;
        /// mod.rs patches each const to `intrinsic_cells_base +
        /// INTRINSIC_CELL_BYTES * row`.
        intrinsic_cell_patches: Vec<(Value, u32)>,
        /// Prop-IC way/row address consts: `(addr I32Const, byte offset from
        /// prop_ic_base)`. Emitted with the real address already baked
        /// (patching them to `prop_ic_base + offset` is a no-op there); an
        /// in-process caller re-patches them against its allocated region.
        prop_ic_patches: Vec<(Value, u32)>,
        /// Adapter-offset placeholders (widened-ABI `call_indirect`): the
        /// Body's table slot is `funcidx - offset`, where funcidx is the
        /// callee's adapter slot. Bodies precede the contiguous adapter
        /// block, so the offset is the compiled-script count -- known only
        /// post-loop; mod.rs patches each placeholder const to it.
        body_off_patches: Vec<Value>,
        /// Ctor-nslots region base placeholders: an unresolved construct
        /// site's fast arm reads `region[4 * funcidx]` (u32 per
        /// funcref-table index, 0 = unknown) to size `create_this` for the
        /// classified ctor's full layout. mod.rs patches the base once the
        /// region is placed; the production caller fills the content from
        /// `ctor_nslots` x `sid_to_index`.
        ctor_nslots_patches: Vec<Value>,
    },
    /// Not compiled -- the script is left interpreted (the always-safe
    /// fallback). The reason (first unsupported op, or a type the fast path
    /// cannot yet handle) is reported for the coverage line. Skipping is sound;
    /// it is never a silent miscompile.
    Skipped(String),
}

/// Every primitive bit set (`PRIM_INT32 .. PRIM_BIGINT`).
pub(crate) use crate::opsem::ALL_PRIMS;

/// The absolute target pc of a relative branch at `pc` with signed `off`.
pub(crate) fn branch_target(pc: Pc, off: i32) -> Pc {
    pc.branch(off)
}

/// Number of frame local slots: the highest local index accessed by
/// `GetLocal`/`SetLocal`/`InitLexical`, plus one (0 if none).
pub(crate) fn max_locals(script: &Script) -> u32 {
    struct Scan<'b> {
        max: &'b mut u32,
    }
    impl Scan<'_> {
        fn note(&mut self, n: u32) {
            *self.max = (*self.max).max(n + 1);
        }
    }
    impl OpcodeVisitor for Scan<'_> {
        fn get_local(&mut self, n: u32) {
            self.note(n);
        }
        fn set_local(&mut self, n: u32) {
            self.note(n);
        }
        fn init_lexical(&mut self, n: u32) {
            self.note(n);
        }
    }
    let mut max = 0u32;
    script.parser().visit(Scan { max: &mut max });
    max
}

thread_local! {
    static EDGE_REBOX: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

/// Back edges whose target is not a `LoopHead`, as (branch pc, target pc).
///
/// SpiderMonkey emits a `LoopHead` at every loop header, so this is empty for
/// any bytecode the parser produced. It is not empty for hand-written
/// bytecode, and the difference matters: the loop-token discipline that makes
/// the emitted version graph reducible (DESIGN.md section 4.9) is keyed on
/// the loop intervals, and an unmarked header gets no interval, hence no
/// token, hence no header re-labeling -- so the cycle can acquire a second
/// entry. The driver refuses such a script rather than emitting a graph whose
/// loop analysis it cannot run.
pub(crate) fn unmarked_back_edges(script: &Script) -> Vec<(u32, u32)> {
    let scan = loop_scan(script);
    scan.back_edges
        .into_iter()
        .filter(|(_, target)| !scan.loopheads.contains(target))
        .collect()
}

pub(crate) fn scan_loop_intervals(script: &Script) -> Vec<(u32, u32)> {
    let scan = loop_scan(script);
    let mut m: HashMap<u32, u32> = HashMap::default();
    for &(bpc, target) in &scan.back_edges {
        if scan.loopheads.contains(&target) {
            let end = bpc + 5;
            let e = m.entry(target).or_insert(end);
            *e = (*e).max(end);
        }
    }
    m.into_iter().collect()
}

/// The one bytecode walk both loop queries need: every `LoopHead` pc, and
/// every backwards branch as (branch pc, target pc).
struct LoopScan {
    pc: Pc,
    loopheads: HashSet<u32>,
    back_edges: Vec<(u32, u32)>,
}

fn loop_scan(script: &Script) -> LoopScan {
    struct Scan(LoopScan);
    impl Scan {
        fn branch(&mut self, off: i32) {
            if off < 0 {
                let pc = self.0.pc;
                self.0
                    .back_edges
                    .push((pc.get(), branch_target(pc, off).get()));
            }
        }
    }
    impl OpcodeVisitor for Scan {
        fn before_op(&mut self, pc: Pc, op: JSOp, _u: usize, _d: usize) {
            self.0.pc = pc;
            if op == JSOp::LoopHead {
                self.0.loopheads.insert(pc.get());
            }
        }
        fn goto_(&mut self, off: i32) {
            self.branch(off);
        }
        fn jump_if_false(&mut self, off: i32) {
            self.branch(off);
        }
        fn jump_if_true(&mut self, off: i32) {
            self.branch(off);
        }
        fn and_(&mut self, off: i32) {
            self.branch(off);
        }
        fn or_(&mut self, off: i32) {
            self.branch(off);
        }
        fn coalesce(&mut self, off: i32) {
            self.branch(off);
        }
    }
    script
        .parser()
        .visit(Scan(LoopScan {
            pc: Pc::new(0),
            loopheads: HashSet::default(),
            back_edges: Vec::new(),
        }))
        .0
}

/// Whether the script uses any closure op (`Lambda`/`GetAliasedVar`/
/// `SetAliasedVar`), so it needs an environment head in the prologue.
pub(crate) fn uses_env_ops(script: &Script) -> bool {
    use JSOp::*;
    script.parser().opcodes().any(|op| {
        matches!(
            op,
            Lambda
                | GetAliasedVar
                | SetAliasedVar
                | GetAliasedDebugVar
                | InitAliasedLexical
                | PushLexicalEnv
                | PopLexicalEnv
                | FreshenLexicalEnv
                | RecreateLexicalEnv
                | PushClassBodyEnv
                | PushVarEnv
                | EnterWith
                | LeaveWith
                | GetName
                | BindName
                | BindUnqualifiedName
                | BindVar
                | DelName
        )
    })
}

/// Whether the script reads `new.target` (directly or via `super()`), so the
/// prologue must spill the 6th ABI param into a rooted frame slot: the raw
/// i64 param SSA is not forwarded by a moving GC, and any may-GC call before
/// the reading op would leave it stale.
pub(crate) fn uses_new_target(script: &Script) -> bool {
    script.parser().opcodes().any(|op| {
        matches!(
            op,
            JSOp::NewTarget | JSOp::SuperCall | JSOp::SpreadSuperCall
        )
    })
}

/// Whether the script pushes the arguments object (`JSOp::Arguments`), so the
/// prologue must capture it before locals-init: actuals beyond `nargs` live
/// where the locals region starts (`local_base = 16 + 8*nargs`) and are
/// clobbered by the `undefined` seeding. Capturing once in the prologue also
/// gives the required per-activation identity (the interpreter frame caches
/// its args object the same way).
pub(crate) fn uses_arguments(script: &Script) -> bool {
    script
        .parser()
        .opcodes()
        .any(|op| matches!(op, JSOp::Arguments))
}

/// Whether the script reads actual args directly (`JSOp::Rest`/`GetActualArg`),
/// so the frame must keep the actuals beyond the formals intact: they live
/// where the locals region starts and are otherwise clobbered by locals-init.
/// This piggy-backs on the `needs_args_obj` vp-rebase (which moves the variable
/// region above `sp + 8*max(argc - nargs, 0)`), without building an args object.
pub(crate) fn uses_actual_args(script: &Script) -> bool {
    script
        .parser()
        .opcodes()
        .any(|op| matches!(op, JSOp::Rest | JSOp::GetActualArg))
}

/// The set of call pcs where `script`'s `arguments` is forwarded into a
/// syntactic `T.apply(this, arguments)` call -- or `None` when the arguments
/// object cannot be soundly elided. Sound elision requires:
///   - `nargs == 0` (no formals => no mapped aliasing, no `GetArg`/`SetArg`
///     through the object, and the caller-frame actual slots are immutable for
///     the activation -- they are the would-be `arguments` elements);
///   - every value the `Arguments` op produces flows only into such calls,
///     tracked linearly: it may be stored once into a dedicated local (the
///     `arguments` var binding's `Arguments; SetLocal k; Pop` prologue), and
///     every `GetLocal k` must feed an apply-shaped call (kind 2, argc 2) as
///     the immediately-following op. Any other producer/consumer (Dup, another
///     store, an aliased store, `ArgumentsLength`, a jump in between, a second
///     write to `k`) makes the object observable => `None`.
/// Membership keys on the syntactic apply-site map (the callee node is a
/// `.apply` property read) -- compile-time target resolution is not required:
/// the forward helper reads the real callee/target from the stack at runtime,
/// enters a compiled target directly, and falls back to a faithful
/// reconstruction otherwise. What this check must guarantee is only that the
/// object itself is unobservable.
pub(crate) fn compute_apply_fwd_pcs(
    script: &Script,
    apply_sites: &HashMap<Site, CallForm>,
    source_id: u32,
) -> Option<HashSet<Pc>> {
    if script.nargs != 0 {
        return None;
    }
    struct Scan<'a> {
        apply_sites: &'a HashMap<Site, CallForm>,
        sid: u32,
        /// The single local holding the arguments value (its var binding).
        args_local: Option<u32>,
        /// The args value is on top of the operand stack entering the next op.
        on_stack: bool,
        /// The current op is the `SetLocal` that stores the args value.
        expect_set: bool,
        ok: bool,
        saw: bool,
        fwd: HashSet<Pc>,
    }
    impl OpcodeVisitor for Scan<'_> {
        fn before_op(&mut self, pc: Pc, op: JSOp, nuses: usize, _ndefs: usize) {
            use JSOp::*;
            if !self.ok {
                return;
            }
            let entering = self.on_stack;
            self.on_stack = false;
            self.expect_set = false;
            if entering {
                match op {
                    // The prologue store; SetLocal keeps the value on top.
                    SetLocal => {
                        self.expect_set = true;
                        self.on_stack = true;
                    }
                    Pop => {}
                    Call | CallContent | CallIgnoresRv
                        if nuses == 4
                            && self
                                .apply_sites
                                .get(&Site::new(ScriptId::new(self.sid), pc))
                                .is_some_and(|&k| k == CallForm::Apply) =>
                    {
                        self.fwd.insert(Pc::new(pc.get()));
                    }
                    _ => self.ok = false,
                }
            } else {
                match op {
                    Arguments => {
                        self.saw = true;
                        self.on_stack = true;
                    }
                    ArgumentsLength => self.ok = false,
                    _ => {}
                }
            }
        }
        fn set_local(&mut self, n: u32) {
            if !self.ok {
                return;
            }
            if self.expect_set {
                match self.args_local {
                    None => self.args_local = Some(n),
                    Some(k) if k == n => {}
                    Some(_) => self.ok = false,
                }
            } else if self.args_local == Some(n) {
                // Overwriting the args local with another value.
                self.ok = false;
            }
        }
        fn init_lexical(&mut self, n: u32) {
            self.set_local(n);
        }
        fn get_local(&mut self, n: u32) {
            if !self.ok {
                return;
            }
            if self.args_local == Some(n) {
                self.on_stack = true;
            }
        }
    }
    let s = script.parser().visit(Scan {
        apply_sites,
        sid: source_id,
        args_local: None,
        on_stack: false,
        expect_set: false,
        ok: true,
        saw: false,
        fwd: HashSet::default(),
    });
    if s.ok && s.saw && !s.fwd.is_empty() {
        Some(s.fwd)
    } else {
        None
    }
}

/// Call pcs whose callee operand came from a `GetGName` of a syntactic
/// global binding, mapped to that binding id. Carrying it on the operand
/// instead does not work under per-op BBV, which loses operand-local state at
/// every block boundary, so the pcs are pre-scanned.
///
/// Tracked over a straight-line run only: the symbolic stack is cleared at
/// every `JumpTarget`/`LoopHead` (a merge point can be reached with different
/// operands). Generic stack effects come from the visitor's nuses/ndefs, so a
/// new opcode cannot silently desynchronize the model.
///
/// A wrong attribution is harmless, not unsound: the emitted arm still proves
/// itself with the cell's own bits compare, and the reactor only ever arms a
/// cell with a value whose AOT target is the expected callee. Getting it wrong
/// can only cost a missed fast path (or a spurious binding conflict).
/// Also returned: the call pcs whose callee is a property read off a
/// `GetGName` value (`Global.method(...)`, the static-method shape, which
/// on the benchmarks is almost always an engine native such as
/// `String.fromCharCode`) -- the population the native-route keep arms
/// beside the `.call`/`.apply` sites (call.rs `pre_native`).
pub(crate) fn compute_gname_call_bids(
    source: &Source,
    script: &Script,
    names: &Names,
    syn_gnames: &HashMap<NameId, u32>,
) -> (HashMap<Pc, u32>, HashSet<Pc>) {
    #[derive(Clone, Copy)]
    enum Sym {
        Top,
        /// A GetGName, with its syntactic binding when it has one.
        GName(Option<u32>),
        /// A GetProp off a GetGName.
        Method,
    }
    struct Scan<'a> {
        source: &'a Source,
        script: &'a Script,
        names: &'a Names,
        syn_gnames: &'a HashMap<NameId, u32>,
        /// Symbolic operand stack.
        stack: Vec<Sym>,
        /// Set by `before_op` for the `get_g_name` callback to consume.
        pending_gname: bool,
        out: HashMap<Pc, u32>,
        methods: HashSet<Pc>,
    }
    impl OpcodeVisitor for Scan<'_> {
        fn before_op(&mut self, pc: Pc, op: JSOp, nuses: usize, ndefs: usize) {
            use JSOp::*;
            self.pending_gname = false;
            if matches!(op, JumpTarget | LoopHead) {
                self.stack.clear();
                return;
            }
            if let Call | CallContent | CallIgnoresRv | CallIter | CallContentIter = op {
                // Frame is [callee, this, args..]; nuses covers all of it.
                if self.stack.len() >= nuses {
                    match self.stack[self.stack.len() - nuses] {
                        Sym::GName(Some(bid)) => {
                            self.out.insert(pc, bid);
                        }
                        Sym::Method => {
                            self.methods.insert(pc);
                        }
                        _ => {}
                    }
                }
            }
            if self.stack.len() < nuses {
                // Desynchronized (a jump landed mid-expression): resync empty
                // rather than guess -- every entry is a hint, never a proof.
                self.stack.clear();
            } else {
                match op {
                    // The shapes that carry a marker through: `Dup` copies
                    // the top, `Swap` exchanges the top two, a `GetProp` off
                    // a global value marks a method.
                    Dup => {
                        let top = *self.stack.last().unwrap();
                        self.stack.push(top);
                        return;
                    }
                    Swap => {
                        let n = self.stack.len();
                        self.stack.swap(n - 1, n - 2);
                        return;
                    }
                    GetProp if nuses == 1 && ndefs == 1 => {
                        let recv = self.stack.pop().unwrap();
                        self.stack.push(match recv {
                            Sym::GName(_) => Sym::Method,
                            _ => Sym::Top,
                        });
                        return;
                    }
                    _ => {}
                }
                self.stack.truncate(self.stack.len() - nuses);
            }
            if op == GetGName && ndefs == 1 {
                self.pending_gname = true;
                return;
            }
            self.stack.extend((0..ndefs).map(|_| Sym::Top));
        }
        fn get_g_name(&mut self, name_index: u32) {
            if !self.pending_gname {
                return;
            }
            let bid = self
                .script
                .gcthings
                .get(name_index as usize)
                .and_then(|&gc| match self.source.object(gc) {
                    SourceObject::String(s) => self
                        .names
                        .lookup(s.chars())
                        .and_then(|n| self.syn_gnames.get(&n).copied()),
                    _ => None,
                });
            self.stack.push(Sym::GName(bid));
        }
    }
    let s = script.parser().visit(Scan {
        source,
        script,
        names,
        syn_gnames,
        stack: Vec::new(),
        pending_gname: false,
        out: HashMap::default(),
        methods: HashSet::default(),
    });
    (s.out, s.methods)
}

/// Capability gate for the environment model: the translator models a
/// function's environment head as an optional single `CallObject` over the
/// genuine `callee->environment()`. Returns `Some(reason)` (decline) when the
/// function would instantiate environment objects we don't model -- currently
/// a named-lambda environment (created in the prologue, inserting a chain link
/// the runtime helpers' `hops` walk would otherwise miscount). Block/`with`/
/// extra-body-var environments are gated separately by their (unsupported) ops
/// (`PushLexicalEnv`/`EnterWith`/`InitAliasedLexical`/...).
pub(crate) fn env_unsupported(source: &Source, script: &Script) -> Option<String> {
    let bs_id = script.body_scope?;
    let SourceObject::Scope(ScopeData {
        kind, enclosing, ..
    }) = source.object(bs_id)
    else {
        return Some("aliased vars but body scope is not a Scope".to_string());
    };
    // ScopeKind::Function == 0, ScopeKind::Global == 12 (js/src/vm/Scope.h).
    // A Function body's env head is its (optional) CallObject over
    // `callee->environment()`; a Global body's env head is the global lexical
    // environment, which already exists at runtime (nothing is allocated) and is
    // what `NightEnvSetup` returns for a global script. Any other body
    // scope with aliased vars is an environment shape we don't model.
    if *kind != 0 && *kind != 12 {
        return Some(format!(
            "aliased vars under non-Function body scope (kind {kind})"
        ));
    }
    if let Some(enc_id) = enclosing {
        if let SourceObject::Scope(ScopeData {
            is_named_lambda,
            has_environment,
            ..
        }) = source.object(*enc_id)
        {
            if *is_named_lambda && *has_environment {
                return Some("named-lambda environment unsupported".to_string());
            }
        }
    }
    None
}

/// The stable per-module translation context threaded into every script's
/// translation: the resolved helpers, the shared source, the module-wide
/// switches (inline budget, night_compiler/bigint gates), and the read-only analysis
/// tables (likely-class / call / apply / layout / gname-fuse maps). Built once
/// per `translate_all` run and passed by reference; the genuinely per-script
/// inputs (`m`, `atoms`, `source_id`, `script`, `is_global`) stay positional.
pub struct TranslateCtx<'a> {
    pub helpers: Helpers,
    pub source: &'a Source,
    pub opts: &'a Options,
    pub bigint_free: bool,
    pub syn_gnames: &'a HashMap<NameId, u32>,
    /// See `EnvLayout::gcell_bids`.
    pub gcell_bids: &'a HashSet<u32>,
    pub likely_fns: &'a HashMap<NameId, ScriptId>,
    /// The analysis output. Tables the translator reads unchanged are read
    /// straight off this; the `*_in` fields below are the ones the env
    /// layout DERIVES (address-bearing descriptors, merged views).
    pub facts: &'a LikelyFacts,
    /// Sids whose returned flags word some caller can consume (bbv
    /// compute_flag_demand); only these bodies pay accumulator ORs.
    pub flag_demand: &'a rustc_hash::FxHashSet<ScriptId>,
    pub this_layouts_in: &'a HashMap<ScriptId, ThisLayoutIn>,
    pub stamp_ctors_in: &'a HashMap<ScriptId, StampCtorIn>,
    /// Per property name: every layout that predicts it, and where. The
    /// unknown-receiver add arms compare the receiver's runtime stamp key
    /// against these instead of clearing SLOTS on any in-prefix add.
    pub layout_addpred_in: &'a HashMap<NameId, Vec<AddPred>>,
    /// Per ctor script: the slot count `this` must be allocated with to hold
    /// the ctor's full layout in fixed slots.
    pub ctor_nslots_in: &'a HashMap<ScriptId, u32>,
    /// Per this-forwarded init delegate: the stamp its exit advances to.
    pub deleg_restamps_in: &'a HashMap<ScriptId, StampCtorIn>,
    /// Per formal-receiver fill script: (formal index, the stamp its
    /// returns advance the formal's object to).
    pub arg_restamps_in: &'a HashMap<ScriptId, (u32, StampCtorIn)>,
    /// Per post-construction fill site: (local index, the stamp the
    /// sequence's last add advances the local's object to).
    pub local_restamps_in: &'a HashMap<Site, (u32, StampCtorIn)>,
    /// Shared-generated-ctor construct sites (`construct_site_keys`):
    /// per-site stamp descriptors, consulted where the script-keyed
    /// stamp/nslots maps miss (one ctor script, many classes).
    pub construct_sites_in: &'a HashMap<Site, StampCtorIn>,
    /// Object-literal stamp sites: site -> stamped layout id (rows whose
    /// fields all sit in fixed slots). The allocation stores the idx +
    /// SLOTS word so the literal-born population's class-fact guards hit.
    pub lit_stamps_in: &'a HashMap<Site, u32>,
    pub prop_sites_in: &'a HashMap<Site, PropSiteIn>,
    /// Stamp key -> field name -> value mask. Layout-wide, so a receiver
    /// carrying a proven class fact can answer "does this field hold a
    /// number claim?" at a site with no row of its own (see bbv's
    /// store-choke elision).
    pub layout_field_masks_in: &'a HashMap<StampKey, HashMap<NameId, Claim>>,
    /// Same keying as `layout_field_masks_in`, the range claims (absent
    /// name = no claim). Drives the store choke's range action.
    pub layout_field_ranges_in: &'a HashMap<StampKey, HashMap<NameId, ValueRange>>,
    /// Array alloc site -> the whole class word a compiled allocation
    /// writes: the array's stamp key plus the validity bits that seed with
    /// it (`CLASS_WORD_*`), not a bare key.
    pub array_stamp_in: &'a HashMap<Site, u32>,
    /// Element site -> what the read fold may assume and what the write
    /// owes.
    pub array_elem_in: &'a HashMap<Site, ArrayElemIn>,
    /// Intersection of every array claim (see `EnvLayout`).
    pub array_any_claim: Option<ValueRange>,
    /// `facts.elem_sites` merged with `facts.field_sites` (see `EnvLayout`).
    pub likely_elems: &'a HashMap<Site, Claim>,
    /// Global names whose binding is fused to a constant.
    pub fused_gnames: &'a HashMap<NameId, FusedGname>,
}

/// One layout's prediction for a property name: the stamp key a receiver
/// must carry, and the byte offset that layout puts the name at. The
/// unknown-receiver add arm keeps SLOTS when the receiver's live key matches
/// a pair whose offset is the one being assigned.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct AddPred {
    pub key: StampKey,
    pub offset: u32,
}

/// What the analysis predicts about one element site's receiver: the stamp
/// key that identifies its array population, and the value mask and range
/// every element of that population is claimed to hold.
#[derive(Clone, Copy)]
pub struct ArrayElemIn {
    pub key: StampKey,
    pub mask: Prims,
    pub range: ValueRange,
}

/// A global binding proven to hold one constant: the address of the fuse
/// word that invalidates the claim, and the boxed value to fold in while it
/// reads zero.
#[derive(Clone, Copy)]
pub struct FusedGname {
    pub fuse_addr: u32,
    pub boxed: u64,
}

/// One fuse-guarded direct-call arm a body claimed. `wasm/mod.rs` patches
/// `enabled` to 1 and `call` to the callee once the binding's expected callee
/// is confirmed unique and compiled; an arm whose callee never compiles stays
/// dead behind its `enabled` 0.
#[derive(Clone, Copy)]
pub struct FuseCallPatch {
    /// The `enabled` constant the emitted guard tests.
    pub enabled: Value,
    /// The stub call the direct call replaces.
    pub call: Value,
    /// The global binding the callee was read from.
    pub binding: u32,
    /// The callee this arm predicts.
    pub callee: ScriptId,
}

/// The value-boxing forms that must agree between the synthetic helper
/// bodies here and the inline lowerings in `bbv`: a NaN reaching the boxed
/// representation has to be canonical (a raw NaN payload aliases the nunbox
/// tag space), and a double that is exactly an int32 -- but not -0 -- re-tags
/// as int32. Two emitters, one definition.
pub(super) trait BoxEmit {
    fn emit_un(&mut self, op: Operator, a: Value, result: Type) -> Value;
    fn emit_bin(&mut self, op: Operator, a: Value, b: Value, result: Type) -> Value;
    fn emit_i64c(&mut self, value: u64) -> Value;
    fn emit_sel(&mut self, ty: Type, a: Value, b: Value, cond: Value) -> Value;
}

pub(super) fn box_int32<E: BoxEmit>(e: &mut E, v: Value) -> Value {
    let payload = e.emit_un(Operator::I64ExtendI32U, v, Type::I64);
    let tag = e.emit_i64c(TAG_INT32 << 32);
    e.emit_bin(Operator::I64Or, payload, tag, Type::I64)
}

pub(super) fn canon_nan_f64<E: BoxEmit>(e: &mut E, f: Value) -> Value {
    let selfeq = e.emit_bin(Operator::F64Eq, f, f, Type::I32);
    let canon_bits = e.emit_i64c(0x7FF8_0000_0000_0000);
    let canon = e.emit_un(Operator::F64ReinterpretI64, canon_bits, Type::F64);
    e.emit_sel(Type::F64, f, canon, selfeq)
}

pub(super) fn box_f64_canonical<E: BoxEmit>(e: &mut E, f: Value) -> Value {
    let i = e.emit_un(Operator::I32TruncSatF64S, f, Type::I32);
    let back = e.emit_un(Operator::F64ConvertI32S, i, Type::F64);
    let eq = e.emit_bin(Operator::F64Eq, back, f, Type::I32);
    let bits = e.emit_un(Operator::I64ReinterpretF64, f, Type::I64);
    let negzero = e.emit_i64c(0x8000_0000_0000_0000);
    let is_negzero = e.emit_bin(Operator::I64Eq, bits, negzero, Type::I32);
    let not_negzero = e.emit_un(Operator::I32Eqz, is_negzero, Type::I32);
    let is_int32 = e.emit_bin(Operator::I32And, eq, not_negzero, Type::I32);
    let payload = e.emit_un(Operator::I64ExtendI32U, i, Type::I64);
    let tag = e.emit_i64c(TAG_INT32 << 32);
    let boxed_int = e.emit_bin(Operator::I64Or, payload, tag, Type::I64);
    e.emit_sel(Type::I64, boxed_int, bits, is_int32)
}

/// Minimal IR emitter for synthetic in-module helper bodies (no operand
/// stack / script state -- just blocks, ops, terminators): the ones that
/// are emitted once per module and called, rather than inlined at every
/// site (`night_ta_get`, `night_ic_get`, `night_call_classify`). No
/// context, no facts, no version identity: a helper body is the same code
/// every time.
pub(super) struct RawEmit {
    pub(super) body: FunctionBody,
    pub(super) cur: Block,
    mem: Memory,
}

impl RawEmit {
    pub(super) fn new(m: &Module, sig: Signature, mem: Memory) -> Self {
        let body = FunctionBody::new(m, sig);
        let cur = body.entry;
        RawEmit { body, cur, mem }
    }

    pub(super) fn param(&self, i: usize) -> Value {
        self.body.blocks[self.body.entry].params[i].1
    }

    pub(super) fn i32c(&mut self, value: u32) -> Value {
        let ty = self.body.single_type_list(Type::I32);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::I32Const { value },
            Default::default(),
            ty,
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn i64c(&mut self, value: u64) -> Value {
        let ty = self.body.single_type_list(Type::I64);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::I64Const { value },
            Default::default(),
            ty,
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    fn f64c(&mut self, value: f64) -> Value {
        let ty = self.body.single_type_list(Type::F64);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::F64Const {
                value: value.to_bits(),
            },
            Default::default(),
            ty,
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn un(&mut self, op: Operator, a: Value, result: Type) -> Value {
        let args = self.body.arg_pool.single(a);
        let ty = self.body.single_type_list(result);
        let v = self.body.add_value(ValueDef::Operator(op, args, ty));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn bin(&mut self, op: Operator, a: Value, b: Value, result: Type) -> Value {
        let args = self.body.arg_pool.double(a, b);
        let ty = self.body.single_type_list(result);
        let v = self.body.add_value(ValueDef::Operator(op, args, ty));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn sel(&mut self, ty: Type, a: Value, b: Value, cond: Value) -> Value {
        let args = self.body.arg_pool.from_iter([a, b, cond].into_iter());
        let tys = self.body.single_type_list(ty);
        let v = self
            .body
            .add_value(ValueDef::Operator(Operator::TypedSelect { ty }, args, tys));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn load(&mut self, op: Operator, addr: Value, result: Type) -> Value {
        let args = self.body.arg_pool.single(addr);
        let ty = self.body.single_type_list(result);
        let v = self.body.add_value(ValueDef::Operator(op, args, ty));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn ld32(&mut self, addr: Value, offset: u32) -> Value {
        let memory = MemoryArg {
            align: 2,
            offset,
            memory: self.mem,
        };
        self.load(Operator::I32Load { memory }, addr, Type::I32)
    }

    pub(super) fn store(&mut self, op: Operator, addr: Value, value: Value) {
        let args = self.body.arg_pool.double(addr, value);
        let v = self
            .body
            .add_value(ValueDef::Operator(op, args, Default::default()));
        self.body.append_to_block(self.cur, v);
    }

    pub(super) fn marg(&self, align: u8, offset: u32) -> MemoryArg {
        MemoryArg {
            align: align.into(),
            offset,
            memory: self.mem,
        }
    }

    pub(super) fn condbr(&mut self, cond: Value, if_true: Block, if_false: Block) {
        self.body.set_terminator(
            self.cur,
            Terminator::CondBr {
                cond,
                if_true: BlockTarget {
                    block: if_true,
                    args: vec![],
                },
                if_false: BlockTarget {
                    block: if_false,
                    args: vec![],
                },
            },
        );
    }

    pub(super) fn ret(&mut self, values: Vec<Value>) {
        self.body
            .set_terminator(self.cur, Terminator::Return { values });
    }

    fn box_int32(&mut self, v: Value) -> Value {
        box_int32(self, v)
    }

    fn canon_nan_f64(&mut self, f: Value) -> Value {
        canon_nan_f64(self, f)
    }

    fn box_f64_canonical(&mut self, f: Value) -> Value {
        box_f64_canonical(self, f)
    }

    /// The clasp-classify chain shared by both helpers: load the receiver's
    /// clasp, compare against the 9 fixed-length TA classes (most-frequent
    /// kinds first), branch to the matching arm or `miss`. Returns the arm
    /// blocks in `ORDER_TA_KINDS` order; `self.cur` ends at `miss`.
    fn ta_classify(&mut self, obj: Value, ta_class_base: u32, miss: Block) -> Vec<Block> {
        let shape = self.ld32(obj, SHAPE_OFFSET);
        let base = self.ld32(shape, SHAPE_BASESHAPE_OFFSET);
        let clasp = self.ld32(base, BASESHAPE_CLASP_OFFSET);
        let arms: Vec<Block> = ORDER_TA_KINDS
            .iter()
            .map(|_| self.body.add_block())
            .collect();
        for (i, &k) in ORDER_TA_KINDS.iter().enumerate() {
            let cslot = self.i32c(ta_class_base + 4 * (u32::from(k.code()) - 1));
            let want = self.ld32(cslot, 0);
            let is_k = self.bin(Operator::I32Eq, clasp, want, Type::I32);
            let next = if i + 1 == ORDER_TA_KINDS.len() {
                miss
            } else {
                self.body.add_block()
            };
            self.condbr(is_k, arms[i], next);
            self.cur = next;
        }
        arms
    }

    /// Bounds-check `idx` against the TA's element count; in-bounds returns
    /// the element address for `kind`, OOB branches to `miss`.
    fn ta_elem_addr(&mut self, obj: Value, idx: Value, kind: TaKind, miss: Block) -> Value {
        let len = self.ld32(obj, TA_LENGTH_PAYLOAD_OFFSET);
        let inb = self.bin(Operator::I32LtU, idx, len, Type::I32);
        let ldb = self.body.add_block();
        self.condbr(inb, ldb, miss);
        self.cur = ldb;
        let data = self.ld32(obj, TA_DATA_PAYLOAD_OFFSET);
        let shift = kind.log2_bytes();
        if shift == 0 {
            self.bin(Operator::I32Add, data, idx, Type::I32)
        } else {
            let s = self.i32c(shift);
            let off = self.bin(Operator::I32Shl, idx, s, Type::I32);
            self.bin(Operator::I32Add, data, off, Type::I32)
        }
    }

    /// Kind-specific store of an unboxed int32 (no terminator). Mirrors
    /// Translator::emit_ta_store_int.
    fn ta_store_int(&mut self, addr: Value, kind: TaKind, v: Value) {
        match kind {
            TaKind::Int8 | TaKind::Uint8 => {
                let memory = self.marg(0, 0);
                self.store(Operator::I32Store8 { memory }, addr, v);
            }
            TaKind::Uint8Clamped => {
                let zero = self.i32c(0);
                let cap = self.i32c(255);
                let is_neg = self.bin(Operator::I32LtS, v, zero, Type::I32);
                let lo = self.sel(Type::I32, zero, v, is_neg);
                let over = self.bin(Operator::I32GtS, lo, cap, Type::I32);
                let c = self.sel(Type::I32, cap, lo, over);
                let memory = self.marg(0, 0);
                self.store(Operator::I32Store8 { memory }, addr, c);
            }
            TaKind::Int16 | TaKind::Uint16 => {
                let memory = self.marg(1, 0);
                self.store(Operator::I32Store16 { memory }, addr, v);
            }
            TaKind::Int32 | TaKind::Uint32 => {
                let memory = self.marg(2, 0);
                self.store(Operator::I32Store { memory }, addr, v);
            }
            TaKind::Float32 => {
                let f = self.un(Operator::F32ConvertI32S, v, Type::F32);
                let memory = self.marg(2, 0);
                self.store(Operator::F32Store { memory }, addr, f);
            }
            TaKind::Float64 => {
                let d = self.un(Operator::F64ConvertI32S, v, Type::F64);
                let memory = self.marg(3, 0);
                self.store(Operator::F64Store { memory }, addr, d);
            }
        }
    }
}

impl BoxEmit for RawEmit {
    fn emit_un(&mut self, op: Operator, a: Value, result: Type) -> Value {
        self.un(op, a, result)
    }
    fn emit_bin(&mut self, op: Operator, a: Value, b: Value, result: Type) -> Value {
        self.bin(op, a, b, result)
    }
    fn emit_i64c(&mut self, value: u64) -> Value {
        self.i64c(value)
    }
    fn emit_sel(&mut self, ty: Type, a: Value, b: Value, cond: Value) -> Value {
        self.sel(ty, a, b, cond)
    }
}

/// Classify-chain order for the polymorphic TA helpers: byte views first
/// (asm.js-style heaps), then the int/float word kinds.
const ORDER_TA_KINDS: [TaKind; 9] = [
    TaKind::Uint8,
    TaKind::Int32,
    TaKind::Float64,
    TaKind::Uint32,
    TaKind::Uint8Clamped,
    TaKind::Float32,
    TaKind::Int8,
    TaKind::Int16,
    TaKind::Uint16,
];

// Inline-IC way field offsets and the mega-table key/payload offsets, mirrored
// from the layout note above (and from `bbv::abi`, which spells the same bytes
// for the inlined arms).
const IC_WAY_RECVSHAPE: u32 = 0;
const IC_WAY_MONO_OFF: u32 = 4;
const IC_WAY_HOLDERPTR: u32 = 8;
const MEGA_SHAPE: u32 = 0;
const MEGA_ATOM: u32 = 4;
const MEGA_HOLDERPTR: u32 = 8;
/// `NativeObject::slots_`, the out-of-line slot vector (mirrors `bbv::abi`).
const NATIVE_SLOTS_OFFSET: u32 = 8;

impl RawEmit {
    /// Boxed-value tag test: the high word against `tag`.
    pub(crate) fn tag_is(&mut self, boxed: Value, tag: u64) -> Value {
        let shift = self.i64c(32);
        let hi64 = self.bin(Operator::I64ShrU, boxed, shift, Type::I64);
        let hi = self.un(Operator::I32WrapI64, hi64, Type::I32);
        let t = self.i32c(tag as u32);
        self.bin(Operator::I32Eq, hi, t, Type::I32)
    }

    /// Load an object slot from a cache row's coordinate (`NightSlotEnc`:
    /// byte offset | is-dynamic bit). The inline twin is
    /// `Bbv::emit_slot_addr`.
    fn slot_load(&mut self, obj: Value, slot_enc: Value) -> Value {
        let one = self.i32c(1);
        let is_dynamic = self.bin(Operator::I32And, slot_enc, one, Type::I32);
        let mask = self.i32c(!1);
        let off = self.bin(Operator::I32And, slot_enc, mask, Type::I32);
        let slots_ptr = self.ld32(obj, NATIVE_SLOTS_OFFSET);
        let slot_base = self.sel(Type::I32, slots_ptr, obj, is_dynamic);
        let addr = self.bin(Operator::I32Add, slot_base, off, Type::I32);
        let memory = self.marg(3, 0);
        self.load(Operator::I64Load { memory }, addr, Type::I64)
    }

    /// The shared hit tail: validate the holder's live shape, then read the
    /// slot. `entry_base + hp_off` is `[holderPtr, holderShape, slotEnc]` in
    /// both the per-site way and the mega row, which is what lets one tail
    /// serve both probes.
    pub(crate) fn ic_hit_tail(
        &mut self,
        objptr: Value,
        entry_base: Value,
        hp_off: u32,
        miss: Block,
    ) -> Value {
        let hp = self.ld32(entry_base, hp_off);
        let chs = self.ld32(entry_base, hp_off + 4);
        let slot_enc = self.ld32(entry_base, hp_off + 8);
        let zero = self.i32c(0);
        let hp_is_own = self.bin(Operator::I32Eq, hp, zero, Type::I32);
        let base = self.sel(Type::I32, objptr, hp, hp_is_own);
        let live_hs = self.ld32(base, SHAPE_OFFSET);
        let ok = self.bin(Operator::I32Eq, live_hs, chs, Type::I32);
        let load_blk = self.body.add_block();
        self.condbr(ok, load_blk, miss);
        self.cur = load_blk;
        self.slot_load(base, slot_enc)
    }
}

/// In-module generic property-get IC probe: `night_ic_get(recvBoxed, atomId,
/// wayBase) -> boxed` with magic bits signalling a miss.
///
/// This is the fact-free property read -- the arm a site takes when the
/// analysis knows no layout for it. It is the same code at every such site,
/// varying only in the per-site way address and the atom id, so it is emitted
/// once and called rather than inlined 43,000 times. A monomorphic site pays
/// one direct call; the alternative it replaces is ~290 bytes of holder tail,
/// poly sentinel, mega hash and a duplicate hit tail at every site.
///
/// Pure leaf: linear-memory reads only, no GC, no engine crossing, so the
/// caller keeps its facts and its track across the call.
pub fn build_ic_get_helper(m: &mut Module, mem: Memory, mega_get_base: u32) -> Func {
    let sig = m.signatures.push(SignatureData {
        params: vec![Type::I64, Type::I32, Type::I32],
        returns: vec![Type::I64],
    });
    let mut e = RawEmit::new(m, sig, mem);
    let recv_boxed = e.param(0);
    let atom_v = e.param(1);
    let way_base = e.param(2);

    let miss = e.body.add_block();
    let way0 = e.body.add_block();
    let is_obj = e.tag_is(recv_boxed, TAG_OBJECT);
    e.condbr(is_obj, way0, miss);

    e.cur = miss;
    let magic = e.i64c(TAG_MAGIC << 32);
    e.ret(vec![magic]);

    e.cur = way0;
    let objptr = e.un(Operator::I32WrapI64, recv_boxed, Type::I32);
    let shape = e.ld32(objptr, SHAPE_OFFSET);
    // The way chain, sharing one hit block (the inline arm's twin): the
    // matched way's address is the block parameter.
    let hit_blk = e.body.add_block();
    let way = e.body.add_blockparam(hit_blk, Type::I32);
    let poly_blk = e.body.add_block();
    for w in 0..INLINE_IC_WAYS {
        let wb = if w == 0 {
            way_base
        } else {
            let off = e.i32c(w * INLINE_IC_WAY_BYTES);
            e.bin(Operator::I32Add, way_base, off, Type::I32)
        };
        let wshape = e.ld32(wb, IC_WAY_RECVSHAPE);
        let m = e.bin(Operator::I32Eq, shape, wshape, Type::I32);
        let next = if w + 1 < INLINE_IC_WAYS {
            e.body.add_block()
        } else {
            poly_blk
        };
        e.body.set_terminator(
            e.cur,
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
        e.cur = next;
    }

    // The hit: the pre-decoded own fixed-slot byte offset, else the holder
    // tail.
    e.cur = hit_blk;
    let moff = e.ld32(way, IC_WAY_MONO_OFF);
    let zero = e.i32c(0);
    let is_fast = e.bin(Operator::I32Ne, moff, zero, Type::I32);
    let fastw_blk = e.body.add_block();
    let tail_blk = e.body.add_block();
    e.condbr(is_fast, fastw_blk, tail_blk);
    e.cur = fastw_blk;
    let addr = e.bin(Operator::I32Add, objptr, moff, Type::I32);
    let memory = e.marg(3, 0);
    let fast = e.load(Operator::I64Load { memory }, addr, Type::I64);
    e.ret(vec![fast]);
    e.cur = tail_blk;
    let r = e.ic_hit_tail(objptr, way, IC_WAY_HOLDERPTR, miss);
    e.ret(vec![r]);

    // Past the ways. A site with a free way (the fill is in order, so the
    // last way empty means one is free) MISSES here, so the C++ helper's
    // populate fills the way: the mega table is keyed by (shape, atom) alone
    // and another site may already have seeded this pair, which would
    // otherwise serve this site from the hash forever with its ways empty.
    // A full site probes the mega table for its extra shapes.
    e.cur = poly_blk;
    let last_off = e.i32c((INLINE_IC_WAYS - 1) * INLINE_IC_WAY_BYTES);
    let last_way = e.bin(Operator::I32Add, way_base, last_off, Type::I32);
    let last_shape = e.ld32(last_way, IC_WAY_RECVSHAPE);
    let last_empty = e.un(Operator::I32Eqz, last_shape, Type::I32);
    let mega_blk = e.body.add_block();
    e.condbr(last_empty, miss, mega_blk);
    e.cur = mega_blk;
    // The hash mirrors `Bbv::emit_mega_probe` / NightRuntime.cpp's MegaGetSlot.
    // Inlined, the atom half folds into an immediate; here the atom is a
    // parameter, so it costs one multiply on a path that is never hot.
    let three = e.i32c(3);
    let sh = e.bin(Operator::I32ShrU, shape, three, Type::I32);
    let k1 = e.i32c(2654435761);
    let h1 = e.bin(Operator::I32Mul, sh, k1, Type::I32);
    let k2c = e.i32c(0x9e37_79b9);
    let k2 = e.bin(Operator::I32Mul, atom_v, k2c, Type::I32);
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
    let m_atom = e.bin(Operator::I32Eq, eatom, atom_v, Type::I32);
    let m_hit = e.bin(Operator::I32And, m_shape, m_atom, Type::I32);
    let mega_hit_blk = e.body.add_block();
    e.condbr(m_hit, mega_hit_blk, miss);
    e.cur = mega_hit_blk;
    let r = e.ic_hit_tail(objptr, entry, MEGA_HOLDERPTR, miss);
    e.ret(vec![r]);

    m.funcs
        .push(FuncDecl::Body(sig, "night_ic_get".to_string(), e.body))
}

/// Build the two in-module polymorphic typed-array element helpers, used by
/// elem sites with no (or a wrong) compile-time kind prediction. Both are
/// pure leaves (no GC, no engine crossing, no rooting):
///   - `night_ta_get(objptr, idx) -> boxed` -- magic-tagged bits signal a miss
///     (a real TA element is always a number, never magic);
///   - `night_ta_set(objptr, idx, val) -> stored?` -- 0 on any miss (not a TA,
///     OOB, non-number value, non-int32-exact double into an integer kind).
/// The caller reaches them only with an object receiver and int32 key (the
/// dense-arm precondition), so the clasp chain dereference is safe.
pub fn build_ta_poly_helpers(m: &mut Module, mem: Memory, ta_class_base: u32) -> (Func, Func) {
    let get_sig = m.signatures.push(SignatureData {
        params: vec![Type::I32, Type::I32],
        returns: vec![Type::I64],
    });
    let ta_get = {
        let mut e = RawEmit::new(m, get_sig, mem);
        let obj = e.param(0);
        let idx = e.param(1);
        let miss = e.body.add_block();
        let arms = e.ta_classify(obj, ta_class_base, miss);
        e.cur = miss;
        let magic = e.i64c(TAG_MAGIC << 32);
        e.ret(vec![magic]);
        for (i, &k) in ORDER_TA_KINDS.iter().enumerate() {
            e.cur = arms[i];
            let addr = e.ta_elem_addr(obj, idx, k, miss);
            let boxed = match k {
                TaKind::Int8 => {
                    let memory = e.marg(0, 0);
                    let u = e.load(Operator::I32Load8U { memory }, addr, Type::I32);
                    let v = e.un(Operator::I32Extend8S, u, Type::I32);
                    e.box_int32(v)
                }
                TaKind::Uint8 | TaKind::Uint8Clamped => {
                    let memory = e.marg(0, 0);
                    let v = e.load(Operator::I32Load8U { memory }, addr, Type::I32);
                    e.box_int32(v)
                }
                TaKind::Int16 => {
                    let memory = e.marg(1, 0);
                    let u = e.load(Operator::I32Load16U { memory }, addr, Type::I32);
                    let v = e.un(Operator::I32Extend16S, u, Type::I32);
                    e.box_int32(v)
                }
                TaKind::Uint16 => {
                    let memory = e.marg(1, 0);
                    let v = e.load(Operator::I32Load16U { memory }, addr, Type::I32);
                    e.box_int32(v)
                }
                TaKind::Int32 => {
                    let memory = e.marg(2, 0);
                    let v = e.load(Operator::I32Load { memory }, addr, Type::I32);
                    e.box_int32(v)
                }
                TaKind::Uint32 => {
                    let memory = e.marg(2, 0);
                    let v = e.load(Operator::I32Load { memory }, addr, Type::I32);
                    let f = e.un(Operator::F64ConvertI32U, v, Type::F64);
                    let boxed_dbl = e.box_f64_canonical(f);
                    let boxed_int = e.box_int32(v);
                    let zero = e.i32c(0);
                    let is_small = e.bin(Operator::I32GeS, v, zero, Type::I32);
                    e.sel(Type::I64, boxed_int, boxed_dbl, is_small)
                }
                TaKind::Float32 => {
                    let memory = e.marg(2, 0);
                    let f = e.load(Operator::F32Load { memory }, addr, Type::F32);
                    let d = e.un(Operator::F64PromoteF32, f, Type::F64);
                    let d = e.canon_nan_f64(d);
                    e.box_f64_canonical(d)
                }
                TaKind::Float64 => {
                    let memory = e.marg(3, 0);
                    let d = e.load(Operator::F64Load { memory }, addr, Type::F64);
                    let d = e.canon_nan_f64(d);
                    e.box_f64_canonical(d)
                }
            };
            e.ret(vec![boxed]);
        }
        m.funcs
            .push(FuncDecl::Body(get_sig, "night_ta_get".to_string(), e.body))
    };

    let set_sig = m.signatures.push(SignatureData {
        params: vec![Type::I32, Type::I32, Type::I64],
        returns: vec![Type::I32],
    });
    let ta_set = {
        let mut e = RawEmit::new(m, set_sig, mem);
        let obj = e.param(0);
        let idx = e.param(1);
        let val = e.param(2);
        let miss = e.body.add_block();
        let arms = e.ta_classify(obj, ta_class_base, miss);
        e.cur = miss;
        let zero = e.i32c(0);
        e.ret(vec![zero]);
        for (i, &k) in ORDER_TA_KINDS.iter().enumerate() {
            e.cur = arms[i];
            let addr = e.ta_elem_addr(obj, idx, k, miss);
            let shift32 = e.i64c(32);
            let hi64 = e.bin(Operator::I64ShrU, val, shift32, Type::I64);
            let hi = e.un(Operator::I32WrapI64, hi64, Type::I32);
            let int_tag = e.i32c(TAG_INT32 as u32);
            let is_int = e.bin(Operator::I32Eq, hi, int_tag, Type::I32);
            let int_blk = e.body.add_block();
            let chk_dbl = e.body.add_block();
            e.condbr(is_int, int_blk, chk_dbl);
            e.cur = int_blk;
            let v = e.un(Operator::I32WrapI64, val, Type::I32);
            e.ta_store_int(addr, k, v);
            let one = e.i32c(1);
            e.ret(vec![one]);
            e.cur = chk_dbl;
            let clear = e.i32c(0xFFFF_FF80);
            let is_dbl = e.bin(Operator::I32LeU, hi, clear, Type::I32);
            let dbl_blk = e.body.add_block();
            e.condbr(is_dbl, dbl_blk, miss);
            e.cur = dbl_blk;
            let f = e.un(Operator::F64ReinterpretI64, val, Type::F64);
            match k {
                TaKind::Int8
                | TaKind::Uint8
                | TaKind::Int16
                | TaKind::Uint16
                | TaKind::Int32
                | TaKind::Uint32 => {
                    let i32v = e.un(Operator::I32TruncSatF64S, f, Type::I32);
                    let back = e.un(Operator::F64ConvertI32S, i32v, Type::F64);
                    let exact = e.bin(Operator::F64Eq, back, f, Type::I32);
                    let ok_blk = e.body.add_block();
                    e.condbr(exact, ok_blk, miss);
                    e.cur = ok_blk;
                    e.ta_store_int(addr, k, i32v);
                }
                TaKind::Uint8Clamped => {
                    let z = e.f64c(0.0);
                    let cap = e.f64c(255.0);
                    let lo = e.bin(Operator::F64Max, f, z, Type::F64);
                    let c = e.bin(Operator::F64Min, lo, cap, Type::F64);
                    let r = e.un(Operator::F64Nearest, c, Type::F64);
                    let i32v = e.un(Operator::I32TruncSatF64S, r, Type::I32);
                    let memory = e.marg(0, 0);
                    e.store(Operator::I32Store8 { memory }, addr, i32v);
                }
                TaKind::Float32 => {
                    let g = e.un(Operator::F32DemoteF64, f, Type::F32);
                    let memory = e.marg(2, 0);
                    e.store(Operator::F32Store { memory }, addr, g);
                }
                TaKind::Float64 => {
                    let memory = e.marg(3, 0);
                    e.store(Operator::F64Store { memory }, addr, f);
                }
            }
            let one2 = e.i32c(1);
            e.ret(vec![one2]);
        }
        m.funcs
            .push(FuncDecl::Body(set_sig, "night_ta_set".to_string(), e.body))
    };

    (ta_get, ta_set)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::facts::CallResolution;
    use crate::source::SourceObjectId;
    use waffle::entity::EntityRef;
    use waffle::SignatureData;
    use waffle::{MemoryData, Module};

    /// A `TranslateCtx` with every analysis table empty -- the shape a
    /// script gets when there is no likely-type input at all. The engine
    /// builds its ctx in `wasm/mod.rs`; tests that need one table filled in
    /// use struct-update syntax over this.
    fn empty_ctx<'a>(helpers: Helpers, source: &'a Source, opts: &'a Options) -> TranslateCtx<'a> {
        TranslateCtx {
            helpers,
            source,
            opts,
            bigint_free: false,
            syn_gnames: empty_syn_gnames(),
            gcell_bids: empty_gcell_bids(),
            likely_fns: empty_likely_fns(),
            facts: empty_facts(),
            flag_demand: empty_flag_demand(),
            this_layouts_in: empty_this_layouts(),
            stamp_ctors_in: empty_stamp_ctors(),
            layout_addpred_in: empty_layout_addpred(),
            ctor_nslots_in: empty_ctor_nslots(),
            deleg_restamps_in: empty_stamp_ctors(),
            arg_restamps_in: empty_arg_restamps(),
            local_restamps_in: empty_local_restamps(),
            construct_sites_in: empty_construct_sites(),
            lit_stamps_in: empty_lit_stamps(),
            prop_sites_in: empty_prop_sites(),
            layout_field_masks_in: empty_layout_field_masks(),
            layout_field_ranges_in: empty_layout_field_ranges(),
            array_stamp_in: empty_array_stamp(),
            array_elem_in: empty_array_elem(),
            array_any_claim: None,
            likely_elems: empty_elem_sites(),
            fused_gnames: empty_fused_gnames(),
        }
    }

    /// Translate one script with no analysis input, through the production
    /// entry point -- the engine calls `bbv::translate_script` directly, and
    /// this must not become a second way in.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn translate_script(
        m: &mut Module,
        helpers: Helpers,
        source: &Source,
        atoms: &mut AtomTable,
        source_id: u32,
        script: &Script,
        opts: &Options,
    ) -> Result<Outcome, String> {
        let ctx = empty_ctx(helpers, source, opts);
        crate::wasm::bbv::translate_script(&ctx, m, atoms, ScriptId::new(source_id), script, false)
    }

    /// `translate_script` with inlining off and the night tier disabled.
    pub(crate) fn translate_script_bbv(
        m: &mut Module,
        helpers: Helpers,
        source: &Source,
        atoms: &mut AtomTable,
        source_id: u32,
        script: &Script,
    ) -> Result<Outcome, String> {
        let opts = Options::default();
        let ctx = empty_ctx(helpers, source, &opts);
        crate::wasm::bbv::translate_script(&ctx, m, atoms, ScriptId::new(source_id), script, false)
    }

    /// Define a `fn $name() -> &'static $ty` returning a process-shared
    /// empty (`Default`) analysis table: what a script sees when it is
    /// translated without whole-module analysis input.
    macro_rules! empty_table {
        ($name:ident, $ty:ty) => {
            fn $name() -> &'static $ty {
                static EMPTY: std::sync::OnceLock<$ty> = std::sync::OnceLock::new();
                EMPTY.get_or_init(<$ty>::default)
            }
        };
    }

    empty_table!(empty_facts, LikelyFacts);

    /// A `LikelyFacts` with one table filled in.
    fn facts_with(fill: impl FnOnce(&mut LikelyFacts)) -> LikelyFacts {
        let mut f = LikelyFacts::default();
        fill(&mut f);
        f
    }
    empty_table!(empty_construct_sites, HashMap<Site, StampCtorIn>);
    empty_table!(empty_lit_stamps, HashMap<Site, u32>);
    empty_table!(empty_fused_gnames, HashMap<NameId, FusedGname>);
    empty_table!(empty_prop_sites, HashMap<Site, PropSiteIn>);
    empty_table!(empty_elem_sites, HashMap<Site, Claim>);
    empty_table!(empty_this_layouts, HashMap<ScriptId, ThisLayoutIn>);
    empty_table!(empty_stamp_ctors, HashMap<ScriptId, StampCtorIn>);
    empty_table!(empty_arg_restamps, HashMap<ScriptId, (u32, StampCtorIn)>);
    empty_table!(empty_local_restamps, HashMap<Site, (u32, StampCtorIn)>);
    empty_table!(empty_layout_addpred, HashMap<NameId, Vec<AddPred>>);
    empty_table!(empty_ctor_nslots, HashMap<ScriptId, u32>);
    empty_table!(empty_likely_fns, HashMap<NameId, ScriptId>);
    empty_table!(empty_gcell_bids, HashSet<u32>);
    empty_table!(empty_layout_field_masks, HashMap<StampKey, HashMap<NameId, Claim>>);
    empty_table!(
        empty_layout_field_ranges,
        HashMap<StampKey, HashMap<NameId, ValueRange>>
    );
    empty_table!(empty_array_stamp, HashMap<Site, u32>);
    empty_table!(empty_array_elem, HashMap<Site, ArrayElemIn>);
    empty_table!(empty_syn_gnames, HashMap<NameId, u32>);
    empty_table!(empty_flag_demand, rustc_hash::FxHashSet<ScriptId>);
    fn op_byte(o: JSOp) -> u8 {
        o as u16 as u8
    }

    fn stub(m: &mut Module, sig: Signature, ret_i32: bool, name: &str) -> Func {
        let mut body = FunctionBody::new(m, sig);
        let entry = body.entry;
        let values = if ret_i32 {
            let ty = body.single_type_list(Type::I32);
            let z = body.add_value(ValueDef::Operator(
                Operator::I32Const { value: 0 },
                Default::default(),
                ty,
            ));
            body.append_to_block(entry, z);
            vec![z]
        } else {
            vec![]
        };
        body.set_terminator(entry, Terminator::Return { values });
        m.funcs
            .push(waffle::FuncDecl::Body(sig, name.to_string(), body))
    }

    fn stub_i64(m: &mut Module, sig: Signature, name: &str) -> Func {
        let mut body = FunctionBody::new(m, sig);
        let entry = body.entry;
        let ty = body.single_type_list(Type::I64);
        let z = body.add_value(ValueDef::Operator(
            Operator::I64Const { value: 0 },
            Default::default(),
            ty,
        ));
        body.append_to_block(entry, z);
        body.set_terminator(entry, Terminator::Return { values: vec![z] });
        m.funcs
            .push(waffle::FuncDecl::Body(sig, name.to_string(), body))
    }

    fn stub_f64(m: &mut Module, sig: Signature, name: &str) -> Func {
        let mut body = FunctionBody::new(m, sig);
        let entry = body.entry;
        let ty = body.single_type_list(Type::F64);
        let z = body.add_value(ValueDef::Operator(
            Operator::F64Const { value: 0 },
            Default::default(),
            ty,
        ));
        body.append_to_block(entry, z);
        body.set_terminator(entry, Terminator::Return { values: vec![z] });
        m.funcs
            .push(waffle::FuncDecl::Body(sig, name.to_string(), body))
    }

    fn module_with_helpers() -> (Module<'static>, Helpers) {
        let mut m = Module::empty();
        let mem = m.memories.push(MemoryData {
            initial_pages: 1,
            maximum_pages: None,
            segments: Vec::new(),
        });
        // The compiled-body ABI signature + a funcref table, for
        // specialized-call `call_indirect`.
        let night_abi_sig = m.signatures.push(SignatureData {
            params: vec![
                Type::I32,
                Type::I32,
                Type::I32,
                Type::I32,
                Type::I32,
                Type::I64,
            ],
            returns: vec![Type::I32],
        });
        let indirect_table = m.tables.push(waffle::TableData {
            ty: Type::FuncRef,
            initial: 1,
            max: None,
            func_elements: Some(vec![waffle::Func::invalid()]),
        });
        // callee_night_target: (callee i64) -> i64.
        let cat_sig = m.signatures.push(SignatureData {
            params: vec![Type::I64],
            returns: vec![Type::I64],
        });
        let callee_night_target = stub_i64(&mut m, cat_sig, "night_runtime_callee_night_target");
        let direct_call_stub = stub(&mut m, night_abi_sig, true, "night_direct_stub");
        let night_abi_sig2 = m.signatures.push(SignatureData {
            params: vec![
                Type::I32,
                Type::I32,
                Type::I32,
                Type::I32,
                Type::I32,
                Type::I64,
            ],
            returns: vec![Type::I32, Type::I32],
        });
        let direct_call_stub2 = {
            let mut body = FunctionBody::new(&m, night_abi_sig2);
            let entry = body.entry;
            let ty = body.single_type_list(Type::I32);
            let one = body.add_value(ValueDef::Operator(
                Operator::I32Const { value: 1 },
                Default::default(),
                ty,
            ));
            body.append_to_block(entry, one);
            // Flags word (thread C polarity): all-set = effects happened;
            // the inert stub must never read as a clean return.
            let z = body.add_value(ValueDef::Operator(
                Operator::I32Const { value: 3 },
                Default::default(),
                ty,
            ));
            body.append_to_block(entry, z);
            body.set_terminator(
                entry,
                Terminator::Return {
                    values: vec![one, z],
                },
            );
            m.funcs.push(waffle::FuncDecl::Body(
                night_abi_sig2,
                "night_direct_stub2".to_string(),
                body,
            ))
        };
        // All may-GC helpers take `(cx, top, ...args)` -> i32 (top is the GC scan
        // limit + the scratch out-slot; helpers write any result there).
        let add_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I64, Type::I64],
            returns: vec![Type::I32],
        });
        let call_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I32, Type::I32],
            returns: vec![Type::I32],
        });
        let getp_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I64, Type::I32],
            returns: vec![Type::I32],
        });
        let setp_sig = m.signatures.push(SignatureData {
            params: vec![
                Type::I32,
                Type::I32,
                Type::I64,
                Type::I32,
                Type::I64,
                Type::I32,
            ],
            returns: vec![Type::I32],
        });
        let getg_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I32],
            returns: vec![Type::I32],
        });
        let gete_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I64, Type::I64],
            returns: vec![Type::I32],
        });
        let sete_sig = m.signatures.push(SignatureData {
            params: vec![
                Type::I32,
                Type::I32,
                Type::I64,
                Type::I64,
                Type::I64,
                Type::I32,
            ],
            returns: vec![Type::I32],
        });
        let add = stub(&mut m, add_sig, true, "night_runtime_add");
        let concat = stub(&mut m, add_sig, true, "night_runtime_concat");
        let call = stub(&mut m, call_sig, true, "night_runtime_call");
        let call_iter = stub(&mut m, call_sig, true, "night_runtime_call_iter");
        let native_dispatch = stub(&mut m, call_sig, true, "night_runtime_native_dispatch");
        // apply_fwd: (cx i32, top i32, applyFn i64, target i64, this i64,
        // callerSp i32, callerArgc i32) -> i32.
        let apply_fwd_sig = m.signatures.push(SignatureData {
            params: vec![
                Type::I32,
                Type::I32,
                Type::I64,
                Type::I64,
                Type::I64,
                Type::I32,
                Type::I32,
            ],
            returns: vec![Type::I32],
        });
        let apply_fwd = stub(&mut m, apply_fwd_sig, true, "night_runtime_apply_fwd");
        // construct: (cx i32, top i32, frame i32, argc i32, nSlots i32,
        // stampWord i32) -> i32.
        let construct_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32; 6],
            returns: vec![Type::I32],
        });
        let construct = stub(&mut m, construct_sig, true, "night_runtime_construct");
        let rest_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32; 5],
            returns: vec![Type::I32],
        });
        let get_property = stub(&mut m, getp_sig, true, "night_runtime_get_property");
        let set_property = stub(&mut m, setp_sig, true, "night_runtime_set_property");
        // IC get: (cx i32, top i32, recv i64, atomId i32, cacheIdx i32) -> i32.
        let getic_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I64, Type::I32, Type::I32],
            returns: vec![Type::I32],
        });
        let get_prop_ic_miss = stub(&mut m, getic_sig, true, "night_runtime_get_prop_ic_miss");
        // IC set: (cx, top, recv i64, atomId i32, val i64, cacheIdx i32,
        // strict i32) -> i32.
        let setic_sig = m.signatures.push(SignatureData {
            params: vec![
                Type::I32,
                Type::I32,
                Type::I64,
                Type::I32,
                Type::I64,
                Type::I32,
                Type::I32,
            ],
            returns: vec![Type::I32],
        });
        let set_prop_ic_miss = stub(&mut m, setic_sig, true, "night_runtime_set_prop_ic_miss");
        let binop_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I32, Type::I64, Type::I64],
            returns: vec![Type::I32],
        });
        // get_gname: (cx i32, top i32, atomId i32, forTypeof i32) -> i32.
        let getg2_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I32, Type::I32],
            returns: vec![Type::I32],
        });
        let get_gname = stub(&mut m, getg2_sig, true, "night_runtime_get_gname");
        let get_element = stub(&mut m, gete_sig, true, "night_runtime_get_element");
        let set_element = stub(&mut m, sete_sig, true, "night_runtime_set_element");
        let tonum_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I64],
            returns: vec![Type::I32],
        });
        let binop = stub(&mut m, binop_sig, true, "night_runtime_binop");
        let compare = stub(&mut m, binop_sig, true, "night_runtime_compare");
        let string = stub(&mut m, getg_sig, true, "night_runtime_string");
        let get_intrinsic = stub(&mut m, getg_sig, true, "night_runtime_get_intrinsic");
        // get_intrinsic_cell: (cx, top, atomId, cellAddr) -> i32.
        let gic_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I32, Type::I32],
            returns: vec![Type::I32],
        });
        let get_intrinsic_cell = stub(&mut m, gic_sig, true, "night_runtime_get_intrinsic_cell");
        let strlit_verify = stub(&mut m, getg_sig, true, "night_runtime_strlit_verify");
        let chars_eq_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32],
            returns: vec![Type::I32],
        });
        let str_chars_eq = stub(&mut m, chars_eq_sig, true, "night_runtime_str_chars_eq");
        let tonumeric = stub(&mut m, tonum_sig, true, "night_runtime_tonumeric");
        let pos = stub(&mut m, tonum_sig, true, "night_runtime_pos");
        let neg = stub(&mut m, tonum_sig, true, "night_runtime_neg");
        // instanceof: (cx, top, l i64, r i64, cellAddr i32) -> ok.
        let iof_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I64, Type::I64, Type::I32],
            returns: vec![Type::I32],
        });
        let instanceof_ = stub(&mut m, iof_sig, true, "night_runtime_instanceof");
        // del_prop: (cx, top, val i64, atomId i32, strict i32) -> ok.
        let delp_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I64, Type::I32, Type::I32],
            returns: vec![Type::I32],
        });
        let del_prop = stub(&mut m, delp_sig, true, "night_runtime_del_prop");
        // arguments: (cx, top, sp i32, argc i32) -> ok.
        let args_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I32, Type::I32],
            returns: vec![Type::I32],
        });
        let arguments_ = stub(&mut m, args_sig, true, "night_runtime_arguments");
        // arguments_env: (cx, top, sp i32, argc i32, env i64) -> ok.
        let args_env_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I32, Type::I32, Type::I64],
            returns: vec![Type::I32],
        });
        let arguments_env = stub(&mut m, args_env_sig, true, "night_runtime_arguments_env");
        // in/has_own: (cx, top, id i64, val i64) -> ok (= gete_sig shape).
        let in_ = stub(&mut m, gete_sig, true, "night_runtime_in");
        let has_own = stub(&mut m, gete_sig, true, "night_runtime_has_own");
        let to_property_key = stub(&mut m, tonum_sig, true, "night_runtime_to_property_key");
        // mutate_proto: (cx, top, obj i64, proto i64) -> ok (= gete_sig shape).
        let mutate_proto = stub(&mut m, gete_sig, true, "night_runtime_mutate_proto");
        // init_home_object: (cx, top, fn i64, homeObj i64) -> ok (= gete_sig).
        let init_home_object = stub(&mut m, gete_sig, true, "night_runtime_init_home_object");
        // super_base / super_fun: (cx, top, callee i64) -> ok (= tonum_sig shape).
        let super_base = stub(&mut m, tonum_sig, true, "night_runtime_super_base");
        let super_fun = stub(&mut m, tonum_sig, true, "night_runtime_super_fun");
        // get_prop_super: (cx, top, recv i64, superBase i64, atomId i32) -> ok
        // (= iof_sig shape).
        let get_prop_super = stub(&mut m, iof_sig, true, "night_runtime_get_prop_super");
        // get_elem_super: (cx, top, recv i64, key i64, superBase i64) -> ok
        // (= sete_sig shape).
        let get_elem_super = stub(&mut m, sete_sig, true, "night_runtime_get_elem_super");
        // set_prop_super: (cx, top, recv i64, superBase i64, atomId i32, val i64,
        // strict i32) -> ok.
        let sps_sig = m.signatures.push(SignatureData {
            params: vec![
                Type::I32,
                Type::I32,
                Type::I64,
                Type::I64,
                Type::I32,
                Type::I64,
                Type::I32,
            ],
            returns: vec![Type::I32],
        });
        let set_prop_super = stub(&mut m, sps_sig, true, "night_runtime_set_prop_super");
        // set_elem_super: (cx, top, recv i64, key i64, superBase i64, val i64,
        // strict i32) -> ok.
        let ses_sig = m.signatures.push(SignatureData {
            params: vec![
                Type::I32,
                Type::I32,
                Type::I64,
                Type::I64,
                Type::I64,
                Type::I64,
                Type::I32,
            ],
            returns: vec![Type::I32],
        });
        let set_elem_super = stub(&mut m, ses_sig, true, "night_runtime_set_elem_super");
        // tostring: (cx, top, v i64) -> ok (= tonum_sig shape).
        let tostring = stub(&mut m, tonum_sig, true, "night_runtime_tostring");
        // pow: (cx, top, a i64, b i64) -> ok (= gete_sig shape).
        let pow = stub(&mut m, gete_sig, true, "night_runtime_pow");
        // check_obj_coercible / check_this: (cx, top, v i64) -> ok (= tonum_sig).
        let check_obj_coercible =
            stub(&mut m, tonum_sig, true, "night_runtime_check_obj_coercible");
        let check_class_heritage = stub(
            &mut m,
            tonum_sig,
            true,
            "night_runtime_check_class_heritage",
        );
        // create_generator: (cx, top, callee i64, env i64) -> ok (= gete_sig).
        let create_generator = stub(&mut m, gete_sig, true, "night_runtime_create_generator");
        // gen_suspend: (cx, gen i64, k i32, locals i32, nlocals i32, ops i32,
        // nops i32, env i64) -> i32. Leaf (no top).
        let gen_suspend_sig = m.signatures.push(SignatureData {
            params: vec![
                Type::I32,
                Type::I64,
                Type::I32,
                Type::I32,
                Type::I32,
                Type::I32,
                Type::I32,
                Type::I64,
            ],
            returns: vec![Type::I32],
        });
        let gen_suspend = stub(&mut m, gen_suspend_sig, true, "night_runtime_gen_suspend");
        // gen_restore: (cx, gen i64, locals i32, nlocals i32, env i32,
        // ops i32) -> i32. Leaf (no top).
        let gen_restore_sig = m.signatures.push(SignatureData {
            params: vec![
                Type::I32,
                Type::I64,
                Type::I32,
                Type::I32,
                Type::I32,
                Type::I32,
            ],
            returns: vec![Type::I32],
        });
        let gen_restore = stub(&mut m, gen_restore_sig, true, "night_runtime_gen_restore");
        // gen_check_resume: (cx, top, gen i64, val i64, kind i32,
        // rval_addr i32) -> ok.
        let gen_check_resume_sig = m.signatures.push(SignatureData {
            params: vec![
                Type::I32,
                Type::I32,
                Type::I64,
                Type::I64,
                Type::I32,
                Type::I32,
            ],
            returns: vec![Type::I32],
        });
        let gen_check_resume = stub(
            &mut m,
            gen_check_resume_sig,
            true,
            "night_runtime_gen_check_resume",
        );
        // gen_closing: (cx) -> i32. Leaf.
        let gen_closing_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32],
            returns: vec![Type::I32],
        });
        let gen_closing = stub(&mut m, gen_closing_sig, true, "night_runtime_gen_closing");
        // gen_final: (cx, top, gen i64) -> ok (= tonum_sig shape).
        let gen_final = stub(&mut m, tonum_sig, true, "night_runtime_gen_final");
        // async_await / async_resolve: (cx, top, gen i64, val i64) -> ok
        // (= gete_sig shape).
        let async_await = stub(&mut m, gete_sig, true, "night_runtime_async_await");
        let async_resolve = stub(&mut m, gete_sig, true, "night_runtime_async_resolve");
        // async_reject: (cx, top, gen i64, reason i64, stack i64) -> ok
        // (= sete_sig shape).
        let async_reject = stub(&mut m, sete_sig, true, "night_runtime_async_reject");
        // can_skip_await: (cx, top, val i64) -> ok (= tonum_sig shape).
        let can_skip_await = stub(&mut m, tonum_sig, true, "night_runtime_can_skip_await");
        // maybe_extract_await: (cx, top, val i64, canSkip i32) -> ok.
        let maybe_extract_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I64, Type::I32],
            returns: vec![Type::I32],
        });
        let maybe_extract_await = stub(
            &mut m,
            maybe_extract_sig,
            true,
            "night_runtime_maybe_extract_await",
        );
        let check_this = stub(&mut m, tonum_sig, true, "night_runtime_check_this");
        // check_is_obj: (cx, top, v i64, kind i32) -> ok.
        let check_is_obj_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I64, Type::I32],
            returns: vec![Type::I32],
        });
        let check_is_obj = stub(&mut m, check_is_obj_sig, true, "night_runtime_check_is_obj");
        // check_lexical: (cx, top, v i64, script i32, pc i32) -> ok (= delp_sig).
        let check_lexical = stub(&mut m, delp_sig, true, "night_runtime_check_lexical");
        // throw_set_const: (cx, top, script i32, pc i32) -> void.
        let tsc_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I32, Type::I32],
            returns: vec![],
        });
        let throw_set_const = stub(&mut m, tsc_sig, false, "night_runtime_throw_set_const");
        // push_lexical_env / push_class_body_env: (cx, top, env i64, script i32,
        // pc i32) -> ok (= delp_sig shape).
        let push_lexical_env = stub(&mut m, delp_sig, true, "night_runtime_push_lexical_env");
        let push_class_body_env = stub(&mut m, delp_sig, true, "night_runtime_push_class_body_env");
        // freshen_lexical_env / recreate_lexical_env: (cx, top, env i64) -> ok
        // (= tonum_sig shape).
        let freshen_lexical_env =
            stub(&mut m, tonum_sig, true, "night_runtime_freshen_lexical_env");
        let recreate_lexical_env = stub(
            &mut m,
            tonum_sig,
            true,
            "night_runtime_recreate_lexical_env",
        );
        // init_glexical / push_var_env: (cx, top, i64, script i32, pc i32) -> ok
        // (= delp_sig shape).
        let init_glexical = stub(&mut m, delp_sig, true, "night_runtime_init_glexical");
        let push_var_env = stub(&mut m, delp_sig, true, "night_runtime_push_var_env");
        // get_name: (cx, top, env i64, atomId i32, forTypeof i32) -> ok
        // (= delp_sig shape).
        let get_name = stub(&mut m, delp_sig, true, "night_runtime_get_name");
        // bind_name / get_bound_name / bind_unqualified_name / del_name:
        // (cx, top, env i64, atomId i32) -> ok (= getp_sig shape).
        let bind_name = stub(&mut m, getp_sig, true, "night_runtime_bind_name");
        let get_bound_name = stub(&mut m, getp_sig, true, "night_runtime_get_bound_name");
        let bind_unqualified_name = stub(
            &mut m,
            getp_sig,
            true,
            "night_runtime_bind_unqualified_name",
        );
        let del_name = stub(&mut m, getp_sig, true, "night_runtime_del_name");
        // bind_var: (cx, top, env i64) -> ok (= tonum_sig shape).
        let bind_var = stub(&mut m, tonum_sig, true, "night_runtime_bind_var");
        // enter_with: (cx, top, env i64, val i64, script i32, pc i32) -> ok.
        let enter_with_sig = m.signatures.push(SignatureData {
            params: vec![
                Type::I32,
                Type::I32,
                Type::I64,
                Type::I64,
                Type::I32,
                Type::I32,
            ],
            returns: vec![Type::I32],
        });
        let enter_with = stub(&mut m, enter_with_sig, true, "night_runtime_enter_with");
        // throw_msg: (cx, top, kind i32) -> void.
        let tmsg_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I32],
            returns: vec![],
        });
        let throw_msg = stub(&mut m, tmsg_sig, false, "night_runtime_throw_msg");
        // builtin_object: (cx, top, kind i32) -> ok (= getg_sig shape).
        let builtin_object = stub(&mut m, getg_sig, true, "night_runtime_builtin_object");
        // builtin_object_cell: (cx, top, kind, cellAddr) -> ok (= gic_sig shape).
        let builtin_object_cell = stub(&mut m, gic_sig, true, "night_runtime_builtin_object_cell");
        // del_elem: (cx, top, val i64, key i64, strict i32) -> ok.
        let del_elem_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I64, Type::I64, Type::I32],
            returns: vec![Type::I32],
        });
        let del_elem = stub(&mut m, del_elem_sig, true, "night_runtime_del_elem");
        // global_this: (cx, top) -> ok.
        let gthis_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32],
            returns: vec![Type::I32],
        });
        let global_this = stub(&mut m, gthis_sig, true, "night_runtime_global_this");
        // regexp: (cx, top, script i32, index i32) -> ok (= args_sig shape).
        let regexp = stub(&mut m, args_sig, true, "night_runtime_regexp");
        // init_prop_getset: (cx, top, obj i64, atomId i32, fn i64, kind i32) -> ok.
        let ipgs_sig = m.signatures.push(SignatureData {
            params: vec![
                Type::I32,
                Type::I32,
                Type::I64,
                Type::I32,
                Type::I64,
                Type::I32,
            ],
            returns: vec![Type::I32],
        });
        let init_prop_getset = stub(&mut m, ipgs_sig, true, "night_runtime_init_prop_getset");
        let to_bool_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I64],
            returns: vec![Type::I32],
        });
        let to_boolean = stub(&mut m, to_bool_sig, true, "night_runtime_to_boolean");
        // typeof: (cx i32, val i64) -> i64 (boxed string).
        let typeof_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I64],
            returns: vec![Type::I64],
        });
        let typeof_ = stub_i64(&mut m, typeof_sig, "night_runtime_typeof");
        // typeof_eq / constant_strict_eq: (cx i32, val i64, operand i32) -> i32.
        let typeof_eq_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I64, Type::I32],
            returns: vec![Type::I32],
        });
        let typeof_eq = stub(&mut m, typeof_eq_sig, true, "night_runtime_typeof_eq");
        let constant_strict_eq = stub(
            &mut m,
            typeof_eq_sig,
            true,
            "night_runtime_constant_strict_eq",
        );
        // bind_unqualified_gname: (cx i32, top i32, atomId i32) -> i32 (= getg_sig).
        let bind_unqualified_gname = stub(
            &mut m,
            getg_sig,
            true,
            "night_runtime_bind_unqualified_gname",
        );
        // set_name: (cx i32, top i32, env i64, atomId i32, val i64, strict i32) -> i32.
        let set_name_sig = m.signatures.push(SignatureData {
            params: vec![
                Type::I32,
                Type::I32,
                Type::I64,
                Type::I32,
                Type::I64,
                Type::I32,
            ],
            returns: vec![Type::I32],
        });
        let set_name = stub(&mut m, set_name_sig, true, "night_runtime_set_name");
        let new_obj_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I32],
            returns: vec![Type::I32],
        });
        let new_object = stub(&mut m, new_obj_sig, true, "night_runtime_new_object");
        let new_arr_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I32, Type::I32],
            returns: vec![Type::I32],
        });
        let new_array = stub(&mut m, new_arr_sig, true, "night_runtime_new_array");
        let init_prop_sig = m.signatures.push(SignatureData {
            params: vec![
                Type::I32,
                Type::I32,
                Type::I64,
                Type::I32,
                Type::I64,
                Type::I32,
                Type::I32,
            ],
            returns: vec![Type::I32],
        });
        let init_prop = stub(&mut m, init_prop_sig, true, "night_runtime_init_prop");
        let init_elem_sig = m.signatures.push(SignatureData {
            params: vec![
                Type::I32,
                Type::I32,
                Type::I64,
                Type::I64,
                Type::I64,
                Type::I32,
            ],
            returns: vec![Type::I32],
        });
        let init_elem = stub(&mut m, init_elem_sig, true, "night_runtime_init_elem");
        // init_elem_getset: (cx, top, obj i64, key i64, fn i64, kind i32) -> ok
        // (= init_elem_sig shape).
        let init_elem_getset = stub(
            &mut m,
            init_elem_sig,
            true,
            "night_runtime_init_elem_getset",
        );
        // check_private_field: (cx, top, obj i64, key i64, cond i32, kind i32) -> ok.
        let cpf_sig = m.signatures.push(SignatureData {
            params: vec![
                Type::I32,
                Type::I32,
                Type::I64,
                Type::I64,
                Type::I32,
                Type::I32,
            ],
            returns: vec![Type::I32],
        });
        let check_private_field = stub(&mut m, cpf_sig, true, "night_runtime_check_private_field");
        // new_private_name: (cx, top, atomId i32) -> ok (= new_obj_sig shape).
        let new_private_name = stub(&mut m, new_obj_sig, true, "night_runtime_new_private_name");
        // env_setup: (cx i32, top i32, sp i32, script i32) -> i32.
        let env_setup_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I32, Type::I32],
            returns: vec![Type::I32],
        });
        let env_setup = stub(&mut m, env_setup_sig, true, "night_runtime_env_setup");
        // global_decl_instantiation: (cx i32, top i32, script i32, idx i32) -> i32.
        let global_decl_instantiation = stub(
            &mut m,
            env_setup_sig,
            true,
            "night_runtime_global_decl_instantiation",
        );
        // object: (cx i32, script i32, idx i32) -> i64.
        let object_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I32],
            returns: vec![Type::I64],
        });
        let object = stub_i64(&mut m, object_sig, "night_runtime_object");
        let get_aliased_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I64, Type::I32, Type::I32],
            returns: vec![Type::I64],
        });
        let get_aliased = stub_i64(&mut m, get_aliased_sig, "night_runtime_get_aliased");
        let set_aliased_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I64, Type::I32, Type::I32, Type::I64],
            returns: vec![],
        });
        let set_aliased = stub(&mut m, set_aliased_sig, false, "night_runtime_set_aliased");
        let lambda_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I64, Type::I32, Type::I32],
            returns: vec![Type::I32],
        });
        let lambda = stub(&mut m, lambda_sig, true, "night_runtime_lambda");
        let exception_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32],
            returns: vec![Type::I32],
        });
        let exception = stub(&mut m, exception_sig, true, "night_runtime_exception");
        let throw_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I64],
            returns: vec![],
        });
        let throw = stub(&mut m, throw_sig, false, "night_runtime_throw");
        let tws_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I64, Type::I64],
            returns: vec![],
        });
        let throw_with_stack = stub(&mut m, tws_sig, false, "night_runtime_throw_with_stack");
        let gef_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I32],
            returns: vec![Type::I32],
        });
        let get_exception_for_finally = stub(
            &mut m,
            gef_sig,
            true,
            "night_runtime_get_exception_for_finally",
        );
        // night_runtime_post_write_barrier(ownerBits: i64, slot: i32, valBits: i64) -> void
        let pwb_sig = m.signatures.push(SignatureData {
            params: vec![Type::I64, Type::I32, Type::I64],
            returns: vec![],
        });
        let post_write_barrier = stub(&mut m, pwb_sig, false, "night_runtime_post_write_barrier");
        // night_runtime_post_write_barrier_elem(ownerBits: i64, index: i32, valBits: i64) -> void
        let pwbe_sig = m.signatures.push(SignatureData {
            params: vec![Type::I64, Type::I32, Type::I64],
            returns: vec![],
        });
        let post_write_barrier_elem = stub(
            &mut m,
            pwbe_sig,
            false,
            "night_runtime_post_write_barrier_elem",
        );
        // night_runtime_pre_write_barrier(valBits: i64) -> void
        let prewb_sig = m.signatures.push(SignatureData {
            params: vec![Type::I64],
            returns: vec![],
        });
        let pre_write_barrier = stub(&mut m, prewb_sig, false, "night_runtime_pre_write_barrier");
        // resolve_global_slot: (cx i32, bindingId i32) -> i32.
        let rgs_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32],
            returns: vec![Type::I32],
        });
        let resolve_global_slot = stub(&mut m, rgs_sig, true, "night_runtime_resolve_global_slot");
        let resolve_global_slot_guarded = stub(
            &mut m,
            rgs_sig,
            true,
            "night_runtime_resolve_global_slot_guarded",
        );
        let bv_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32],
            returns: vec![Type::I64],
        });
        let binding_value = stub_i64(&mut m, bv_sig, "night_runtime_binding_value");
        // set_global: (cx i32, bindingId i32, valBits i64) -> void.
        let setg_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I64],
            returns: vec![],
        });
        let set_global = stub(&mut m, setg_sig, false, "night_runtime_set_global");
        let bw_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32],
            returns: vec![],
        });
        let binding_written = stub(&mut m, bw_sig, false, "night_runtime_binding_written");
        // create_this: (cx i32, top i32, calleeBits i64, newTargetBits i64,
        // nSlots i32, cellAddr i32, stampWord i32) -> i32.
        let create_this_sig = m.signatures.push(SignatureData {
            params: vec![
                Type::I32,
                Type::I32,
                Type::I64,
                Type::I64,
                Type::I32,
                Type::I32,
                Type::I32,
            ],
            returns: vec![Type::I32],
        });
        let create_this = stub(&mut m, create_this_sig, true, "night_runtime_create_this");
        // rest: (cx, top, sp i32, argc i32, nformal i32) -> ok (= construct_sig).
        let rest = stub(&mut m, rest_sig, true, "night_runtime_rest");
        // implicit_this / check_this_reinit / obj_with_proto: (cx, top, v i64) ->
        // ok (= tonum_sig shape).
        let implicit_this = stub(&mut m, tonum_sig, true, "night_runtime_implicit_this");
        let check_this_reinit = stub(&mut m, tonum_sig, true, "night_runtime_check_this_reinit");
        let obj_with_proto = stub(&mut m, tonum_sig, true, "night_runtime_obj_with_proto");
        // check_return: (cx, top, thisv i64, rval i64) -> ok (= gete_sig shape).
        let check_return = stub(&mut m, gete_sig, true, "night_runtime_check_return");
        // set_fun_name: (cx, top, fun i64, name i64, prefixKind i32) -> ok
        // (= iof_sig shape).
        let set_fun_name = stub(&mut m, iof_sig, true, "night_runtime_set_fun_name");
        // Baseline-tier helpers, with their real signatures (the module
        // must validate the calls baseline bodies make).
        let sig = |m: &mut Module, params: &[Type], ret: Type| {
            m.signatures.push(SignatureData {
                params: params.to_vec(),
                returns: vec![ret],
            })
        };
        use Type::{I32 as W, I64 as J};
        let s = sig(&mut m, &[W, W, W, W], W);
        let bigint = stub(&mut m, s, true, "night_runtime_bigint");
        let s = sig(&mut m, &[W, W, J], W);
        let non_syntactic_global_this =
            stub(&mut m, s, true, "night_runtime_non_syntactic_global_this");
        let take_dispose_capability =
            stub(&mut m, s, true, "night_runtime_take_dispose_capability");
        let s = sig(&mut m, &[W, W, W, W, J], W);
        let set_intrinsic = stub(&mut m, s, true, "night_runtime_set_intrinsic");
        let s = sig(&mut m, &[W, J, W], J);
        let env_callee = stub_i64(&mut m, s, "night_runtime_env_callee");
        let s = sig(&mut m, &[W, W, W, W, J, W, W], W);
        let eval = stub(&mut m, s, true, "night_runtime_eval");
        let s = sig(&mut m, &[W, W, J, J, J, J, W, W], W);
        let spread_eval = stub(&mut m, s, true, "night_runtime_spread_eval");
        let s = sig(&mut m, &[W, W, W, J, J], W);
        let dynamic_import = stub(&mut m, s, true, "night_runtime_dynamic_import");
        let s = sig(&mut m, &[W, W, W], W);
        let import_meta = stub(&mut m, s, true, "night_runtime_import_meta");
        let s = sig(&mut m, &[W, W, J, W, W], W);
        let get_import = stub(&mut m, s, true, "night_runtime_get_import");
        let s = sig(&mut m, &[W, W, J, J, J, J, W], W);
        let add_disposable = stub(&mut m, s, true, "night_runtime_add_disposable");
        let s = sig(&mut m, &[W, W, J, J], W);
        let create_suppressed_error =
            stub(&mut m, s, true, "night_runtime_create_suppressed_error");
        let s = sig(&mut m, &[W, W, J, J, J], W);
        let resume = stub(&mut m, s, true, "night_runtime_resume");
        // fun_with_proto: (cx, top, env i64, proto i64, script i32, funcIndex i32)
        // -> ok.
        let fwp_sig = m.signatures.push(SignatureData {
            params: vec![
                Type::I32,
                Type::I32,
                Type::I64,
                Type::I64,
                Type::I32,
                Type::I32,
            ],
            returns: vec![Type::I32],
        });
        let fun_with_proto = stub(&mut m, fwp_sig, true, "night_runtime_fun_with_proto");
        // no_extra_indexed: (obj i32) -> i32 (leaf); gen_is_closing: (cx) -> i32.
        let nei_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32],
            returns: vec![Type::I32],
        });
        let no_extra_indexed = stub(&mut m, nei_sig, true, "night_runtime_no_extra_indexed");
        let gen_is_closing = stub(&mut m, nei_sig, true, "night_runtime_gen_is_closing");
        // math_unary: (kind i32, x f64) -> f64; math_pow: (x f64, y f64) -> f64.
        let mu_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::F64],
            returns: vec![Type::F64],
        });
        let math_unary = stub_f64(&mut m, mu_sig, "night_runtime_math_unary");
        let mp_sig = m.signatures.push(SignatureData {
            params: vec![Type::F64, Type::F64],
            returns: vec![Type::F64],
        });
        let math_pow = stub_f64(&mut m, mp_sig, "night_runtime_math_pow");
        let fmod = stub_f64(&mut m, mp_sig, "night_runtime_fmod");
        // box_nonstrict_this: (cx, top, this i64) -> i32.
        let bnt_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I64],
            returns: vec![Type::I32],
        });
        let box_nonstrict_this = stub(&mut m, bnt_sig, true, "night_runtime_box_nonstrict_this");
        // get_mapped_arg: (argsobj i64, i i32) -> i64.
        let gma_sig = m.signatures.push(SignatureData {
            params: vec![Type::I64, Type::I32],
            returns: vec![Type::I64],
        });
        let get_mapped_arg = stub_i64(&mut m, gma_sig, "night_runtime_get_mapped_arg");
        // set_mapped_arg: (argsobj i64, i i32, val i64) -> ().
        let sma_sig = m.signatures.push(SignatureData {
            params: vec![Type::I64, Type::I32, Type::I64],
            returns: vec![],
        });
        let set_mapped_arg = stub(&mut m, sma_sig, false, "night_runtime_set_mapped_arg");
        // validate_this_layout: (this i64, layout_id i32) -> ().
        let vtl_sig = m.signatures.push(SignatureData {
            params: vec![Type::I64, Type::I32],
            returns: vec![],
        });
        let validate_this_layout =
            stub(&mut m, vtl_sig, false, "night_runtime_validate_this_layout");
        // iter: (cx, top, val i64) -> i32; more_iter: (cx, iter i64) -> i64;
        // end_iter: (cx, iter i64) -> ().
        let iter_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I64],
            returns: vec![Type::I32],
        });
        let iter_ = stub(&mut m, iter_sig, true, "night_runtime_iter");
        let mi_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I64],
            returns: vec![Type::I64],
        });
        let more_iter = stub_i64(&mut m, mi_sig, "night_runtime_more_iter");
        let ei_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I64],
            returns: vec![],
        });
        let end_iter = stub(&mut m, ei_sig, false, "night_runtime_end_iter");
        // close_iter_for_exception: (cx, top, done i64, iter i64) -> ().
        let cife_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32, Type::I64, Type::I64],
            returns: vec![],
        });
        let close_iter_for_exception = stub(
            &mut m,
            cife_sig,
            false,
            "night_runtime_close_iter_for_exception",
        );
        // symbol: (cx i32, code i32) -> i64.
        let symbol_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I32],
            returns: vec![Type::I64],
        });
        let symbol = stub_i64(&mut m, symbol_sig, "night_runtime_symbol");
        // optimize_get_iterator: (cx i32, v i64) -> i32.
        let ogi_sig = m.signatures.push(SignatureData {
            params: vec![Type::I32, Type::I64],
            returns: vec![Type::I32],
        });
        let optimize_get_iterator =
            stub(&mut m, ogi_sig, true, "night_runtime_optimize_get_iterator");
        // close_iter: (cx, top, iter i64, kind i32) -> ok (= check_is_obj shape).
        let close_iter = stub(&mut m, check_is_obj_sig, true, "night_runtime_close_iter");
        // to_async_iter: (cx, top, iter i64, next i64) -> ok (= gete_sig shape).
        let to_async_iter = stub(&mut m, gete_sig, true, "night_runtime_to_async_iter");
        // spread_call: (cx, top, callee i64, this i64, arr i64, newTarget i64,
        // constructing i32) -> ok.
        let spread_sig = m.signatures.push(SignatureData {
            params: vec![
                Type::I32,
                Type::I32,
                Type::I64,
                Type::I64,
                Type::I64,
                Type::I64,
                Type::I32,
            ],
            returns: vec![Type::I32],
        });
        let spread_call = stub(&mut m, spread_sig, true, "night_runtime_spread_call");
        // optimize_spread_call: (cx, top, v i64) -> ok (= tonum_sig shape).
        let optimize_spread_call = stub(
            &mut m,
            tonum_sig,
            true,
            "night_runtime_optimize_spread_call",
        );
        let (ta_get_poly, ta_set_poly) = build_ta_poly_helpers(&mut m, mem, 64 + 8 * BC_COUNT);
        let ic_get_poly = build_ic_get_helper(&mut m, mem, 64 + 8 * BC_COUNT);
        let ic_set_cold = crate::wasm::build_ic_set_cold_helper(
            &mut m,
            mem,
            64 + 8 * BC_COUNT + MEGA_GET_SIZE * MEGA_GET_ENTRY_BYTES,
        );
        let call_classify = crate::wasm::build_call_classify_helper(&mut m, mem, 64 + 8 * BC_COUNT);
        let elem_append_check =
            crate::wasm::build_elem_append_helper(&mut m, mem, 64 + 8 * BC_COUNT, false);
        let (elem_mega_get, elem_mega_set_probe) = crate::wasm::build_elem_mega_helpers(
            &mut m,
            mem,
            64 + 8 * BC_COUNT,
            64 + 8 * BC_COUNT + MEGA_GET_SIZE * MEGA_GET_ENTRY_BYTES,
        );
        (
            m,
            Helpers {
                mem,
                census: None,
                ta_get_poly,
                ta_set_poly,
                ic_get_poly,
                ic_set_cold,
                elem_mega_get,
                elem_mega_set_probe,
                call_classify,
                elem_append_check,
                night_abi_sig,
                indirect_table,
                direct_call_stub,
                night_abi_sig2,
                direct_call_stub2,
                callee_night_target,
                add,
                concat,
                call,
                call_iter,
                native_dispatch,
                apply_fwd,
                construct,
                get_property,
                set_property,
                get_prop_ic_miss,
                set_prop_ic_miss,
                get_gname,
                get_element,
                set_element,
                binop,
                compare,
                string,
                get_intrinsic,
                get_intrinsic_cell,
                strlit_verify,
                str_chars_eq,
                tonumeric,
                pos,
                neg,
                instanceof_,
                del_prop,
                arguments_,
                arguments_env,
                box_nonstrict_this,
                get_mapped_arg,
                set_mapped_arg,
                validate_this_layout,
                iter_,
                more_iter,
                end_iter,
                close_iter_for_exception,
                symbol,
                optimize_get_iterator,
                close_iter,
                to_async_iter,
                spread_call,
                optimize_spread_call,
                in_,
                has_own,
                to_property_key,
                mutate_proto,
                init_home_object,
                super_base,
                super_fun,
                get_prop_super,
                get_elem_super,
                set_prop_super,
                set_elem_super,
                tostring,
                pow,
                check_obj_coercible,
                check_class_heritage,
                create_generator,
                gen_suspend,
                gen_restore,
                gen_check_resume,
                gen_closing,
                gen_final,
                async_await,
                async_resolve,
                async_reject,
                can_skip_await,
                maybe_extract_await,
                check_is_obj,
                check_this,
                check_lexical,
                throw_set_const,
                push_lexical_env,
                push_class_body_env,
                freshen_lexical_env,
                recreate_lexical_env,
                init_glexical,
                get_name,
                bind_name,
                get_bound_name,
                bind_unqualified_name,
                bind_var,
                del_name,
                push_var_env,
                enter_with,
                throw_msg,
                builtin_object,
                builtin_object_cell,
                del_elem,
                global_this,
                regexp,
                init_prop_getset,
                to_boolean,
                typeof_,
                typeof_eq,
                constant_strict_eq,
                bind_unqualified_gname,
                set_name,
                new_object,
                new_array,
                init_prop,
                init_elem,
                init_elem_getset,
                check_private_field,
                new_private_name,
                env_setup,
                get_aliased,
                set_aliased,
                lambda,
                exception,
                throw,
                throw_with_stack,
                get_exception_for_finally,
                global_decl_instantiation,
                object,
                post_write_barrier,
                post_write_barrier_elem,
                pre_write_barrier,
                resolve_global_slot,
                resolve_global_slot_guarded,
                set_global,
                binding_written,
                binding_value,
                global_slots_base: 0,
                prop_ic_base: 0,
                prop_ic_gen_base: 0,
                this_cells_base: 0,
                this_slots_base: 0,
                mega_get_base: 0,
                mega_set_base: 0,
                append_cache_base: 0,
                accessor_cache_base: 0,
                night_stack_limit_base: 4,
                fn_class_slot: 8,
                static_strings_slot: 16,
                atom_table_slot: 20,
                nursery_pos_slot: 24,
                nursery_end_slot: 28,
                str_ccat_cell: 32,
                str_cat_cell: 40,
                str_fcc_cell: 48,
                str_fuse_addr_slot: 56,
                dda_fuse_addr_slot: 57,
                dyncode_fuse_word: 64 + 8 * BC_COUNT + 40 + 12,
                array_class_slot: 60,
                args_class_base: 64 + 8 * BC_COUNT + 40,
                strlit_slot: 64 + 8 * BC_COUNT + 40 + 16,
                builtin_cells_base: 64,
                math_natives_base: 4096,
                ta_class_base: 64 + 8 * BC_COUNT,
                math_unary,
                math_pow,
                fmod,
                global_vals_base: 0,
                create_this,
                rest,
                implicit_this,
                check_this_reinit,
                check_return,
                obj_with_proto,
                fun_with_proto,
                set_fun_name,
                bigint,
                non_syntactic_global_this,
                set_intrinsic,
                env_callee,
                eval,
                spread_eval,
                dynamic_import,
                import_meta,
                get_import,
                add_disposable,
                take_dispose_capability,
                create_suppressed_error,
                resume,
                no_extra_indexed,
                gen_is_closing,
            },
        )
    }

    fn script(bytecode: Vec<u8>, nargs: u16) -> Script {
        Script {
            bytecode,
            addr: 0,
            gcthings: Vec::new(),
            resume_offsets: Vec::new(),
            try_notes: Vec::new(),
            scope_notes: Vec::new(),
            body_scope: None,
            nargs,
            is_generator_or_async: false,
            is_class_ctor: false,
            strict: true,
            has_mapped_args: false,
        }
    }

    /// `function leaf(x) { return x + 1; }` with x proven Int32. Asserts
    /// it compiles and the emitted module validates (which checks the
    /// box/unbox Wasm types end to end).
    #[test]
    fn leaf_add_one_compiles_and_validates() {
        // GetArg 0; One; Add; Return
        let code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::One),
            op_byte(JSOp::Add),
            op_byte(JSOp::Return),
        ];
        let s = script(code, 1);
        // def_types: arg0 (pc 0) Int32, Add result (pc 4) Int32.
        let (mut m, helpers) = module_with_helpers();
        let source = Source {
            objects: vec![],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        let mut atoms = AtomTable::new(Names::default());

        let outcome = translate_script(
            &mut m,
            helpers,
            &source,
            &mut atoms,
            7,
            &s,
            &Options::default(),
        )
        .expect("translate");
        let (sig, body) = match outcome {
            Outcome::Compiled { sig, body, .. } => (sig, body),
            Outcome::Skipped(op) => panic!("unexpectedly skipped on {op:?}"),
        };
        m.funcs
            .push(waffle::FuncDecl::Body(sig, "leaf".to_string(), body));

        let bytes = m.to_wasm_bytes().expect("serialize");
        if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
            let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
        }
        waffle::wasmparser::validate(&bytes).expect("emitted module validates");
    }

    /// The BBV driver compiles the same leaf, GEN-only, and the module
    /// validates end to end.
    #[test]
    fn bbv_leaf_add_one_compiles_and_validates() {
        let code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::One),
            op_byte(JSOp::Add),
            op_byte(JSOp::Return),
        ];
        let s = script(code, 1);
        let (mut m, helpers) = module_with_helpers();
        let source = Source {
            objects: vec![],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        let mut atoms = AtomTable::new(Names::default());
        let outcome =
            translate_script_bbv(&mut m, helpers, &source, &mut atoms, 7, &s).expect("translate");
        let (sig, body) = match outcome {
            Outcome::Compiled { sig, body, .. } => (sig, body),
            Outcome::Skipped(op) => panic!("unexpectedly skipped on {op:?}"),
        };
        m.funcs
            .push(waffle::FuncDecl::Body(sig, "leaf".to_string(), body));
        let bytes = m.to_wasm_bytes().expect("serialize");
        if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
            let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
        }
        waffle::wasmparser::validate(&bytes).expect("emitted module validates");
    }

    /// The BBV driver handles branchy control flow (a JumpIfFalse diamond
    /// merging through the version table) and a call frame.
    #[test]
    fn bbv_branch_and_call_validate() {
        // GetArg 0; JumpIfFalse +14; GetArg 0; Undefined; Call 0; Return;
        // fall-through: Zero; Return
        let code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::JumpIfFalse),
            13,
            0,
            0,
            0,
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::Undefined),
            op_byte(JSOp::Call),
            0,
            0,
            op_byte(JSOp::Return),
            op_byte(JSOp::Zero),
            op_byte(JSOp::Return),
        ];
        let s = script(code, 1);
        let (mut m, helpers) = module_with_helpers();
        let source = Source {
            objects: vec![],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        let mut atoms = AtomTable::new(Names::default());
        let outcome =
            translate_script_bbv(&mut m, helpers, &source, &mut atoms, 8, &s).expect("translate");
        let (sig, body) = match outcome {
            Outcome::Compiled { sig, body, .. } => (sig, body),
            Outcome::Skipped(op) => panic!("unexpectedly skipped on {op:?}"),
        };
        m.funcs
            .push(waffle::FuncDecl::Body(sig, "f".to_string(), body));
        let bytes = m.to_wasm_bytes().expect("serialize");
        if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
            let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
        }
        waffle::wasmparser::validate(&bytes).expect("emitted module validates");
    }

    /// An int32 counter loop through the BBV version table. Exercises
    /// literal facts, SetLocal strong update, the theta OPT join on the back
    /// edge (the header's int32 ctx is preserved by the body), the i32
    /// compare form, and the Add int arm's per-arm overflow continuation.
    #[test]
    fn bbv_int_loop_versions_validate() {
        // pc0: Zero; pc1: SetLocal 0; pc5: Pop;
        // pc6: LoopHead; pc12: GetLocal 0; pc16: Int8 10; pc18: Lt;
        // pc19: JumpIfFalse +21 (-> pc40);
        // pc24: GetLocal 0; pc28: One; pc29: Add; pc30: SetLocal 0;
        // pc34: Pop; pc35: Goto -29 (-> pc6);
        // pc40: Zero; pc41: Return
        let code = vec![
            op_byte(JSOp::Zero),
            op_byte(JSOp::SetLocal),
            0,
            0,
            0,
            op_byte(JSOp::Pop),
            op_byte(JSOp::LoopHead),
            0,
            0,
            0,
            0,
            0,
            op_byte(JSOp::GetLocal),
            0,
            0,
            0,
            op_byte(JSOp::Int8),
            10,
            op_byte(JSOp::Lt),
            op_byte(JSOp::JumpIfFalse),
            21,
            0,
            0,
            0,
            op_byte(JSOp::GetLocal),
            0,
            0,
            0,
            op_byte(JSOp::One),
            op_byte(JSOp::Add),
            op_byte(JSOp::SetLocal),
            0,
            0,
            0,
            op_byte(JSOp::Pop),
            op_byte(JSOp::Goto),
            (-29i32 as u32 & 0xFF) as u8,
            0xFF,
            0xFF,
            0xFF,
            op_byte(JSOp::Zero),
            op_byte(JSOp::Return),
        ];
        let s = script(code, 0);
        let (mut m, helpers) = module_with_helpers();
        let source = Source {
            objects: vec![],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        let mut atoms = AtomTable::new(Names::default());
        let outcome =
            translate_script_bbv(&mut m, helpers, &source, &mut atoms, 9, &s).expect("translate");
        let (sig, body) = match outcome {
            Outcome::Compiled { sig, body, .. } => (sig, body),
            Outcome::Skipped(op) => panic!("unexpectedly skipped on {op:?}"),
        };
        m.funcs
            .push(waffle::FuncDecl::Body(sig, "loop".to_string(), body));
        let bytes = m.to_wasm_bytes().expect("serialize");
        if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
            let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
        }
        waffle::wasmparser::validate(&bytes).expect("emitted module validates");
    }

    /// Mixed-type arith arms validate -- an argument of unknown type
    /// through Add/Mul/compare exercises the tag-tested per-arm
    /// continuations (int fall-through, f64 and helper side arms).
    #[test]
    fn bbv_unknown_type_arith_arms_validate() {
        // GetArg 0; One; Add; GetArg 0; Mul; GetArg 0; Lt; Return
        let code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::One),
            op_byte(JSOp::Add),
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::Mul),
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::Lt),
            op_byte(JSOp::Return),
        ];
        let s = script(code, 1);
        let (mut m, helpers) = module_with_helpers();
        let source = Source {
            objects: vec![],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        let mut atoms = AtomTable::new(Names::default());
        let outcome =
            translate_script_bbv(&mut m, helpers, &source, &mut atoms, 10, &s).expect("translate");
        let (sig, body) = match outcome {
            Outcome::Compiled { sig, body, .. } => (sig, body),
            Outcome::Skipped(op) => panic!("unexpectedly skipped on {op:?}"),
        };
        m.funcs
            .push(waffle::FuncDecl::Body(sig, "arms".to_string(), body));
        let bytes = m.to_wasm_bytes().expect("serialize");
        if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
            let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
        }
        waffle::wasmparser::validate(&bytes).expect("emitted module validates");
    }

    /// The elem fast arms validate -- a GetElem (dense read +
    /// string arm + hole fall-through) and a SetElem (dense overwrite +
    /// careful arm + inline append/hole arm) on an unknown-type receiver.
    #[test]
    fn bbv_elem_arms_validate() {
        // GetArg 0; One; GetElem; Pop; GetArg 0; One; GetArg 0; SetElem;
        // Return
        let code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::One),
            op_byte(JSOp::GetElem),
            op_byte(JSOp::Pop),
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::One),
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::SetElem),
            op_byte(JSOp::Return),
        ];
        let s = script(code, 1);
        let (mut m, helpers) = module_with_helpers();
        let source = Source {
            objects: vec![],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        let mut atoms = AtomTable::new(Names::default());
        let outcome =
            translate_script_bbv(&mut m, helpers, &source, &mut atoms, 11, &s).expect("translate");
        let (sig, body) = match outcome {
            Outcome::Compiled { sig, body, .. } => (sig, body),
            Outcome::Skipped(op) => panic!("unexpectedly skipped on {op:?}"),
        };
        m.funcs
            .push(waffle::FuncDecl::Body(sig, "elem".to_string(), body));
        let bytes = m.to_wasm_bytes().expect("serialize");
        if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
            let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
        }
        waffle::wasmparser::validate(&bytes).expect("emitted module validates");
    }

    /// The gname inline arms validate -- a GetGName through the
    /// fused-literal arm + guarded syntactic arm, an inline
    /// BindUnqualifiedGName, and a SetGName through the guarded store arm
    /// (barriers + fuse maintenance).
    #[test]
    fn bbv_gname_inline_arms_validate() {
        let source = Source {
            objects: vec![SourceObject::String(JsString::from("g"))],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        // GetGName g; Pop; BindUnqualifiedGName g; GetArg 0; SetGName g;
        // Return
        let code = vec![
            op_byte(JSOp::GetGName),
            0,
            0,
            0,
            0,
            op_byte(JSOp::Pop),
            op_byte(JSOp::BindUnqualifiedGName),
            0,
            0,
            0,
            0,
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::SetGName),
            0,
            0,
            0,
            0,
            op_byte(JSOp::Return),
        ];
        let mut s = script(code, 1);
        s.gcthings = vec![SourceObjectId::new(0)];
        let (mut m, helpers) = module_with_helpers();
        let mut atoms = AtomTable::new(Names::default());
        let name = atoms.names.intern_str("g");
        let mut syn: HashMap<NameId, u32> = HashMap::default();
        syn.insert(name, 0);
        let mut fused: HashMap<NameId, FusedGname> = HashMap::default();
        fused.insert(
            name,
            FusedGname {
                fuse_addr: 4096,
                boxed: (TAG_INT32 << 32) | 42,
            },
        );
        let opts = Options::default();
        let ctx = TranslateCtx {
            helpers,
            source: &source,
            opts: &opts,
            bigint_free: false,
            syn_gnames: &syn,
            gcell_bids: empty_gcell_bids(),
            likely_fns: empty_likely_fns(),
            facts: empty_facts(),
            flag_demand: empty_flag_demand(),
            this_layouts_in: empty_this_layouts(),
            stamp_ctors_in: empty_stamp_ctors(),
            layout_addpred_in: empty_layout_addpred(),
            ctor_nslots_in: empty_ctor_nslots(),
            deleg_restamps_in: empty_stamp_ctors(),
            arg_restamps_in: empty_arg_restamps(),
            local_restamps_in: empty_local_restamps(),
            construct_sites_in: empty_construct_sites(),
            lit_stamps_in: empty_lit_stamps(),
            prop_sites_in: empty_prop_sites(),
            layout_field_masks_in: empty_layout_field_masks(),
            layout_field_ranges_in: empty_layout_field_ranges(),
            array_stamp_in: empty_array_stamp(),
            array_elem_in: empty_array_elem(),
            array_any_claim: None,
            likely_elems: empty_elem_sites(),
            fused_gnames: &fused,
        };
        let outcome = crate::wasm::bbv::translate_script(
            &ctx,
            &mut m,
            &mut atoms,
            ScriptId::new(12),
            &s,
            false,
        )
        .expect("translate");
        let (sig, body) = match outcome {
            Outcome::Compiled { sig, body, .. } => (sig, body),
            Outcome::Skipped(op) => panic!("unexpectedly skipped on {op:?}"),
        };
        m.funcs
            .push(waffle::FuncDecl::Body(sig, "gname".to_string(), body));
        let bytes = m.to_wasm_bytes().expect("serialize");
        if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
            let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
        }
        waffle::wasmparser::validate(&bytes).expect("emitted module validates");
    }

    /// The stamp-guarded fixed-slot GetProp arms + the ctor-return
    /// stamp validate under bbv -- a plain (range) guard, a typed
    /// (SHALLOW-word) guard, and a stamping ctor's return.
    #[test]
    fn bbv_durable_cls_fact_elides_second_guard_validate() {
        // The first class-fact guard's pass writes a durable cls
        // fact back to the arg slot; the second access at a same-range
        // site is fact-implied (identity guard and object test elided --
        // untyped sites go straight to the slot load).
        let source = Source {
            objects: vec![SourceObject::String(JsString::from("f"))],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        // GetArg 0; GetProp f; Pop; GetArg 0; GetProp f; Return
        let code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::GetProp),
            0,
            0,
            0,
            0,
            op_byte(JSOp::Pop),
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::GetProp),
            0,
            0,
            0,
            0,
            op_byte(JSOp::Return),
        ];
        let mut s = script(code, 1);
        s.gcthings = vec![SourceObjectId::new(0)];
        let (mut m, helpers) = module_with_helpers();
        let mut atoms = AtomTable::new(Names::default());
        let mut sites: HashMap<Site, PropSiteIn> = HashMap::default();
        for pc in [3, 12] {
            sites.insert(
                Site::from_raw(21, pc),
                PropSiteIn {
                    shallow_possible: true,
                    cell_addr: 4096,
                    slot: 0,
                    layout_id: 3,
                    hi_layout_id: 5,
                    claim: Claim::NONE,
                    range: None,
                },
            );
        }
        let opts = Options::default();
        let ctx = TranslateCtx {
            helpers,
            source: &source,
            opts: &opts,
            bigint_free: false,
            syn_gnames: empty_syn_gnames(),
            gcell_bids: empty_gcell_bids(),
            likely_fns: empty_likely_fns(),
            facts: empty_facts(),
            flag_demand: empty_flag_demand(),
            this_layouts_in: empty_this_layouts(),
            stamp_ctors_in: empty_stamp_ctors(),
            layout_addpred_in: empty_layout_addpred(),
            ctor_nslots_in: empty_ctor_nslots(),
            deleg_restamps_in: empty_stamp_ctors(),
            arg_restamps_in: empty_arg_restamps(),
            local_restamps_in: empty_local_restamps(),
            construct_sites_in: empty_construct_sites(),
            lit_stamps_in: empty_lit_stamps(),
            prop_sites_in: &sites,
            layout_field_masks_in: empty_layout_field_masks(),
            layout_field_ranges_in: empty_layout_field_ranges(),
            array_stamp_in: empty_array_stamp(),
            array_elem_in: empty_array_elem(),
            array_any_claim: None,
            likely_elems: empty_elem_sites(),
            fused_gnames: empty_fused_gnames(),
        };
        let outcome = crate::wasm::bbv::translate_script(
            &ctx,
            &mut m,
            &mut atoms,
            ScriptId::new(21),
            &s,
            false,
        )
        .expect("translate");
        let (sig, body) = match outcome {
            Outcome::Compiled { sig, body, .. } => (sig, body),
            Outcome::Skipped(op) => panic!("unexpectedly skipped on {op:?}"),
        };
        m.funcs
            .push(waffle::FuncDecl::Body(sig, "clsfact".to_string(), body));
        let bytes = m.to_wasm_bytes().expect("serialize");
        if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
            let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
        }
        waffle::wasmparser::validate(&bytes).expect("emitted module validates");
    }

    #[test]
    fn bbv_class_fact_get_and_stamp_validate() {
        let source = Source {
            objects: vec![SourceObject::String(JsString::from("f"))],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        // GetArg 0; GetProp f; Pop; GetArg 0; GetProp f; Return
        let code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::GetProp),
            0,
            0,
            0,
            0,
            op_byte(JSOp::Pop),
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::GetProp),
            0,
            0,
            0,
            0,
            op_byte(JSOp::Return),
        ];
        let mut s = script(code, 1);
        s.gcthings = vec![SourceObjectId::new(0)];
        let (mut m, helpers) = module_with_helpers();
        let mut atoms = AtomTable::new(Names::default());
        let mut sites: HashMap<Site, PropSiteIn> = HashMap::default();
        // pc 3: plain range guard (mask 0); pc 12: typed numeric mask.
        sites.insert(
            Site::from_raw(13, 3),
            PropSiteIn {
                shallow_possible: true,
                cell_addr: 4096,
                slot: 0,
                layout_id: 3,
                hi_layout_id: 5,
                claim: Claim::NONE,
                range: None,
            },
        );
        sites.insert(
            Site::from_raw(13, 12),
            PropSiteIn {
                shallow_possible: true,
                cell_addr: 4096,
                slot: 1,
                layout_id: 7,
                hi_layout_id: 7,
                claim: Claim::of_prims(PRIM_INT32 | PRIM_DOUBLE),
                range: None,
            },
        );
        let mut ctors: HashMap<ScriptId, StampCtorIn> = HashMap::default();
        ctors.insert(
            ScriptId::new(13),
            StampCtorIn {
                cell_addr: 8192,
                layout_id: 3,
                fields: vec![],
                masks: vec![],
                ranges: vec![],
                prefix_keys: vec![],
                ext_bound: 0,
            },
        );
        let opts = Options::default();
        let ctx = TranslateCtx {
            helpers,
            source: &source,
            opts: &opts,
            bigint_free: false,
            syn_gnames: empty_syn_gnames(),
            gcell_bids: empty_gcell_bids(),
            likely_fns: empty_likely_fns(),
            facts: empty_facts(),
            flag_demand: empty_flag_demand(),
            this_layouts_in: empty_this_layouts(),
            stamp_ctors_in: &ctors,
            layout_addpred_in: empty_layout_addpred(),
            ctor_nslots_in: empty_ctor_nslots(),
            deleg_restamps_in: empty_stamp_ctors(),
            arg_restamps_in: empty_arg_restamps(),
            local_restamps_in: empty_local_restamps(),
            construct_sites_in: empty_construct_sites(),
            lit_stamps_in: empty_lit_stamps(),
            prop_sites_in: &sites,
            layout_field_masks_in: empty_layout_field_masks(),
            layout_field_ranges_in: empty_layout_field_ranges(),
            array_stamp_in: empty_array_stamp(),
            array_elem_in: empty_array_elem(),
            array_any_claim: None,
            likely_elems: empty_elem_sites(),
            fused_gnames: empty_fused_gnames(),
        };
        let outcome = crate::wasm::bbv::translate_script(
            &ctx,
            &mut m,
            &mut atoms,
            ScriptId::new(13),
            &s,
            false,
        )
        .expect("translate");
        let (sig, body) = match outcome {
            Outcome::Compiled { sig, body, .. } => (sig, body),
            Outcome::Skipped(op) => panic!("unexpectedly skipped on {op:?}"),
        };
        m.funcs
            .push(waffle::FuncDecl::Body(sig, "clsget".to_string(), body));
        let bytes = m.to_wasm_bytes().expect("serialize");
        if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
            let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
        }
        waffle::wasmparser::validate(&bytes).expect("emitted module validates");
    }

    /// Typed-load continuations validate -- a double-evidence GetElem
    /// (dbl-first ladder), a no-evidence GetElem (int-first ladder), and
    /// an int32-only-mask class-fact GetProp (the int-tag split on the
    /// SHALLOW-guarded hit arm), all feeding an Add whose lineages join
    /// through theta.
    #[test]
    fn bbv_typed_load_continuations_validate() {
        let source = Source {
            objects: vec![SourceObject::String(JsString::from("f"))],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        // pc0: GetArg 0; pc3: GetProp f; pc8: Pop;
        // pc9: GetArg 0; pc12: One; pc13: GetElem;
        // pc14: GetArg 0; pc17: Int8 2; pc19: GetElem;
        // pc20: Add; pc21: Return
        let code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::GetProp),
            0,
            0,
            0,
            0,
            op_byte(JSOp::Pop),
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::One),
            op_byte(JSOp::GetElem),
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::Int8),
            2,
            op_byte(JSOp::GetElem),
            op_byte(JSOp::Add),
            op_byte(JSOp::Return),
        ];
        let mut s = script(code, 1);
        s.gcthings = vec![SourceObjectId::new(0)];
        let (mut m, helpers) = module_with_helpers();
        let mut atoms = AtomTable::new(Names::default());
        let mut sites: HashMap<Site, PropSiteIn> = HashMap::default();
        sites.insert(
            Site::from_raw(14, 3),
            PropSiteIn {
                shallow_possible: true,
                cell_addr: 4096,
                slot: 0,
                layout_id: 7,
                hi_layout_id: 7,
                claim: Claim::of_prims(PRIM_INT32),
                range: None,
            },
        );
        let mut elems: HashMap<Site, Claim> = HashMap::default();
        elems.insert(Site::from_raw(14, 13), Claim::of_prims(PRIM_DOUBLE));
        let opts = Options::default();
        let ctx = TranslateCtx {
            helpers,
            source: &source,
            opts: &opts,
            bigint_free: false,
            syn_gnames: empty_syn_gnames(),
            gcell_bids: empty_gcell_bids(),
            likely_fns: empty_likely_fns(),
            facts: empty_facts(),
            flag_demand: empty_flag_demand(),
            this_layouts_in: empty_this_layouts(),
            stamp_ctors_in: empty_stamp_ctors(),
            layout_addpred_in: empty_layout_addpred(),
            ctor_nslots_in: empty_ctor_nslots(),
            deleg_restamps_in: empty_stamp_ctors(),
            arg_restamps_in: empty_arg_restamps(),
            local_restamps_in: empty_local_restamps(),
            construct_sites_in: empty_construct_sites(),
            lit_stamps_in: empty_lit_stamps(),
            prop_sites_in: &sites,
            layout_field_masks_in: empty_layout_field_masks(),
            layout_field_ranges_in: empty_layout_field_ranges(),
            array_stamp_in: empty_array_stamp(),
            array_elem_in: empty_array_elem(),
            array_any_claim: None,
            likely_elems: &elems,
            fused_gnames: empty_fused_gnames(),
        };
        let outcome = crate::wasm::bbv::translate_script(
            &ctx,
            &mut m,
            &mut atoms,
            ScriptId::new(14),
            &s,
            false,
        )
        .expect("translate");
        let (sig, body) = match outcome {
            Outcome::Compiled { sig, body, .. } => (sig, body),
            Outcome::Skipped(op) => panic!("unexpectedly skipped on {op:?}"),
        };
        m.funcs
            .push(waffle::FuncDecl::Body(sig, "typedload".to_string(), body));
        let bytes = m.to_wasm_bytes().expect("serialize");
        if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
            let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
        }
        waffle::wasmparser::validate(&bytes).expect("emitted module validates");
    }

    /// A two-target poly guard chain validates -- both callees spliced
    /// (distinct bodies), each claiming its own funcidx guard patch, the
    /// final miss falling to the generic dispatch.
    #[test]
    fn bbv_inline_poly_chain_validates() {
        // Callee 0 (nargs 1): GetArg 0; One; Add; Return
        // Callee 1 (nargs 1): GetArg 0; Int8 2; Mul; Return
        let c0 = script(
            vec![
                op_byte(JSOp::GetArg),
                0,
                0,
                op_byte(JSOp::One),
                op_byte(JSOp::Add),
                op_byte(JSOp::Return),
            ],
            1,
        );
        let c1 = script(
            vec![
                op_byte(JSOp::GetArg),
                0,
                0,
                op_byte(JSOp::Int8),
                2,
                op_byte(JSOp::Mul),
                op_byte(JSOp::Return),
            ],
            1,
        );
        let source = Source {
            objects: vec![SourceObject::Script(c0), SourceObject::Script(c1)],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        // Caller: GetArg 0 (fn); Undefined (this); GetArg 0 (arg);
        // Call 1 @pc7; Return
        let code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::Undefined),
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::Call),
            1,
            0,
            op_byte(JSOp::Return),
        ];
        let s = script(code, 1);
        let (mut m, helpers) = module_with_helpers();
        let mut atoms = AtomTable::new(Names::default());
        let mut lc: HashMap<Site, CallResolution> = HashMap::default();
        lc.insert(
            Site::from_raw(98, 7),
            CallResolution::Scripted(vec![ScriptId::new(0), ScriptId::new(1)]),
        );
        let opts = Options::default();
        let ctx = TranslateCtx {
            helpers,
            source: &source,
            opts: &opts,
            bigint_free: false,
            syn_gnames: empty_syn_gnames(),
            gcell_bids: empty_gcell_bids(),
            likely_fns: empty_likely_fns(),
            facts: &facts_with(|f| f.call_sites = lc.clone()),
            flag_demand: empty_flag_demand(),
            this_layouts_in: empty_this_layouts(),
            stamp_ctors_in: empty_stamp_ctors(),
            layout_addpred_in: empty_layout_addpred(),
            ctor_nslots_in: empty_ctor_nslots(),
            deleg_restamps_in: empty_stamp_ctors(),
            arg_restamps_in: empty_arg_restamps(),
            local_restamps_in: empty_local_restamps(),
            construct_sites_in: empty_construct_sites(),
            lit_stamps_in: empty_lit_stamps(),
            prop_sites_in: empty_prop_sites(),
            layout_field_masks_in: empty_layout_field_masks(),
            layout_field_ranges_in: empty_layout_field_ranges(),
            array_stamp_in: empty_array_stamp(),
            array_elem_in: empty_array_elem(),
            array_any_claim: None,
            likely_elems: empty_elem_sites(),
            fused_gnames: empty_fused_gnames(),
        };
        let outcome = crate::wasm::bbv::translate_script(
            &ctx,
            &mut m,
            &mut atoms,
            ScriptId::new(98),
            &s,
            false,
        )
        .expect("translate");
        let (sig, body, likely_patches) = match outcome {
            Outcome::Compiled {
                sig,
                body,
                likely_patches,
                ..
            } => (sig, body, likely_patches),
            Outcome::Skipped(op) => panic!("unexpectedly skipped on {op:?}"),
        };
        let mut sids: Vec<u32> = likely_patches.iter().map(|p| p.2).collect();
        sids.sort_unstable();
        assert_eq!(sids, vec![0, 1]);
        m.funcs
            .push(waffle::FuncDecl::Body(sig, "polyinline".to_string(), body));
        let bytes = m.to_wasm_bytes().expect("serialize");
        if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
            let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
        }
        waffle::wasmparser::validate(&bytes).expect("emitted module validates");
    }

    /// Args as ctx slots + guard-pass write-back validate -- two GetElem
    /// accesses on the same argument (the second sees the first's
    /// written-back object-receiver/int32-key proofs), their results
    /// feeding an Add.
    #[test]
    fn bbv_arg_facts_writeback_validate() {
        // GetArg 0; One; GetElem; GetArg 0; Int8 2; GetElem; Add; Return
        let code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::One),
            op_byte(JSOp::GetElem),
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::Int8),
            2,
            op_byte(JSOp::GetElem),
            op_byte(JSOp::Add),
            op_byte(JSOp::Return),
        ];
        let s = script(code, 1);
        let (mut m, helpers) = module_with_helpers();
        let source = Source {
            objects: vec![],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        let mut atoms = AtomTable::new(Names::default());
        let outcome =
            translate_script_bbv(&mut m, helpers, &source, &mut atoms, 15, &s).expect("translate");
        let (sig, body) = match outcome {
            Outcome::Compiled { sig, body, .. } => (sig, body),
            Outcome::Skipped(op) => panic!("unexpectedly skipped on {op:?}"),
        };
        m.funcs
            .push(waffle::FuncDecl::Body(sig, "argfacts".to_string(), body));
        let bytes = m.to_wasm_bytes().expect("serialize");
        if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
            let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
        }
        waffle::wasmparser::validate(&bytes).expect("emitted module validates");
    }

    /// A counter loop containing a guarded gname read validates after
    /// LICM (the prologue's engine-table/shape loads hoist to the split
    /// preheader; the guard diamond stays).
    #[test]
    fn bbv_licm_gname_loop_validates() {
        let source = Source {
            objects: vec![SourceObject::String(JsString::from("g"))],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        // pc0: Zero; SetLocal 0; Pop;
        // pc6: LoopHead; pc12: GetGName g; pc17: Pop;
        // pc18: GetLocal 0; Int8 10; Lt; JumpIfFalse +21 (-> pc46);
        // pc30: GetLocal 0; One; Add; SetLocal 0; Pop; Goto -35 (-> pc6);
        // pc46: Zero; Return
        let code = vec![
            op_byte(JSOp::Zero),
            op_byte(JSOp::SetLocal),
            0,
            0,
            0,
            op_byte(JSOp::Pop),
            op_byte(JSOp::LoopHead),
            0,
            0,
            0,
            0,
            0,
            op_byte(JSOp::GetGName),
            0,
            0,
            0,
            0,
            op_byte(JSOp::Pop),
            op_byte(JSOp::GetLocal),
            0,
            0,
            0,
            op_byte(JSOp::Int8),
            10,
            op_byte(JSOp::Lt),
            op_byte(JSOp::JumpIfFalse),
            21,
            0,
            0,
            0,
            op_byte(JSOp::GetLocal),
            0,
            0,
            0,
            op_byte(JSOp::One),
            op_byte(JSOp::Add),
            op_byte(JSOp::SetLocal),
            0,
            0,
            0,
            op_byte(JSOp::Pop),
            op_byte(JSOp::Goto),
            (-35i32 as u32 & 0xFF) as u8,
            0xFF,
            0xFF,
            0xFF,
            op_byte(JSOp::Zero),
            op_byte(JSOp::Return),
        ];
        let mut s = script(code, 0);
        s.gcthings = vec![SourceObjectId::new(0)];
        let (mut m, helpers) = module_with_helpers();
        let mut atoms = AtomTable::new(Names::default());
        // The id has to come from the table the translator will use.
        let name = atoms.names.intern_str("g");
        let mut syn: HashMap<NameId, u32> = HashMap::default();
        syn.insert(name, 0);
        let opts = Options::default();
        let ctx = TranslateCtx {
            helpers,
            source: &source,
            opts: &opts,
            bigint_free: false,
            syn_gnames: &syn,
            gcell_bids: empty_gcell_bids(),
            likely_fns: empty_likely_fns(),
            facts: empty_facts(),
            flag_demand: empty_flag_demand(),
            this_layouts_in: empty_this_layouts(),
            stamp_ctors_in: empty_stamp_ctors(),
            layout_addpred_in: empty_layout_addpred(),
            ctor_nslots_in: empty_ctor_nslots(),
            deleg_restamps_in: empty_stamp_ctors(),
            arg_restamps_in: empty_arg_restamps(),
            local_restamps_in: empty_local_restamps(),
            construct_sites_in: empty_construct_sites(),
            lit_stamps_in: empty_lit_stamps(),
            prop_sites_in: empty_prop_sites(),
            layout_field_masks_in: empty_layout_field_masks(),
            layout_field_ranges_in: empty_layout_field_ranges(),
            array_stamp_in: empty_array_stamp(),
            array_elem_in: empty_array_elem(),
            array_any_claim: None,
            likely_elems: empty_elem_sites(),
            fused_gnames: empty_fused_gnames(),
        };
        let outcome = crate::wasm::bbv::translate_script(
            &ctx,
            &mut m,
            &mut atoms,
            ScriptId::new(14),
            &s,
            false,
        )
        .expect("translate");
        let (sig, body) = match outcome {
            Outcome::Compiled { sig, body, .. } => (sig, body),
            Outcome::Skipped(op) => panic!("unexpectedly skipped on {op:?}"),
        };
        m.funcs
            .push(waffle::FuncDecl::Body(sig, "licm".to_string(), body));
        let bytes = m.to_wasm_bytes().expect("serialize");
        if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
            let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
        }
        waffle::wasmparser::validate(&bytes).expect("emitted module validates");
    }

    /// An elem access with mixed Int32|Double evidence inside a loop
    /// admits dirty-arm forks (the elem slow arm is a may-GC side arm);
    /// the post-call back edge routes into a twin header version and the
    /// emitted graph must stay reducible (Compiled, not Skipped) and
    /// validate.
    #[test]
    fn bbv_post_call_twin_headers_validate() {
        // pc0: Zero; pc1: SetLocal 0; pc5: Pop;
        // pc6: LoopHead; pc12: GetLocal 0; pc16: Int8 10; pc18: Lt;
        // pc19: JumpIfFalse +30 (-> pc49);
        // pc24: GetArg 0; pc27: GetLocal 0; pc31: GetElem; pc32: Pop;
        // pc33: GetLocal 0; pc37: One; pc38: Add; pc39: SetLocal 0;
        // pc43: Pop; pc44: Goto -38 (-> pc6);
        // pc49: Zero; pc50: Return
        let code = vec![
            op_byte(JSOp::Zero),
            op_byte(JSOp::SetLocal),
            0,
            0,
            0,
            op_byte(JSOp::Pop),
            op_byte(JSOp::LoopHead),
            0,
            0,
            0,
            0,
            0,
            op_byte(JSOp::GetLocal),
            0,
            0,
            0,
            op_byte(JSOp::Int8),
            10,
            op_byte(JSOp::Lt),
            op_byte(JSOp::JumpIfFalse),
            30,
            0,
            0,
            0,
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::GetLocal),
            0,
            0,
            0,
            op_byte(JSOp::GetElem),
            op_byte(JSOp::Pop),
            op_byte(JSOp::GetLocal),
            0,
            0,
            0,
            op_byte(JSOp::One),
            op_byte(JSOp::Add),
            op_byte(JSOp::SetLocal),
            0,
            0,
            0,
            op_byte(JSOp::Pop),
            op_byte(JSOp::Goto),
            (-38i32 as u32 & 0xFF) as u8,
            0xFF,
            0xFF,
            0xFF,
            op_byte(JSOp::Zero),
            op_byte(JSOp::Return),
        ];
        let s = script(code, 1);
        let (mut m, helpers) = module_with_helpers();
        let source = Source {
            objects: vec![],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        let mut atoms = AtomTable::new(Names::default());
        let mut elems: HashMap<Site, Claim> = HashMap::default();
        elems.insert(
            Site::from_raw(9, 31),
            Claim::of_prims(PRIM_INT32 | PRIM_DOUBLE),
        );
        let opts = Options::default();
        let ctx = TranslateCtx {
            helpers,
            source: &source,
            opts: &opts,
            bigint_free: false,
            syn_gnames: empty_syn_gnames(),
            gcell_bids: empty_gcell_bids(),
            likely_fns: empty_likely_fns(),
            facts: empty_facts(),
            flag_demand: empty_flag_demand(),
            this_layouts_in: empty_this_layouts(),
            stamp_ctors_in: empty_stamp_ctors(),
            layout_addpred_in: empty_layout_addpred(),
            ctor_nslots_in: empty_ctor_nslots(),
            deleg_restamps_in: empty_stamp_ctors(),
            arg_restamps_in: empty_arg_restamps(),
            local_restamps_in: empty_local_restamps(),
            construct_sites_in: empty_construct_sites(),
            lit_stamps_in: empty_lit_stamps(),
            prop_sites_in: empty_prop_sites(),
            layout_field_masks_in: empty_layout_field_masks(),
            layout_field_ranges_in: empty_layout_field_ranges(),
            array_stamp_in: empty_array_stamp(),
            array_elem_in: empty_array_elem(),
            array_any_claim: None,
            likely_elems: &elems,
            fused_gnames: empty_fused_gnames(),
        };
        let outcome = crate::wasm::bbv::translate_script(
            &ctx,
            &mut m,
            &mut atoms,
            ScriptId::new(9),
            &s,
            false,
        )
        .expect("translate");
        let (sig, body) = match outcome {
            Outcome::Compiled { sig, body, .. } => (sig, body),
            Outcome::Skipped(op) => panic!("unexpectedly skipped on {op:?}"),
        };
        m.funcs
            .push(waffle::FuncDecl::Body(sig, "twins".to_string(), body));
        let bytes = m.to_wasm_bytes().expect("serialize");
        if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
            let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
        }
        waffle::wasmparser::validate(&bytes).expect("emitted module validates");
    }

    /// An inlined leaf callee inside a caller loop keeps the caller's loop
    /// tokens and frame facts through the splice (segment-site mapping), so
    /// the return-tail back edge rejoins the caller's own header lineage
    /// rather than eroding through a TOK_SIDE entry.
    #[test]
    fn bbv_inline_in_loop_token_continuity_validates() {
        // Callee (objects[0], nargs 1): GetArg 0; One; Add; Return
        let callee = script(
            vec![
                op_byte(JSOp::GetArg),
                0,
                0,
                op_byte(JSOp::One),
                op_byte(JSOp::Add),
                op_byte(JSOp::Return),
            ],
            1,
        );
        let source = Source {
            objects: vec![SourceObject::Script(callee)],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        // Caller: same loop shape as the twin test, Call at pc32 with the
        // mono likely-callee evidence.
        let code = vec![
            op_byte(JSOp::Zero),
            op_byte(JSOp::SetLocal),
            0,
            0,
            0,
            op_byte(JSOp::Pop),
            op_byte(JSOp::LoopHead),
            0,
            0,
            0,
            0,
            0,
            op_byte(JSOp::GetLocal),
            0,
            0,
            0,
            op_byte(JSOp::Int8),
            10,
            op_byte(JSOp::Lt),
            op_byte(JSOp::JumpIfFalse),
            33,
            0,
            0,
            0,
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::Undefined),
            op_byte(JSOp::GetLocal),
            0,
            0,
            0,
            op_byte(JSOp::Call),
            1,
            0,
            op_byte(JSOp::Pop),
            op_byte(JSOp::GetLocal),
            0,
            0,
            0,
            op_byte(JSOp::One),
            op_byte(JSOp::Add),
            op_byte(JSOp::SetLocal),
            0,
            0,
            0,
            op_byte(JSOp::Pop),
            op_byte(JSOp::Goto),
            (-41i32 as u32 & 0xFF) as u8,
            0xFF,
            0xFF,
            0xFF,
            op_byte(JSOp::Zero),
            op_byte(JSOp::Return),
        ];
        let s = script(code, 1);
        let (mut m, helpers) = module_with_helpers();
        let mut atoms = AtomTable::new(Names::default());
        let mut lc: HashMap<Site, CallResolution> = HashMap::default();
        lc.insert(
            Site::from_raw(98, 32),
            CallResolution::Scripted(vec![ScriptId::new(0)]),
        );
        let opts = Options::default();
        let ctx = TranslateCtx {
            helpers,
            source: &source,
            opts: &opts,
            bigint_free: false,
            syn_gnames: empty_syn_gnames(),
            gcell_bids: empty_gcell_bids(),
            likely_fns: empty_likely_fns(),
            facts: &facts_with(|f| f.call_sites = lc.clone()),
            flag_demand: empty_flag_demand(),
            this_layouts_in: empty_this_layouts(),
            stamp_ctors_in: empty_stamp_ctors(),
            layout_addpred_in: empty_layout_addpred(),
            ctor_nslots_in: empty_ctor_nslots(),
            deleg_restamps_in: empty_stamp_ctors(),
            arg_restamps_in: empty_arg_restamps(),
            local_restamps_in: empty_local_restamps(),
            construct_sites_in: empty_construct_sites(),
            lit_stamps_in: empty_lit_stamps(),
            prop_sites_in: empty_prop_sites(),
            layout_field_masks_in: empty_layout_field_masks(),
            layout_field_ranges_in: empty_layout_field_ranges(),
            array_stamp_in: empty_array_stamp(),
            array_elem_in: empty_array_elem(),
            array_any_claim: None,
            likely_elems: empty_elem_sites(),
            fused_gnames: empty_fused_gnames(),
        };
        let outcome = crate::wasm::bbv::translate_script(
            &ctx,
            &mut m,
            &mut atoms,
            ScriptId::new(98),
            &s,
            false,
        )
        .expect("translate");
        let (sig, body, likely_patches) = match outcome {
            Outcome::Compiled {
                sig,
                body,
                likely_patches,
                ..
            } => (sig, body, likely_patches),
            Outcome::Skipped(op) => panic!("unexpectedly skipped on {op:?}"),
        };
        assert!(
            likely_patches.iter().any(|p| p.2 == 0),
            "callee spliced (funcidx guard patch present)"
        );
        m.funcs
            .push(waffle::FuncDecl::Body(sig, "inloop".to_string(), body));
        let bytes = m.to_wasm_bytes().expect("serialize");
        if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
            let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
        }
        waffle::wasmparser::validate(&bytes).expect("emitted module validates");
    }

    /// Nested depth -- f(g) is spliced at the root site, and f's interior
    /// call of its argument is resolved via the (callee_sid, local_pc)
    /// evidence translation and spliced at depth 2 (both funcidx guard
    /// patches present).
    #[test]
    fn bbv_nested_inline_validates() {
        // f (objects[0], nargs 1): GetArg 0; Undefined; Int8 5; Call 1
        //   @local pc6; Return
        let f = script(
            vec![
                op_byte(JSOp::GetArg),
                0,
                0,
                op_byte(JSOp::Undefined),
                op_byte(JSOp::Int8),
                5,
                op_byte(JSOp::Call),
                1,
                0,
                op_byte(JSOp::Return),
            ],
            1,
        );
        // g (objects[1], nargs 1): GetArg 0; One; Add; Return
        let g = script(
            vec![
                op_byte(JSOp::GetArg),
                0,
                0,
                op_byte(JSOp::One),
                op_byte(JSOp::Add),
                op_byte(JSOp::Return),
            ],
            1,
        );
        let source = Source {
            objects: vec![SourceObject::Script(f), SourceObject::Script(g)],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        // Root (nargs 2): GetArg 0 (f); Undefined; GetArg 1 (g);
        // Call 1 @pc7; Return
        let code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::Undefined),
            op_byte(JSOp::GetArg),
            1,
            0,
            op_byte(JSOp::Call),
            1,
            0,
            op_byte(JSOp::Return),
        ];
        let s = script(code, 2);
        let (mut m, helpers) = module_with_helpers();
        let mut atoms = AtomTable::new(Names::default());
        let mut lc: HashMap<Site, CallResolution> = HashMap::default();
        lc.insert(
            Site::from_raw(98, 7),
            CallResolution::Scripted(vec![ScriptId::new(0)]),
        );
        lc.insert(
            Site::from_raw(0, 6),
            CallResolution::Scripted(vec![ScriptId::new(1)]),
        );
        let opts = Options::default();
        let ctx = TranslateCtx {
            helpers,
            source: &source,
            opts: &opts,
            bigint_free: false,
            syn_gnames: empty_syn_gnames(),
            gcell_bids: empty_gcell_bids(),
            likely_fns: empty_likely_fns(),
            facts: &facts_with(|f| f.call_sites = lc.clone()),
            flag_demand: empty_flag_demand(),
            this_layouts_in: empty_this_layouts(),
            stamp_ctors_in: empty_stamp_ctors(),
            layout_addpred_in: empty_layout_addpred(),
            ctor_nslots_in: empty_ctor_nslots(),
            deleg_restamps_in: empty_stamp_ctors(),
            arg_restamps_in: empty_arg_restamps(),
            local_restamps_in: empty_local_restamps(),
            construct_sites_in: empty_construct_sites(),
            lit_stamps_in: empty_lit_stamps(),
            prop_sites_in: empty_prop_sites(),
            layout_field_masks_in: empty_layout_field_masks(),
            layout_field_ranges_in: empty_layout_field_ranges(),
            array_stamp_in: empty_array_stamp(),
            array_elem_in: empty_array_elem(),
            array_any_claim: None,
            likely_elems: empty_elem_sites(),
            fused_gnames: empty_fused_gnames(),
        };
        let outcome = crate::wasm::bbv::translate_script(
            &ctx,
            &mut m,
            &mut atoms,
            ScriptId::new(98),
            &s,
            false,
        )
        .expect("translate");
        let (sig, body, likely_patches) = match outcome {
            Outcome::Compiled {
                sig,
                body,
                likely_patches,
                ..
            } => (sig, body, likely_patches),
            Outcome::Skipped(op) => panic!("unexpectedly skipped on {op:?}"),
        };
        let mut sids: Vec<u32> = likely_patches.iter().map(|p| p.2).collect();
        sids.sort_unstable();
        sids.dedup();
        assert_eq!(sids, vec![0, 1], "both splice guards present");
        m.funcs
            .push(waffle::FuncDecl::Body(sig, "nested".to_string(), body));
        let bytes = m.to_wasm_bytes().expect("serialize");
        if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
            let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
        }
        waffle::wasmparser::validate(&bytes).expect("emitted module validates");
    }

    /// Under-application -- argc 1 into a nargs-2 callee pads the missing
    /// formal with undefined and still splices.
    #[test]
    fn bbv_inline_argc_padding_validates() {
        // Callee (objects[0], nargs 2): GetArg 1; Return
        let callee = script(vec![op_byte(JSOp::GetArg), 1, 0, op_byte(JSOp::Return)], 2);
        let source = Source {
            objects: vec![SourceObject::Script(callee)],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        // Root: GetArg 0; Undefined; GetArg 0; Call 1 @pc7; Return
        let code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::Undefined),
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::Call),
            1,
            0,
            op_byte(JSOp::Return),
        ];
        let s = script(code, 1);
        let (mut m, helpers) = module_with_helpers();
        let mut atoms = AtomTable::new(Names::default());
        let mut lc: HashMap<Site, CallResolution> = HashMap::default();
        lc.insert(
            Site::from_raw(98, 7),
            CallResolution::Scripted(vec![ScriptId::new(0)]),
        );
        let opts = Options::default();
        let ctx = TranslateCtx {
            helpers,
            source: &source,
            opts: &opts,
            bigint_free: false,
            syn_gnames: empty_syn_gnames(),
            gcell_bids: empty_gcell_bids(),
            likely_fns: empty_likely_fns(),
            facts: &facts_with(|f| f.call_sites = lc.clone()),
            flag_demand: empty_flag_demand(),
            this_layouts_in: empty_this_layouts(),
            stamp_ctors_in: empty_stamp_ctors(),
            layout_addpred_in: empty_layout_addpred(),
            ctor_nslots_in: empty_ctor_nslots(),
            deleg_restamps_in: empty_stamp_ctors(),
            arg_restamps_in: empty_arg_restamps(),
            local_restamps_in: empty_local_restamps(),
            construct_sites_in: empty_construct_sites(),
            lit_stamps_in: empty_lit_stamps(),
            prop_sites_in: empty_prop_sites(),
            layout_field_masks_in: empty_layout_field_masks(),
            layout_field_ranges_in: empty_layout_field_ranges(),
            array_stamp_in: empty_array_stamp(),
            array_elem_in: empty_array_elem(),
            array_any_claim: None,
            likely_elems: empty_elem_sites(),
            fused_gnames: empty_fused_gnames(),
        };
        let outcome = crate::wasm::bbv::translate_script(
            &ctx,
            &mut m,
            &mut atoms,
            ScriptId::new(98),
            &s,
            false,
        )
        .expect("translate");
        let (sig, body, likely_patches) = match outcome {
            Outcome::Compiled {
                sig,
                body,
                likely_patches,
                ..
            } => (sig, body, likely_patches),
            Outcome::Skipped(op) => panic!("unexpectedly skipped on {op:?}"),
        };
        assert!(likely_patches.iter().any(|p| p.2 == 0), "splice happened");
        m.funcs
            .push(waffle::FuncDecl::Body(sig, "argcpad".to_string(), body));
        let bytes = m.to_wasm_bytes().expect("serialize");
        if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
            let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
        }
        waffle::wasmparser::validate(&bytes).expect("emitted module validates");
    }

    /// Construct splice: a mono resolved `new` site splices the ctor body
    /// (inline `this` allocation + the ctor-exit stamp + the
    /// `is_object(ret) ? ret : this` completion at the segment return),
    /// and the ctor's construct-`this` cell is claimed.
    #[test]
    fn bbv_inline_construct_validates() {
        // Ctor (objects[0], nargs 1): GetArg 0; Pop; RetRval
        let ctor = script(
            vec![
                op_byte(JSOp::GetArg),
                0,
                0,
                op_byte(JSOp::Pop),
                op_byte(JSOp::RetRval),
            ],
            1,
        );
        let source = Source {
            objects: vec![SourceObject::Script(ctor)],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        // Root: GetArg 0 (the ctor); IsConstructing; GetArg 1 (the arg);
        // DupAt 2 (newTarget = the ctor); New 1 @pc8; Return
        let code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::IsConstructing),
            op_byte(JSOp::GetArg),
            1,
            0,
            op_byte(JSOp::DupAt),
            2,
            0,
            0,
            op_byte(JSOp::New),
            1,
            0,
            op_byte(JSOp::Return),
        ];
        let s = script(code, 2);
        let (mut m, helpers) = module_with_helpers();
        let mut atoms = AtomTable::new(Names::default());
        let mut lc: HashMap<Site, CallResolution> = HashMap::default();
        lc.insert(
            Site::from_raw(98, 11),
            CallResolution::Scripted(vec![ScriptId::new(0)]),
        );
        let opts = Options::default();
        let ctx = TranslateCtx {
            helpers,
            source: &source,
            opts: &opts,
            bigint_free: false,
            syn_gnames: empty_syn_gnames(),
            gcell_bids: empty_gcell_bids(),
            likely_fns: empty_likely_fns(),
            facts: &facts_with(|f| f.call_sites = lc.clone()),
            flag_demand: empty_flag_demand(),
            this_layouts_in: empty_this_layouts(),
            stamp_ctors_in: empty_stamp_ctors(),
            layout_addpred_in: empty_layout_addpred(),
            ctor_nslots_in: empty_ctor_nslots(),
            deleg_restamps_in: empty_stamp_ctors(),
            arg_restamps_in: empty_arg_restamps(),
            local_restamps_in: empty_local_restamps(),
            construct_sites_in: empty_construct_sites(),
            lit_stamps_in: empty_lit_stamps(),
            prop_sites_in: empty_prop_sites(),
            layout_field_masks_in: empty_layout_field_masks(),
            layout_field_ranges_in: empty_layout_field_ranges(),
            array_stamp_in: empty_array_stamp(),
            array_elem_in: empty_array_elem(),
            array_any_claim: None,
            likely_elems: empty_elem_sites(),
            fused_gnames: empty_fused_gnames(),
        };
        let outcome = crate::wasm::bbv::translate_script(
            &ctx,
            &mut m,
            &mut atoms,
            ScriptId::new(98),
            &s,
            false,
        )
        .expect("translate");
        let (sig, body, likely_patches, construct_cell_patches) = match outcome {
            Outcome::Compiled {
                sig,
                body,
                likely_patches,
                construct_cell_patches,
                ..
            } => (sig, body, likely_patches, construct_cell_patches),
            Outcome::Skipped(op) => panic!("unexpectedly skipped on {op:?}"),
        };
        assert!(
            likely_patches.iter().any(|p| p.2 == 0),
            "ctor body spliced (funcidx guard patch present)"
        );
        assert!(
            !construct_cell_patches.is_empty(),
            "construct-this cell claimed"
        );
        m.funcs
            .push(waffle::FuncDecl::Body(sig, "newsplice".to_string(), body));
        let bytes = m.to_wasm_bytes().expect("serialize");
        if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
            let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
        }
        waffle::wasmparser::validate(&bytes).expect("emitted module validates");
    }

    /// A proven `T.apply(this, arguments)`
    /// site forwards the caller's actuals through `night_runtime_apply_fwd`
    /// and the arguments object is never built.
    #[test]
    fn bbv_apply_forward_validates() {
        // nargs 0 (the `Class.create` forwarder shape):
        //   Arguments; SetLocal 0; Pop; Undefined x3; GetLocal 0;
        //   Call 2 @pc13; Return
        let code = vec![
            op_byte(JSOp::Arguments),
            op_byte(JSOp::SetLocal),
            0,
            0,
            0,
            op_byte(JSOp::Pop),
            op_byte(JSOp::Undefined),
            op_byte(JSOp::Undefined),
            op_byte(JSOp::Undefined),
            op_byte(JSOp::GetLocal),
            0,
            0,
            0,
            op_byte(JSOp::Call),
            2,
            0,
            op_byte(JSOp::Return),
        ];
        let s = script(code, 0);
        let source = Source {
            objects: vec![],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        let (mut m, helpers) = module_with_helpers();
        let mut atoms = AtomTable::new(Names::default());
        // kind 2 == a `.apply` property read feeding this call site.
        let mut apply_sites: HashMap<Site, CallForm> = HashMap::default();
        apply_sites.insert(Site::from_raw(97, 13), CallForm::Apply);
        assert_eq!(
            compute_apply_fwd_pcs(&s, &apply_sites, 97),
            Some([Pc::new(13)].into_iter().collect()),
            "the flow check proves the forward"
        );
        let opts = Options::default();
        let ctx = TranslateCtx {
            helpers,
            source: &source,
            opts: &opts,
            bigint_free: false,
            syn_gnames: empty_syn_gnames(),
            gcell_bids: empty_gcell_bids(),
            likely_fns: empty_likely_fns(),
            facts: &facts_with(|f| f.apply_sites = apply_sites.clone()),
            flag_demand: empty_flag_demand(),
            this_layouts_in: empty_this_layouts(),
            stamp_ctors_in: empty_stamp_ctors(),
            layout_addpred_in: empty_layout_addpred(),
            ctor_nslots_in: empty_ctor_nslots(),
            deleg_restamps_in: empty_stamp_ctors(),
            arg_restamps_in: empty_arg_restamps(),
            local_restamps_in: empty_local_restamps(),
            construct_sites_in: empty_construct_sites(),
            lit_stamps_in: empty_lit_stamps(),
            prop_sites_in: empty_prop_sites(),
            layout_field_masks_in: empty_layout_field_masks(),
            layout_field_ranges_in: empty_layout_field_ranges(),
            array_stamp_in: empty_array_stamp(),
            array_elem_in: empty_array_elem(),
            array_any_claim: None,
            likely_elems: empty_elem_sites(),
            fused_gnames: empty_fused_gnames(),
        };
        let outcome = crate::wasm::bbv::translate_script(
            &ctx,
            &mut m,
            &mut atoms,
            ScriptId::new(97),
            &s,
            false,
        )
        .expect("translate");
        let (sig, body) = match outcome {
            Outcome::Compiled { sig, body, .. } => (sig, body),
            Outcome::Skipped(op) => panic!("unexpectedly skipped on {op:?}"),
        };
        let calls = |f: Func| {
            body.values.entries().any(|(_, d)| {
                matches!(
                    d,
                    ValueDef::Operator(Operator::Call { function_index }, ..)
                        if *function_index == f
                )
            })
        };
        assert!(calls(helpers.apply_fwd), "the forward helper is emitted");
        assert!(
            !calls(helpers.arguments_) && !calls(helpers.arguments_env),
            "the arguments object is elided"
        );
        m.funcs
            .push(waffle::FuncDecl::Body(sig, "applyfwd".to_string(), body));
        let bytes = m.to_wasm_bytes().expect("serialize");
        if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
            let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
        }
        waffle::wasmparser::validate(&bytes).expect("emitted module validates");
    }

    /// Inlining: a mono likely call splices the callee body through the
    /// pc-space segment machinery (guard + child frame + return edge) and
    /// the module validates.
    #[test]
    fn bbv_inline_call_validates() {
        // Callee (objects[0], nargs 1): GetArg 0; One; Add; Return
        let callee_code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::One),
            op_byte(JSOp::Add),
            op_byte(JSOp::Return),
        ];
        let callee = script(callee_code, 1);
        let source = Source {
            objects: vec![SourceObject::Script(callee)],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        // Caller: GetArg 0 (fn); Undefined (this); GetArg 0 (arg);
        // Call 1 @pc7; Return
        let code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::Undefined),
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::Call),
            1,
            0,
            op_byte(JSOp::Return),
        ];
        let s = script(code, 1);
        let (mut m, helpers) = module_with_helpers();
        let mut atoms = AtomTable::new(Names::default());
        let mut lc: HashMap<Site, CallResolution> = HashMap::default();
        lc.insert(
            Site::from_raw(99, 7),
            CallResolution::Scripted(vec![ScriptId::new(0)]),
        );
        let opts = Options::default();
        let ctx = TranslateCtx {
            helpers,
            source: &source,
            opts: &opts,
            bigint_free: false,
            syn_gnames: empty_syn_gnames(),
            gcell_bids: empty_gcell_bids(),
            likely_fns: empty_likely_fns(),
            facts: &facts_with(|f| f.call_sites = lc.clone()),
            flag_demand: empty_flag_demand(),
            this_layouts_in: empty_this_layouts(),
            stamp_ctors_in: empty_stamp_ctors(),
            layout_addpred_in: empty_layout_addpred(),
            ctor_nslots_in: empty_ctor_nslots(),
            deleg_restamps_in: empty_stamp_ctors(),
            arg_restamps_in: empty_arg_restamps(),
            local_restamps_in: empty_local_restamps(),
            construct_sites_in: empty_construct_sites(),
            lit_stamps_in: empty_lit_stamps(),
            prop_sites_in: empty_prop_sites(),
            layout_field_masks_in: empty_layout_field_masks(),
            layout_field_ranges_in: empty_layout_field_ranges(),
            array_stamp_in: empty_array_stamp(),
            array_elem_in: empty_array_elem(),
            array_any_claim: None,
            likely_elems: empty_elem_sites(),
            fused_gnames: empty_fused_gnames(),
        };
        let outcome = crate::wasm::bbv::translate_script(
            &ctx,
            &mut m,
            &mut atoms,
            ScriptId::new(99),
            &s,
            false,
        )
        .expect("translate");
        let (sig, body, likely_patches) = match outcome {
            Outcome::Compiled {
                sig,
                body,
                likely_patches,
                ..
            } => (sig, body, likely_patches),
            Outcome::Skipped(op) => panic!("unexpectedly skipped on {op:?}"),
        };
        // Two patches, both naming the callee: the splice's own funcidx
        // guard const, and the likely-callee direct arm its generic miss
        // path arms (a guard const plus the static stub `call` to rewrite).
        assert_eq!(likely_patches.len(), 2);
        assert!(likely_patches.iter().all(|p| p.2 == 0));
        assert_eq!(
            likely_patches.iter().filter(|p| p.0 != p.1).count(),
            1,
            "exactly one patch carries a distinct stub call to rewrite"
        );
        m.funcs
            .push(waffle::FuncDecl::Body(sig, "inline".to_string(), body));
        let bytes = m.to_wasm_bytes().expect("serialize");
        if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
            let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
        }
        waffle::wasmparser::validate(&bytes).expect("emitted module validates");
    }

    /// Locals-into-SSA: an int-typed hot local live across an inline call
    /// inside a loop exercises the carrier machinery end to end -- the
    /// typed block param at the loop versions, the raw-i32 carrier
    /// surviving the CallGc kill sweep (numbers are GC-immune), and the
    /// cross-frame return edge reloading the caller's slot under the
    /// restored caller facts.
    #[test]
    fn bbv_local_carrier_across_inline_call_validates() {
        // Callee (objects[0], nargs 1): GetArg 0; One; Add; Return
        let callee_code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::One),
            op_byte(JSOp::Add),
            op_byte(JSOp::Return),
        ];
        let callee = script(callee_code, 1);
        let source = Source {
            objects: vec![SourceObject::Script(callee)],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        // pc0: Zero; pc1: SetLocal 0; pc5: Pop;
        // pc6: LoopHead (6 bytes);
        // pc12: GetArg 0 (fn); pc15: Undefined (this); pc16: GetArg 0;
        // pc19: Call 1; pc22: Pop;
        // pc23: GetLocal 0; pc27: One; pc28: Add; pc29: SetLocal 0;
        // pc33: Pop;
        // pc34: GetLocal 0; pc38: Int8 10; pc40: Lt;
        // pc41: JumpIfFalse +10 (-> pc51); pc46: Goto -40 (-> pc6);
        // pc51: GetLocal 0; pc55: Return
        let code = vec![
            op_byte(JSOp::Zero),
            op_byte(JSOp::SetLocal),
            0,
            0,
            0,
            op_byte(JSOp::Pop),
            op_byte(JSOp::LoopHead),
            0,
            0,
            0,
            0,
            0,
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::Undefined),
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::Call),
            1,
            0,
            op_byte(JSOp::Pop),
            op_byte(JSOp::GetLocal),
            0,
            0,
            0,
            op_byte(JSOp::One),
            op_byte(JSOp::Add),
            op_byte(JSOp::SetLocal),
            0,
            0,
            0,
            op_byte(JSOp::Pop),
            op_byte(JSOp::GetLocal),
            0,
            0,
            0,
            op_byte(JSOp::Int8),
            10,
            op_byte(JSOp::Lt),
            op_byte(JSOp::JumpIfFalse),
            10,
            0,
            0,
            0,
            op_byte(JSOp::Goto),
            (-40i32 as u32 & 0xFF) as u8,
            0xFF,
            0xFF,
            0xFF,
            op_byte(JSOp::GetLocal),
            0,
            0,
            0,
            op_byte(JSOp::Return),
        ];
        let s = script(code, 1);
        let (mut m, helpers) = module_with_helpers();
        let mut atoms = AtomTable::new(Names::default());
        let mut lc: HashMap<Site, CallResolution> = HashMap::default();
        lc.insert(
            Site::from_raw(98, 19),
            CallResolution::Scripted(vec![ScriptId::new(0)]),
        );
        let opts = Options::default();
        let ctx = TranslateCtx {
            helpers,
            source: &source,
            opts: &opts,
            bigint_free: false,
            syn_gnames: empty_syn_gnames(),
            gcell_bids: empty_gcell_bids(),
            likely_fns: empty_likely_fns(),
            facts: &facts_with(|f| f.call_sites = lc.clone()),
            flag_demand: empty_flag_demand(),
            this_layouts_in: empty_this_layouts(),
            stamp_ctors_in: empty_stamp_ctors(),
            layout_addpred_in: empty_layout_addpred(),
            ctor_nslots_in: empty_ctor_nslots(),
            deleg_restamps_in: empty_stamp_ctors(),
            arg_restamps_in: empty_arg_restamps(),
            local_restamps_in: empty_local_restamps(),
            construct_sites_in: empty_construct_sites(),
            lit_stamps_in: empty_lit_stamps(),
            prop_sites_in: empty_prop_sites(),
            layout_field_masks_in: empty_layout_field_masks(),
            layout_field_ranges_in: empty_layout_field_ranges(),
            array_stamp_in: empty_array_stamp(),
            array_elem_in: empty_array_elem(),
            array_any_claim: None,
            likely_elems: empty_elem_sites(),
            fused_gnames: empty_fused_gnames(),
        };
        let outcome = crate::wasm::bbv::translate_script(
            &ctx,
            &mut m,
            &mut atoms,
            ScriptId::new(98),
            &s,
            false,
        )
        .expect("translate");
        let (sig, body, likely_patches) = match outcome {
            Outcome::Compiled {
                sig,
                body,
                likely_patches,
                ..
            } => (sig, body, likely_patches),
            Outcome::Skipped(op) => panic!("unexpectedly skipped on {op:?}"),
        };
        assert!(likely_patches.iter().any(|p| p.2 == 0), "splice happened");
        // The carriers engaged: some version block carries a raw-i32 local
        // param at a stack-empty pc (the loop-header lineage's int
        // counter) -- without carriers every stack-empty version had zero
        // params.
        let has_i32_param_block = body
            .blocks
            .values()
            .any(|b| !b.params.is_empty() && b.params.iter().all(|&(t, _)| t == waffle::Type::I32));
        assert!(has_i32_param_block, "no i32-only-param version minted");
        m.funcs
            .push(waffle::FuncDecl::Body(sig, "carrier".to_string(), body));
        let bytes = m.to_wasm_bytes().expect("serialize");
        if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
            let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
        }
        waffle::wasmparser::validate(&bytes).expect("emitted module validates");
    }

    /// A script containing an op in the bail set is skipped (left interpreted),
    /// never partially compiled. `Pow` has no compiled form yet.
    #[test]
    fn unsupported_op_is_skipped() {
        // GetArg 0; ForceInterpreter; Return -- ForceInterpreter is a permanent
        // member of the bail set (it exists to force interpretation and is never
        // compilable), so this test is stable as op coverage grows.
        let code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::ForceInterpreter),
            op_byte(JSOp::Return),
        ];
        let s = script(code, 1);
        let (mut m, helpers) = module_with_helpers();
        let source = Source {
            objects: vec![],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        let mut atoms = AtomTable::new(Names::default());
        match translate_script(
            &mut m,
            helpers,
            &source,
            &mut atoms,
            0,
            &s,
            &Options::default(),
        )
        .expect("translate")
        {
            Outcome::Skipped(reason) => assert!(reason.contains("ForceInterpreter"), "{reason}"),
            Outcome::Compiled { .. } => panic!("should not compile a bail-set op"),
        }
    }

    /// `typeof`, `TypeofEq`, and `StrictConstantEq/Ne` compile to leaf-helper
    /// calls and the emitted module validates (box/unbox types end to end).
    #[test]
    fn typeof_and_constant_compares_validate() {
        // GetArg 0; Typeof; Pop; GetArg 0; TypeofEq 0x83; Pop;
        // GetArg 0; StrictConstantNe 0,0; Return
        let code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::Typeof),
            op_byte(JSOp::Pop),
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::TypeofEq),
            0x83,
            op_byte(JSOp::Pop),
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::StrictConstantNe),
            0,
            0,
            op_byte(JSOp::Return),
        ];
        let s = script(code, 1);
        let (mut m, helpers) = module_with_helpers();
        let source = Source {
            objects: vec![],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        let mut atoms = AtomTable::new(Names::default());
        let outcome = translate_script(
            &mut m,
            helpers,
            &source,
            &mut atoms,
            0,
            &s,
            &Options::default(),
        )
        .expect("translate");
        let (sig, body) = match outcome {
            Outcome::Compiled { sig, body, .. } => (sig, body),
            Outcome::Skipped(reason) => panic!("unexpectedly skipped: {reason}"),
        };
        m.funcs
            .push(waffle::FuncDecl::Body(sig, "tf".to_string(), body));
        let bytes = m.to_wasm_bytes().expect("serialize");
        if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
            let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
        }
        waffle::wasmparser::validate(&bytes).expect("emitted module validates");
    }

    /// Like `compile_and_validate` but for a pre-built `Script` (e.g. with
    /// try-notes), with no proven types.
    fn compile_and_validate_script(s: Script, source_id: u32) {
        let (mut m, helpers) = module_with_helpers();
        let source = Source {
            objects: vec![],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        let mut atoms = AtomTable::new(Names::default());
        match translate_script(
            &mut m,
            helpers,
            &source,
            &mut atoms,
            source_id,
            &s,
            &Options::default(),
        )
        .expect("translate")
        {
            Outcome::Compiled { sig, body, .. } => {
                if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
                    let ir = format!("{}", body.display("", None));
                    let _ = std::fs::write(std::path::Path::new(&dir).join("test.ir"), ir);
                }
                m.funcs
                    .push(waffle::FuncDecl::Body(sig, "f".to_string(), body));
                let bytes = m.to_wasm_bytes().expect("serialize");
                if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
                    let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
                }
                waffle::wasmparser::validate(&bytes).expect("emitted module validates");
            }
            Outcome::Skipped(reason) => panic!("unexpectedly skipped: {reason}"),
        }
    }

    /// Compile `s` with the baseline tier and assert the emitted module
    /// validates.
    fn baseline_compile_and_validate(s: Script) {
        let (mut m, helpers) = module_with_helpers();
        let source = Source {
            objects: vec![],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        let mut atoms = AtomTable::new(Names::default());
        let opts = Options::default();
        let ctx = empty_ctx(helpers, &source, &opts);
        match crate::wasm::baseline::translate_script(
            &ctx,
            &mut m,
            &mut atoms,
            ScriptId::new(1),
            &s,
            false,
        )
        .expect("translate")
        {
            Outcome::Compiled { sig, body, .. } => {
                m.funcs
                    .push(waffle::FuncDecl::Body(sig, "f".to_string(), body));
                let bytes = m.to_wasm_bytes().expect("serialize");
                waffle::wasmparser::validate(&bytes).expect("emitted module validates");
            }
            Outcome::Skipped(reason) => panic!("unexpectedly skipped: {reason}"),
        }
    }

    /// Every op with an inline int32 or ToBoolean fast path
    /// (`docs/BASELINE.md` §3.1) compiles, fast and slow arms, into a valid
    /// module.
    #[test]
    fn baseline_fast_paths_validate() {
        use JSOp::*;
        let get_arg = |n: u8| [op_byte(GetArg), n, 0];
        // `return a0 OP a1` (`a0[a1]` for GetElem)
        for op in [
            Add, Sub, Mul, Div, Mod, BitAnd, BitOr, BitXor, Lsh, Rsh, Ursh, Lt, Gt, Le, Ge, Eq, Ne,
            StrictEq, StrictNe, GetElem,
        ] {
            let mut code = get_arg(0).to_vec();
            code.extend(get_arg(1));
            code.extend([op_byte(op), op_byte(Return)]);
            baseline_compile_and_validate(script(code, 2));
        }
        // `return OP a0`
        for op in [Inc, Dec, Neg, Pos, BitNot, Not, ToNumeric] {
            let mut code = get_arg(0).to_vec();
            code.extend([op_byte(op), op_byte(Return)]);
            baseline_compile_and_validate(script(code, 1));
        }
        // `if (a0) return a0; return a1;`, both polarities: @0 GetArg 0;
        // @3 JumpIf* +9 (-> @12); @8 GetArg 0; @11 Return; @12 GetArg 1 ...
        for op in [JumpIfFalse, JumpIfTrue] {
            let mut code = get_arg(0).to_vec();
            code.extend([op_byte(op), 9, 0, 0, 0]);
            code.extend(get_arg(0));
            code.push(op_byte(Return));
            code.extend(get_arg(1));
            code.push(op_byte(Return));
            baseline_compile_and_validate(script(code, 2));
        }
        // `return a0 && a1` / `a0 || a1`:
        // @0 GetArg 0; @3 And/Or +9 (-> @12); @8 Pop; @9 GetArg 1; @12 Return
        for op in [And, Or] {
            let mut code = get_arg(0).to_vec();
            code.extend([op_byte(op), 9, 0, 0, 0, op_byte(Pop)]);
            code.extend(get_arg(1));
            code.push(op_byte(Return));
            baseline_compile_and_validate(script(code, 2));
        }
    }

    #[test]
    fn baseline_branches_calls_and_handlers_validate() {
        // `if (1) return 42; return 99;`
        let code = vec![
            op_byte(JSOp::One),
            op_byte(JSOp::JumpIfFalse),
            8,
            0,
            0,
            0,
            op_byte(JSOp::Int8),
            42,
            op_byte(JSOp::Return),
            op_byte(JSOp::Int8),
            99,
            op_byte(JSOp::Return),
        ];
        baseline_compile_and_validate(script(code, 0));

        // try { throw 0 } catch { return exception }
        let code = vec![
            op_byte(JSOp::Try),
            op_byte(JSOp::Zero),
            op_byte(JSOp::Throw),
            op_byte(JSOp::Nop),
            op_byte(JSOp::Exception),
            op_byte(JSOp::Return),
        ];
        let mut s = script(code, 0);
        s.try_notes = vec![crate::bytecode::TryNote {
            kind: crate::bytecode::TryNoteKind::Catch,
            stack_depth: 0,
            start: Pc::new(1),
            length: 3,
        }];
        baseline_compile_and_validate(s);

        // try { throw 0 } finally { ... }: the landing pushes three values.
        let code = vec![
            op_byte(JSOp::Try),
            op_byte(JSOp::Zero),
            op_byte(JSOp::Throw),
            op_byte(JSOp::Nop),
            op_byte(JSOp::PopN),
            3,
            0,
            op_byte(JSOp::RetRval),
        ];
        let mut s = script(code, 0);
        s.try_notes = vec![crate::bytecode::TryNote {
            kind: crate::bytecode::TryNoteKind::Finally,
            stack_depth: 0,
            start: Pc::new(1),
            length: 3,
        }];
        baseline_compile_and_validate(s);

        // A loop calling its argument: `for (;;) { if (!a0()) return; }`
        // @0 LoopHead; @6 GetArg 0; @9 Undefined; @10 Call 0;
        // @13 JumpIfFalse +10 (-> @23); @18 Goto -18 (-> @0); @23 RetRval
        let code = vec![
            op_byte(JSOp::LoopHead),
            0,
            0,
            0,
            0,
            0,
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::Undefined),
            op_byte(JSOp::Call),
            0,
            0,
            op_byte(JSOp::JumpIfFalse),
            10,
            0,
            0,
            0,
            op_byte(JSOp::Goto),
            (-18i32) as u8,
            0xff,
            0xff,
            0xff,
            op_byte(JSOp::RetRval),
        ];
        assert_eq!(JSOp::LoopHead.len(), 6);
        baseline_compile_and_validate(script(code, 1));
    }

    /// Compile `code` and assert the emitted module validates (exercises the
    /// CFG: blocks, terminators, blockparams).
    fn compile_and_validate(code: Vec<u8>, nargs: u16, source_id: u32) {
        let s = script(code, nargs);
        let (mut m, helpers) = module_with_helpers();
        let source = Source {
            objects: vec![],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        let mut atoms = AtomTable::new(Names::default());
        match translate_script(
            &mut m,
            helpers,
            &source,
            &mut atoms,
            source_id,
            &s,
            &Options::default(),
        )
        .expect("translate")
        {
            Outcome::Compiled { sig, body, .. } => {
                if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
                    let ir = format!("{}", body.display("", None));
                    let _ = std::fs::write(std::path::Path::new(&dir).join("test.ir"), ir);
                }
                m.funcs
                    .push(waffle::FuncDecl::Body(sig, "f".to_string(), body));
                let bytes = m.to_wasm_bytes().expect("serialize");
                if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
                    let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
                }
                waffle::wasmparser::validate(&bytes).expect("emitted module validates");
            }
            Outcome::Skipped(reason) => panic!("unexpectedly skipped: {reason}"),
        }
    }

    /// A `new`-site sequence compiles via the generic construct helper:
    /// `GetArg 0` (callee); `IsConstructing` (the magic `this` placeholder);
    /// `DupAt 1` (newTarget = the callee); `New 0`; `Return`. Exercises the
    /// construct frame `[callee, this_placeholder, newTarget]` and `DupAt`.
    #[test]
    fn new_op_compiles_and_validates() {
        let code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::IsConstructing),
            op_byte(JSOp::DupAt),
            1,
            0,
            0,
            op_byte(JSOp::New),
            0,
            0,
            op_byte(JSOp::Return),
        ];
        compile_and_validate(code, 1, 31);
    }

    /// A property inline-cache site (a `GetProp` in production/no-TI mode)
    /// lowers to the inline hit path + `night_runtime_get_prop_ic_miss` with a per-site
    /// cache index, and the module validates. `GetArg 0` (the receiver);
    /// `GetProp "f"`; `Return`.
    #[test]
    fn property_ic_compiles_and_validates() {
        // gcthings[0] = the property-name string "f".
        let source = Source {
            objects: vec![SourceObject::String(JsString::from("f"))],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        let code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::GetProp),
            0,
            0,
            0,
            0,
            op_byte(JSOp::Return),
        ];
        let mut s = script(code, 1);
        s.gcthings = vec![SourceObjectId::new(0)];
        let (mut m, helpers) = module_with_helpers();
        let mut atoms = AtomTable::new(Names::default());
        // The generalized get IC fires at every `GetProp` site, claiming
        // one per-site cache index.
        match translate_script(
            &mut m,
            helpers,
            &source,
            &mut atoms,
            3,
            &s,
            &Options::default(),
        )
        .expect("translate")
        {
            Outcome::Compiled { sig, body, .. } => {
                if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
                    let ir = format!("{}", body.display("", None));
                    let _ = std::fs::write(std::path::Path::new(&dir).join("test.ir"), ir);
                }
                m.funcs
                    .push(waffle::FuncDecl::Body(sig, "f".to_string(), body));
                let bytes = m.to_wasm_bytes().expect("serialize");
                if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
                    let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
                }
                waffle::wasmparser::validate(&bytes).expect("emitted module validates");
                // The IC site claimed cache index 0.
                assert_eq!(atoms.prop_cache_count(), 1);
            }
            Outcome::Skipped(reason) => panic!("unexpectedly skipped: {reason}"),
        }
    }

    /// A compare on operands the analysis did not prove Int32 lowers to the
    /// generic boxed
    /// tag-guarded inline fast path (`call_indirect`-style diamond: runtime
    /// Int32-tag test -> inline i32 compare, else `night_runtime_compare`) and the
    /// module validates. `GetArg 0; GetArg 0; Lt; Return`.
    #[test]
    fn tag_guarded_compare_validates() {
        let code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::Lt),
            op_byte(JSOp::Return),
        ];
        // No pc marked Int32: the operands are untyped -> the tag-guard fires.
        compile_and_validate(code, 1, 51);
    }

    /// Arithmetic on operands the analysis did not prove Int32 lowers to the
    /// generic boxed
    /// tag-guarded inline path (with the folded overflow guard for `Sub`) and
    /// the module validates. `GetArg 0; GetArg 0; Sub; Return`. (Overflow
    /// *behavior* is validated by `test-arith-overflow.js` end to end.)
    #[test]
    fn tag_guarded_arith_validates() {
        let code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::Sub),
            op_byte(JSOp::Return),
        ];
        compile_and_validate(code, 1, 53);
    }

    /// A branch on a non-Int32/Bool condition uses the generic `night_runtime_to_boolean`
    /// helper instead of declining: `GetArg 0` (untyped) `JumpIfFalse`.
    #[test]
    fn generic_to_boolean_branch_validates() {
        // @0 GetArg 0; @3 JumpIfFalse +8 (-> @11); @8 Int8 1; @10 Return;
        // @11 Int8 2; @13 Return.  pc 0 has no proven type -> generic ToBoolean.
        let code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::JumpIfFalse),
            8,
            0,
            0,
            0,
            op_byte(JSOp::Int8),
            1,
            op_byte(JSOp::Return),
            op_byte(JSOp::Int8),
            2,
            op_byte(JSOp::Return),
        ];
        // No pc marked Int32: the arg is untyped, forcing the generic path.
        compile_and_validate(code, 1, 41);
    }

    /// An array literal: `NewArray 2; One; InitElemArray 0; Zero; One;
    /// InitElemInc; Pop; Return` exercises new_array, init_elem (const key),
    /// and InitElemInc (index increment).
    #[test]
    fn array_literal_compiles_and_validates() {
        let code = vec![
            op_byte(JSOp::NewArray),
            2,
            0,
            0,
            0,
            op_byte(JSOp::One), // value for index 0
            op_byte(JSOp::InitElemArray),
            0,
            0,
            0,
            0,
            op_byte(JSOp::Zero), // index for InitElemInc
            op_byte(JSOp::One),  // value
            op_byte(JSOp::InitElemInc),
            op_byte(JSOp::Pop), // drop the incremented index
            op_byte(JSOp::Return),
        ];
        compile_and_validate(code, 0, 42);
    }

    /// A function using aliased-var ops compiles: it reserves an env-head slot,
    /// emits the prologue `env_setup`, and routes `GetAliasedVar`/`SetAliasedVar`
    /// through the env helpers. `GetArg 0; SetAliasedVar 0,2; GetAliasedVar 0,2;
    /// Return` under a Function body scope with an environment.
    #[test]
    fn aliased_var_compiles_and_validates() {
        let code = vec![
            op_byte(JSOp::GetArg),
            0,
            0,
            op_byte(JSOp::SetAliasedVar),
            0,
            0, // hops u16 = 0
            2,
            0,
            0, // slot u24 = 2
            op_byte(JSOp::GetAliasedVar),
            0,
            0,
            2,
            0,
            0,
            op_byte(JSOp::Return),
        ];
        let mut source = Source {
            objects: vec![],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        let scope_id = source.push(SourceObject::Scope(ScopeData {
            kind: 0, // ScopeKind::Function
            has_environment: true,
            enclosing: None,
            bindings: vec![],
            is_named_lambda: false,
            env_nfixed: None,
            env_slot_values: vec![],
        }));
        let mut s = script(code, 1);
        s.body_scope = Some(scope_id);
        let (mut m, helpers) = module_with_helpers();
        let mut atoms = AtomTable::new(Names::default());
        match translate_script(
            &mut m,
            helpers,
            &source,
            &mut atoms,
            50,
            &s,
            &Options::default(),
        )
        .expect("translate")
        {
            Outcome::Compiled { sig, body, .. } => {
                if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
                    let ir = format!("{}", body.display("", None));
                    let _ = std::fs::write(std::path::Path::new(&dir).join("test.ir"), ir);
                }
                m.funcs
                    .push(waffle::FuncDecl::Body(sig, "f".to_string(), body));
                let bytes = m.to_wasm_bytes().expect("serialize");
                if let Some(dir) = std::env::var_os("NIGHT_TEST_DUMP") {
                    let _ = std::fs::write(std::path::Path::new(&dir).join("test.wasm"), &bytes);
                }
                waffle::wasmparser::validate(&bytes).expect("emitted module validates");
            }
            Outcome::Skipped(reason) => panic!("unexpectedly skipped: {reason}"),
        }
    }

    /// A function with aliased vars under a named-lambda environment is declined
    /// (the env model doesn't insert the named-lambda chain link).
    #[test]
    fn named_lambda_env_is_skipped() {
        let code = vec![
            op_byte(JSOp::GetAliasedVar),
            0,
            0,
            2,
            0,
            0,
            op_byte(JSOp::Return),
        ];
        let mut source = Source {
            objects: vec![],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        };
        let nl = source.push(SourceObject::Scope(ScopeData {
            kind: 5, // ScopeKind::NamedLambda
            has_environment: true,
            enclosing: None,
            bindings: vec![],
            is_named_lambda: true,
            env_nfixed: None,
            env_slot_values: vec![],
        }));
        let fscope = source.push(SourceObject::Scope(ScopeData {
            kind: 0,
            has_environment: false,
            enclosing: Some(nl),
            bindings: vec![],
            is_named_lambda: false,
            env_nfixed: None,
            env_slot_values: vec![],
        }));
        let mut s = script(code, 0);
        s.body_scope = Some(fscope);
        let (mut m, helpers) = module_with_helpers();
        let mut atoms = AtomTable::new(Names::default());
        match translate_script(
            &mut m,
            helpers,
            &source,
            &mut atoms,
            51,
            &s,
            &Options::default(),
        )
        .expect("translate")
        {
            Outcome::Skipped(reason) => assert!(reason.contains("named-lambda"), "{reason}"),
            Outcome::Compiled { .. } => panic!("named-lambda env should be declined"),
        }
    }

    /// A try/catch landing pad compiles: `Try; Zero; Throw` inside a Catch
    /// region routes the throw to the handler (`Exception; Return`), which is
    /// reached only via the exception edge. Exercises the exception routing.
    #[test]
    fn catch_landing_pad_compiles_and_validates() {
        let code = vec![
            op_byte(JSOp::Try),       // @0
            op_byte(JSOp::Zero),      // @1 (the value to throw)
            op_byte(JSOp::Throw),     // @2 (in the try region -> handler @4)
            op_byte(JSOp::Nop),       // @3 (padding so handler_pc = 1+3 = 4)
            op_byte(JSOp::Exception), // @4 (catch handler entry)
            op_byte(JSOp::Return),    // @5
        ];
        let mut s = script(code, 0);
        s.try_notes = vec![crate::bytecode::TryNote {
            kind: crate::bytecode::TryNoteKind::Catch,
            stack_depth: 0,
            start: Pc::new(1),
            length: 3,
        }];
        compile_and_validate_script(s, 60);
    }

    /// `if (1) return 42; return 99;` -> a CondBr with two return blocks. The
    /// condition is a truthy Int32 const used directly as the branch test.
    #[test]
    fn if_branch_compiles_and_validates() {
        // @0 One; @1 JumpIfFalse +8 (-> @9); @6 Int8 42; @8 Return;
        // @9 Int8 99; @11 Return
        let code = vec![
            op_byte(JSOp::One),
            op_byte(JSOp::JumpIfFalse),
            8,
            0,
            0,
            0,
            op_byte(JSOp::Int8),
            42,
            op_byte(JSOp::Return),
            op_byte(JSOp::Int8),
            99,
            op_byte(JSOp::Return),
        ];
        compile_and_validate(code, 0, 11);
    }

    /// A value live across an unconditional branch becomes a `Boxed`
    /// blockparam: `One; Goto L; L: Return` returns the carried 1.
    #[test]
    fn blockparam_across_goto_validates() {
        // @0 One; @1 Goto +5 (-> @6); @6 Return  (the [1] is carried to @6)
        let code = vec![
            op_byte(JSOp::One),
            op_byte(JSOp::Goto),
            5,
            0,
            0,
            0,
            op_byte(JSOp::Return),
        ];
        compile_and_validate(code, 0, 12);
    }

    /// A backward branch (a loop) to a non-entry leader: validates that a
    /// back-edge to an already-created block is wired without re-creating
    /// blockparams. (The loop head must not be the entry block, whose params
    /// are the ABI args.)
    #[test]
    fn backward_branch_loop_validates() {
        // @0 Zero; @1 Pop;            (entry, distinct from the loop head)
        // @2 LoopHead;                (loop head, 6 bytes)
        // @8 One; @9 JumpIfFalse -7 (back to @2); @14 Int8 7; @16 Return
        let code = vec![
            op_byte(JSOp::Zero),     // @0
            op_byte(JSOp::Pop),      // @1
            op_byte(JSOp::LoopHead), // @2
            0,
            0,
            0,
            0,
            0,                          // ic_index u32 + depth_hint u8 (@3..@7)
            op_byte(JSOp::One),         // @8
            op_byte(JSOp::JumpIfFalse), // @9
            0xF9,                       // off = -7 => target = 9 - 7 = @2
            0xFF,
            0xFF,
            0xFF,
            op_byte(JSOp::Int8), // @14 (fall-through, truthy)
            7,
            op_byte(JSOp::Return), // @16
        ];
        compile_and_validate(code, 0, 13);
    }
}
