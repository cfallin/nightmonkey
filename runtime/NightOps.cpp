/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80: */

/*
 * Engine-half implementations of the bytecode operations a compiled body
 * cannot do itself: names and global bindings, the unary/relational slow
 * paths, environments and closures, arguments objects, exceptions, and
 * construct. `night_runtime_*` in NightRuntime.cpp is the Wasm ABI shim in
 * front of these; the property-cache and inline-heap halves live in
 * NightInlineCaches.cpp and NightInlineHeap.cpp. The interpreter name
 * operations borrowed from SpiderMonkey live in NightOpsInterp.cpp.
 */

#include "runtime/NightOps.h"
#include "runtime/NightObjectWord.h"
#include "runtime/NightOpsInterp.h"
#include "vm/Opcodes.h"

#include "mozilla/Maybe.h"

#include "jsapi.h"
#include "jsnum.h"

#include "builtin/Eval.h"
#include "builtin/ModuleObject.h"
#include "gc/GC.h"
#include "js/EnvironmentChain.h"      // JS::SupportUnscopables
#include "js/friend/ErrorMessages.h"  // js::GetErrorMessage, JSMSG_*
#include "js/Id.h"                    // jsid / JS::PropertyKey
#include "runtime/NightRegistration.h"
#include "vm/ArgumentsObject.h"
#include "vm/BigIntType.h"
#include "vm/BytecodeUtil.h"  // JSDVG_SEARCH_STACK, JSDVG_IGNORE_STACK
#include "vm/EqualityOperations.h"
#include "vm/GlobalObject.h"
#include "vm/JSContext.h"
#include "vm/JSFunction.h"
#include "vm/JSObject.h"
#include "vm/JSScript.h"
#include "vm/ObjectFuse.h"  // js::ObjectFuse (AOT constant-gname arm)
#include "vm/Opcodes.h"
#include "vm/PlainObject.h"  // js::PlainObject
#include "vm/Scope.h"
#include "vm/Shape.h"
#include "vm/SharedStencil.h"  // GCThingIndex
#include "vm/StringType.h"
#include "vm/Watchtower.h"  // js::Watchtower (AOT global-slot store hook)

#include "vm/ArgumentsObject-inl.h"
#include "vm/EnvironmentObject-inl.h"
#include "vm/Interpreter-inl.h"
#include "vm/JSFunction-inl.h"  // JSFunction::getAllocKindForThis
#include "vm/JSObject-inl.h"    // js::NewObjectGCKind
#include "vm/JSScript-inl.h"
#include "vm/NativeObject-inl.h"
#include "vm/ObjectOperations-inl.h"
#include "vm/PlainObject-inl.h"  // js::CreateThis
#include "vm/Stack-inl.h"

#ifdef ENABLE_JS_NIGHTMONKEY

using namespace js;

namespace js {
namespace night {

// Global-name read for AOT codegen's `GetGName` (the `night_runtime_get_gname`
// helper forwards here). Resolves exactly as the interpreter's CASE(GetGName):
// against the global lexical environment chain (handles var, function, let,
// const). Takes the pre-interned name (gAtomIds) so no per-call atomization.
// Non-static so NightRuntime.cpp can call it.
bool NightGetGName(JSContext* cx, JS::Handle<JS::PropertyKey> id,
                   bool forTypeof, JS::MutableHandleValue out) {
  MOZ_ASSERT(id.isAtom());
  Rooted<PropertyName*> name(cx, id.toAtom()->asPropertyName());
  Rooted<JSObject*> env(cx, &cx->global()->lexicalEnvironment());
  MOZ_ASSERT(!cx->global()->hasNonSyntacticScope());
  // A `GetGName` feeding a `typeof` must not throw for an undeclared name (it
  // yields "undefined"): use the same TypeOf-mode lookup the interpreter
  // selects via `IsTypeOfNameOp(nextOp)`. The `nextOp` sentinel only needs to
  // satisfy that predicate (Typeof) or not (GetGName).
  JSOp nextOp = forTypeof ? JSOp::Typeof : JSOp::GetGName;
  return NightGetNameOperation(cx, env, name, nextOp, out);
}

// Resolve a global binding name to its encoded `gGlobalSlots` entry. The
// binding is a `function`/`var` global (the codegen view only resolves those)
// -- an own data property of the global object, instantiated before any access
// by GlobalOrEvalDeclInstantiation -- so a non-allocating `lookupPure` always
// succeeds. Encoding (v2): `bit0` resolved, `bit1` is-dynamic-slot, `bit2`
// writable (the inline WRITE arm requires it; the read arm ignores it),
// `bits[31:3]` the slot index (fixed slot index, or the dynamic index
// `slot - numFixedSlots`).
uint32_t NightResolveGlobalSlot(JSContext* cx, JS::PropertyKey id) {
  GlobalObject* global = cx->global();
  mozilla::Maybe<PropertyInfo> prop = global->lookupPure(id);
  MOZ_RELEASE_ASSERT(prop.isSome() && prop->isDataProperty(),
                     "AOT global binding is not an own data property");
  uint32_t slot = prop->slot();
  uint32_t nfixed = global->numFixedSlots();
  uint32_t isDynamic = (slot >= nfixed) ? 1u : 0u;
  uint32_t idx = isDynamic ? (slot - nfixed) : slot;
  uint32_t writable = prop->writable() ? 1u : 0u;
  return 1u | (isDynamic << 1) | (writable << 2) | (idx << 3);
}

// The guarded variant for syntactically-collected (no-TI) bindings: `id` is an
// arbitrary `GetGName` operand, so failure is normal. Cacheable iff the name is
// an own plain data slot of the global OBJECT and is not shadowed by a global
// LEXICAL binding (`GetNameOperation` consults the lexical environment first;
// for the single analyzed script all lexicals are instantiated before any
// bytecode read runs, so shadowing is decided once, here). `*shapeOut` gets the
// global's shape word: the inline read guards it, so any later reshape
// (delete / redefine-as-accessor / property add) misses and re-resolves. TDZ,
// typeof-of-undeclared, and everything unresolved stay on the generic path.
uint32_t NightResolveGlobalSlotGuarded(JSContext* cx, JS::PropertyKey id,
                                       uint32_t* shapeOut) {
  *shapeOut = 0;
  GlobalObject* global = cx->global();
  if (global->lexicalEnvironment().lookupPure(id).isSome()) {
    return 0;
  }
  mozilla::Maybe<PropertyInfo> prop = global->lookupPure(id);
  if (prop.isNothing() || !prop->isDataProperty() || !prop->hasSlot()) {
    return 0;
  }
  uint32_t slot = prop->slot();
  uint32_t nfixed = global->numFixedSlots();
  uint32_t isDynamic = (slot >= nfixed) ? 1u : 0u;
  uint32_t idx = isDynamic ? (slot - nfixed) : slot;
  uint32_t writable = prop->writable() ? 1u : 0u;
  *shapeOut = uint32_t(reinterpret_cast<uintptr_t>(global->shape()));
  return 1u | (isDynamic << 1) | (writable << 2) | (idx << 3);
}

// Unary `-x` slow path: NegOperation (ToNumeric + negate), exactly CASE(Neg).
bool NightNeg(JSContext* cx, uint64_t aBits, uint64_t* out) {
  RootedValue v(cx, JS::Value::fromRawBits(aBits));
  if (!NegOperation(cx, &v, &v)) {
    return false;
  }
  *out = v.get().asRawBits();
  return true;
}

// `Inc`/`Dec` slow paths, exactly CASE(Inc)/CASE(Dec): the post-ToNumeric
// operand is a number or a BigInt.
bool NightInc(JSContext* cx, uint64_t aBits, uint64_t* out) {
  RootedValue v(cx, JS::Value::fromRawBits(aBits));
  RootedValue res(cx);
  if (!IncOperation(cx, v, &res)) {
    return false;
  }
  *out = res.get().asRawBits();
  return true;
}

bool NightDec(JSContext* cx, uint64_t aBits, uint64_t* out) {
  RootedValue v(cx, JS::Value::fromRawBits(aBits));
  RootedValue res(cx);
  if (!DecOperation(cx, v, &res)) {
    return false;
  }
  *out = res.get().asRawBits();
  return true;
}

// `l instanceof r`, exactly CASE(Instanceof): a primitive rhs throws
// JSMSG_BAD_INSTANCEOF_RHS; else the full InstanceofOperator (proto walk /
// Symbol.hasInstance). Boxed boolean to *out.
bool NightInstanceof(JSContext* cx, uint64_t lBits, uint64_t rBits,
                     uint64_t* out) {
  RootedValue rref(cx, JS::Value::fromRawBits(rBits));
  if (rref.isPrimitive()) {
    ReportValueError(cx, JSMSG_BAD_INSTANCEOF_RHS, -1, rref, nullptr);
    return false;
  }
  RootedObject obj(cx, &rref.toObject());
  RootedValue lval(cx, JS::Value::fromRawBits(lBits));
  bool cond = false;
  if (!InstanceofOperator(cx, obj, lval, &cond)) {
    return false;
  }
  *out = JS::BooleanValue(cond).asRawBits();
  return true;
}

// `delete val.name`, exactly CASE(DelProp)/CASE(StrictDelProp) by flag.
bool NightDelProp(JSContext* cx, uint64_t valBits, JS::PropertyKey id,
                  bool strict, uint64_t* out) {
  RootedValue val(cx, JS::Value::fromRawBits(valBits));
  Rooted<PropertyName*> name(cx, id.toAtom()->asPropertyName());
  bool res = false;
  bool ok = strict ? DelPropOperation<true>(cx, val, name, &res)
                   : DelPropOperation<false>(cx, val, name, &res);
  if (!ok) {
    return false;
  }
  *out = JS::BooleanValue(res).asRawBits();
  return true;
}

// The address of OptimizeStringCharOpsFuse's guard word in the current realm
// (0 == intact; Watchtower pops it on any mutation of String.prototype's
// charCodeAt/charAt or String.fromCharCode). The compiled module's inline
// string-method arms guard on it.
size_t* NightStringCharOpsFuseWord(JSContext* cx) {
  return cx->realm()->realmFuses.optimizeStringCharOpsFuse.fuseRef();
}

size_t* NightEmulatesUndefinedFuseWord(JSContext* cx) {
  return cx->runtime()
      ->runtimeFuses.ref()
      .hasSeenObjectEmulateUndefinedFuse.fuseRef();
}

// Read global binding `id`'s current value for the per-binding fuse cell:
// the compiled read/call arms serve the cached bits while the cell's fuse
// word is 1, and every compiled global write path blows the word on a value
// change (NightRuntime.cpp hooks). Fails (cell stays cold) for non-data
// bindings and NURSERY values (the linmem cache is not a GC root; tenured
// values only move under a compacting major GC, which zeroes the cache region).
bool NightTryBindingValue(JSContext* cx, JS::PropertyKey id, uint64_t* valOut,
                          bool* nurseryOut) {
  GlobalObject* global = cx->global();
  mozilla::Maybe<PropertyInfo> prop = global->lookupPure(id);
  if (prop.isNothing() || !prop->isDataProperty() || !prop->hasSlot()) {
    return false;
  }
  const Value& v = global->getSlot(prop->slot());
  if (v.isGCThing() && gc::IsInsideNursery(v.toGCThing())) {
    // A caller that can re-write the cell when the nursery moves the
    // value takes the bits and the flag; every other caller is refused.
    if (!nurseryOut) {
      return false;
    }
    *nurseryOut = true;
  }
  *valOut = v.asRawBits();
  return true;
}

bool NightArguments(JSContext* cx, uint64_t calleeBits, const JS::Value* args,
                    uint32_t argc, uint64_t* out) {
  RootedFunction callee(
      cx, &JS::Value::fromRawBits(calleeBits).toObject().as<JSFunction>());
  RootedObject scopeChain(cx, callee->environment());
  ArgumentsObject* obj = ArgumentsObject::createFromValueArray(
      cx, HandleValueArray::fromMarkedLocation(argc, args), callee, scopeChain,
      argc);
  if (!obj) {
    return false;
  }
  *out = JS::ObjectValue(*obj).asRawBits();
  return true;
}

// Like NightArguments but uses the activation's environment head `envBits` as
// the scope chain. When the callee `needsCallObject()` and its args object
// aliases formals, `createFromValueArray` (via `MaybeForwardToCallObject`)
// stores the CallObject in the args object and replaces each closed-over
// formal's element with a JS_FORWARD-to-call-object magic, so `arguments[i]`
// and the aliased binding stay the same slot. `envBits` is this activation's
// CallObject in that case (built by the environment prologue); when the callee
// has no CallObject the forwarding gate is false and the scope chain is inert.
bool NightArgumentsEnv(JSContext* cx, uint64_t calleeBits,
                       const JS::Value* args, uint32_t argc, uint64_t envBits,
                       uint64_t* out) {
  RootedFunction callee(
      cx, &JS::Value::fromRawBits(calleeBits).toObject().as<JSFunction>());
  RootedObject scopeChain(cx, &JS::Value::fromRawBits(envBits).toObject());
  ArgumentsObject* obj = ArgumentsObject::createFromValueArray(
      cx, HandleValueArray::fromMarkedLocation(argc, args), callee, scopeChain,
      argc);
  if (!obj) {
    return false;
  }
  *out = JS::ObjectValue(*obj).asRawBits();
  return true;
}

// Store `valBits` into a resolved global-object binding's slot via
// `NativeObject::setSlot`, which runs the incremental/generational write
// barriers. Leaf (the store + barriers never move objects).
void NightSetGlobalSlot(JSContext* cx, JS::PropertyKey id, uint64_t valBits) {
  GlobalObject* global = cx->global();
  mozilla::Maybe<PropertyInfo> prop = global->lookupPure(id);
  MOZ_RELEASE_ASSERT(prop.isSome() && prop->isDataProperty(),
                     "AOT global binding is not an own data property");
  // The raw setSlot below bypasses SetExistingProperty, so run the
  // Watchtower value-change hook here -- the global's ObjectFuse (constant
  // gname arm) depends on seeing every write. NoGC variant: this is a leaf.
  Value v = JS::Value::fromRawBits(valBits);
  Watchtower::watchPropertyValueChange<NoGC>(cx, global, id, v, *prop);
  global->setSlot(prop->slot(), v);
}

// `BindUnqualifiedGName`: resolve the binding object for an unqualified
// assignment to a global name (the global object, for an undeclared name).
// Mirrors the interpreter's CASE(BindUnqualifiedGName) (looks up against the
// global lexical environment). May GC/throw; writes the boxed env object to
// out.
bool NightBindUnqualifiedGName(JSContext* cx, JS::Handle<JS::PropertyKey> id,
                               JS::MutableHandleValue out) {
  MOZ_ASSERT(id.isAtom());
  Rooted<PropertyName*> name(cx, id.toAtom()->asPropertyName());
  Rooted<JSObject*> envChain(cx, &cx->global()->lexicalEnvironment());
  MOZ_ASSERT(!cx->global()->hasNonSyntacticScope());
  JSObject* env = LookupNameUnqualified(cx, name, envChain);
  if (!env) {
    return false;
  }
  out.setObject(*env);
  return true;
}

// `SetGName`/`SetName` (and strict forms): assign `valBits` to `name` on the
// binding object `envBits` produced by a preceding `Bind*`. The assignment is
// NightSetNameOperation, the body of js::SetNameOperation (which we cannot
// call directly: it derives name + strictness from script/pc, which an AOT
// body lacks). May GC/throw.
bool NightSetName(JSContext* cx, JS::Handle<JS::PropertyKey> id,
                  uint64_t envBits, uint64_t valBits, bool strict) {
  MOZ_ASSERT(id.isAtom());
  Rooted<JSObject*> env(cx, &JS::Value::fromRawBits(envBits).toObject());
  RootedValue val(cx, JS::Value::fromRawBits(valBits));
  // Strict unqualified assignment to a nonexistent binding is a
  // ReferenceError. The engine's check (MaybeReportUndeclaredVarAssignment
  // under SetNonexistentProperty) decides strictness by pc-sniffing the
  // interpreter frame, which an AOT activation does not have, so it would
  // silently DEFINE the global; enforce it here where `strict` is in hand.
  if (strict && env->isUnqualifiedVarObj()) {
    bool found;
    if (!HasProperty(cx, env, id, &found)) {
      return false;
    }
    if (!found) {
      UniqueChars bytes =
          IdToPrintableUTF8(cx, id, IdToPrintableBehavior::IdIsIdentifier);
      if (!bytes) {
        return false;
      }
      JS_ReportErrorNumberUTF8(cx, GetErrorMessage, nullptr,
                               JSMSG_UNDECLARED_VAR, bytes.get());
      return false;
    }
  }
  return NightSetNameOperation(cx, env, id, val, strict);
}

// --- closure support ---------------------------------------------------
// The AOT body's ABI carries a trailing `JSScript*` param so these helpers
// can resolve function-template gcthings and build the environment. The body
// keeps the "environment head" (this function's CallObject, or
// `callee->environment()` when it needs none) in a rooted frame slot; the
// helpers below walk/clone from it. Defined here (reactor-only) where the
// engine internals are visible; the `night_runtime_*` exports in
// NightRuntime.cpp forward to them.

// Environment prologue: build the environment head for the function whose
// compiled-body frame is at
// `spPtr` (callee at frame[0]). When the callee needs a CallObject, allocate
// one over `callee->environment()` (aliased formals are copied in by the body's
// GetFrameArg/SetAliasedVar bytecode, as the interpreter prologue relies on);
// otherwise the head is `callee->environment()` itself. Writes it boxed to
// *out.
bool NightEnvSetup(JSContext* cx, void* spPtr, void* scriptPtr, uint64_t* out) {
  // A global (top-level) script's environment head is the global lexical
  // environment -- it already exists at runtime (nothing is allocated), and is
  // exactly the env `NightGetGName`/`NightBindUnqualifiedGName` use. Top-level
  // `Lambda`s capture it (spec 2b). The frame has no callee for a global
  // script.
  JSScript* script = reinterpret_cast<JSScript*>(scriptPtr);
  if (script->isGlobalCode()) {
    MOZ_RELEASE_ASSERT(!script->hasNonSyntacticScope());
    *out = ObjectValue(cx->global()->lexicalEnvironment()).asRawBits();
    return true;
  }
  JS::Value* frame = reinterpret_cast<JS::Value*>(spPtr);
  RootedFunction callee(cx, &frame[0].toObject().as<JSFunction>());
  RootedObject enclosing(cx, callee->environment());
  // A named lambda that captures its own name gets that binding's
  // environment first, as js::InitFunctionEnvironmentObjects does. (BBV
  // gates such functions out at compile time, translate.rs
  // `env_unsupported`; the baseline tier compiles them.)
  if (callee->needsNamedLambdaEnvironment()) {
    NamedLambdaObject* declEnv = NamedLambdaObject::createWithoutEnclosing(
        cx, callee, gc::Heap::Default);
    if (!declEnv) {
      return false;
    }
    declEnv->initEnclosingEnvironment(enclosing);
    enclosing = declEnv;
  }
  if (callee->needsCallObject()) {
    RootedScript script(cx, callee->nonLazyScript());
    // createTemplateObject builds the CallObject with the FunctionScope's
    // environment shape (bindings undefined); the callee slot and the aliased
    // formals are filled below / by the body's bytecode, as createForFrame and
    // the interpreter prologue do.
    CallObject* callobj =
        CallObject::createTemplateObject(cx, script, enclosing);
    if (!callobj) {
      return false;
    }
    callobj->initFixedSlot(CallObject::calleeSlot(), ObjectValue(*callee));
    *out = ObjectValue(*callobj).asRawBits();
  } else {
    *out = ObjectValue(*enclosing).asRawBits();
  }
  return true;
}

// `GlobalOrEvalDeclInstantiation` (pc 0 of a global script): instantiate the
// hoisted global `function`/`var` declarations onto the global. The env for a
// global script is the global lexical environment (= the interpreter's
// `REGS.fp()->environmentChain()` for a global frame). May GC/throw.
bool NightGlobalDeclInstantiation(JSContext* cx, void* scriptPtr,
                                  uint32_t gcthingIndex) {
  RootedScript script(cx, reinterpret_cast<JSScript*>(scriptPtr));
  RootedObject env(cx, &cx->global()->lexicalEnvironment());
  MOZ_RELEASE_ASSERT(!script->hasNonSyntacticScope());
  return GlobalOrEvalDeclInstantiation(cx, env, script,
                                       GCThingIndex(gcthingIndex));
}

// `Object`: push the precompiled (run-once) object `script->getObject(idx)`.
// Leaf: a load of an already-rooted GC pointer from the script (no GC/throw).
uint64_t NightObject(JSContext* cx, void* scriptPtr, uint32_t gcthingIndex) {
  (void)cx;
  JSScript* script = reinterpret_cast<JSScript*>(scriptPtr);
  return ObjectValue(*script->getObject(GCThingIndex(gcthingIndex)))
      .asRawBits();
}

// Walk `hops` enclosing links from the boxed environment `envBits`.
static EnvironmentObject& NightWalkEnv(uint64_t envBits, uint32_t hops) {
  JSObject* env = &JS::Value::fromRawBits(envBits).toObject();
  for (uint32_t i = 0; i < hops; i++) {
    env = &env->as<EnvironmentObject>().enclosingEnvironment();
  }
  return env->as<EnvironmentObject>();
}

// `typeof val`: the type string. `TypeOfOperation` returns a runtime-pinned
// common atom, so this is a leaf (no GC, no throw).
uint64_t NightTypeof(JSContext* cx, uint64_t valBits) {
  JSString* str =
      TypeOfOperation(JS::Value::fromRawBits(valBits), cx->runtime());
  return JS::StringValue(str).asRawBits();
}

// `GetAliasedVar`: read environment slot `slot` after walking `hops`. Leaf (no
// GC/throw); returns the boxed value.
uint64_t NightGetAliased(JSContext* cx, uint64_t envBits, uint32_t hops,
                         uint32_t slot) {
  (void)cx;
  return NightWalkEnv(envBits, hops).getSlot(slot).asRawBits();
}

// `SetAliasedVar`: write environment slot `slot` after walking `hops`. Leaf.
void NightSetAliased(JSContext* cx, uint64_t envBits, uint32_t hops,
                     uint32_t slot, uint64_t valBits) {
  (void)cx;
  EnvironmentObject& env = NightWalkEnv(envBits, hops);
  EnvironmentCoordinate ec;
  ec.setHops(hops);
  ec.setSlot(slot);
  env.setAliasedBinding(ec, JS::Value::fromRawBits(valBits));
}

// `Lambda`: clone the function template `script->getFunction(funcIndex)`,
// capturing the environment head `envBits`. May GC; writes the closure to *out.
bool NightLambda(JSContext* cx, uint64_t envBits, void* scriptPtr,
                 uint32_t funcIndex, uint64_t* out) {
  RootedObject env(cx, &JS::Value::fromRawBits(envBits).toObject());
  JSScript* script = reinterpret_cast<JSScript*>(scriptPtr);
  RootedFunction fun(cx, script->getFunction(GCThingIndex(funcIndex)));
  JSObject* obj = Lambda(cx, fun, env);
  if (!obj) {
    return false;
  }
  *out = ObjectValue(*obj).asRawBits();
  return true;
}

// Call-site specialization: classify a runtime call target. If
// `calleeBits` is an interpreted JSFunction with a compiled AOT body, return
// `(JSScript* << 32) | nightFuncIndex` (with a non-zero low half); otherwise
// return 0 so the caller falls back to the generic `night_runtime_call` path.
// Leaf: a few flag/field loads, no GC, no allocation, no user code. The packed
// result avoids a memory round-trip: the low 32 bits are the funcref table
// index (the `call_indirect` operand), the high 32 bits are the callee's
// `JSScript*` (the compiled-body ABI's 5th argument). Pointers are 32-bit on
// wasm32, so both halves fit.
uint64_t NightCalleeNightTarget(uint64_t calleeBits) {
  static_assert(sizeof(void*) == 4,
                "the packed (JSScript* << 32) | funcIndex result truncates a "
                "pointer unless pointers are 32-bit (wasm32)");
  JS::Value v = JS::Value::fromRawBits(calleeBits);
  if (!v.isObject()) {
    return 0;
  }
  JSObject* obj = &v.toObject();
  if (!obj->is<JSFunction>()) {
    return 0;
  }
  JSFunction* fun = &obj->as<JSFunction>();
  if (!fun->isInterpreted() || !fun->hasBaseScript() || !fun->hasBytecode()) {
    return 0;
  }
  // A class constructor has no [[Call]]: a CALL-site dispatch of its body
  // would run it instead of throwing. Generic path (which throws).
  if (fun->isClassConstructor()) {
    return 0;
  }
  JSScript* script = fun->nonLazyScript();
  uint32_t index = script->externalTierWord();
  if (index == 0) {
    return 0;
  }
  return (uint64_t(uint32_t(reinterpret_cast<uintptr_t>(script))) << 32) |
         uint64_t(index);
}

// `Exception` op: get and clear the pending exception, boxed into *out.
// May fail (e.g. an interrupt), in which case the error propagates. No
// PENDING exception at a catch entry means the error is uncatchable
// (termination): fail so the handler chain unwinds instead of catching.
bool NightException(JSContext* cx, uint64_t* out) {
  if (!cx->isExceptionPending()) {
    return false;
  }
  RootedValue res(cx);
  if (!GetAndClearException(cx, &res)) {
    return false;
  }
  *out = res.get().asRawBits();
  return true;
}

// `Throw` op: set the value as the pending exception (capturing a stack,
// as the interpreter's CASE(Throw) does via ThrowOperation).
void NightThrow(JSContext* cx, uint64_t valBits) {
  RootedValue v(cx, JS::Value::fromRawBits(valBits));
  // ThrowOperation always returns false; the exception is now pending.
  (void)ThrowOperation(cx, v);
}

// `ThrowWithStack` op: re-raise `val` with the saved exception `stack`
// (a finally's re-throw), as the interpreter's CASE(ThrowWithStack).
void NightThrowWithStack(JSContext* cx, uint64_t valBits, uint64_t stackBits) {
  RootedValue v(cx, JS::Value::fromRawBits(valBits));
  RootedValue stack(cx, JS::Value::fromRawBits(stackBits));
  (void)ThrowWithStackOperation(cx, v, stack);
}

// A finally's exceptional entry: read the pending exception value + stack
// and clear it, so the body can push the `[exc, excStack, true]` triple.
// Returns false when NO exception is pending -- an uncatchable error
// (termination), which must skip the finally body and keep unwinding.
bool NightGetExceptionForFinally(JSContext* cx, uint64_t* excOut,
                                 uint64_t* stackOut) {
  if (!cx->isExceptionPending()) {
    return false;
  }
  RootedValue exc(cx);
  RootedValue stack(cx);
  if (!cx->getPendingException(&exc)) {
    exc.setUndefined();
  }
  if (!cx->getPendingExceptionStack(&stack)) {
    stack.setNull();
  }
  cx->clearPendingException();
  *excOut = exc.get().asRawBits();
  *stackOut = stack.get().asRawBits();
  return true;
}

// Allocation sizing for a specialized `new`: an EMPTY plain object
// on `proto` whose alloc kind reserves a fixed slot for every predicted field
// -- the max of the engine's own ctor-body property-count estimate and the
// analysis's full layout row length `n` (delegate-assigned fields included),
// so the prediction only ever GROWS the allocation. No properties are defined
// here; the ctor's stores create them in creation order, all landing in fixed
// slots. May GC (allocates; can create the callee's script).
static JSObject* AllocNSlots(JSContext* cx, HandleFunction callee, uint32_t n,
                             HandleObject proto) {
  MOZ_RELEASE_ASSERT(n <= 16);
  gc::AllocKind kind = NewObjectGCKind();
  if (!JSFunction::getAllocKindForThis(cx, callee, kind)) {
    return nullptr;
  }
  kind = gc::GetGCObjectKind(
      std::max(size_t(gc::GetGCKindSlots(kind)), size_t(n)));
  // A null proto from GetPrototypeFromConstructor means "the realm default"
  // (the ctor's `.prototype` is a non-object), NOT a null-proto object --
  // exactly ThisShapeForFunction's else-branch.
  RootedObject p(cx, proto);
  if (!p) {
    p = &cx->global()->getObjectPrototype();
  }
  return NewPlainObjectWithProtoAndAllocKind(cx, p, kind);
}

// `night_runtime_construct`'s engine half: the compiled `new C()`.
// The frame at `spPtr` is `[callee, this_placeholder, arg0.., newTarget]`.
// `nSlots` is the construct site's predicted fixed-slot count (the resolved
// ctor's full layout row length), or `NO_NSLOTS` for an ordinary `new`. There
// is no global state and no CreateThis hook: a sized site creates an empty
// `this` with enough fixed slots and runs the constructor on it via
// `InternalConstructWithProvidedThis` (the same entry the JITs use when they
// create `this` caller-side); the ordinary case lets `js::Construct` create
// `this` itself. Writes the boxed result to `*out`.
static constexpr uint32_t NIGHT_NO_NSLOTS = UINT32_MAX;

bool NightConstruct(JSContext* cx, void* spPtr, uint32_t argc, uint32_t nSlots,
                    uint32_t stampWord, uint64_t* out) {
  JS::Value* frame = reinterpret_cast<JS::Value*>(spPtr);
  RootedValue callee(cx, frame[0]);
  RootedValue newTargetVal(cx, frame[2 + argc]);
  // ConstructFromStack's precondition check: js::Construct and
  // InternalConstructWithProvidedThis require a constructor callee (a
  // non-constructor here, e.g. `class X extends null` whose super is
  // Function.prototype, is undefined behavior past this point).
  if (!IsConstructor(callee)) {
    ReportValueError(cx, JSMSG_NOT_CONSTRUCTOR, JSDVG_SEARCH_STACK, callee,
                     nullptr);
    return false;
  }
  if (!newTargetVal.isObject()) {
    JS_ReportErrorASCII(cx,
                        "night_runtime_construct: new.target is not an object");
    return false;
  }
  ConstructArgs args(cx);
  if (!args.init(cx, argc)) {
    return false;
  }
  for (uint32_t i = 0; i < argc; i++) {
    args[i].set(frame[2 + i]);
  }

  RootedValue rval(cx);
  // Provided-this is only legal for a SCRIPTED non-derived constructor: a
  // derived ctor must start with the uninitialized-this magic (super()
  // creates `this`), and a native/bound/proxy constructor creates its own
  // object (InternalConstruct requires the IS_CONSTRUCTING magic there).
  // The nSlots prediction resolves the callee statically, but this generic
  // helper can see ANY runtime callee -- everything else falls to the
  // ordinary js::Construct path below.
  bool provideThis =
      nSlots != NIGHT_NO_NSLOTS && callee.isObject() &&
      callee.toObject().is<JSFunction>() &&
      !callee.toObject().as<JSFunction>().isNativeFun() &&
      !callee.toObject().as<JSFunction>().constructorNeedsUninitializedThis();
  if (provideThis) {
    // Sized allocation: synthesize an empty `this` with enough fixed slots
    // (proto from newTarget) and construct on it -- no CreateThis hook.
    RootedFunction fun(cx, &callee.toObject().as<JSFunction>());
    RootedObject newTarget(cx, &newTargetVal.toObject());
    RootedObject proto(cx);
    if (!GetPrototypeFromConstructor(cx, newTarget, JSProto_Object, &proto)) {
      return false;
    }
    RootedObject thisObj(cx, AllocNSlots(cx, fun, nSlots, proto));
    if (!thisObj) {
      return false;
    }
    // Fresh pre-construction object: seed the site's alloc word (sentinel
    // + validity bits + early key when the compiled site resolved one) --
    // the generic-path population needs the key so its adds are checkable
    // and SLOTS can survive to the stamp. A mispredicted runtime callee is
    // harmless: the ctor-exit stamp's ownership gate declines a foreign
    // key, and the add checks only ever CLEAR the bit.
    if (stampWord != 0) {
      js::night::NightSetClassWord(thisObj, stampWord, js::night::NightBumpSite::ConstructStamp);
    } else {
      js::night::NightSetConstructingSentinel(thisObj);
    }
    RootedValue thisv(cx, ObjectValue(*thisObj));
    if (!InternalConstructWithProvidedThis(cx, callee, thisv, args,
                                           newTargetVal, &rval)) {
      return false;
    }
  } else {
    RootedObject obj(cx);
    if (!js::Construct(cx, callee, args, newTargetVal, &obj)) {
      return false;
    }
    rval.setObject(*obj);
  }
  *out = rval.get().asRawBits();
  return true;
}

// Direct construct: create the `this` object for a specialized `new` whose
// callee is a single resolved scripted constructor (direct-called inline). A
// sized site (`nSlots != NIGHT_NO_NSLOTS`) gets an empty object with enough
// fixed slots for the predicted layout (see `AllocNSlots`); else the ordinary
// `CreateThis(callee, newTarget)` the interpreter/JITs build. Only
// base constructors compile (derived use `SuperCall`, unsupported), so
// `CreateThis` yields a real object, never the derived-class uninitialized-this
// magic.
bool NightCreateThis(JSContext* cx, uint64_t calleeBits, uint64_t newTargetBits,
                     uint32_t nSlots, uint64_t* out, uint32_t stampWord) {
  RootedValue ntv(cx, JS::Value::fromRawBits(newTargetBits));
  if (!ntv.isObject()) {
    JS_ReportErrorASCII(
        cx, "night_runtime_create_this: new.target is not an object");
    return false;
  }
  RootedObject newTarget(cx, &ntv.toObject());
  RootedValue cv(cx, JS::Value::fromRawBits(calleeBits));
  RootedFunction callee(cx, &cv.toObject().as<JSFunction>());
  // A derived-class constructor starts with the uninitialized-this magic
  // (super() creates `this`), so the static-layout path below (which
  // pre-creates an object) must not apply.
  bool derived = callee->constructorNeedsUninitializedThis();
  if (nSlots != NIGHT_NO_NSLOTS && !derived) {
    RootedObject proto(cx);
    if (!GetPrototypeFromConstructor(cx, newTarget, JSProto_Object, &proto)) {
      return false;
    }
    RootedObject thisObj(cx, AllocNSlots(cx, callee, nSlots, proto));
    if (!thisObj) {
      return false;
    }
    js::night::NightSetClassWord(thisObj, stampWord, js::night::NightBumpSite::ConstructStamp);
    *out = ObjectValue(*thisObj).asRawBits();
    return true;
  }
  RootedValue thisv(cx);
  if (!CreateThis(cx, callee, newTarget, GenericObject, &thisv)) {
    return false;
  }
  // Derived ctors get the uninitialized-this magic; everything else a fresh
  // object (stamped with the site's class word).
  MOZ_RELEASE_ASSERT(
      thisv.isObject() || (derived && thisv.isMagic(JS_UNINITIALIZED_LEXICAL)),
      "AOT direct construct: unexpected CreateThis result");
  if (thisv.isObject()) {
    js::night::NightSetClassWord(&thisv.toObject(), stampWord, js::night::NightBumpSite::ConstructStamp);
  }
  *out = thisv.get().asRawBits();
  return true;
}

}  // namespace night
}  // namespace js

#endif  // ENABLE_JS_NIGHTMONKEY
