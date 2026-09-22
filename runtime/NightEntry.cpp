/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

/*
 * Entering AOT-compiled (wasm) function bodies from the engine: the
 * interpreter's dispatch hooks, the apply/call forwarding fast path, and the
 * generator resume hook. Everything here builds a compiled-body frame on the
 * AOT value stack and calls through the funcref table; the helpers compiled
 * code calls on the way back out live in the other night/runtime files.
 */

#include "runtime/NightEntry.h"

#include "js/friend/StackLimits.h"            // js::ReportOverRecursed
#include "runtime/NightRegistration.h"  // js::night::gNightActivated
#include "runtime/NightStack.h"         // js::nightrt::AutoNightReentry
#include "vm/ArgumentsObject.h"
#include "vm/ArrayObject.h"
#include "vm/GeneratorObject.h"
#include "vm/GlobalObject.h"
#include "vm/JSContext.h"
#include "vm/JSFunction.h"
#include "vm/JSObject.h"
#include "vm/JSScript.h"

#include "vm/ArgumentsObject-inl.h"    // js::ArgumentsObject::element
#include "vm/EnvironmentObject-inl.h"  // lexicalEnvironment().thisObject()
#include "vm/JSScript-inl.h"
#include "vm/NativeObject-inl.h"  // js::ArrayObject::getDenseElement
#include "vm/Stack-inl.h"

#ifdef ENABLE_JS_NIGHTMONKEY

using namespace js;

namespace js {
namespace night {

// The JS-to-JS compiled-body Wasm ABI as a C function pointer. LLVM lowers a C
// function pointer to an i32 index into __indirect_function_table, so calling
// through
// `(NightFn)(uintptr_t)index` lowers to a call_indirect of this exact
// signature. See docs/DESIGN.md section 8.3.
using NightFn = int32_t (*)(JSContext* cx, void* sp, uint32_t argc,
                            uint64_t* retvalOut, void* script,
                            uint64_t newTarget);

// Build `script`'s incoming compiled-body frame on the AOT value stack and
// dispatch to its AOT body, writing the boxed result into *rvalOut on success.
// Returns NotEntered when the script has no AOT body, so the caller falls
// through to the interpreter; a frame that would overflow the AOT stack is
// over-recursion (Error).
static EnterNightStatus EnterNight(JSContext* cx, JSScript* script,
                                   const CallArgs& args, bool constructing,
                                   Value* rvalOut) {
  uint32_t index = script->externalTierWord();
  if (index == 0) {
    return EnterNightStatus::NotEntered;
  }
  if (!js::night::gNightActivated) {
    return EnterNightStatus::NotEntered;
  }

  // frameBase() is the sp to build at; the saved top is restored when this
  // re-entry returns (NightStack.h re-entrancy contract).
  js::nightrt::AutoNightReentry reentry(cx);
  js::nightrt::NightStack& stack = js::nightrt::TheNightStack();
  JS::Value* sp = reentry.frameBase();

  uint32_t argc = args.length();
  // The compiled body reads its formals positionally (GetArg i -> sp+16+8i) for
  // all `nargs` declared formals, so the frame must provide a slot for every
  // formal -- missing actuals (a call with fewer args than formals) are padded
  // with `undefined`, exactly as the interpreter frame does. Frame layout:
  // [callee, this, formal0..formal(N-1)] where N = max(argc, nargs).
  uint32_t nformals = script->function() ? script->function()->nargs() : 0;
  uint32_t nslots = argc > nformals ? argc : nformals;
  JS::Value* frameTop = sp + 2 + nslots;
  if (frameTop + js::nightrt::kNightStackHeadroomSlots > stack.limit()) {
    // The AOT stack is the tier's recursion budget: exhausting it is
    // over-recursion, not a reason to continue on the interpreter's stack.
    ReportOverRecursed(cx);
    return EnterNightStatus::Error;
  }

  sp[0] = args.calleev();
  sp[1] = args.thisv();
  for (uint32_t i = 0; i < argc; i++) {
    sp[2 + i] = args[i];
  }
  for (uint32_t i = argc; i < nslots; i++) {
    sp[2 + i] = JS::UndefinedValue();
  }

  // Root the frame across the call: [base, top) is traced/forwarded, and the
  // callee builds its own frame above `top`.
  stack.setTop(frameTop);

  uint64_t retval = 0;
  NightFn fn = reinterpret_cast<NightFn>(static_cast<uintptr_t>(index));
  // The body receives its own JSScript (compiled-body ABI) so closure ops can
  // resolve function-template gcthings and build their environment, and its
  // boxed new.target (undefined for an ordinary call; the frame slot above the
  // actuals holds it for a construct, rooted there by the caller).
  uint64_t newTarget = constructing ? args.newTarget().get().asRawBits()
                                    : JS::UndefinedValue().asRawBits();
  int32_t err = fn(cx, reinterpret_cast<void*>(sp), argc, &retval,
                   reinterpret_cast<void*>(script), newTarget);
  if (err != 0) {
    // An exception is pending in cx ); propagate the engine error path.
    return EnterNightStatus::Error;
  }
  *rvalOut = JS::Value::fromRawBits(retval);
  // Construct semantics: a constructor that returns a non-object yields the
  // freshly-created `this` instead (the interpreter frame epilogue normally
  // does this; the AOT body has no such frame). `this` (args.thisv()) is the
  // new object for a base constructor; a derived constructor's `this` is the
  // uninitialized magic, but its body always returns an object or throws
  // (CheckReturn), so the substitution never applies there. Note:
  // `args.isConstructing()` is unreliable here -- it tests the magic `this`,
  // which `MaybeCreateThisFor Constructor` already replaced with the real
  // object -- so the caller threads the construct flag explicitly.
  if (constructing && !rvalOut->isObject()) {
    *rvalOut = args.thisv();
  }
  return EnterNightStatus::Ok;
}

// Build a global (ordinal-0) script's compiled-body frame on the AOT value
// stack and dispatch to its AOT body (spec 2d). A global script takes no
// formals (argc 0); `this` is the global `this` binding (globalThis); the env
// head is recomputed by NightEnvSetup from the script (which ignores the frame
// callee for global code, so the callee slot is a placeholder). The body's
// first op is GlobalOrEvalDeclInstantiation. Writes the boxed completion value
// to *rvalOut.
static EnterNightStatus EnterNightGlobal(JSContext* cx, JSScript* script,
                                         Value* rvalOut) {
  uint32_t index = script->externalTierWord();
  if (index == 0) {
    return EnterNightStatus::NotEntered;
  }
  if (!js::night::gNightActivated) {
    return EnterNightStatus::NotEntered;
  }
  js::nightrt::AutoNightReentry reentry(cx);
  js::nightrt::NightStack& stack = js::nightrt::TheNightStack();
  JS::Value* sp = reentry.frameBase();
  // Frame layout: [callee_placeholder, this]; no formals.
  JS::Value* frameTop = sp + 2;
  if (frameTop + js::nightrt::kNightStackHeadroomSlots > stack.limit()) {
    // The AOT stack is the tier's recursion budget: exhausting it is
    // over-recursion, not a reason to continue on the interpreter's stack.
    ReportOverRecursed(cx);
    return EnterNightStatus::Error;
  }
  // A global body has no callee, so slot 0 carries the SCRIPT instead --
  // as a private-GC-thing Value, which the AOT stack's tracer forwards like
  // any other. The body re-derives its `JSScript*` from here on every use
  // rather than holding the ABI parameter in a wasm local, because `SCRIPT`
  // is a compacting GC kind (see `Bbv::cur_script_value`).
  sp[0] = JS::PrivateGCThingValue(script);
  sp[1] = ObjectValue(*cx->global()->lexicalEnvironment().thisObject());
  stack.setTop(frameTop);

  uint64_t retval = 0;
  NightFn fn = reinterpret_cast<NightFn>(static_cast<uintptr_t>(index));
  // Global code has no new.target.
  int32_t err =
      fn(cx, reinterpret_cast<void*>(sp), 0, &retval,
         reinterpret_cast<void*>(script), JS::UndefinedValue().asRawBits());
  if (err != 0) {
    return EnterNightStatus::Error;  // pending exception; propagate
  }
  *rvalOut = JS::Value::fromRawBits(retval);
  return EnterNightStatus::Ok;
}

// RunScript / C++-API entry point. Function-invocation states dispatch via
// EnterNight; the top-level (global) Execute state dispatches via
// EnterNightGlobal once the top-level is compiled into the closed world (spec
// 2d).
EnterNightStatus MaybeEnterNight(JSContext* cx, RunState& state) {
  if (state.isExecute()) {
    JSScript* script = state.script();
    if (script->isGlobalCode() && script->externalTierWord() != 0 &&
        !script->hasNonSyntacticScope()) {
      Value rval;
      EnterNightStatus status = EnterNightGlobal(cx, script, &rval);
      if (status == EnterNightStatus::Ok) {
        state.setReturnValue(rval);
      }
      return status;
    }
    return EnterNightStatus::NotEntered;
  }
  if (!state.isInvoke()) {
    return EnterNightStatus::NotEntered;
  }
  Value rval;
  EnterNightStatus status =
      EnterNight(cx, state.script(), state.asInvoke()->args(),
                 state.asInvoke()->constructing(), &rval);
  if (status == EnterNightStatus::Ok) {
    state.setReturnValue(rval);
  }
  return status;
}

// Interpreter inline-call fast path.
EnterNightStatus MaybeEnterNight(JSContext* cx, const CallArgs& args,
                                 JSScript* script, bool constructing) {
  Value rval;
  EnterNightStatus status = EnterNight(cx, script, args, constructing, &rval);
  if (status == EnterNightStatus::Ok) {
    args.rval().set(rval);
  }
  return status;
}

EnterNightStatus NightApplyOrCall(JSContext* cx, const Value& targetv,
                                  const Value& thisv, const Value* argv,
                                  uint32_t argc, const Value* applyArr,
                                  uint64_t* rvalOut) {
  if (!targetv.isObject() || !targetv.toObject().is<JSFunction>()) {
    return EnterNightStatus::NotEntered;
  }
  JSFunction* target = &targetv.toObject().as<JSFunction>();
  if (!target->hasBaseScript()) {
    return EnterNightStatus::NotEntered;
  }
  // A class constructor has no [[Call]]: fun_call/fun_apply on it must take
  // the generic path, which throws the proper TypeError.
  if (target->isClassConstructor()) {
    return EnterNightStatus::NotEntered;
  }
  BaseScript* bs = target->baseScript();
  if (!bs->hasBytecode()) {
    return EnterNightStatus::NotEntered;
  }
  JSScript* script = bs->asJSScript();
  uint32_t index = script->externalTierWord();
  if (index == 0) {
    return EnterNightStatus::NotEntered;
  }
  if (!js::night::gNightActivated) {
    return EnterNightStatus::NotEntered;
  }

  js::nightrt::AutoNightReentry reentry(cx);
  js::nightrt::NightStack& stack = js::nightrt::TheNightStack();
  JS::Value* sp = reentry.frameBase();

  // Resolve the argument source. For `apply`, `applyArr` is the (single)
  // array-like argument: null/undefined -> no args; an ArgumentsObject with
  // no overridden elements/length -> its initial elements; a packed dense
  // array -> its dense elements. Anything else: NotEntered.
  uint32_t nformals = target->nargs();
  uint32_t nactuals = argc;
  ArgumentsObject* ao = nullptr;
  ArrayObject* arr = nullptr;
  if (applyArr) {
    if (applyArr->isNullOrUndefined()) {
      nactuals = 0;
    } else if (!applyArr->isObject()) {
      return EnterNightStatus::NotEntered;
    } else if (applyArr->toObject().is<ArgumentsObject>()) {
      ao = &applyArr->toObject().as<ArgumentsObject>();
      if (ao->hasOverriddenLength() || ao->hasOverriddenElement()) {
        return EnterNightStatus::NotEntered;
      }
      nactuals = ao->initialLength();
    } else if (applyArr->toObject().is<ArrayObject>()) {
      arr = &applyArr->toObject().as<ArrayObject>();
      uint32_t len = arr->length();
      if (arr->getDenseInitializedLength() < len) {
        return EnterNightStatus::NotEntered;  // holes / sparse
      }
      nactuals = len;
    } else {
      return EnterNightStatus::NotEntered;
    }
  }

  uint32_t nslots = nactuals > nformals ? nactuals : nformals;
  JS::Value* frameTop = sp + 2 + nslots;
  if (frameTop + js::nightrt::kNightStackHeadroomSlots > stack.limit()) {
    // The AOT stack is the tier's recursion budget: exhausting it is
    // over-recursion, not a reason to continue on the interpreter's stack.
    ReportOverRecursed(cx);
    return EnterNightStatus::Error;
  }

  sp[0] = targetv;
  sp[1] = thisv;
  if (ao) {
    for (uint32_t i = 0; i < nactuals; i++) {
      const Value& v = ao->element(i);
      if (MOZ_UNLIKELY(v.isMagic())) {
        return EnterNightStatus::NotEntered;  // call-object-forwarded formal
      }
      sp[2 + i] = v;
    }
  } else if (arr) {
    for (uint32_t i = 0; i < nactuals; i++) {
      const Value& v = arr->getDenseElement(i);
      if (MOZ_UNLIKELY(v.isMagic())) {
        return EnterNightStatus::NotEntered;  // hole
      }
      sp[2 + i] = v;
    }
  } else {
    for (uint32_t i = 0; i < nactuals; i++) {
      sp[2 + i] = argv[i];
    }
  }
  for (uint32_t i = nactuals; i < nslots; i++) {
    sp[2 + i] = JS::UndefinedValue();
  }

  stack.setTop(frameTop);
  uint64_t retval = 0;
  NightFn fn = reinterpret_cast<NightFn>(static_cast<uintptr_t>(index));
  // apply/call forwarding is always an ordinary call: new.target = undefined.
  int32_t err =
      fn(cx, reinterpret_cast<void*>(sp), nactuals, &retval,
         reinterpret_cast<void*>(script), JS::UndefinedValue().asRawBits());
  if (err != 0) {
    return EnterNightStatus::Error;
  }
  *rvalOut = retval;
  return EnterNightStatus::Ok;
}

bool IsNightResumable(AbstractGeneratorObject* gen) {
  JSFunction& callee = gen->callee();
  return callee.hasBaseScript() && callee.baseScript()->hasBytecode() &&
         callee.nonLazyScript()->externalTierWord() != 0;
}

// The interpreter Resume hook: re-enter a compiled generator body at its
// saved resume index. The body's entry dispatcher restores the saved frame
// state via NightGenRestore, so this only stages callee/this and calls. After
// the call the generator is either suspended again (the body yielded) or
// done (returned/threw): a still-running generator is closed here, exactly
// as the interpreter's frame teardown would.
EnterNightStatus EnterNightResume(JSContext* cx,
                                  Handle<AbstractGeneratorObject*> genObj,
                                  HandleValue arg, HandleValue kindVal,
                                  MutableHandleValue rvalOut) {
  JSFunction* callee = &genObj->callee();
  JSScript* script = callee->nonLazyScript();
  uint32_t index = script->externalTierWord();
  MOZ_ASSERT(index != 0);
  MOZ_ASSERT(genObj->isSuspended());

  js::nightrt::AutoNightReentry reentry(cx);
  js::nightrt::NightStack& stack = js::nightrt::TheNightStack();
  JS::Value* sp = reentry.frameBase();
  uint32_t nargs = callee->nargs();
  JS::Value* frameTop = sp + 2 + nargs;
  // The resume descriptor sits just above the frame head (unscanned: the
  // published top stays below it; the body consumes it before any GC).
  if (frameTop + 3 + js::nightrt::kNightStackHeadroomSlots > stack.limit()) {
    // A suspended AOT generator cannot fall back to the interpreter (the
    // storage layout is the AOT's own); treat exhaustion as over-recursion.
    ReportOverRecursed(cx);
    return EnterNightStatus::Error;
  }
  sp[0] = ObjectValue(*callee);
  // The resume sentinel: a generator body's entry dispatch re-enters the
  // state machine when the frame `this` is this magic (never a legit fresh
  // `this`), avoiding an extra ABI param on every ordinary call.
  sp[1] = JS::MagicValue(JS_GENERATOR_CLOSING);
  // Formal slots are never read on resume (the frontend routes formals
  // through bindings captured before InitialYield); undefined keeps the
  // scanned region valid.
  for (uint32_t i = 0; i < nargs; i++) {
    sp[2 + i] = JS::UndefinedValue();
  }
  stack.setTop(frameTop);

  uint32_t* desc = reinterpret_cast<uint32_t*>(frameTop);
  desc[0] = genObj->resumeIndex();
  desc[1] = uint32_t(kindVal.toInt32());
  frameTop[1] = ObjectValue(*genObj);
  frameTop[2] = arg;

  uint64_t retval = 0;
  NightFn fn = reinterpret_cast<NightFn>(static_cast<uintptr_t>(index));
  int32_t err =
      fn(cx, reinterpret_cast<void*>(sp), 0, &retval,
         reinterpret_cast<void*>(script), JS::UndefinedValue().asRawBits());
  if (err != 0) {
    // An uncaught throw in a generator body closes the generator (the
    // interpreter does this during frame unwind).
    if (!genObj->isClosed()) {
      genObj->setClosed(cx);
    }
    return EnterNightStatus::Error;
  }
  if (!genObj->isSuspended() && !genObj->isClosed()) {
    // Ran to completion (FinalYieldRval or a forced .return()).
    genObj->setClosed(cx);
  }
  rvalOut.set(JS::Value::fromRawBits(retval));
  return EnterNightStatus::Ok;
}

}  // namespace night
}  // namespace js

#endif  // ENABLE_JS_NIGHTMONKEY
