/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

/*
 * Entry points into AOT-compiled (wasm) function bodies: the dispatch hooks
 * the interpreter calls when a script has a compiled body. The helpers the
 * compiled code itself calls are declared in NightOps.h,
 * NightInlineCaches.h, NightInlineHeap.h and NightGenerator.h.
 */

#ifndef night_runtime_NightEntry_h
#define night_runtime_NightEntry_h

#ifdef ENABLE_JS_NIGHTMONKEY

#  include "vm/Interpreter.h"
#  include "vm/Stack.h"

namespace js {

class AbstractGeneratorObject;

namespace night {

enum class EnterNightStatus { Error, Ok, NotEntered };

// Dispatch `state`'s script to its AOT body if it has one; NotEntered means
// the caller falls through to the interpreter.
EnterNightStatus MaybeEnterNight(JSContext* cx, RunState& state);

// Call-path variant: dispatch the callee's compiled body for a call or
// construct invocation.
EnterNightStatus MaybeEnterNight(JSContext* cx, const CallArgs& args,
                                 JSScript* funScript, bool constructing);

// `f.apply(thisArg, args)` / `f.call(thisArg, ...)` forwarding: when the
// runtime callee of a generic AOT call is the fun_apply/fun_call native and
// the TARGET function has a compiled AOT body, dispatch the target directly,
// skipping the native + js::Call + InternalCall round trip. For `apply`,
// `applyArr` names the single array-like argument (ArgumentsObject / packed
// dense array / null-or-undefined); for `call`, `argv`/`argc` are the
// forwarded arguments. NotEntered for any shape the fast path does not cover
// (the caller falls back to the generic native).
EnterNightStatus NightApplyOrCall(JSContext* cx, const JS::Value& targetv,
                                  const JS::Value& thisv, const JS::Value* argv,
                                  uint32_t argc, const JS::Value* applyArr,
                                  uint64_t* rvalOut);

// Whether `gen`'s body was AOT-compiled, in which case JSOp::Resume must
// re-enter it through EnterNightResume: the interpreter cannot resume it,
// because the saved stack-storage layout is the AOT's own.
bool IsNightResumable(AbstractGeneratorObject* gen);

// The interpreter Resume hook: re-enter a compiled generator body at its
// saved resume index.
EnterNightStatus EnterNightResume(JSContext* cx,
                                  Handle<AbstractGeneratorObject*> genObj,
                                  HandleValue arg, HandleValue kindVal,
                                  MutableHandleValue rvalOut);

}  // namespace night
}  // namespace js

#endif  // ENABLE_JS_NIGHTMONKEY

#endif  // night_runtime_NightEntry_h
