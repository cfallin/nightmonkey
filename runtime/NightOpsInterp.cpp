/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

/*
 * Provenance: the code in this file is borrowed from SpiderMonkey and remains
 * under the MPL 2.0 (unlike the rest of NightMonkey, which is Apache-2.0):
 *
 * - NightGetNameOperation is a copy of the static-inline GetNameOperation in
 *   js/src/vm/Interpreter.cpp.
 * - NightSetNameOperation is the body of js::SetNameOperation in
 *   js/src/vm/Interpreter-inl.h, minus its script/pc decoding (the caller
 *   passes the name and strictness, which an AOT body has in hand).
 * - NightDirectEval is the DIRECT_EVAL path of the static EvalKernel in
 *   js/src/builtin/Eval.cpp, with the caller's script, pc and env chain
 *   passed in (a NightMonkey frame is not an AbstractFramePtr). It omits
 *   EvalKernel's two optimizations, the eval cache and the JSON fast path,
 *   neither of which changes the result.
 */

#include "runtime/NightOpsInterp.h"

#include "frontend/BytecodeCompiler.h"  // js::frontend::CompileEvalScript
#include "js/CompilationAndEvaluation.h"  // JS::UpdateDebugMetadata
#include "js/SourceText.h"
#include "js/StableStringChars.h"
#include "vm/BytecodeUtil.h"  // js::IsTypeOfNameOp, js::IsStrictEvalPC
#include "vm/Interpreter.h"   // js::ExecuteKernel
#include "vm/JSScript.h"      // js::DescribeScriptedCallerForDirectEval
#include "vm/EnvironmentObject.h"
#include "vm/JSObject.h"
#include "vm/NativeObject.h"

#include "vm/EnvironmentObject-inl.h"
#include "vm/Interpreter-inl.h"  // js::GetEnvironmentName
#include "vm/NativeObject-inl.h"
#include "vm/ObjectOperations-inl.h"

#ifdef ENABLE_JS_NIGHTMONKEY

namespace js {
namespace night {

bool NightGetNameOperation(JSContext* cx, JS::HandleObject envChain,
                           JS::Handle<PropertyName*> name, JSOp nextOp,
                           JS::MutableHandleValue vp) {
  /* Kludge to allow (typeof foo == "undefined") tests. */
  if (js::IsTypeOfNameOp(nextOp)) {
    return js::GetEnvironmentName<js::GetNameMode::TypeOf>(cx, envChain, name,
                                                           vp);
  }
  return js::GetEnvironmentName<js::GetNameMode::Normal>(cx, envChain, name,
                                                         vp);
}

bool NightSetNameOperation(JSContext* cx, JS::HandleObject env,
                           JS::Handle<JS::PropertyKey> id, JS::HandleValue val,
                           bool strict) {
  // In strict mode, assigning to an undeclared global variable is an
  // error. To detect this, we call NativeSetProperty directly and pass
  // Unqualified. It stores the error, if any, in |result|.
  bool ok;
  ObjectOpResult result;
  RootedValue receiver(cx, ObjectValue(*env));
  if (env->isUnqualifiedVarObj()) {
    Rooted<NativeObject*> varobj(cx);
    if (env->is<DebugEnvironmentProxy>()) {
      varobj =
          &env->as<DebugEnvironmentProxy>().environment().as<NativeObject>();
    } else {
      varobj = &env->as<NativeObject>();
    }
    MOZ_ASSERT(!varobj->getOpsSetProperty());
    ok = NativeSetProperty<Unqualified>(cx, varobj, id, val, receiver, result);
  } else {
    ok = SetProperty(cx, env, id, val, receiver, result);
  }
  return ok && result.checkStrictModeError(cx, env, id, strict);
}

bool NightDirectEval(JSContext* cx, JS::HandleValue v, JS::HandleObject env,
                     JS::HandleScript callerScript, jsbytecode* pc,
                     JS::MutableHandleValue vp) {
  // "Dynamic Code Brand Checks" adds support for Object values.
  // https://tc39.es/proposal-dynamic-code-brand-checks/#sec-performeval
  // Steps 2-4.
  JS::RootedString str(cx);
  if (v.isString()) {
    str = v.toString();
  } else if (v.isObject()) {
    JS::RootedObject obj(cx, &v.toObject());
    if (!cx->getCodeForEval(obj, &str)) {
      return false;
    }
  }
  if (!str) {
    vp.set(v);
    return true;
  }

  // Steps 6-8.
  JS::RootedVector<JSString*> parameterStrings(cx);
  JS::RootedVector<JS::Value> parameterArgs(cx);
  bool canCompileStrings = cx->bypassCSPForDebugger;
  if (!canCompileStrings &&
      !cx->isRuntimeCodeGenEnabled(JS::RuntimeCode::JS, str,
                                   JS::CompilationType::DirectEval,
                                   parameterStrings, str, parameterArgs, v,
                                   &canCompileStrings)) {
    return false;
  }
  if (!canCompileStrings) {
    JS_ReportErrorNumberASCII(cx, js::GetErrorMessage, nullptr,
                              JSMSG_CSP_BLOCKED_EVAL);
    return false;
  }

  // Step 9 ff.
  JS::Rooted<JSLinearString*> linearStr(cx, str->ensureLinear(cx));
  if (!linearStr) {
    return false;
  }

  uint32_t lineno;
  const char* filename;
  bool mutedErrors;
  uint32_t pcOffset;
  js::DescribeScriptedCallerForDirectEval(cx, callerScript, pc, &filename,
                                          &lineno, &pcOffset, &mutedErrors);
  const char* introducerFilename = filename;
  if (callerScript->scriptSource()->introducerFilename()) {
    introducerFilename = callerScript->scriptSource()->introducerFilename();
  }

  JS::Rooted<js::Scope*> enclosing(cx, callerScript->innermostScope(pc));

  JS::CompileOptions options(cx);
  options.setIsRunOnce(true)
      .setNoScriptRval(false)
      .setMutedErrors(mutedErrors)
      .setDeferDebugMetadata();
  JS::RootedScript introScript(cx);
  if (js::IsStrictEvalPC(pc)) {
    options.setForceStrictMode();
  }
  if (introducerFilename) {
    options.setFileAndLine(filename, 1);
    options.setIntroductionInfo(introducerFilename, "eval", lineno, pcOffset);
    introScript = callerScript;
  } else {
    options.setFileAndLine("eval", 1);
    options.setIntroductionType("eval");
  }
  options.setNonSyntacticScope(
      enclosing->hasOnChain(js::ScopeKind::NonSyntactic));

  JS::AutoStableStringChars linearChars(cx);
  if (!linearChars.initTwoByte(cx, linearStr)) {
    return false;
  }
  JS::SourceText<char16_t> srcBuf;
  if (!srcBuf.initMaybeBorrowed(cx, linearChars)) {
    return false;
  }
  JS::RootedScript script(
      cx, js::frontend::CompileEvalScript(cx, options, srcBuf, enclosing, env));
  if (!script) {
    return false;
  }
  JS::RootedValue undefValue(cx);
  JS::InstantiateOptions instantiateOptions(options);
  if (!JS::UpdateDebugMetadata(cx, script, instantiateOptions, undefValue,
                               nullptr, introScript, callerScript)) {
    return false;
  }
  return js::ExecuteKernel(cx, script, env, js::NullFramePtr() /* evalInFrame */,
                           vp);
}

}  // namespace night
}  // namespace js

#endif  // ENABLE_JS_NIGHTMONKEY
