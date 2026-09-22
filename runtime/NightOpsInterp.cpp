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
 */

#include "runtime/NightOpsInterp.h"

#include "vm/BytecodeUtil.h"  // js::IsTypeOfNameOp
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

}  // namespace night
}  // namespace js

#endif  // ENABLE_JS_NIGHTMONKEY
