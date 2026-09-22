/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80: */

/*
 * Interpreter name-operation helpers used by NightOps.cpp, kept in their own
 * translation unit (NightOpsInterp.cpp) because they are borrowed from
 * SpiderMonkey's interpreter; see the provenance note there.
 */

#ifndef night_runtime_NightOpsInterp_h
#define night_runtime_NightOpsInterp_h

#ifdef ENABLE_JS_NIGHTMONKEY

#  include "js/Id.h"
#  include "js/RootingAPI.h"
#  include "js/TypeDecls.h"
#  include "js/Value.h"
#  include "vm/Opcodes.h"  // JSOp

namespace js {

class PropertyName;

namespace night {

// The interpreter's static-inline GetNameOperation: look `name` up on
// `envChain`, in TypeOf mode when `nextOp` is a typeof-consuming op.
bool NightGetNameOperation(JSContext* cx, JS::HandleObject envChain,
                           JS::Handle<PropertyName*> name, JSOp nextOp,
                           JS::MutableHandleValue vp);

// The assignment half of js::SetNameOperation, with the name and strictness
// supplied by the caller rather than derived from script/pc.
bool NightSetNameOperation(JSContext* cx, JS::HandleObject env,
                           JS::Handle<JS::PropertyKey> id, JS::HandleValue val,
                           bool strict);

}  // namespace night
}  // namespace js

#endif  // ENABLE_JS_NIGHTMONKEY

#endif  // night_runtime_NightOpsInterp_h
