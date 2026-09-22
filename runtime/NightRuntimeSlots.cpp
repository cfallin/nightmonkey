/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80: */

#include "runtime/NightRuntimeSlots.h"

#include "vm/JSFunction.h"      // JSFunction, js::FunctionExtended
#include "vm/JSFunction-inl.h"  // JSFunction::get/setExtendedSlot

// Isolated TU: see NightRuntimeSlots.h. Do not add hot-path reactor code here.

namespace js {
namespace night {

JSObject* NightGetHomeObject(JSFunction* fn) {
  return &fn->getExtendedSlot(js::FunctionExtended::METHOD_HOMEOBJECT_SLOT)
              .toObject();
}

void NightSetHomeObject(JSFunction* fn, JSObject* homeObj) {
  fn->setExtendedSlot(js::FunctionExtended::METHOD_HOMEOBJECT_SLOT,
                      JS::ObjectValue(*homeObj));
}

}  // namespace night
}  // namespace js
