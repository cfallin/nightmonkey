/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// Out-of-line wrappers for the few `*-inl.h` accessors the reactor needs.
// Kept in their own translation unit (NightRuntimeSlots.cpp, a non-unified
// SOURCES entry) so the heavy inline headers they pull in do NOT perturb the
// optimization of the hot helpers in NightRuntime.cpp's TU -- pulling
// `JSFunction-inl.h` into NightRuntime.cpp measurably regresses the hot
// helpers.

#ifndef night_runtime_NightRuntimeSlots_h
#define night_runtime_NightRuntimeSlots_h

#include "js/TypeDecls.h"  // JSObject, JSFunction

namespace js {
namespace night {

// The method [[HomeObject]] extended slot (JSOp::InitHomeObject / SuperBase).
JSObject* NightGetHomeObject(JSFunction* fn);
void NightSetHomeObject(JSFunction* fn, JSObject* homeObj);

}  // namespace night
}  // namespace js

#endif  // night_runtime_NightRuntimeSlots_h
