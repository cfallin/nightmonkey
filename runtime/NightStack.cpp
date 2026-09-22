/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80: */

#include "runtime/NightStack.h"

#include "js/TracingAPI.h"  // JS::TraceRoot
#include "js/Utility.h"     // js_calloc, js_free

namespace js {
namespace nightrt {

// 256K boxed Values (2 MiB). AOT frames push roots here and bump `top`; the
// stack is fixed-size, and a frame that would not fit falls back to the
// interpreter.
static constexpr size_t kCapacitySlots = 256 * 1024;

NightStack::NightStack()
    : base_(static_cast<JS::Value*>(
          js_calloc(kCapacitySlots * sizeof(JS::Value)))),
      top_(base_),
      limit_(base_ ? base_ + kCapacitySlots : nullptr) {}

NightStack::~NightStack() { js_free(base_); }

void NightStack::trace(JSTracer* trc) {
  // Every live slot is a boxed JS::Value root. JS::TraceRoot handles non-GC
  // Values (numbers, undefined, ...) and forwards moved pointers in place.
  for (JS::Value* slot = base_; slot < top_; slot++) {
    JS::TraceRoot(trc, slot, "aot-value-stack-slot");
  }
}

NightStack& TheNightStack() {
  static NightStack stack;
  return stack;
}

AutoNightReentry::AutoNightReentry(JSContext* cx)
    : stack_(TheNightStack()), savedTop_(stack_.top()) {}

}  // namespace nightrt
}  // namespace js
