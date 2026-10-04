/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80: */

#include "runtime/NightStack.h"

#include "runtime/NightContext.h"

#include <stdlib.h>  // aligned_alloc, free
#include <string.h>  // memset

#include "js/TracingAPI.h"  // JS::TraceRoot

namespace js {
namespace nightrt {

// kNightStackSlots boxed Values, aligned to the region's size (see
// NightStack.h). AOT frames push roots here and bump `top`; the stack is
// fixed-size, and a frame that would not fit falls back to the interpreter.
static JS::Value* AllocRegion() {
  void* p = aligned_alloc(kNightStackBytes, kNightStackBytes);
  if (p) {
    memset(p, 0, kNightStackBytes);
  }
  return static_cast<JS::Value*>(p);
}

NightStack::NightStack()
    : base_(AllocRegion()),
      top_(base_),
      limit_(base_ ? base_ + kNightStackSlots : nullptr) {}

NightStack::~NightStack() { free(base_); }

void NightStack::trace(JSTracer* trc) {
  traces_++;
  tracedSlots_ += uint64_t(top_ - base_);
  // Every live slot is a boxed JS::Value root. JS::TraceRoot handles non-GC
  // Values (numbers, undefined, ...) and forwards moved pointers in place.
  for (JS::Value* slot = base_; slot < top_; slot++) {
    JS::TraceRoot(trc, slot, "aot-value-stack-slot");
  }
}

NightStack& TheNightStack(JSContext* cx) { return TheNightStackInline(cx); }

AutoNightReentry::AutoNightReentry(JSContext* cx)
    : stack_(TheNightStack(cx)), savedTop_(stack_.top()) {}

}  // namespace nightrt
}  // namespace js
