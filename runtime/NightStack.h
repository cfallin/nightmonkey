/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80: */

// The AOT value stack: a single contiguous, upward-growing array of boxed
// JS::Values that is the *sole* GC root for object references held by
// AOT-compiled Wasm code. One per JSContext, in the context's external-tier
// state (NightContextState, made by the ExternalCompilerHooks newContext
// hook; reached as js::nightrt::TheNightStack(cx)), and traced (and, under
// a moving GC, forwarded) as a root region over [base, top) by the
// traceRoots hook on EVERY GC (minor and major), exactly like the
// interpreter and JIT stacks -- an embedding extra-roots tracer would be
// skipped on minor (nursery) GC, leaving freshly-allocated nursery pointers
// in AOT frame slots stale. See docs/DESIGN.md section 9.
//
// The region is 1 << Night_valueStackLog2 bytes, aligned to its size: a
// frame [sp, end) fits iff its last byte has sp's high bits, which compiled
// code tests with no load of the limit.
//
// Rooting / re-entrancy contract:
//   - `top` is the current free slot; [base, top) is live and rooted.
//   - Before any may-GC call into the runtime, an AOT function writes its
//     working top into `top`. That serves two purposes at once: it is the GC
//     scan limit (helpers that allocate trace [base, top)), and it is the base
//     of any frame a re-entrant call will build.
//   - When native code (the engine call path, or night_runtime_call) re-enters
//   a Wasm
//     AOT function, the new frame base is sp == top. Because the callee runs
//     above sp and bumps `top` at its own may-GC points, the native side wraps
//     the re-entry in AutoNightReentry, which restores `top` once the nested
//     activation returns and its frame is popped.
//   - Direct AOT-to-AOT Wasm calls pass sp explicitly and do
//     not need the guard; `top` self-corrects at the callee's next may-GC
//     point.

#ifndef night_runtime_NightStack_h
#define night_runtime_NightStack_h

#include "mozilla/Attributes.h"  // MOZ_RAII
#include "mozilla/Likely.h"      // MOZ_LIKELY

#include <stddef.h>
#include <stdint.h>

#include "js/TypeDecls.h"  // JSContext, JSTracer (correct public-API visibility)
#include "js/Value.h"      // JS::Value
#include "runtime/NightRegionShape.h"

namespace js {
namespace nightrt {

// Headroom a compiled body may use above its incoming frame without a
// check: the compiled call guard (compiler/src/wasm/mir/lower.rs
// and baseline/codegen.rs, HEADROOM) admits a direct call only when frame top + this
// stays below the limit, and the engine-side entry paths must reserve the
// same, or a body entered near the limit writes past the stack.
static constexpr size_t kNightStackHeadroomSlots = (64 * 1024) / sizeof(JS::Value);

// The region's size in bytes and in slots.
static constexpr size_t kNightStackBytes = size_t(1) << js::night::Night_valueStackLog2;
static constexpr size_t kNightStackSlots = kNightStackBytes / sizeof(JS::Value);

class NightStack {
 public:
  // Allocates the backing region (so it exists from the context's creation,
  // before any AOT frame runs), aligned to its size. Tracing is wired in via
  // the traceRoots hook; there is no separate registration step.
  NightStack();
  ~NightStack();

  // The free top and the base of the live region. [base(), top()) is rooted.
  JS::Value* base() const { return base_; }
  JS::Value* top() const { return top_; }
  JS::Value* limit() const { return limit_; }
  void setTop(JS::Value* top) { top_ = top; }

  bool valid() const { return base_ != nullptr; }

  // Traces [base, top) as JS::Value roots (called from JSContext::trace on
  // every GC). `JS::TraceRoot` forwards moved pointers in place and is a no-op
  // for non-GC Values (numbers, undefined, ...).
  void trace(JSTracer* trc);

  // `NIGHT_GC_STATS`: the traces of the stack, and the slots they covered.
  uint64_t traces() const { return traces_; }
  uint64_t tracedSlots() const { return tracedSlots_; }

 private:
  uint64_t traces_ = 0;
  uint64_t tracedSlots_ = 0;
  JS::Value* base_;
  JS::Value* top_;
  JS::Value* limit_;
};

// The context's value stack (runtime/NightContext.h).
NightStack& TheNightStack(JSContext* cx);

// RAII guard for a native -> AOT re-entry: saves the free top on entry and
// restores it on scope exit (see the re-entrancy contract above). frameBase()
// is the sp the re-entered frame should be built at.
class MOZ_RAII AutoNightReentry {
 public:
  explicit AutoNightReentry(JSContext* cx);
  ~AutoNightReentry() { stack_.setTop(savedTop_); }

  JS::Value* frameBase() const { return savedTop_; }

 private:
  NightStack& stack_;
  JS::Value* savedTop_;
};

}  // namespace nightrt
}  // namespace js

#endif  // night_runtime_NightStack_h
