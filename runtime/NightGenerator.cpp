/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include "builtin/Promise.h"  // js::AsyncFunctionAwait, js::CanSkipAwait, js::ExtractAwaitValue
#include "vm/AsyncFunction.h"  // js::AsyncFunctionResolve, js::AsyncFunctionReject
#include "vm/GeneratorObject.h"
#include "vm/JSContext.h"
#include "vm/JSFunction.h"
#include "vm/JSScript.h"

#include "vm/NativeObject-inl.h"

#ifdef ENABLE_JS_NIGHTMONKEY
namespace js {
namespace night {

// ---- Generator engine half for compiled (AOT) generator bodies. The AOT
// owns both ends of the stack-storage layout ([locals..., operands...],
// counts fixed at compile time): a script is AOT-compiled or interpreted
// for the whole run, so a generator suspended by an AOT body is always
// resumed by the AOT Resume hook (EnterNightResume), never the interpreter.

// `JSOp::Generator`: create this frame's generator object. `envBits` is the
// frame's env head (boxed) when the body has one, else undefined (the
// callee's static environment is used, as createFromFrame does).
bool NightCreateGenerator(JSContext* cx, uint64_t calleeBits, uint64_t envBits,
                          uint64_t* out) {
  RootedFunction callee(
      cx, &JS::Value::fromRawBits(calleeBits).toObject().as<JSFunction>());
  RootedScript script(cx, callee->nonLazyScript());
  JS::Value env = JS::Value::fromRawBits(envBits);
  RootedObject envChain(
      cx, env.isObject() ? &env.toObject() : callee->environment());
  // Left null: AOT-compiled generators do not support an arguments object.
  Rooted<ArgumentsObject*> argsObj(cx);
  AbstractGeneratorObject* gen =
      AbstractGeneratorObject::create(cx, callee, script, envChain, argsObj);
  if (!gen) {
    return false;
  }
  *out = ObjectValue(*gen).asRawBits();
  return true;
}

namespace {
// Iterates [locals, locals+nlocals) then [ops, ops+nops), for the one-pass
// barriered dense-array init below.
struct TwoRangeIter {
  const JS::Value* locals;
  uint32_t nlocals;
  const JS::Value* ops;
  uint32_t i;

  JS::Value operator*() const {
    return i < nlocals ? locals[i] : ops[i - nlocals];
  }
  TwoRangeIter& operator++() {
    i++;
    return *this;
  }
  TwoRangeIter operator++(int) {
    TwoRangeIter t = *this;
    i++;
    return t;
  }
  bool operator!=(const TwoRangeIter& o) const { return i != o.i; }
  ptrdiff_t operator-(const TwoRangeIter& o) const {
    return ptrdiff_t(i) - ptrdiff_t(o.i);
  }
};
}  // namespace

// Suspend at resume index `k`: save the frame's locals + live operands into
// the generator's stack storage and update its env chain. Leaf: the storage
// array was created with script->nslots() capacity, which bounds
// nlocals + nops, so no allocation (asserted) -- callers hold raw Values.
void NightGenSuspend(JSContext* cx, uint64_t genBits, uint32_t k,
                     JS::Value* locals, uint32_t nlocals, JS::Value* ops,
                     uint32_t nops, uint64_t envBits) {
  auto& gen =
      JS::Value::fromRawBits(genBits).toObject().as<AbstractGeneratorObject>();
  ArrayObject& storage = gen.stackStorage();
  MOZ_RELEASE_ASSERT(storage.getDenseInitializedLength() == 0);
  MOZ_RELEASE_ASSERT(storage.getDenseCapacity() >= nlocals + nops);
  TwoRangeIter begin{locals, nlocals, ops, 0};
  TwoRangeIter end{locals, nlocals, ops, nlocals + nops};
  MOZ_ALWAYS_TRUE(storage.initDenseElementsFromRange(cx, begin, end));
  gen.setResumeIndex(int32_t(k));
  JS::Value env = JS::Value::fromRawBits(envBits);
  if (env.isObject()) {
    gen.setEnvironmentChain(env.toObject());
  }
}

// Resume: copy the saved state back into the frame (locals at `locals`,
// operands at `ops`, env head into *envSlot when non-null), empty the
// storage, mark the generator running. Leaf (plain reads; no GC). Returns
// the restored operand count.
uint32_t NightGenRestore(JSContext* cx, uint64_t genBits, JS::Value* locals,
                         uint32_t nlocals, JS::Value* envSlot, JS::Value* ops) {
  auto& gen =
      JS::Value::fromRawBits(genBits).toObject().as<AbstractGeneratorObject>();
  ArrayObject& storage = gen.stackStorage();
  uint32_t len = storage.getDenseInitializedLength();
  MOZ_RELEASE_ASSERT(len >= nlocals);
  for (uint32_t i = 0; i < nlocals; i++) {
    locals[i] = storage.getDenseElement(i);
  }
  for (uint32_t i = nlocals; i < len; i++) {
    ops[i - nlocals] = storage.getDenseElement(i);
  }
  storage.setDenseInitializedLength(0);
  if (envSlot) {
    *envSlot = ObjectValue(gen.environmentChain());
  }
  gen.setRunning();
  return len - nlocals;
}

// `JSOp::CheckResumeKind`, non-Next kinds (called with the operands rooted
// in the frame). Always raises, mirroring GeneratorThrowOrReturn: Throw sets
// the pending exception to val; Return stages val in the frame's rval slot
// and raises the JS_GENERATOR_CLOSING magic, so the body's section-5 routing
// runs enclosing finallys (which observe it via IsGenClosing) and the
// generator error epilogue converts a surviving magic into a normal return.
bool NightGenCheckResume(JSContext* cx, uint64_t genBits, uint64_t valBits,
                         uint32_t kind, JS::Value* rvalSlot) {
  RootedValue val(cx, JS::Value::fromRawBits(valBits));
  if (GeneratorResumeKind(kind) == GeneratorResumeKind::Throw) {
    cx->setPendingException(val, ShouldCaptureStack::Maybe);
    return false;
  }
  MOZ_ASSERT(GeneratorResumeKind(kind) == GeneratorResumeKind::Return);
  *rvalSlot = val;
  RootedValue closing(cx, MagicValue(JS_GENERATOR_CLOSING));
  cx->setPendingException(closing, nullptr);
  return false;
}

// The generator error epilogue's closing check: a pending
// JS_GENERATOR_CLOSING magic means a forced .return() finished unwinding
// its finallys -- clear it and return 1 (the body then returns the rval
// register normally); any other pending exception returns 0. Leaf.
// Peek-only variant for the catch-pad closing split (`ProcessTryNotes`
// skips Catch notes while closing): the magic must STAY pending so the
// rerouted unwind's finallys and the error epilogue still observe it. Leaf.
int32_t NightGenIsClosing(JSContext* cx) {
  if (!cx->isExceptionPending()) {
    return 0;
  }
  RootedValue exc(cx);
  if (!cx->getPendingException(&exc)) {
    return 0;
  }
  return exc.isMagic(JS_GENERATOR_CLOSING) ? 1 : 0;
}

int32_t NightGenClosing(JSContext* cx) {
  if (!NightGenIsClosing(cx)) {
    return 0;
  }
  cx->clearPendingException();
  return 1;
}

// `JSOp::FinalYieldRval`: the generator ran to completion; close it (the
// interpreter's finalSuspend).
void NightGenFinal(JSContext* cx, uint64_t genBits) {
  RootedObject gen(cx, &JS::Value::fromRawBits(genBits).toObject());
  AbstractGeneratorObject::finalSuspend(cx, gen);
}

// `JSOp::AsyncAwait`: register the await continuation on `value`'s promise;
// result is the promise the initial call returns.
bool NightAsyncAwait(JSContext* cx, uint64_t genBits, uint64_t valBits,
                     uint64_t* out) {
  Rooted<AsyncFunctionGeneratorObject*> gen(
      cx, &JS::Value::fromRawBits(genBits)
               .toObject()
               .as<AsyncFunctionGeneratorObject>());
  RootedValue val(cx, JS::Value::fromRawBits(valBits));
  JSObject* promise = AsyncFunctionAwait(cx, gen, val);
  if (!promise) {
    return false;
  }
  *out = ObjectValue(*promise).asRawBits();
  return true;
}

// `JSOp::AsyncResolve`: fulfill the async function's result promise.
bool NightAsyncResolve(JSContext* cx, uint64_t genBits, uint64_t valBits,
                       uint64_t* out) {
  Rooted<AsyncFunctionGeneratorObject*> gen(
      cx, &JS::Value::fromRawBits(genBits)
               .toObject()
               .as<AsyncFunctionGeneratorObject>());
  RootedValue val(cx, JS::Value::fromRawBits(valBits));
  JSObject* promise = AsyncFunctionResolve(cx, gen, val);
  if (!promise) {
    return false;
  }
  *out = ObjectValue(*promise).asRawBits();
  return true;
}

// `JSOp::AsyncReject`: reject the async function's result promise.
bool NightAsyncReject(JSContext* cx, uint64_t genBits, uint64_t reasonBits,
                      uint64_t stackBits, uint64_t* out) {
  Rooted<AsyncFunctionGeneratorObject*> gen(
      cx, &JS::Value::fromRawBits(genBits)
               .toObject()
               .as<AsyncFunctionGeneratorObject>());
  RootedValue reason(cx, JS::Value::fromRawBits(reasonBits));
  RootedValue stack(cx, JS::Value::fromRawBits(stackBits));
  JSObject* promise = AsyncFunctionReject(cx, gen, reason, stack);
  if (!promise) {
    return false;
  }
  *out = ObjectValue(*promise).asRawBits();
  return true;
}

// `JSOp::CanSkipAwait`: whether awaiting `value` can skip the suspension.
bool NightCanSkipAwait(JSContext* cx, uint64_t valBits, uint64_t* out) {
  RootedValue val(cx, JS::Value::fromRawBits(valBits));
  bool canSkip = false;
  if (!CanSkipAwait(cx, val, &canSkip)) {
    return false;
  }
  *out = JS::BooleanValue(canSkip).asRawBits();
  return true;
}

// `JSOp::MaybeExtractAwaitValue`: when `canSkip`, replace the awaited value
// with its resolved value; else pass it through.
bool NightMaybeExtractAwait(JSContext* cx, uint64_t valBits, uint32_t canSkip,
                            uint64_t* out) {
  RootedValue val(cx, JS::Value::fromRawBits(valBits));
  if (canSkip) {
    if (!ExtractAwaitValue(cx, val, &val)) {
      return false;
    }
  }
  *out = val.get().asRawBits();
  return true;
}

}  // namespace night
}  // namespace js
#endif  // ENABLE_JS_NIGHTMONKEY
