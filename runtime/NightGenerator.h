/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

/*
 * The engine half of compiled generator and async-function bodies: creating
 * the generator object, saving and restoring the frame across a suspend, and
 * the resume-kind, closing and await protocol. The AOT owns both ends of the
 * stack-storage layout, so a generator suspended by a compiled body is always
 * resumed by one (see NightEntry.h's EnterNightResume).
 */

#ifndef night_runtime_NightGenerator_h
#define night_runtime_NightGenerator_h

#ifdef ENABLE_JS_NIGHTMONKEY

#  include <stdint.h>

#  include "js/TypeDecls.h"
#  include "js/Value.h"

namespace js {
namespace night {

// `Generator`: create this frame's generator object. `envBits` is the frame's
// env head (boxed) when the body has one, else undefined.
bool NightCreateGenerator(JSContext* cx, uint64_t calleeBits, uint64_t envBits,
                          uint64_t* out);
// `InitialYield`/`Yield`: save locals + live operands into the generator's
// stack storage and update its env chain. Leaf (the storage array was sized
// at creation, so no allocation).
void NightGenSuspend(JSContext* cx, uint64_t genBits, uint32_t k,
                     JS::Value* locals, uint32_t nlocals, JS::Value* ops,
                     uint32_t nops, uint64_t envBits);
// Resume: copy the saved state back into the frame and mark the generator
// running; returns the restored operand count. Leaf.
uint32_t NightGenRestore(JSContext* cx, uint64_t genBits, JS::Value* locals,
                         uint32_t nlocals, JS::Value* envSlot, JS::Value* ops);
// `CheckResumeKind`, non-Next kinds: always raises (Throw sets the pending
// exception; Return stages the value and raises JS_GENERATOR_CLOSING).
bool NightGenCheckResume(JSContext* cx, uint64_t genBits, uint64_t valBits,
                         uint32_t kind, JS::Value* rvalSlot);
// The closing check: 1 when a JS_GENERATOR_CLOSING magic is pending.
// `NightGenClosing` clears it; `NightGenIsClosing` peeks (the catch-pad split
// needs the magic to stay pending). Both leaf.
int32_t NightGenClosing(JSContext* cx);
int32_t NightGenIsClosing(JSContext* cx);
// `FinalYieldRval`: the generator ran to completion; close it.
void NightGenFinal(JSContext* cx, uint64_t genBits);

// The async-function protocol: `AsyncAwait` registers the await
// continuation, `AsyncResolve`/`AsyncReject` settle the result promise, and
// the CanSkipAwait pair short-circuits an already-resolved await.
bool NightAsyncAwait(JSContext* cx, uint64_t genBits, uint64_t valBits,
                     uint64_t* out);
bool NightAsyncResolve(JSContext* cx, uint64_t genBits, uint64_t valBits,
                       uint64_t* out);
bool NightAsyncReject(JSContext* cx, uint64_t genBits, uint64_t reasonBits,
                      uint64_t stackBits, uint64_t* out);
bool NightCanSkipAwait(JSContext* cx, uint64_t valBits, uint64_t* out);
bool NightMaybeExtractAwait(JSContext* cx, uint64_t valBits, uint32_t canSkip,
                            uint64_t* out);

}  // namespace night
}  // namespace js

#endif  // ENABLE_JS_NIGHTMONKEY

#endif  // night_runtime_NightGenerator_h
