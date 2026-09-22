/* -*- Mode: C; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sw=2 et tw=0 ft=c:
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#ifndef night_runtime_Night_h
#define night_runtime_Night_h

#include <stddef.h>
#include <stdint.h>

#include "js/TypeDecls.h"

// NIGHTMONKEY_DEBUG gates the runtime's diagnostic surface: the batch and
// capture progress reporting, and the crash-on-failure that turns a silent
// in-process degradation into a test failure. Defined by
// --enable-nightmonkey-debug; off in every shipped configuration.

namespace js {

#ifdef ENABLE_JS_NIGHTMONKEY
// Snapshot-registration extras (external transform flow): resolve the
// self-hosted allowlist against the live global and force-compile regex
// bytecode for `root`'s tree, recording both in the registration block so
// the external tool compiles them like every other lane. Call right after
// JS::NightRegisterRoot, before the wizer snapshot.
bool NightSnapshotCaptureExtras(JSContext* cx, JS::Handle<JSScript*> root);

// Snapshot heap oracle: transcribe the live post-setup object graph (own
// data properties, dense elements, prototype links) of the Plain/Array/
// interpreted-Function objects reachable from the global and the registered
// scripts' gcthings into the registration block. Call after the top level
// has executed and before the wizer snapshot; forces a full GC first so the
// recorded addresses are tenured and stable. Read-only facts: the analysis
// consults them and every consumer still guards at runtime.
bool NightSnapshotCaptureHeap(JSContext* cx);

namespace night {
// Two-bit-stamp per-add SLOTS maintenance: check a property add against the
// receiver's predicted layout and clear the SLOTS bit on deviation. Call
// after the slot is assigned. `nfixed` is the receiver's numFixedSlots().
void NightAddPropCheck(JSObject* obj, JS::PropertyKey id, uint32_t slot,
                       uint32_t nfixed);

// Global-object write hooks, called from the engine's own property paths so
// that an INTERPRETED global write (a declined script, a generator, eval)
// blows exactly the fuses it invalidates: the value-conditional form for a
// data-slot store (a same-bits rewrite stays armed, as in the compiled
// handshake), the unconditional form for delete and redefinition.
void NightGlobalDataStore(JS::PropertyKey id, uint64_t valueBits);
void NightGlobalKeyBlow(JS::PropertyKey id);

// Blow the dynamic-code fuse: source text has been handed to the frontend,
// so a value of any type -- a BigInt in particular -- can now be minted by
// code the AOT analysis never saw. Called from ScriptSource::assignSource,
// the sole point every frontend compile from source passes through.
// Monotone and one-way; there is no un-blow.
void NightBlowDynamicCodeFuse();

// The registered script graph IS what the analysis scanned, so everything
// compiled up to and including it is accounted for: registration re-arms
// the fuse. Every compile after this point is genuinely novel source.
void NightRearmDynamicCodeFuse();

// Whether the shell is wizening: the program's top level running under
// --night-snapshot, whose objects become the image population. Set by the
// shell before the top level runs; cleared by NightSnapshotCaptureHeap
// before the snapshot freezes memory, so the resumed image never sees it.
bool NightWizening();
void NightSetWizening(bool on);

// The fixed-slot floor of an object constructed while wizening. An image
// object never meets the compiled construct path, which sizes an
// allocation to the analysis's full layout row; the interpreter sizes it
// by the ctor body's own property-count estimate (zero for a delegating
// ctor), and a fixed-slot count cannot grow afterwards, so a
// post-construction fill lands in dynamic slots and the object can never
// advance past its prefix key. One object kind above the engine's default
// (OBJECT4 -> OBJECT8) at 32 bytes per image object.
static constexpr size_t kWizenThisSlots = 8;
}  // namespace night
#endif

#ifdef ENABLE_JS_NIGHTMONKEY_INPROCESS
// In-process AOT compilation (wasm shell under wasm-jit-runner): compile
// `script`'s tree and arm dispatch into the injected bodies. One batch per
// process; later calls are no-ops. Failures degrade to the interpreter
// (returning true); false means a real error (pending exception).
bool CompileInProcess(JSContext* cx, JS::Handle<JSScript*> script);
#endif

}  // namespace js

#endif  // night_runtime_Night_h
