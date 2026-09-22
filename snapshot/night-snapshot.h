/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#ifndef js_night_snapshot_night_snapshot_h
#define js_night_snapshot_night_snapshot_h

#include <stdint.h>

#include "compiler/night-compiler.h"

#ifdef __cplusplus
extern "C" {
#endif

// In-process live-heap walk (wasm32 only): read the JSScript graph rooted at
// the NightRegistration block's roots directly out of this process's memory,
// producing the Source graph night_inproc_build consumes.
typedef void night_snapshot_walk_t;

// Walk from the registration block at `reg_addr` (the address of
// js::night::gNightRegistration), plus `n_extra` extra BaseScript roots
// (self-hosted builtins joining the batch; their trees must already be in
// the registration digest -- see js::night::NightAppendDigestTree). Null on
// failure (message on stderr); free with night_snapshot_walk_delete.
night_snapshot_walk_t* night_snapshot_walk_live(
    uint32_t reg_addr, const uint32_t* extra_script_addrs, uint32_t n_extra);

// The walked Source graph (borrowed from the handle; valid until delete).
night_source_t* night_snapshot_walk_source(night_snapshot_walk_t* walk);
night_source_object_t night_snapshot_walk_root(night_snapshot_walk_t* walk);

// Source id of extra root `i` (the walker dedups by address, so two extras
// can share an id).
night_source_object_t night_snapshot_walk_extra_root(
    night_snapshot_walk_t* walk, uint32_t i);

// BaseScript address of the walked script with the given source id (the
// nightFuncIndex patch target); 0 if the id is not a walked script.
uint32_t night_snapshot_walk_script_addr(night_snapshot_walk_t* walk,
                                         uint32_t source_id);

void night_snapshot_walk_delete(night_snapshot_walk_t* walk);

#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // js_night_snapshot_night_snapshot_h
