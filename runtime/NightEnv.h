/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#ifndef night_runtime_NightEnv_h
#define night_runtime_NightEnv_h

#include <stddef.h>
#include <stdint.h>

#include "js/TypeDecls.h"

namespace js {
namespace night {

// The AOT runtime environment night_runtime_install_env consumes: the
// serialized-table pointers and the reserved region bases.
//
// NIGHT_ENV_REGIONS is the single source of truth for that wire. Generated
// from it, in this order: `struct NightEnvDesc` and the `NightEnvRegion`
// indices below, the snapshot flow's `NightRegistration::regionTable`, and
// -- via night-compiler's build.rs, which parses this macro -- the Rust
// `RegionWords` struct both writers fill in. Entries may only be appended,
// and any change to the list needs a `NightAotAbiVersion` bump.
//
// The second argument is the wire kind, which is the one thing the two
// flows disagree about:
//   Table -- the start of a serialized table. Snapshot flow: an absolute
//            linear-memory address (the tool wrote the table into memory it
//            claimed). In-process flow: a byte OFFSET into the env_desc
//            buffer, which the reader rebases onto that buffer's address.
//   Len   -- a byte length or region size; identical in both flows.
//   Addr  -- an absolute linear-memory address in both flows.
#define NIGHT_ENV_REGIONS(_) \
  _(atomPtr, Table)          \
  _(atomLen, Len)            \
  _(gbindPtr, Table)         \
  _(gbindLen, Len)           \
  _(layoutPtr, Table)        \
  _(layoutLen, Len)          \
  _(fusePtr, Table)          \
  _(fuseLen, Len)            \
  _(regexPtr, Table)         \
  _(regexLen, Len)           \
  _(gslotsPtr, Addr)         \
  _(propicPtr, Addr)         \
  _(propicLen, Len)          \
  _(propicGenPtr, Addr)      \
  _(layoutCellsPtr, Addr)    \
  _(callCellsPtr, Addr)      \
  _(callCellsLen, Len)       \
  _(allocCellsPtr, Addr)     \
  _(allocCellsLen, Len)      \
  _(intrinsicCellsPtr, Addr) \
  _(intrinsicCellsLen, Len)  \
  _(fuseCellsPtr, Addr)      \
  _(megaGetPtr, Addr)        \
  _(megaSetPtr, Addr)        \
  _(mathNativesPtr, Addr)    \
  _(appendCachePtr, Addr)    \
  _(accessorCachePtr, Addr)

enum class NightEnvRegion : uint32_t {
#define NIGHT_ENV_REGION_ENUM(name, kind) name,
  NIGHT_ENV_REGIONS(NIGHT_ENV_REGION_ENUM)
#undef NIGHT_ENV_REGION_ENUM
      Count,
};

static constexpr uint32_t NightEnvRegionCount = uint32_t(NightEnvRegion::Count);

enum class NightEnvRegionKind { Table, Len, Addr };

struct NightEnvDesc {
#define NIGHT_ENV_REGION_FIELD(name, kind) uint32_t name = 0;
  NIGHT_ENV_REGIONS(NIGHT_ENV_REGION_FIELD)
#undef NIGHT_ENV_REGION_FIELD
};

// The in-process env_desc wire (built by night-compiler's
// `wasm::inprocess`, read by CompileInProcess): a header of
// `NightEnvDescHeaderWords` little-endian u32 words,
//   0 abiVersion   -- NightAotAbiVersion
//   1 regionCount  -- NightEnvRegionCount
//   2 strlitOff    -- byte offset of the string-literal blob in this buffer
//   3 strlitLen    -- its length (0 = none)
//   4 strlitAddr   -- absolute address to copy it to (0 = none)
// then `regionCount` words in NIGHT_ENV_REGIONS order, then the serialized
// tables the Table words point into. The strlit words have no NightEnvDesc
// field: the blob is consumed by the reader itself, not by install_env.
static constexpr uint32_t NightEnvDescHeaderWords = 5;

// Interpret one in-process region word: a Table word is a byte offset into
// the env_desc buffer at `descBase`, every other kind is already what it
// says (an absolute address, or a length).
inline uint32_t NightEnvRegionValue(NightEnvRegionKind kind, uint32_t word,
                                    uint32_t descBase) {
  return kind == NightEnvRegionKind::Table ? descBase + word : word;
}

#ifdef ENABLE_JS_NIGHTMONKEY
// Resolve a dotted global path ("Array.prototype.forEach") to a JSFunction;
// a final "@@name" component is a well-known-symbol key, "%Name%" a
// self-hosting intrinsic. Null (no pending exception) when unresolved.
JSFunction* ResolveGlobalPath(JSContext* cx, const char* path, size_t len);
#endif

}  // namespace night
}  // namespace js

// Install the runtime side of the AOT environment described by `env`:
// atom/global-binding tables, region-base globals and their GC-zeroing
// callbacks, host-constant slots, builtin/math/string identity cells,
// TA/args/strlit inline metadata, the regex matcher table, and the AOT stack
// limit. Returns false with a pending/reported exception on failure.
// C linkage to match the night_runtime_* ABI surface (not itself a wasm
// export).
extern "C" bool night_runtime_install_env(JSContext* cx,
                                          const js::night::NightEnvDesc& env);

// Blow every gname/binding value fuse and forbid re-arming. Required whenever
// interpreted code can write globals without going through the compiled
// hooks (any interpreter coverage: skipped scripts, eval, shell evaluate).
extern "C" void night_runtime_distrust_global_fuses();

// Arm the gname fuses from the live global values (snapshot activation
// for executedAtInit roots, where the predicted writes ran pre-snapshot).
// Call after night_runtime_install_env.
extern "C" void night_runtime_arm_gname_fuses_from_live(JSContext* cx);

// A global lexical binding was just added for the name whose PropertyKey raw
// bits are `idBits`, shadowing any same-named global-object binding: the
// resolved gname row/fuses for that name must be invalidated (the next
// read/write re-resolves, sees the shadow, and stays on the generic path).
// No-op when AOT is not active.
extern "C" void night_runtime_global_lexical_shadow_added(uintptr_t idBits);

#endif  // night_runtime_NightEnv_h
