/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// In-process AOT compilation (the --night-inprocess shell flag, under
// wasm-jit-runner): register the script as an AOT root, walk the live heap
// with the night-snapshot reader, compile the tree into function blobs with
// night_inproc_build, inject them into the running instance via the runner
// hostcalls, install the runtime environment, and arm each compiled script's
// nightFuncIndex. Any failure past registration degrades to the interpreter
// (fatal under NIGHTMONKEY_DEBUG).

#include "mozilla/Assertions.h"

#include <set>
#include <stdio.h>
#include <stdlib.h>
#include <string>
#include <string.h>
#include <utility>
#include <vector>

#include "js/GCVector.h"
#include "compiler/night-compiler.h"
#include "runtime/Night.h"
#include "runtime/NightEnv.h"
#include "runtime/NightHelperList.h"
#include "runtime/NightInprocHost.h"
#include "runtime/NightRegistration.h"
#include "runtime/NightSnapshotExtras.h"
#include "snapshot/night-snapshot.h"
#include "vm/JSContext.h"
#include "vm/JSFunction.h"
#include "vm/JSScript.h"

#include "vm/JSScript-inl.h"

using namespace js;

// night_alloc_fn: zeroed, 8-aligned, never freed (the regions live for the
// rest of the process, matching the reserved-region discipline).
static uint32_t InprocAlloc(size_t size) {
  void* p = calloc(1, size + 8);
  if (!p) {
    return 0;
  }
  uintptr_t addr = reinterpret_cast<uintptr_t>(p);
  return static_cast<uint32_t>((addr + 7) & ~uintptr_t(7));
}

static bool InprocFail(const char* what) {
  fprintf(stderr, "night: inprocess: %s; staying interpreted\n", what);
#ifdef NIGHTMONKEY_DEBUG
  MOZ_CRASH("in-process AOT compilation failed");
#endif
  return true;
}

bool js::CompileInProcess(JSContext* cx, JS::Handle<JSScript*> script) {
  // Single batch: only the first registered tree compiles; everything else
  // (eval, -f prologues, other realms) stays interpreted.
  if (night::gNightActivated || night::gNightRegistration.numRoots != 0) {
    return true;
  }

  if (!JS::NightRegisterRoot(cx, script, /* executedAtInit = */ false)) {
    return false;
  }

  int32_t tableBase = night::InprocHostTableSize();
  if (tableBase < 0) {
    return InprocFail(
        "wasm_table_size hostcall failed (not running under "
        "wasm-jit-runner?)");
  }

  // Self-hosted builtins join the batch: resolve against the live global,
  // delazify each tree, and add it to the registration digest so the walker
  // can read it.
  JS::RootedVector<JSScript*> shScripts(cx);
  std::vector<const char*> shPaths;
  if (!night::ResolveSelfHostedRoots(cx, &shScripts, shPaths)) {
    return InprocFail("selfhosted resolution failed");
  }

  // Regex literal programs (user tree + self-hosted trees). May GC; done
  // before the walk takes raw heap addresses.
  std::set<std::pair<std::u16string, uint32_t>> regexSeen;
  std::vector<night::NightRegexProgram> regexPrograms;
  if (!night::CollectRegexPrograms(cx, script, regexSeen, regexPrograms)) {
    return InprocFail("regex collection failed");
  }
  for (size_t i = 0; i < shScripts.length(); i++) {
    JS::Rooted<JSScript*> sh(cx, shScripts[i]);
    if (!night::CollectRegexPrograms(cx, sh, regexSeen, regexPrograms)) {
      return InprocFail("regex collection failed");
    }
  }

  std::vector<uint32_t> shAddrs;
  for (size_t i = 0; i < shScripts.length(); i++) {
    shAddrs.push_back(
        static_cast<uint32_t>(reinterpret_cast<uintptr_t>(shScripts[i].get())));
  }

  // The walk reads the registration block's raw addresses, and the
  // delazification and regex compilation above can GC. Re-derive the mirror
  // from the traced copies first, exactly as the snapshot flow does before
  // its capture (NightRegistration.h).
  if (!night::NightSealSnapshotAddresses(cx)) {
    return InprocFail("sealing the registration addresses failed");
  }

  night_snapshot_walk_t* walk = night_snapshot_walk_live(
      static_cast<uint32_t>(
          reinterpret_cast<uintptr_t>(&night::gNightRegistration)),
      shAddrs.empty() ? nullptr : shAddrs.data(),
      static_cast<uint32_t>(shAddrs.size()));
  if (!walk) {
    return InprocFail("live-heap walk failed");
  }

  night_source_t* walkSource = night_snapshot_walk_source(walk);
  for (size_t i = 0; i < shPaths.size(); i++) {
    night_source_mark_selfhosted(
        walkSource,
        night_snapshot_walk_extra_root(walk, static_cast<uint32_t>(i)),
        reinterpret_cast<const uint8_t*>(shPaths[i]),
        static_cast<uint32_t>(strlen(shPaths[i])));
  }
  for (const night::NightRegexProgram& rp : regexPrograms) {
    night_source_add_regex_program(
        walkSource, reinterpret_cast<const uint16_t*>(rp.pattern.data()),
        static_cast<uint32_t>(rp.pattern.size()), rp.flags,
        rp.latin1.empty() ? nullptr : rp.latin1.data(),
        static_cast<uint32_t>(rp.latin1.size()),
        rp.twobyte.empty() ? nullptr : rp.twobyte.data(),
        static_cast<uint32_t>(rp.twobyte.size()), rp.numRegisters,
        rp.pairCount);
  }

  const char* names[night::kNightHelperCount];
  const char* sigs[night::kNightHelperCount];
  uint32_t funcptrs[night::kNightHelperCount];
  for (size_t i = 0; i < night::kNightHelperCount; i++) {
    names[i] = night::kNightHelpers[i].name;
    sigs[i] = night::kNightHelpers[i].sig;
    funcptrs[i] = night::kNightHelpers[i].funcptr;
  }

  night_inproc_out_t* out = night_inproc_build(
      walkSource, night_snapshot_walk_root(walk), names, sigs, funcptrs,
      static_cast<uint32_t>(night::kNightHelperCount),
      static_cast<uint32_t>(tableBase), InprocAlloc);
  if (!out) {
    night_snapshot_walk_delete(walk);
    return InprocFail("batch build failed");
  }

  uint32_t nblobs = night_inproc_num_blobs(out);
  std::vector<uint32_t> blobPtrs(nblobs), blobLens(nblobs), got(nblobs);
  for (uint32_t i = 0; i < nblobs; i++) {
    blobPtrs[i] = static_cast<uint32_t>(
        reinterpret_cast<uintptr_t>(night_inproc_blob_ptr(out, i)));
    blobLens[i] = night_inproc_blob_len(out, i);
  }
  uint32_t nextern = night_inproc_num_externs(out);
  if (night::InprocHostAddFuncs(blobPtrs.data(), blobLens.data(), nblobs,
                                night_inproc_extern_indices(out), nextern,
                                got.data()) != 0) {
    night_snapshot_walk_delete(walk);
    night_inproc_delete(out);
    return InprocFail("wasm_add_funcs2 hostcall failed");
  }
  for (uint32_t i = 0; i < nblobs; i++) {
    if (got[i] != static_cast<uint32_t>(tableBase) + i) {
      fprintf(stderr,
              "night: inprocess: blob %u landed at table[%u], predicted %u\n",
              i, got[i], static_cast<uint32_t>(tableBase) + i);
      night_snapshot_walk_delete(walk);
      night_inproc_delete(out);
      return InprocFail("table index prediction mismatch");
    }
  }

  // The env_desc wire is documented at NightEnvDescHeaderWords in
  // NightEnv.h: a fixed header, then one word per NIGHT_ENV_REGIONS entry.
  // Check the version and the region count the same way the external
  // reader checks the layout descriptor -- a silently shifted word here is
  // a wrong region base, which no guard downstream can catch.
  const uint8_t* desc = night_inproc_env_desc_ptr(out);
  uint32_t descLen = night_inproc_env_desc_len(out);
  auto word = [&](uint32_t i) {
    uint32_t w;
    memcpy(&w, desc + 4 * i, sizeof(w));
    return w;
  };
  if (descLen < night::NightEnvDescHeaderWords * sizeof(uint32_t)) {
    night_snapshot_walk_delete(walk);
    return InprocFail("environment descriptor too short");
  }
  if (word(0) != night::NightAotAbiVersion ||
      word(1) != night::NightEnvRegionCount) {
    fprintf(stderr,
            "night: inprocess: environment descriptor is ABI v%u with %u "
            "regions, engine expects v%u with %u\n",
            word(0), word(1), night::NightAotAbiVersion,
            night::NightEnvRegionCount);
    night_snapshot_walk_delete(walk);
    return InprocFail("environment descriptor ABI mismatch");
  }
  if (descLen < (night::NightEnvDescHeaderWords + night::NightEnvRegionCount) *
                    sizeof(uint32_t)) {
    night_snapshot_walk_delete(walk);
    return InprocFail("environment descriptor truncated");
  }
  uint32_t descBase = static_cast<uint32_t>(reinterpret_cast<uintptr_t>(desc));

  // String-literal payload: copy into its reserved region before any
  // compiled code runs (bodies read literals at absolute addresses).
  uint32_t strlitOff = word(2);
  uint32_t strlitLen = word(3);
  uint32_t strlitAddr = word(4);
  if (strlitAddr && strlitLen) {
    memcpy(reinterpret_cast<void*>(static_cast<uintptr_t>(strlitAddr)),
           desc + strlitOff, strlitLen);
  }

  night::NightEnvDesc env;
#define NIGHT_INPROC_REGION_WORD(name, kind)                                  \
  env.name =                                                                  \
      night::NightEnvRegionValue(night::NightEnvRegionKind::kind,             \
                                 word(night::NightEnvDescHeaderWords +        \
                                      uint32_t(night::NightEnvRegion::name)), \
                                 descBase);
  NIGHT_ENV_REGIONS(NIGHT_INPROC_REGION_WORD)
#undef NIGHT_INPROC_REGION_WORD

  // The installed tables alias the descriptor buffer; `out` is deliberately
  // never deleted.
  if (!night_runtime_install_env(cx, env)) {
    night_snapshot_walk_delete(walk);
    return false;
  }
  // In-process mode always has interpreter coverage (skipped scripts, eval,
  // shell evaluate, -f prologues): interpreted global writes bypass the
  // compiled fuse hooks, so the value fuses cannot be trusted.
  night_runtime_distrust_global_fuses();

  uint32_t nscripts = night_inproc_num_scripts(out);
  uint32_t armed = 0;
  for (uint32_t i = 0; i < nscripts; i++) {
    uint32_t sid = night_inproc_script_source_id(out, i);
    uint32_t addr = night_snapshot_walk_script_addr(walk, sid);
    if (!addr) {
      fprintf(stderr,
              "night: inprocess: script source#%u has no heap address\n", sid);
      continue;
    }
    auto* base =
        reinterpret_cast<js::BaseScript*>(static_cast<uintptr_t>(addr));
    base->setExternalTierWord(static_cast<uint32_t>(tableBase) +
                            night_inproc_script_blob(out, i));
    armed++;
  }
  night_snapshot_walk_delete(walk);

#ifdef NIGHTMONKEY_DEBUG
  fprintf(stderr,
          "night: inprocess batch: %u scripts compiled (%u armed), %u blobs, "
          "table base %d\n",
          nscripts, armed, nblobs, tableBase);
#else
  (void)armed;
#endif
  night::gNightActivated = true;
  return true;
}
