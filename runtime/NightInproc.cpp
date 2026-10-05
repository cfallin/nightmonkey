/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80: */

// In-process AOT compilation (the --night-inprocess shell flag, under
// wasm-jit-runner): register the script as an AOT root, record the
// self-hosted roots and regex programs as the snapshot flow does, and ask the
// host to compile (the night_compile hostcall). The host walks this
// instance's live heap, compiles the tree natively, and injects the bodies;
// the stub then installs the runtime environment and arms each compiled
// script's nightFuncIndex. Any failure past registration degrades to the
// interpreter (fatal under NIGHTMONKEY_DEBUG).

#include "mozilla/Assertions.h"

#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "runtime/Night.h"
#include "runtime/NightEnv.h"
#include "runtime/NightHelperList.h"
#include "runtime/NightInprocHost.h"
#include "runtime/NightRegistration.h"
#include "vm/JSContext.h"
#include "vm/JSScript.h"

#include "vm/JSScript-inl.h"

using namespace js;

// The allocator the host's night_compile calls back for the compiler's
// regions and the buffers it returns: zeroed, 8-aligned, never freed (the
// regions live for the rest of the process, matching the reserved-region
// discipline).
extern "C" __attribute__((export_name("night_inproc_alloc"))) uint32_t
night_inproc_alloc(uint32_t size) {
  void* p = calloc(1, size_t(size) + 8);
  if (!p) {
    return 0;
  }
  uintptr_t addr = reinterpret_cast<uintptr_t>(p);
  return static_cast<uint32_t>((addr + 7) & ~uintptr_t(7));
}

// A failed batch leaves every script interpreted, which every test then
// passes: under NIGHT_INPROC_STRICT (the test harnesses' shell wrapper sets
// it) that is fatal, as it always is in a debug build.
static bool InprocFail(const char* what) {
  fprintf(stderr, "night: inprocess: %s; staying interpreted\n", what);
#ifdef NIGHTMONKEY_DEBUG
  MOZ_CRASH("in-process AOT compilation failed");
#endif
  const char* strict = getenv("NIGHT_INPROC_STRICT");
  if (strict && strict[0] && strict[0] != '0') {
    fflush(stderr);
    abort();
  }
  return true;
}

// Install the environment from an env_desc buffer (which the installed
// tables alias, so it must stay live) and arm each compiled script: the
// script map is `nscripts` {BaseScript address, table index} pairs. Returns
// false only on an engine error; a malformed descriptor degrades to the
// interpreter.
static bool InstallAndArm(JSContext* cx, const uint8_t* desc, uint32_t descLen,
                          const uint32_t* scriptMap, uint32_t nscripts) {
  // The env_desc wire is documented at NightEnvDescHeaderWords in
  // NightEnv.h: a fixed header, then one word per NIGHT_ENV_REGIONS entry.
  // Check the version and the region count the same way the external
  // reader checks the layout descriptor -- a silently shifted word here is
  // a wrong region base, which no guard downstream can catch.
  auto word = [&](uint32_t i) {
    uint32_t w;
    memcpy(&w, desc + 4 * i, sizeof(w));
    return w;
  };
  if (descLen < night::NightEnvDescHeaderWords * sizeof(uint32_t)) {
    return InprocFail("environment descriptor too short");
  }
  if (word(0) != night::NightAotAbiVersion ||
      word(1) != night::NightEnvRegionCount) {
    fprintf(stderr,
            "night: inprocess: environment descriptor is ABI v%u with %u "
            "regions, engine expects v%u with %u\n",
            word(0), word(1), night::NightAotAbiVersion,
            night::NightEnvRegionCount);
    return InprocFail("environment descriptor ABI mismatch");
  }
  if (descLen < (night::NightEnvDescHeaderWords + night::NightEnvRegionCount) *
                    sizeof(uint32_t)) {
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

  if (!night_runtime_install_env(cx, env)) {
    return false;
  }
  // Interpreted code (skipped scripts, eval, shell evaluate, -f prologues)
  // writes globals through the engine's own property paths, which run the
  // fuse hooks (NightGlobalDataStore / NightGlobalKeyBlow), so the value
  // fuses are as trustworthy here as in a snapshot (NightRegistration.cpp).

  for (uint32_t i = 0; i < nscripts; i++) {
    auto* base = reinterpret_cast<js::BaseScript*>(
        static_cast<uintptr_t>(scriptMap[2 * i]));
    base->setExternalTierWord(scriptMap[2 * i + 1]);
  }
  return true;
}

static const char* gInprocOptions = nullptr;

void js::SetInprocOptions(const char* options) { gInprocOptions = options; }

static uint32_t Addr(const void* p) {
  return static_cast<uint32_t>(reinterpret_cast<uintptr_t>(p));
}

// The night_compile request reads kNightHelpers as {name, funcptr, sig}
// words (see wasm-jit-runner/src/compile.rs).
#ifdef __wasm32__
static_assert(sizeof(night::NightHelperEntry) == 12 &&
                  offsetof(night::NightHelperEntry, name) == 0 &&
                  offsetof(night::NightHelperEntry, funcptr) == 4 &&
                  offsetof(night::NightHelperEntry, sig) == 8,
              "night_compile reads the helper table as three u32 words");
#endif

// The host compiles: record the self-hosted roots and regex programs in the
// registration block exactly as the snapshot flow does, seal the addresses,
// and make one hostcall. The host walks this instance's memory, compiles,
// injects the bodies and returns the env_desc and the script map, both in
// buffers from night_inproc_alloc.
static bool CompileInHost(JSContext* cx, JS::Handle<JSScript*> script) {
  // Delazifies the self-hosted trees and compiles regexes, so it may GC.
  if (!NightSnapshotCaptureExtras(cx, script)) {
    return InprocFail("recording the self-hosted roots and regex programs failed");
  }
  // The walk reads the registration block's raw addresses: re-derive them
  // from the traced copies, as the snapshot flow does before its capture
  // (NightRegistration.h).
  if (!night::NightSealSnapshotAddresses(cx)) {
    return InprocFail("sealing the registration addresses failed");
  }

  uint32_t req[night::kNightCompileRequestWords] = {
      night::kNightCompileRequestVersion,
      Addr(&night::gNightRegistration),
      Addr(night::kNightHelpers),
      static_cast<uint32_t>(night::kNightHelperCount),
      Addr(gInprocOptions),
  };
  uint32_t resp[night::kNightCompileResponseWords] = {};
  if (night::InprocHostCompile(req, sizeof(req), resp) != 0) {
    return InprocFail("night_compile hostcall failed");
  }
  const uint8_t* desc =
      reinterpret_cast<const uint8_t*>(static_cast<uintptr_t>(resp[0]));
  const uint32_t* scriptMap =
      reinterpret_cast<const uint32_t*>(static_cast<uintptr_t>(resp[2]));
  if (!InstallAndArm(cx, desc, resp[1], scriptMap, resp[3])) {
    return false;
  }
#ifdef NIGHTMONKEY_DEBUG
  fprintf(stderr,
          "night: inprocess batch (host): %u scripts armed, %u blobs, table "
          "base %u\n",
          resp[3], resp[4], resp[5]);
#endif
  night::gNightActivated = true;
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

  return CompileInHost(cx, script);
}
