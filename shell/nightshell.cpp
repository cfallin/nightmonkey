/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// The NightMonkey shell: the SpiderMonkey JS shell (linked as libjsshell)
// with the night runtime's engine hooks installed and the shell extension
// that drives the two compilation flows.
//
// - Snapshot flow (--night-snapshot, always on under wizer initialization):
//   every script the shell compiles is registered as an AOT root and the
//   post-top-level heap is captured; the `nightmonkey` host binary
//   transforms the wizer snapshot, and the resumed image activates the
//   compiled bodies and calls the program's global main().
// - In-process flow (--night-inprocess, test-only, under wasm-jit-runner):
//   the positional script (or -e code without one) is compiled inside the
//   running shell and dispatched into the injected bodies.

#include <optional>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "jsapi.h"        // JS_DefineFunction
#include "jsfriendapi.h"  // js::RunJobs

#include "js/CallAndConstruct.h"  // JS_CallFunctionName
#include "js/CallArgs.h"
#include "js/Value.h"
#include "runtime/Night.h"
#include "runtime/NightHooks.h"
#include "runtime/NightRegistration.h"
#include "shell/jsoptparse.h"
#include "shell/jsshell.h"
#include "vm/JSContext.h"

#ifdef JS_SHELL_WIZER
#  include <wizer.h>
#endif

using namespace js;
using namespace js::shell;
using js::cli::OptionParser;

static bool enableNightSnapshot = false;
#ifdef ENABLE_JS_NIGHTMONKEY_INPROCESS
static bool enableNightInprocess = false;
#endif

static bool AddOptions(OptionParser& op) {
  if (!op.addBoolOption('\0', "night-snapshot",
                        "Register the script as an AOT snapshot root and "
                        "capture the post-top-level heap, for wizening by "
                        "the nightmonkey compiler")) {
    return false;
  }
#ifdef ENABLE_JS_NIGHTMONKEY_INPROCESS
  if (!op.addBoolOption('\0', "night-inprocess",
                        "AOT-compile the positional script (or -e code) "
                        "in-process and dispatch into the injected wasm "
                        "bodies (requires the wasm-jit-runner hostcalls)")) {
    return false;
  }
#endif
  return true;
}

static bool OptionsParsed(OptionParser& op) {
  enableNightSnapshot = op.getBoolOption("night-snapshot");
  night::NightSetWizening(enableNightSnapshot);
#ifdef ENABLE_JS_NIGHTMONKEY_INPROCESS
  enableNightInprocess = op.getBoolOption("night-inprocess");
#endif
  return true;
}

// nightTierEnabled(): true iff the AOT tier is active in this shell
// (--night-inprocess, or an activated AOT snapshot). Tests that cannot run
// under the tier are listed in tests/*-excludes.txt rather than consulting
// this, so it is for ad-hoc scripts.
static bool NightTierEnabled(JSContext* cx, unsigned argc, JS::Value* vp) {
  JS::CallArgs args = JS::CallArgsFromVp(argc, vp);
  bool enabled = night::gNightActivated;
#ifdef ENABLE_JS_NIGHTMONKEY_INPROCESS
  enabled = enabled || enableNightInprocess;
#endif
  args.rval().setBoolean(enabled);
  return true;
}

static bool DefineGlobals(JSContext* cx, JS::HandleObject global) {
  return JS_DefineFunction(cx, global, "nightTierEnabled", NightTierEnabled, 0,
                           0) != nullptr;
}

static bool WantsFullParse(bool primary) {
  if (enableNightSnapshot) {
    return true;
  }
#ifdef ENABLE_JS_NIGHTMONKEY_INPROCESS
  if (enableNightInprocess && primary) {
    return true;
  }
#endif
  return false;
}

static bool ScriptCompiled(JSContext* cx, JS::HandleScript script,
                           bool primary) {
  if (enableNightSnapshot) {
    if (!JS::NightRegisterRoot(cx, script, /* executedAtInit = */ true)) {
      return false;
    }
    if (!NightSnapshotCaptureExtras(cx, script)) {
      return false;
    }
  }
#ifdef ENABLE_JS_NIGHTMONKEY_INPROCESS
  if (enableNightInprocess && primary) {
    if (!CompileInProcess(cx, script)) {
      return false;
    }
  }
#endif
  return true;
}

static bool ScriptExecuted(JSContext* cx, JS::HandleScript script,
                           bool primary) {
  // The heap the top level just built is the analysis oracle; capture it
  // before the wizer snapshot freezes memory.
  if (enableNightSnapshot && !NightSnapshotCaptureHeap(cx)) {
    return false;
  }
  return true;
}

static bool ContextCreated(JSContext* cx) {
  night::NightInstallHooks(cx->runtime());
  return true;
}

static const ShellExtension kExtension = {
    AddOptions,     OptionsParsed,  ContextCreated, DefineGlobals,
    WantsFullParse, ScriptCompiled, ScriptExecuted,
};

static void Install() { SetShellExtension(&kExtension); }

#ifdef JS_SHELL_WIZER

static std::optional<JSAndShellContext> wizenedContext;

static void WizerInit() {
  Install();
  // Wizening a NightMonkey shell exists only to produce an AOT snapshot, so
  // the snapshot root registration is always on: the top level runs here,
  // during wizening, and the resumed snapshot calls the program's main().
  const int argc = 2;
  char* argv[3] = {strdup("js"), strdup("--night-snapshot"), nullptr};

  auto ret = ShellMain(argc, argv, /* retainContext = */ true);
  if (!ret.is<JSAndShellContext>()) {
    fprintf(stderr, "Could not execute shell main during Wizening!\n");
    abort();
  }
  wizenedContext = std::move(ret.as<JSAndShellContext>());
}

WIZER_INIT(WizerInit);

int main(int argc, char** argv) {
  if (!wizenedContext) {
    Install();
    return ShellMain(argc, argv, /* retainContext = */ false).as<int>();
  }

  JSContext* cx = wizenedContext.value().cx;
  JS::RootedObject glob(cx, wizenedContext.value().glob);
  JSAutoRealm ar(cx, glob);

  // Activate the compiled bodies of a transformed snapshot; an untransformed
  // one simply runs interpreted.
  JS::NightActivate(cx);

  JS::Rooted<JS::Value> ret(cx);
  if (!JS_CallFunctionName(cx, glob, "main", JS::HandleValueArray::empty(),
                           &ret)) {
    fprintf(stderr, "Failed to call main() in Wizened JS source!\n");
    abort();
  }
  // Drain the microtask queue, as the shell's own run loop does after every
  // script: a program whose main() leaves promise continuations queued would
  // otherwise exit with them unrun.
  RunJobs(cx);
  return 0;
}

#else  // !JS_SHELL_WIZER

int main(int argc, char** argv) {
  Install();
  return ShellMain(argc, argv, /* retainContext = */ false).as<int>();
}

#endif
