/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80: */

#include "runtime/NightHooks.h"

#include "runtime/Night.h"
#include "runtime/NightEntry.h"
#include "runtime/NightEnv.h"
#include "runtime/NightObjectWord.h"
#include "runtime/NightRegExp.h"
#include "runtime/NightStack.h"
#include "vm/GeneratorObject.h"
#include "vm/Interpreter.h"
#include "vm/NativeObject.h"

using namespace js;
using namespace js::night;

static uint32_t BumpSiteOf(JS::ExternalObjectMutation why) {
  switch (why) {
    case JS::ExternalObjectMutation::ToDictionary:
      return NightBumpSite::ToDictionary;
    case JS::ExternalObjectMutation::ChangeProperty:
      return NightBumpSite::ChangeProperty;
    case JS::ExternalObjectMutation::ChangeCustomDataProp:
      return NightBumpSite::ChangeCustomDataProp;
    case JS::ExternalObjectMutation::RemoveProperty:
      return NightBumpSite::RemoveProperty;
    case JS::ExternalObjectMutation::FreezeOrSeal:
      return NightBumpSite::FreezeOrSeal;
    case JS::ExternalObjectMutation::Swap:
      return NightBumpSite::ObjectSwap;
    case JS::ExternalObjectMutation::ObjectFlagChange:
      return NightBumpSite::ObjectFlagChange;
    case JS::ExternalObjectMutation::StoredValue:
      return NightBumpSite::StoredValue;
  }
  return 0;
}

// NightMonkey keeps its state process-wide (one runtime per wasm instance),
// so the per-context state is unused; the slot is there for a tier that
// keeps state per context.
static void* NightNewContext(JSContext* cx) { return nullptr; }

static void NightDestroyContext(JSContext* cx, void* state) {}

static void ObjectDemoted(JSContext* cx, JSObject* obj, uintptr_t oldWord,
                          JS::ExternalObjectMutation why) {
  NightNoteDemotion(oldWord, BumpSiteOf(why));
}

static void PropertyAdded(JSContext* cx, NativeObject* obj, JS::PropertyKey id,
                          uint32_t slot, uint32_t numFixedSlots) {
  NightAddPropCheck(obj, id, slot, numFixedSlots);
}

static void GlobalKeyChanged(JSContext* cx, JS::PropertyKey id) {
  NightGlobalKeyBlow(id);
}

static void GlobalDataStored(JSContext* cx, JS::PropertyKey id,
                             uint64_t valueBits) {
  NightGlobalDataStore(id, valueBits);
}

static void GlobalLexicalShadowAdded(JSContext* cx, uint64_t idBits) {
  night_runtime_global_lexical_shadow_added(uintptr_t(idBits));
}

static JS::ExternalEnterStatus Convert(EnterNightStatus status) {
  switch (status) {
    case EnterNightStatus::Error:
      return JS::ExternalEnterStatus::Error;
    case EnterNightStatus::Ok:
      return JS::ExternalEnterStatus::Ok;
    case EnterNightStatus::NotEntered:
      break;
  }
  return JS::ExternalEnterStatus::NotEntered;
}

static JS::ExternalEnterStatus EnterScript(JSContext* cx, RunState& state) {
  return Convert(MaybeEnterNight(cx, state));
}

static JS::ExternalEnterStatus EnterCall(JSContext* cx, const CallArgs& args,
                                         JSScript* script, bool constructing) {
  return Convert(MaybeEnterNight(cx, args, script, constructing));
}

static bool IsForeignGenerator(JSContext* cx, AbstractGeneratorObject* gen) {
  return IsNightResumable(gen);
}

static JS::ExternalEnterStatus ResumeGenerator(
    JSContext* cx, JS::Handle<AbstractGeneratorObject*> gen,
    JS::HandleValue arg, JS::HandleValue resumeKind,
    JS::MutableHandleValue rval) {
  return Convert(EnterNightResume(cx, gen, arg, resumeKind, rval));
}

static void TraceRoots(JSContext* cx, JSTracer* trc) {
  // The AOT value stack is the sole root region for compiled frames (their
  // args/this/locals/operands are boxed JS::Values living there, not in the
  // GC heap); the engine calls this on every GC, minor and major, so a
  // nursery collection forwards the nursery pointers it holds.
  nightrt::NightStack& stack = nightrt::TheNightStack();
  if (stack.valid()) {
    stack.trace(trc);
  }
}

static void SourceAssigned(JSContext* cx) { NightBlowDynamicCodeFuse(); }

JS::ExternalCompilerHooks js::night::gNightHooks = {
    /* newContext */ NightNewContext,
    /* destroyContext */ NightDestroyContext,
    /* objectDemoted */ ObjectDemoted,
    /* storeClearMask */ kStoreClearMask,
    /* storeNonNumberClearMask */ kStoreNonNumberClearMask,
    /* propertyAdded */ PropertyAdded,
    /* globalKeyChanged */ GlobalKeyChanged,
    /* globalDataStored */ GlobalDataStored,
    /* globalLexicalShadowAdded */ GlobalLexicalShadowAdded,
    /* enterScript */ EnterScript,
    /* enterCall */ EnterCall,
    /* isForeignGenerator */ IsForeignGenerator,
    /* resumeGenerator */ ResumeGenerator,
    /* traceRoots */ TraceRoots,
    /* sourceAssigned */ SourceAssigned,
    /* minConstructorThisSlots */ 0,
    /* regexpMatch */ irregexp::TryNightRegexMatch,
};

void js::night::NightInstallHooks(JSRuntime* rt) {
  JS::SetExternalCompilerHooks(rt, &gNightHooks);
}
