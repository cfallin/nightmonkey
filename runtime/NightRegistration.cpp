/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80: */

#include "runtime/NightRegistration.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <vector>

#include "frontend/SourceNotes.h"  // SrcNoteIterator
#include "gc/GC.h"
#include "js/GCAPI.h"
#include "js/GCVector.h"
#include "js/HashTable.h"
#include "js/shadow/String.h"
#include "runtime/Night.h"
#include "runtime/NightContext.h"
#include "runtime/NightEnv.h"
#include "runtime/NightStack.h"
#include "vm/ArrayObject.h"
#include "vm/JSContext.h"
#include "vm/JSFunction.h"
#include "vm/JSScript.h"
#include "vm/NativeObject.h"
#include "vm/PlainObject.h"
#include "vm/RegExpObject.h"
#include "vm/Scope.h"
#include "vm/Shape.h"
#include "vm/SharedStencil.h"
#include "vm/StringType.h"

#include "vm/JSScript-inl.h"

namespace js {
namespace night {

NightRegistration gNightRegistration;
bool gNightActivated = false;

static NightLayoutDescriptor gNightLayoutDescriptor;

// Roots recorded in the registration block, kept alive (and, with compaction
// disabled, in place) for the lifetime of the runtime.
static PersistentRooted<GCVector<JSScript*, 0, SystemAllocPolicy>>*
    gNightRoots = nullptr;

void NightBuildLayoutDescriptor() {
  NightLayoutDescriptor& d = gNightLayoutDescriptor;
  d.abiVersion = NightAotAbiVersion;
  d.buildIdHash = 0;
  d.numFields = uint32_t(NightLayoutField::Count);
#define NIGHT_LAYOUT_FILL(name, expr) \
  d.fields[uint32_t(NightLayoutField::name)] = uint32_t(expr);
  NIGHT_LAYOUT_FIELDS(NIGHT_LAYOUT_FILL)
#undef NIGHT_LAYOUT_FILL
}

// Eagerly delazify every function script reachable from `script` so the
// snapshot contains bytecode for the whole tree, collecting the scripts.
static bool DelazifyTree(JSContext* cx, JS::Handle<JSScript*> script,
                         GCVector<JSScript*, 0, SystemAllocPolicy>& scripts) {
  Rooted<GCVector<JSScript*, 0, SystemAllocPolicy>> worklist(cx);
  if (!worklist.append(script)) {
    return false;
  }
  Rooted<JSScript*> current(cx);
  Rooted<JSFunction*> fun(cx);
  while (!worklist.empty()) {
    current = worklist.popCopy();
    if (!scripts.append(current)) {
      return false;
    }
    for (JS::GCCellPtr thing : current->gcthings()) {
      if (!thing.is<JSObject>()) {
        continue;
      }
      JSObject* obj = &thing.as<JSObject>();
      if (!obj->is<JSFunction>()) {
        continue;
      }
      fun = &obj->as<JSFunction>();
      if (!fun->isInterpreted()) {
        continue;
      }
      JSScript* inner = JSFunction::getOrCreateScript(cx, fun);
      if (!inner) {
        return false;
      }
      if (!worklist.append(inner)) {
        return false;
      }
    }
  }
  return true;
}

// Digest format (little-endian u32 unless noted):
//   u32 numScripts
//   per script: u32 scriptAddr, u32 ngcthings, u8 kinds[ngcthings]
//     (JS::TraceKind per gcthing entry, 0xff for a null entry; padded to 4)
//   u32 numScopes
//   per scope: u32 scopeAddr, u32 numBindings,
//     per binding: u32 nameAtomAddr (0 for elided), u32 isVar,
//                  u32 hasEnvSlot, u32 slot
//   u32 numScripts (source positions, diagnostics only: the visualizer)
//   per script: u32 scriptAddr, u32 lineno, u32 column (one-origin),
//     u32 sourceStart, u32 sourceEnd, u32 numEntries,
//     per entry: u32 pc, u32 line, u32 column -- the position from that pc
//     on, at each source note that moves it (as PCToLineNumber reads them)
static void AppendU32(std::vector<uint8_t>& out, uint32_t v) {
  out.push_back(uint8_t(v));
  out.push_back(uint8_t(v >> 8));
  out.push_back(uint8_t(v >> 16));
  out.push_back(uint8_t(v >> 24));
}

static bool BuildDigest(
    JSContext* cx, const GCVector<JSScript*, 0, SystemAllocPolicy>& scripts,
    std::vector<uint8_t>& out) {
  out.clear();
  AppendU32(out, uint32_t(scripts.length()));
  // Scopes reachable from any script's gcthings, plus enclosing chains.
  Rooted<GCVector<Scope*, 0, SystemAllocPolicy>> scopes(cx);
  HashSet<Scope*, DefaultHasher<Scope*>, SystemAllocPolicy> seenScopes;
  auto addScope = [&](Scope* scope) -> bool {
    auto p = seenScopes.lookupForAdd(scope);
    if (p) {
      return true;
    }
    return seenScopes.add(p, scope) && scopes.append(scope);
  };
  for (JSScript* script : scripts) {
    AppendU32(out, uint32_t(reinterpret_cast<uintptr_t>(script)));
    auto things = script->gcthings();
    AppendU32(out, uint32_t(things.Length()));
    for (JS::GCCellPtr thing : things) {
      out.push_back(thing ? uint8_t(thing.kind()) : 0xff);
      if (thing && thing.is<Scope>()) {
        if (!addScope(&thing.as<Scope>())) {
          return false;
        }
      }
    }
    while (out.size() % 4 != 0) {
      out.push_back(0);
    }
  }
  // Close over enclosing chains.
  for (size_t i = 0; i < scopes.length(); i++) {
    if (Scope* enclosing = scopes[i]->enclosing()) {
      if (!addScope(enclosing)) {
        return false;
      }
    }
  }
  AppendU32(out, uint32_t(scopes.length()));
  for (Scope* scope : scopes) {
    AppendU32(out, uint32_t(reinterpret_cast<uintptr_t>(scope)));
    size_t countPos = out.size();
    AppendU32(out, 0);
    uint32_t n = 0;
    for (BindingIter bi(scope); bi; bi++) {
      JSAtom* name = bi.name();
      BindingLocation loc = bi.location();
      bool hasEnvSlot = loc.kind() == BindingLocation::Kind::Environment;
      AppendU32(out, uint32_t(reinterpret_cast<uintptr_t>(name)));
      AppendU32(out, bi.kind() == BindingKind::Var ? 1 : 0);
      AppendU32(out, hasEnvSlot ? 1 : 0);
      AppendU32(out, hasEnvSlot ? loc.slot() : 0);
      n++;
    }
    out[countPos] = uint8_t(n);
    out[countPos + 1] = uint8_t(n >> 8);
    out[countPos + 2] = uint8_t(n >> 16);
    out[countPos + 3] = uint8_t(n >> 24);
  }
  AppendU32(out, uint32_t(scripts.length()));
  for (JSScript* script : scripts) {
    AppendU32(out, uint32_t(reinterpret_cast<uintptr_t>(script)));
    unsigned startLine = script->lineno();
    JS::LimitedColumnNumberOneOrigin startCol(script->column());
    AppendU32(out, startLine);
    AppendU32(out, startCol.oneOriginValue());
    AppendU32(out, script->sourceStart());
    AppendU32(out, script->sourceEnd());
    size_t countPos = out.size();
    AppendU32(out, 0);
    uint32_t n = 0;
    unsigned lineno = startLine;
    JS::LimitedColumnNumberOneOrigin column = startCol;
    ptrdiff_t offset = 0;
    for (SrcNoteIterator iter(script->notes(), script->notesEnd());
         !iter.atEnd(); ++iter) {
      const auto* sn = *iter;
      offset += sn->delta();
      SrcNoteType type = sn->type();
      if (type == SrcNoteType::SetLine) {
        lineno = SrcNote::SetLine::getLine(sn, startLine);
        column = JS::LimitedColumnNumberOneOrigin();
      } else if (type == SrcNoteType::SetLineColumn) {
        lineno = SrcNote::SetLineColumn::getLine(sn, startLine);
        column = SrcNote::SetLineColumn::getColumn(sn);
      } else if (type == SrcNoteType::NewLine) {
        lineno++;
        column = JS::LimitedColumnNumberOneOrigin();
      } else if (type == SrcNoteType::NewLineColumn) {
        lineno++;
        column = SrcNote::NewLineColumn::getColumn(sn);
      } else if (type == SrcNoteType::ColSpan) {
        column += SrcNote::ColSpan::getSpan(sn);
      } else {
        continue;
      }
      AppendU32(out, uint32_t(offset));
      AppendU32(out, lineno);
      AppendU32(out, column.oneOriginValue());
      n++;
    }
    out[countPos] = uint8_t(n);
    out[countPos + 1] = uint8_t(n >> 8);
    out[countPos + 2] = uint8_t(n >> 16);
    out[countPos + 3] = uint8_t(n >> 24);
  }
  return true;
}

// Owns the digest buffer recorded in the registration block.
static std::vector<uint8_t>* gDigest = nullptr;

}  // namespace night
}  // namespace js

using namespace js;
using namespace js::night;

// All scripts of all registered roots' trees, in registration order; kept
// alive alongside the roots for digest rebuilds.
static PersistentRooted<GCVector<JSScript*, 0, SystemAllocPolicy>>*
    gNightAllScripts = nullptr;

size_t js::night::NightAllScriptsLength() {
  return gNightAllScripts ? gNightAllScripts->get().length() : 0;
}

JSScript* js::night::NightAllScriptAt(size_t i) {
  return gNightAllScripts->get()[i];
}

// Re-derive every raw address the registration block mirrors, from the copies
// the GC actually traces. The block is a wire format for a tool that reads
// this process's memory image, so it holds `JSScript*`s and `Scope*`s as bare
// u32s -- nothing traces those, and a compacting GC during the top level moves
// what they point at. The AUTHORITATIVE copies are rooted
// (`gNightRoots`/`gNightAllScripts` are `PersistentRooted`, so a moving GC
// updates them in place), and the digest is a pure function of that vector, so
// the mirror is derived data and can simply be rebuilt.
//
// Call once, after the last GC before the snapshot and before anything reads
// the block. Everything recorded after this point -- the heap oracle's object
// addresses -- is captured with no GC in between.
bool js::night::NightSealSnapshotAddresses(JSContext* cx) {
  NightRegistration& reg = gNightRegistration;
  if (reg.numRoots == 0 || !gNightRoots || !gNightAllScripts) {
    return false;
  }
  for (uint32_t i = 0; i < reg.numRoots; i++) {
    reg.roots[i] = uint32_t(reinterpret_cast<uintptr_t>(gNightRoots->get()[i]));
  }
  if (gDigest) {
    if (!BuildDigest(cx, gNightAllScripts->get(), *gDigest)) {
      return false;
    }
    reg.digest = uint32_t(reinterpret_cast<uintptr_t>(gDigest->data()));
    reg.digestLen = uint32_t(gDigest->size());
  }
  return NightSealSelfHostedAddresses();
}

bool js::night::NightAppendDigestTree(JSContext* cx,
                                      JS::Handle<JSScript*> script) {
  NightRegistration& reg = gNightRegistration;
  if (reg.numRoots == 0 || !gNightAllScripts || !gDigest) {
    return false;
  }
  if (!DelazifyTree(cx, script, gNightAllScripts->get())) {
    return false;
  }
  if (!BuildDigest(cx, gNightAllScripts->get(), *gDigest)) {
    return false;
  }
  reg.digest = uint32_t(reinterpret_cast<uintptr_t>(gDigest->data()));
  reg.digestLen = uint32_t(gDigest->size());
  return true;
}

JS_PUBLIC_API bool JS::NightRegisterRoot(JSContext* cx,
                                         JS::Handle<JSScript*> script,
                                         bool executedAtInit) {
  NightRegistration& reg = gNightRegistration;
  if (reg.numRoots == 0) {
    NightBuildLayoutDescriptor();
    reg.abiVersion = NightAotAbiVersion;
    reg.layoutDescriptor =
        uint32_t(reinterpret_cast<uintptr_t>(&gNightLayoutDescriptor));
    reg.cx = uint32_t(reinterpret_cast<uintptr_t>(cx));
    gNightRoots =
        js_new<PersistentRooted<GCVector<JSScript*, 0, SystemAllocPolicy>>>(
            cx, GCVector<JSScript*, 0, SystemAllocPolicy>());
    gNightAllScripts =
        js_new<PersistentRooted<GCVector<JSScript*, 0, SystemAllocPolicy>>>(
            cx, GCVector<JSScript*, 0, SystemAllocPolicy>());
    if (!gNightRoots || !gNightAllScripts) {
      return false;
    }
  }
  if (reg.numRoots >= NightMaxRoots) {
    return false;
  }
  if (!DelazifyTree(cx, script, gNightAllScripts->get())) {
    return false;
  }
  if (!gNightRoots->get().append(script)) {
    return false;
  }
  reg.roots[reg.numRoots] = uint32_t(reinterpret_cast<uintptr_t>(script.get()));
  reg.numRoots++;
  if (executedAtInit) {
    reg.flags |= NightFlagToplevelExecutedAtInit;
  }
  if (!gDigest) {
    gDigest = js_new<std::vector<uint8_t>>();
    if (!gDigest) {
      return false;
    }
  }
  if (!BuildDigest(cx, gNightAllScripts->get(), *gDigest)) {
    return false;
  }
  reg.digest = uint32_t(reinterpret_cast<uintptr_t>(gDigest->data()));
  reg.digestLen = uint32_t(gDigest->size());
  // Compiling this tree is what blew the dynamic-code fuse, and this tree is
  // exactly what the analysis scans: re-arm. Source compiled after this
  // point is source the analysis never saw. Delazifying the tree does not
  // come back through the blow point -- it reuses the ScriptSource.
  NightRearmDynamicCodeFuse();
  return true;
}

// Activation after a transformed snapshot resumes: install the runtime
// environment from the tool-written region table, apply the fuse policy,
// and enable dispatch. The tool already set each compiled script's
// nightFuncIndex_ in the image.
extern "C" void NightCensusTraceRearm();

// `NIGHT_GC_STATS`: at exit, the minor GCs, the bytes they promoted (the
// tenured heap's growth across each), the major GCs, and how many NightStack
// slots the GCs traced as roots (the stack's depth at each, summed).
static JSContext* gStatsCx = nullptr;
static uint64_t gStatsMinor = 0, gStatsPromoted = 0, gStatsStart = 0;
static void NightStatsNursery(JSContext* cx, JS::GCNurseryProgress p,
                              JS::GCReason, void*) {
  uint64_t b = JS_GetGCParameter(cx, JSGC_BYTES);
  if (p == JS::GCNurseryProgress::GC_NURSERY_COLLECTION_START) {
    gStatsStart = b;
  } else {
    gStatsMinor++;
    if (b > gStatsStart) {
      gStatsPromoted += b - gStatsStart;
    }
  }
}
static void NightStatsDump() {
  fprintf(stderr,
          "night: gcstats minor %llu promoted %llu major %u stack-traces "
          "%llu stack-slots %llu\n",
          (unsigned long long)gStatsMinor, (unsigned long long)gStatsPromoted,
          unsigned(JS_GetGCParameter(gStatsCx, JSGC_MAJOR_GC_NUMBER)),
          (unsigned long long)js::nightrt::TheNightStack(gStatsCx).traces(),
          (unsigned long long)js::nightrt::TheNightStack(gStatsCx).tracedSlots());
}

JS_PUBLIC_API void JS::NightClearCaches(JSContext* cx) {
  if (gNightActivated && nightrt::NightStateOf(cx)) {
    js::night::NightClearCaches(cx);
  }
}

JS_PUBLIC_API bool JS::NightActivate(JSContext* cx) {
  NightCensusTraceRearm();
  if (getenv("NIGHT_GC_STATS") && !gStatsCx) {
    gStatsCx = cx;
    JS::AddGCNurseryCollectionCallback(cx, NightStatsNursery, nullptr);
    atexit(NightStatsDump);
  }
  if (gNightActivated) {
    return true;
  }
  if (!gNightRegistration.compiled) {
    return false;
  }
  js::night::NightEnvDesc env;
  static_assert(sizeof(env) == sizeof(gNightRegistration.regionTable),
                "regionTable mirrors NightEnvDesc");
  memcpy(&env, gNightRegistration.regionTable, sizeof(env));
  if (!night_runtime_install_env(cx, env)) {
    return false;
  }
  // Interpreted scripts (declined bodies, generators, eval) write globals
  // through the engine's own property paths, which run the fuse hooks
  // (NightGlobalDataStore / NightGlobalKeyBlow), so the value fuses stay
  // trustworthy without distrusting every global.
  if (gNightRegistration.flags & NightFlagToplevelExecutedAtInit) {
    night_runtime_arm_gname_fuses_from_live(cx);
  }
  gNightActivated = true;
  return true;
}

#ifdef __wasm__
extern "C" __attribute__((export_name("night.registration"), used)) uint32_t
night_registration_addr() {
  return uint32_t(reinterpret_cast<uintptr_t>(&gNightRegistration));
}
#endif
