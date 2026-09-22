/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// Snapshot-registration extras, shared with the in-process batch: the
// self-hosted allowlist resolution and the regex literal program capture
// (forced irregexp bytecode compilation), plus their serialization into the
// registration block for the external `nightmonkey` transform.

#include "runtime/NightSnapshotExtras.h"
#include "runtime/NightHooks.h"

#include "mozilla/Assertions.h"

#include <algorithm>
#include <set>
#include <stdio.h>
#include <string>
#include <string.h>
#include <unordered_map>
#include <utility>
#include <vector>

#include "irregexp/RegExpShim.h"  // ByteArrayData::data (inline)
#include "js/GCVector.h"
#include "runtime/Night.h"
#include "runtime/NightEnv.h"
#include "runtime/NightRegistration.h"
#include "vm/ArrayObject.h"
#include "vm/EnvironmentObject.h"
#include "vm/GlobalObject.h"
#include "vm/JSContext.h"
#include "vm/JSFunction.h"
#include "vm/JSScript.h"
#include "vm/NativeObject.h"
#include "vm/PlainObject.h"
#include "vm/RegExpObject.h"
#include "vm/Shape.h"
#include "vm/StringType.h"
#include "vm/TypedArrayObject.h"

#include "vm/JSObject-inl.h"
#include "vm/JSScript-inl.h"
#include "vm/NativeObject-inl.h"

using namespace js;

// Hot self-hosted builtins compiled into the batch beyond the user tree.
static const char* const kSelfHosted[] = {
    "Array.prototype.forEach",         "Array.prototype.map",
    "Array.prototype.filter",          "String.prototype.split",
    "String.prototype.slice",          "Map.prototype.forEach",
    "Set.prototype.forEach",           "String.prototype.replace",
    "RegExp.prototype.@@replace",      "%RegExpGlobalReplaceOptFunc%",
    "%RegExpLocalReplaceOptSimple%",   "%RegExpGlobalReplaceOptSubst%",
    "Object.prototype.hasOwnProperty", "%Substring%",
    "%RegExpGlobalReplaceOptSimple%",  "RegExp.prototype.@@split",
    "String.prototype.substring",      "String.prototype.match",
    "Object.prototype.valueOf",        "isNaN",
    "String.prototype.substr",         "Number.isNaN",
};

// NightRegexProgram is declared in NightSnapshotExtras.h.

// Force irregexp BYTECODE compilation of a regex literal for both subject
// encodings. Any failure just skips the regex (it stays on the interpreter
// at runtime). May GC.
static void CollectOneRegex(JSContext* cx, JS::Handle<RegExpObject*> reobj,
                            std::set<std::pair<std::u16string, uint32_t>>& seen,
                            std::vector<night::NightRegexProgram>& out) {
  JS::Rooted<JSAtom*> pattern(cx, reobj->getSource());
  uint32_t flagsVal = reobj->getFlags().value();

  std::u16string pat;
  {
    JS::AutoCheckCannotGC nogc;
    if (pattern->hasLatin1Chars()) {
      const JS::Latin1Char* c = pattern->latin1Chars(nogc);
      pat.assign(c, c + pattern->length());
    } else {
      const char16_t* c = pattern->twoByteChars(nogc);
      pat.assign(c, c + pattern->length());
    }
  }
  if (!seen.insert({pat, flagsVal}).second) {
    return;
  }

  RegExpShared* sharedRaw = RegExpObject::getShared(cx, reobj);
  if (!sharedRaw) {
    if (cx->isExceptionPending()) {
      cx->clearPendingException();
    }
    return;
  }
  JS::Rooted<RegExpShared*> shared(cx, sharedRaw);

  // The sample input only selects the compilation slot (and feeds the
  // Boyer-Moore frequency sampling); compile once per encoding.
  JS::Rooted<JSLinearString*> l1sample(cx, cx->names().length);
  static const char16_t kWide[] = {0x1234};
  JS::Rooted<JSLinearString*> tbsample(cx, NewStringCopyN<CanGC>(cx, kWide, 1));
  if (!tbsample) {
    if (cx->isExceptionPending()) {
      cx->clearPendingException();
    }
    return;
  }
  MOZ_ASSERT(l1sample->hasLatin1Chars() && !tbsample->hasLatin1Chars());
  if (!RegExpShared::compileIfNecessary(cx, &shared, l1sample,
                                        RegExpShared::CodeKind::Bytecode) ||
      !RegExpShared::compileIfNecessary(cx, &shared, tbsample,
                                        RegExpShared::CodeKind::Bytecode)) {
    if (cx->isExceptionPending()) {
      cx->clearPendingException();
    }
    return;
  }
  if (shared->kind() != RegExpShared::Kind::RegExp) {
    // Atom-kind patterns use the plain string matcher; nothing to compile.
    return;
  }
  RegExpShared::ByteCode* bcL1 = shared->getByteCode(/*latin1=*/true);
  RegExpShared::ByteCode* bcTB = shared->getByteCode(/*latin1=*/false);
  if (!bcL1 && !bcTB) {
    return;
  }
  night::NightRegexProgram prog;
  prog.pattern = std::move(pat);
  prog.flags = flagsVal;
  if (bcL1) {
    prog.latin1.assign(bcL1->data(), bcL1->data() + bcL1->length());
  }
  if (bcTB) {
    prog.twobyte.assign(bcTB->data(), bcTB->data() + bcTB->length());
  }
  prog.numRegisters = shared->getMaxRegisters();
  prog.pairCount = uint32_t(shared->pairCount());
  out.push_back(std::move(prog));
}

// Pre-pass over a script tree collecting regex literal programs (the tree is
// already delazified). May GC; runs before the walk takes raw heap
// addresses.
bool js::night::CollectRegexPrograms(
    JSContext* cx, JS::Handle<JSScript*> root,
    std::set<std::pair<std::u16string, uint32_t>>& seen,
    std::vector<night::NightRegexProgram>& out) {
  JS::Rooted<GCVector<JSScript*, 0, SystemAllocPolicy>> worklist(cx);
  if (!worklist.append(root)) {
    return false;
  }
  JS::Rooted<JSScript*> current(cx);
  JS::Rooted<JSFunction*> fun(cx);
  JS::Rooted<RegExpObject*> reobj(cx);
  while (!worklist.empty()) {
    current = worklist.popCopy();
    for (JS::GCCellPtr thing : current->gcthings()) {
      if (!thing.is<JSObject>()) {
        continue;
      }
      JSObject* obj = &thing.as<JSObject>();
      if (obj->is<RegExpObject>()) {
        reobj = &obj->as<RegExpObject>();
        CollectOneRegex(cx, reobj, seen, out);
        continue;
      }
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

// Resolve the kSelfHosted allowlist against the live global, delazify each
// tree, and append it to the registration digest. Outputs the resolved
// scripts and their dotted paths (parallel vectors).
bool js::night::ResolveSelfHostedRoots(
    JSContext* cx, JS::MutableHandleVector<JSScript*> shScripts,
    std::vector<const char*>& shPaths) {
  size_t missing = 0;
  for (const char* path : kSelfHosted) {
    JS::Rooted<JSFunction*> fun(
        cx, night::ResolveGlobalPath(cx, path, strlen(path)));
    if (!fun || !fun->isInterpreted()) {
      fprintf(stderr, "night: selfhosted %s: not found\n", path);
      missing++;
      continue;
    }
    JS::Rooted<JSScript*> sh(cx, JSFunction::getOrCreateScript(cx, fun));
    if (!sh) {
      if (cx->isExceptionPending()) {
        cx->clearPendingException();
      }
      fprintf(stderr, "night: selfhosted %s: delazify failed\n", path);
      missing++;
      continue;
    }
    if (!night::NightAppendDigestTree(cx, sh)) {
      return false;
    }
    if (!shScripts.append(sh)) {
      return false;
    }
    shPaths.push_back(path);
  }
  // A renamed or nativized builtin silently drops out of the batch; make the
  // degradation loud enough to notice in a build log.
  if (missing != 0) {
    fprintf(stderr,
            "night: WARNING: selfhosted allowlist: %zu of %zu builtins missing "
            "from the batch\n",
            missing, std::size(kSelfHosted));
  }
  return true;
}

static void AppendU32(std::vector<uint8_t>& out, uint32_t v) {
  out.push_back(uint8_t(v));
  out.push_back(uint8_t(v >> 8));
  out.push_back(uint8_t(v >> 16));
  out.push_back(uint8_t(v >> 24));
}

// The self-hosted half of the address mirror. The serialized buffer records
// each resolved script as a bare u32, which nothing traces; this keeps the
// scripts themselves rooted (so a moving GC updates them) alongside the
// buffer and the byte offset each address was written at, so
// `NightSealSnapshotAddresses` can re-derive the mirror before the snapshot.
struct NightSelfHostedMirror {
  PersistentRooted<GCVector<JSScript*, 0, SystemAllocPolicy>>* scripts =
      nullptr;
  std::vector<uint8_t>* bytes = nullptr;
  std::vector<uint32_t>* offsets = nullptr;
};
static NightSelfHostedMirror gShMirror;

static void PadTo4(std::vector<uint8_t>& out) {
  while (out.size() % 4 != 0) {
    out.push_back(0);
  }
}

// Registration-block self-hosted table (read by the external tool):
//   u32 count, per entry: u32 scriptAddr, u32 nameLen, nameLen UTF-8 bytes
//   (the dotted global path), padded to 4.
// Registration-block regex program table:
//   u32 count, per entry: u32 flags, u32 numRegisters, u32 pairCount,
//   u32 patternLen, patternLen x u16 (padded to 4), u32 latin1Len, bytes
//   (padded to 4), u32 twobyteLen, bytes (padded to 4).
// Both buffers are leaked by design: their addresses are recorded in the
// registration block and must survive into the snapshot.
bool js::NightSnapshotCaptureExtras(JSContext* cx, JS::Handle<JSScript*> root) {
  night::NightRegistration& reg = night::gNightRegistration;
  if (reg.numRoots == 0) {
    return false;
  }

  JS::RootedVector<JSScript*> shScripts(cx);
  std::vector<const char*> shPaths;
  if (!night::ResolveSelfHostedRoots(cx, &shScripts, shPaths)) {
    return false;
  }

  // Regex programs (user tree + self-hosted trees). May GC, so it runs
  // before any address is written down; what is written is re-derived at
  // seal time anyway (NightSealSelfHostedAddresses).
  std::set<std::pair<std::u16string, uint32_t>> regexSeen;
  std::vector<night::NightRegexProgram> regexPrograms;
  if (!night::CollectRegexPrograms(cx, root, regexSeen, regexPrograms)) {
    return false;
  }
  for (size_t i = 0; i < shScripts.length(); i++) {
    JS::Rooted<JSScript*> sh(cx, shScripts[i]);
    if (!night::CollectRegexPrograms(cx, sh, regexSeen, regexPrograms)) {
      return false;
    }
  }

  auto* shBytes = js_new<std::vector<uint8_t>>();
  auto* reBytes = js_new<std::vector<uint8_t>>();
  if (!shBytes || !reBytes) {
    return false;
  }
  auto* shOffsets = js_new<std::vector<uint32_t>>();
  auto* shRoots =
      js_new<PersistentRooted<GCVector<JSScript*, 0, SystemAllocPolicy>>>(
          cx, GCVector<JSScript*, 0, SystemAllocPolicy>());
  if (!shOffsets || !shRoots) {
    return false;
  }
  AppendU32(*shBytes, uint32_t(shScripts.length()));
  for (size_t i = 0; i < shScripts.length(); i++) {
    if (!shRoots->get().append(shScripts[i])) {
      return false;
    }
    shOffsets->push_back(uint32_t(shBytes->size()));
    AppendU32(*shBytes,
              uint32_t(reinterpret_cast<uintptr_t>(shScripts[i].get())));
    size_t len = strlen(shPaths[i]);
    AppendU32(*shBytes, uint32_t(len));
    shBytes->insert(shBytes->end(),
                    reinterpret_cast<const uint8_t*>(shPaths[i]),
                    reinterpret_cast<const uint8_t*>(shPaths[i]) + len);
    PadTo4(*shBytes);
  }
  AppendU32(*reBytes, uint32_t(regexPrograms.size()));
  for (const night::NightRegexProgram& rp : regexPrograms) {
    AppendU32(*reBytes, rp.flags);
    AppendU32(*reBytes, rp.numRegisters);
    AppendU32(*reBytes, rp.pairCount);
    AppendU32(*reBytes, uint32_t(rp.pattern.size()));
    for (char16_t c : rp.pattern) {
      reBytes->push_back(uint8_t(c));
      reBytes->push_back(uint8_t(c >> 8));
    }
    PadTo4(*reBytes);
    AppendU32(*reBytes, uint32_t(rp.latin1.size()));
    reBytes->insert(reBytes->end(), rp.latin1.begin(), rp.latin1.end());
    PadTo4(*reBytes);
    AppendU32(*reBytes, uint32_t(rp.twobyte.size()));
    reBytes->insert(reBytes->end(), rp.twobyte.begin(), rp.twobyte.end());
    PadTo4(*reBytes);
  }
  gShMirror = {shRoots, shBytes, shOffsets};
  reg.selfHosted = uint32_t(reinterpret_cast<uintptr_t>(shBytes->data()));
  reg.selfHostedLen = uint32_t(shBytes->size());
  reg.regexPrograms = uint32_t(reinterpret_cast<uintptr_t>(reBytes->data()));
  reg.regexProgramsLen = uint32_t(reBytes->size());
#ifdef NIGHTMONKEY_DEBUG
  fprintf(
      stderr,
      "night: snapshot extras: %zu selfhosted scripts, %zu regex programs\n",
      size_t(shScripts.length()), regexPrograms.size());
#endif
  return true;
}

// ---- heap oracle -----------------------------------------------------------

namespace {

// One transcribed object. `kind` mirrors the reader's ObjectKind codes.
struct NightHeapEntry {
  JSObject* obj = nullptr;
  const JSClass* clasp = nullptr;
  uint32_t kind = 0;
  JSObject* proto = nullptr;
  std::vector<std::pair<JSAtom*, JS::Value>> props;
  std::vector<std::pair<uint32_t, JS::Value>> elems;
};

constexpr uint32_t kHeapKindPlain = 1;
constexpr uint32_t kHeapKindArray = 2;
constexpr uint32_t kHeapKindFunction = 3;
// Typed arrays: kind 4, with the element kind's 1-based code (the
// compiler's TaKind order, same table as the ta_class rows in
// NightRuntime.cpp) in bits 4..7. No props/elements are transcribed --
// a TA's elements_ is its raw data, not a Value array.
constexpr uint32_t kHeapKindTypedArray = 4;
// Native functions: kind 5, identity only -- no props, no proto, so the
// walk still does not drag in the builtin graph. The reader names the
// native from the function's own atom, which is what lets a native held
// in a variable (`var hasOwn = Object.prototype.hasOwnProperty`) resolve.
constexpr uint32_t kHeapKindNativeFn = 5;

// The walk is unbounded: the oracle transcribes the whole reachable image.
// A missing entry reads as opaque, so a bound is not a soundness
// requirement, but a cap would silently starve the analysis on
// array-heavy setups.

// Only these classes are transcribed; everything else stays opaque. Native
// functions are recorded by identity alone (no props) so the walk does not
// drag in the whole builtin graph through their `.prototype` objects.
static uint32_t TaKindCode(js::Scalar::Type t) {
  // 1-based, the compiler's TaKind order (see NightRuntime.cpp's
  // kKindType and opsem::TaKind::ALL).
  switch (t) {
    case js::Scalar::Int8:
      return 1;
    case js::Scalar::Uint8:
      return 2;
    case js::Scalar::Uint8Clamped:
      return 3;
    case js::Scalar::Int16:
      return 4;
    case js::Scalar::Uint16:
      return 5;
    case js::Scalar::Int32:
      return 6;
    case js::Scalar::Uint32:
      return 7;
    case js::Scalar::Float32:
      return 8;
    case js::Scalar::Float64:
      return 9;
    default:
      return 0;
  }
}

uint32_t HeapKindOf(JSObject* obj) {
  if (obj->is<TypedArrayObject>()) {
    uint32_t code = TaKindCode(obj->as<TypedArrayObject>().type());
    return code ? kHeapKindTypedArray | (code << 4) : 0;
  }
  if (obj->is<JSFunction>()) {
    // Only user-tree functions: a self-hosted (or lazy) builtin's script is
    // not in the registration digest, so the reader could not walk it.
    JSFunction* fun = &obj->as<JSFunction>();
    if (fun->isInterpreted() && fun->hasBaseScript() &&
        !fun->isSelfHostedBuiltin()) {
      return kHeapKindFunction;
    }
    // Self-hosted builtins (`Object.prototype.hasOwnProperty`) count as
    // natives here: identity and name, never their script.
    return fun->isNativeFun() ||
                   (fun->isSelfHostedBuiltin() && fun->hasBaseScript())
               ? kHeapKindNativeFn
               : 0;
  }
  if (obj->is<PlainObject>()) {
    return kHeapKindPlain;
  }
  if (obj->is<ArrayObject>()) {
    return kHeapKindArray;
  }
  return 0;
}

}  // namespace

bool js::night::NightSealSelfHostedAddresses() {
  if (!gShMirror.scripts || !gShMirror.bytes || !gShMirror.offsets) {
    return true;  // no extras captured (the in-process lane serializes none)
  }
  const auto& scripts = gShMirror.scripts->get();
  MOZ_RELEASE_ASSERT(scripts.length() == gShMirror.offsets->size());
  for (size_t i = 0; i < scripts.length(); i++) {
    uint32_t off = (*gShMirror.offsets)[i];
    MOZ_RELEASE_ASSERT(off + 4 <= gShMirror.bytes->size());
    uint32_t addr = uint32_t(reinterpret_cast<uintptr_t>(scripts[i]));
    memcpy(gShMirror.bytes->data() + off, &addr, sizeof(addr));
  }
  return true;
}

static bool gWizening = false;

bool js::night::NightWizening() { return gWizening; }

void js::night::NightSetWizening(bool on) {
  gWizening = on;
  // The fixed-slot floor of an object constructed while wizening, applied
  // through the engine's constructor `this` allocation hook.
  gNightHooks.minConstructorThisSlots = on ? uint32_t(kWizenThisSlots) : 0;
}

bool js::NightSnapshotCaptureHeap(JSContext* cx) {
  gWizening = false;
  night::NightRegistration& reg = night::gNightRegistration;
  if (reg.numRoots == 0) {
    return false;
  }
  JS::Rooted<GlobalObject*> global(cx, cx->global());
  if (!global) {
    return false;
  }

  // The last GC before the snapshot, and the only place a SHRINKING one
  // belongs: it tenures everything the setup built and compacts the image
  // the snapshot is about to freeze. Every address recorded BEFORE now is
  // re-derived from its traced copy immediately after
  // (`NightSealSnapshotAddresses`); everything recorded after -- this
  // function's own object addresses -- runs with no GC in between.
  JS::PrepareForFullGC(cx);
  JS::NonIncrementalGC(cx, JS::GCOptions::Shrink, JS::GCReason::API);
  if (!night::NightSealSnapshotAddresses(cx)) {
    return false;
  }

  // The primordial prototypes are described by the reader's builtin
  // abstractions, so a link to one is left null (transcription falls back to
  // the object's kind).
  JSObject* protoObject = global->maybeGetPrototype(JSProto_Object);
  JSObject* protoArray = global->maybeGetPrototype(JSProto_Array);
  JSObject* protoFunction = global->maybeGetPrototype(JSProto_Function);

  std::vector<NightHeapEntry> entries;
  // Scope -> (environment slot -> the value every live activation holds).
  std::unordered_map<js::Scope*, std::unordered_map<uint32_t, JS::Value>>
      envSlots;
  std::unordered_map<JSObject*, size_t> seen;
  std::vector<JSObject*> worklist;

  // The global is not itself Plain-classed, but it is a property bag like
  // one: its own properties are the `Global(name)` bindings.
  auto kindOf = [&](JSObject* obj) {
    return obj == global ? kHeapKindPlain : HeapKindOf(obj);
  };
  auto enqueue = [&](JSObject* obj) {
    if (!obj || seen.count(obj)) {
      return;
    }
    if (kindOf(obj) == 0) {
      return;
    }
    seen.emplace(obj, size_t(-1));
    worklist.push_back(obj);
  };

  {
    JS::AutoCheckCannotGC nogc;
    enqueue(global);
    // Object-literal gcthings are not reachable from the global, but their
    // property snapshots are what the literal-class seeding reads.
    for (size_t i = 0; i < night::NightAllScriptsLength(); i++) {
      JSScript* script = night::NightAllScriptAt(i);
      for (JS::GCCellPtr thing : script->gcthings()) {
        if (thing && thing.is<JSObject>()) {
          enqueue(&thing.as<JSObject>());
        }
      }
    }

    while (!worklist.empty()) {
      JSObject* obj = worklist.back();
      worklist.pop_back();

      NightHeapEntry entry;
      entry.obj = obj;
      entry.clasp = obj->getClass();
      entry.kind = kindOf(obj);
      if ((entry.kind & 0xf) == kHeapKindTypedArray ||
          entry.kind == kHeapKindNativeFn) {
        // The kind + clasp are the whole record: the analysis needs the
        // view's element kind for receiver homing (or a native's identity),
        // nothing else.
        seen[obj] = entries.size();
        entries.push_back(std::move(entry));
        continue;
      }
      NativeObject* nobj = &obj->as<NativeObject>();
      if (obj->hasStaticPrototype()) {
        JSObject* proto = obj->staticPrototype();
        if (proto != protoObject && proto != protoArray &&
            proto != protoFunction) {
          entry.proto = proto;
        }
      }

      // `slotsExact` (kind bit 8): the object's own properties are exactly
      // data-atom properties at slots 0..n-1, all fixed, non-dictionary --
      // the precondition for the compiler to stamp this image object with
      // a SLOTS-carrying layout word (a skipped accessor or non-atom key
      // shifts positions, so a props-list match alone is not enough).
      bool slotsExact = !nobj->inDictionaryMode();
      js::Vector<uint32_t, 8, SystemAllocPolicy> propSlots;
      for (ShapePropertyIter<NoGC> iter(nobj->shape()); !iter.done(); iter++) {
        if (!iter->isDataProperty()) {
          slotsExact = false;
          continue;
        }
        PropertyKey key = iter->key();
        if (!key.isAtom()) {
          slotsExact = false;
          continue;
        }
        if (iter->slot() >= nobj->numFixedSlots()) {
          slotsExact = false;
        }
        if (!propSlots.append(iter->slot())) {
          slotsExact = false;
        }
        entry.props.emplace_back(key.toAtom(), nobj->getSlot(iter->slot()));
      }
      // ShapePropertyIter runs most-recent-first; the reader wants
      // definition order (it is also the slot order for shared shapes).
      std::reverse(entry.props.begin(), entry.props.end());
      if (slotsExact) {
        std::reverse(propSlots.begin(), propSlots.end());
        for (size_t i = 0; i < propSlots.length(); i++) {
          if (propSlots[i] != i) {
            slotsExact = false;
            break;
          }
        }
      }
      if (slotsExact) {
        entry.kind |= 0x100;
      }

      uint32_t initlen = nobj->getDenseInitializedLength();
      for (uint32_t i = 0; i < initlen; i++) {
        const JS::Value& v = nobj->getDenseElement(i);
        if (!v.isMagic()) {
          entry.elems.emplace_back(i, v);
        }
      }

      // Closure environments: the module pattern reaches every class
      // through a closure-captured alias (`var B = NS.Sub.b2AABB`), so
      // without these slot values the whole namespace resolution stops at
      // the first alias.
      if (obj->is<JSFunction>()) {
        JSObject* env = obj->as<JSFunction>().environment();
        for (int hops = 0; env && hops < 32; hops++) {
          if (env->is<CallObject>()) {
            CallObject& call = env->as<CallObject>();
            JSFunction& callee = call.callee();
            if (callee.hasBytecode()) {
              if (js::Scope* scope = callee.nonLazyScript()->bodyScope()) {
                auto& slots = envSlots[scope];
                uint32_t span = call.slotSpan();
                for (uint32_t i = 0; i < span; i++) {
                  const JS::Value& v = call.getSlot(i);
                  auto it = slots.find(i);
                  if (it == slots.end()) {
                    slots.emplace(i, v);
                  } else if (it->second != v) {
                    // Two live activations disagree: no single value to
                    // report, so the slot reads as unknown.
                    it->second = JS::MagicValue(JS_GENERIC_MAGIC);
                  }
                  if (v.isObject()) {
                    enqueue(&v.toObject());
                  }
                }
              }
            }
          }
          if (!env->is<EnvironmentObject>()) {
            break;
          }
          env = &env->as<EnvironmentObject>().enclosingEnvironment();
        }
      }
      enqueue(entry.proto);
      for (const auto& p : entry.props) {
        if (p.second.isObject()) {
          enqueue(&p.second.toObject());
        }
      }
      for (const auto& e : entry.elems) {
        if (e.second.isObject()) {
          enqueue(&e.second.toObject());
        }
      }
      seen[obj] = entries.size();
      entries.push_back(std::move(entry));
    }
  }

  // Serialized heap-oracle table (read by the external tool):
  //   u32 count, per entry: u32 objAddr, u32 claspAddr, u32 kind,
  //     u32 protoAddr (0 = none/primordial),
  //     u32 numProps, per prop: u32 atomAddr, u32 valueLow, u32 valueHigh,
  //     u32 numElems, per elem: u32 index, u32 valueLow, u32 valueHigh
  // Leaked by design: the address is recorded in the registration block and
  // must survive into the snapshot.
  auto* bytes = js_new<std::vector<uint8_t>>();
  if (!bytes) {
    return false;
  }
  auto appendValue = [&](const JS::Value& v) {
    uint64_t bits = v.asRawBits();
    AppendU32(*bytes, uint32_t(bits));
    AppendU32(*bytes, uint32_t(bits >> 32));
  };
  AppendU32(*bytes, uint32_t(entries.size()));
  for (const NightHeapEntry& e : entries) {
    AppendU32(*bytes, uint32_t(reinterpret_cast<uintptr_t>(e.obj)));
    AppendU32(*bytes, uint32_t(reinterpret_cast<uintptr_t>(e.clasp)));
    AppendU32(*bytes, e.kind);
    AppendU32(*bytes, uint32_t(reinterpret_cast<uintptr_t>(e.proto)));
    AppendU32(*bytes, uint32_t(e.props.size()));
    for (const auto& p : e.props) {
      AppendU32(*bytes, uint32_t(reinterpret_cast<uintptr_t>(p.first)));
      appendValue(p.second);
    }
    AppendU32(*bytes, uint32_t(e.elems.size()));
    for (const auto& el : e.elems) {
      AppendU32(*bytes, el.first);
      appendValue(el.second);
    }
  }
  AppendU32(*bytes, uint32_t(envSlots.size()));
  for (const auto& [scope, slots] : envSlots) {
    AppendU32(*bytes, uint32_t(reinterpret_cast<uintptr_t>(scope)));
    AppendU32(*bytes, uint32_t(slots.size()));
    for (const auto& [slot, v] : slots) {
      AppendU32(*bytes, slot);
      appendValue(v);
    }
  }
  reg.heapObjects = uint32_t(reinterpret_cast<uintptr_t>(bytes->data()));
  reg.heapObjectsLen = uint32_t(bytes->size());
  reg.globalObject = uint32_t(reinterpret_cast<uintptr_t>(global.get()));
#ifdef NIGHTMONKEY_DEBUG
  fprintf(stderr, "night: heap oracle: %zu objects transcribed\n",
          entries.size());
#endif
  return true;
}
