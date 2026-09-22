/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80: */

// AOT snapshot registration: the in-memory contract between an engine
// embedded in a Wasm module and the external AOT transform tool.
//
// During wizer initialization the embedding compiles its script(s) and calls
// JS::NightRegisterRoot for each root. That records the root JSScript, fills
// the layout descriptor (field offsets and flag constants the tool needs to
// read the script graph out of linear memory), and pins tenured-cell
// addresses by disabling compacting GC. The tool locates the registration
// block via the exported constant-returning function "night.registration",
// reads the script graph, appends compiled function bodies, patches each
// script's nightFuncIndex_ in the memory image, and sets `compiled`. After
// wizer resume, the embedding calls JS::NightActivate once; only then does the
// interpreter dispatch into AOT bodies.

#ifndef night_runtime_NightRegistration_h
#define night_runtime_NightRegistration_h

#include <stdint.h>

#include "jstypes.h"

#include "js/TypeDecls.h"
#include "runtime/NightEnv.h"  // NIGHT_ENV_REGIONS, NightEnvRegionCount

namespace js {
namespace night {

// Bump on any change to the registration block, the layout descriptor, or
// the NIGHT_ENV_REGIONS wire.
static constexpr uint32_t NightAotAbiVersion = 8;

// Every field-offset / size / flag-bit constant the external reader
// dereferences. Order is the wire order of `NightLayoutDescriptor::fields`;
// the Rust mirror is generated from this list, so entries must only ever be
// appended (with an ABI version bump on any semantic change). The expression
// is evaluated by NightBuildLayoutDescriptor(); it may be non-constexpr
// (offsetof of private members is exposed through class static accessors).
#define NIGHT_LAYOUT_FIELDS(_)                                                 \
  /* BaseScript */                                                             \
  _(baseScriptSize, sizeof(js::BaseScript))                                    \
  _(baseScriptFunction, js::BaseScript::offsetOfFunction())                    \
  _(baseScriptImmutableFlags, js::BaseScript::offsetOfImmutableFlags())        \
  _(baseScriptMutableFlags, js::BaseScript::offsetOfMutableFlags())            \
  _(baseScriptPrivateData, js::BaseScript::offsetOfPrivateData())              \
  _(baseScriptSharedData, js::BaseScript::offsetOfSharedData())                \
  _(baseScriptNightFuncIndex, js::BaseScript::offsetOfExternalTierWord())        \
  /* ImmutableScriptFlags bits (mask values) */                                \
  _(isfSelfHosted, uint32_t(js::ImmutableScriptFlagsEnum::SelfHosted))         \
  _(isfStrict, uint32_t(js::ImmutableScriptFlagsEnum::Strict))                 \
  _(isfIsAsync, uint32_t(js::ImmutableScriptFlagsEnum::IsAsync))               \
  _(isfIsGenerator, uint32_t(js::ImmutableScriptFlagsEnum::IsGenerator))       \
  _(isfIsFunction, uint32_t(js::ImmutableScriptFlagsEnum::IsFunction))         \
  _(isfNeedsArgsObj, uint32_t(js::ImmutableScriptFlagsEnum::NeedsArgsObj))     \
  _(isfHasMappedArgsObj,                                                       \
    uint32_t(js::ImmutableScriptFlagsEnum::HasMappedArgsObj))                  \
  /* PrivateScriptData */                                                      \
  _(privateScriptDataNGCThings, js::PrivateScriptData::offsetOfNGCThings())    \
  _(privateScriptDataGCThings, js::PrivateScriptData::offsetOfGCThings())      \
  /* GCCellPtr tagging */                                                      \
  _(gcCellPtrKindMask, uint32_t(JS::OutOfLineTraceKindMask))                   \
  _(traceKindObject, uint32_t(JS::TraceKind::Object))                          \
  _(traceKindString, uint32_t(JS::TraceKind::String))                          \
  _(traceKindScript, uint32_t(JS::TraceKind::Script))                          \
  _(traceKindScope, uint32_t(JS::TraceKind::Scope))                            \
  /* SharedImmutableScriptData -> ImmutableScriptData */                       \
  _(sisdISD, js::SharedImmutableScriptData::offsetOfISD())                     \
  _(isdOptArrayOffset, js::ImmutableScriptData::offsetOfResumeOffsetsOffset()) \
  _(isdCodeLength, js::ImmutableScriptData::offsetOfCodeLength())              \
  _(isdMainOffset, js::ImmutableScriptData::offsetOfMainOffset())              \
  _(isdNfixed, js::ImmutableScriptData::offsetOfNfixed())                      \
  _(isdNslots, js::ImmutableScriptData::offsetOfNslots())                      \
  _(isdBodyScopeIndex, js::ImmutableScriptData::offsetOfBodyScopeIndex())      \
  _(isdFunLength, js::ImmutableScriptData::offsetOfFunLength())                \
  _(isdCode, js::ImmutableScriptData::offsetOfCode())                          \
  /* TryNote / ScopeNote trailing arrays */                                    \
  _(tryNoteSize, sizeof(js::TryNote))                                          \
  _(tryNoteKind, offsetof(js::TryNote, kind_))                                 \
  _(tryNoteStackDepth, offsetof(js::TryNote, stackDepth))                      \
  _(tryNoteStart, offsetof(js::TryNote, start))                                \
  _(tryNoteLength, offsetof(js::TryNote, length))                              \
  _(scopeNoteSize, sizeof(js::ScopeNote))                                      \
  _(scopeNoteIndex, offsetof(js::ScopeNote, index))                            \
  _(scopeNoteStart, offsetof(js::ScopeNote, start))                            \
  _(scopeNoteLength, offsetof(js::ScopeNote, length))                          \
  /* JSFunction (a NativeObject; fields live in fixed slots, byte offsets) */  \
  _(functionFlagsAndArgCount, JSFunction::offsetOfFlagsAndArgCount())          \
  _(functionJitInfoOrScript, JSFunction::offsetOfJitInfoOrScript())            \
  _(functionAtom, JSFunction::offsetOfAtom())                                  \
  _(functionFlagsBaseScript, uint32_t(js::FunctionFlags::BASESCRIPT))          \
  _(functionFlagsSelfHostLazy, uint32_t(js::FunctionFlags::SELFHOSTLAZY))      \
  /* JSString (offsets via the public shadow mirror, asserted in            */ \
  /* StringType.h to match the real layout)                                 */ \
  _(stringFlags, JSString::offsetOfFlags())                                    \
  _(stringLength, JSString::offsetOfLength())                                  \
  _(stringAtomBit, JS::shadow::String::ATOM_BIT)                               \
  _(stringLinearBit, JS::shadow::String::LINEAR_BIT)                           \
  _(stringInlineCharsBit, JS::shadow::String::INLINE_CHARS_BIT)                \
  _(stringLatin1CharsBit, JS::shadow::String::LATIN1_CHARS_BIT)                \
  _(stringNonInlineChars, offsetof(JS::shadow::String, nonInlineCharsLatin1))  \
  _(stringInlineStorage, offsetof(JS::shadow::String, inlineStorageLatin1))    \
  /* Scope */                                                                  \
  _(scopeKind, js::Scope::offsetOfKind())                                      \
  _(scopeEnclosing, js::Scope::offsetOfEnclosingScope())                       \
  _(scopeEnvironmentShape, js::Scope::offsetOfEnvironmentShape())              \
  /* JS::Value (NUNBOX32 on wasm32) */                                         \
  _(valueTagShift, 32)                                                         \
  _(valueTagObject, uint32_t(JSVAL_TAG_OBJECT))                                \
  _(valueTagString, uint32_t(JSVAL_TAG_STRING))                                \
  _(valueTagInt32, uint32_t(JSVAL_TAG_INT32))                                  \
  _(valueTagUndefined, uint32_t(JSVAL_TAG_UNDEFINED))                          \
  _(valueTagNull, uint32_t(JSVAL_TAG_NULL))                                    \
  _(valueTagBoolean, uint32_t(JSVAL_TAG_BOOLEAN))                              \
  _(valueTagSymbol, uint32_t(JSVAL_TAG_SYMBOL))                                \
  /* Tags below CLEAR are the high word of a double payload. */                \
  _(valueTagClear, uint32_t(JSVAL_TAG_CLEAR))                                  \
  /* Object class identification: shape (cell header) -> base shape ->      */ \
  /* clasp, compared against these class singletons' addresses.             */ \
  _(shapeBase, js::Shape::offsetOfBaseShape())                                 \
  _(baseShapeClasp, js::BaseShape::offsetOfClasp())                            \
  _(claspFunction, uint32_t(reinterpret_cast<uintptr_t>(&js::FunctionClass)))  \
  _(claspFunctionExtended,                                                     \
    uint32_t(reinterpret_cast<uintptr_t>(&js::ExtendedFunctionClass)))         \
  _(claspPlain,                                                                \
    uint32_t(reinterpret_cast<uintptr_t>(&js::PlainObject::class_)))           \
  _(claspArray,                                                                \
    uint32_t(reinterpret_cast<uintptr_t>(&js::ArrayObject::class_)))           \
  _(claspRegExp,                                                               \
    uint32_t(reinterpret_cast<uintptr_t>(&js::RegExpObject::class_)))          \
  /* Function name resolution (fullExplicitName semantics) */                  \
  _(functionFlagsInferredName, uint32_t(js::FunctionFlags::HAS_INFERRED_NAME)) \
  _(functionFlagsGuessedAtom, uint32_t(js::FunctionFlags::HAS_GUESSED_ATOM))   \
  /* ScopeKind values whose scopes always have an environment */               \
  _(scopeKindWith, uint32_t(js::ScopeKind::With))                              \
  _(scopeKindGlobal, uint32_t(js::ScopeKind::Global))                          \
  _(scopeKindNonSyntactic, uint32_t(js::ScopeKind::NonSyntactic))              \
  _(scopeKindNamedLambda, uint32_t(js::ScopeKind::NamedLambda))                \
  _(scopeKindStrictNamedLambda, uint32_t(js::ScopeKind::StrictNamedLambda))

enum class NightLayoutField : uint32_t {
#define NIGHT_LAYOUT_ENUM(name, expr) name,
  NIGHT_LAYOUT_FIELDS(NIGHT_LAYOUT_ENUM)
#undef NIGHT_LAYOUT_ENUM
      Count,
};

struct NightLayoutDescriptor {
  uint32_t abiVersion;
  uint32_t buildIdHash;
  uint32_t numFields;
  uint32_t fields[uint32_t(NightLayoutField::Count)];
};

static constexpr uint32_t NightMaxRoots = 8;

// Registration flag bits. Bit 1 is reserved and must not be reused: an
// older image may carry it set.
static constexpr uint32_t NightFlagToplevelExecutedAtInit = 1 << 0;

struct NightRegistration {
  uint32_t abiVersion;
  uint32_t layoutDescriptor;  // linear-memory address of the descriptor
  uint32_t cx;                // informational: the registering JSContext
  uint32_t flags;
  uint32_t numRoots;
  uint32_t roots[NightMaxRoots];  // BaseScript* as linear-memory addresses
  // Engine-serialized digest of facts the reader should not derive from raw
  // cell reads: per-script gcthing trace kinds (Script/Scope are out-of-line
  // kinds whose tags live in arena metadata) and per-scope binding lists
  // (BindingIter's per-kind data layouts). See NightBuildDigest for the format.
  uint32_t digest;  // malloc'd buffer address
  uint32_t digestLen;
  // Written by the transform tool:
  uint32_t compiled;
  uint32_t toolVersion;
  // ABI v2 engine-written extras (NightSnapshotCaptureExtras): self-hosted
  // compilation roots and force-compiled regex bytecode programs, serialized
  // (formats documented at the serializers in night/runtime/NightInproc.cpp). 0
  // = absent.
  uint32_t selfHosted;  // malloc'd buffer address
  uint32_t selfHostedLen;
  uint32_t regexPrograms;  // malloc'd buffer address
  uint32_t regexProgramsLen;
  // ABI v2 tool-written region table: the NightEnvDesc field values in
  // NIGHT_ENV_REGIONS order (NightEnv.h), describing the tool-claimed memory
  // regions and serialized side tables. Every word is an absolute
  // linear-memory address or a length -- unlike the in-process env_desc wire,
  // this flow has no descriptor-relative Table offsets. Consumed by
  // JS::NightActivate.
  uint32_t regionTable[js::night::NightEnvRegionCount];
  // ABI v3 engine-written heap oracle (NightSnapshotCaptureHeap): the live
  // post-setup object graph -- own data properties, dense elements, and
  // prototype links of the Plain/Array/interpreted-Function objects reachable
  // from the global and the script gcthings. Read-only facts for the
  // likely-types analysis; 0 = absent (defer mode, or capture disabled).
  uint32_t heapObjects;
  uint32_t heapObjectsLen;
  uint32_t globalObject;  // the live global's address, 0 if not captured
};

extern NightRegistration gNightRegistration;

// True once JS::NightActivate (or the in-process driver) has installed the
// runtime tables; AOT dispatch stays disabled before that.
extern bool gNightActivated;

void NightBuildLayoutDescriptor();

// Delazify `script`'s function tree and add it to the registration digest
// without recording a new root (extra compilation roots beyond the user
// tree, e.g. self-hosted builtins joining an in-process batch). Requires a
// prior JS::NightRegisterRoot.
bool NightAppendDigestTree(JSContext* cx, JS::Handle<JSScript*> script);

// Re-derive every raw address the registration block mirrors from the copies
// the GC traces (the rooted script vectors), so a compacting GC during the
// program's top level cannot leave the block pointing at where a script used
// to be. Call once, after the last GC before the snapshot.
// `NightSealSelfHostedAddresses` is the half that lives with the extras.
bool NightSealSnapshotAddresses(JSContext* cx);
bool NightSealSelfHostedAddresses();

// All scripts of all registered roots' trees, in registration order (the
// heap capture seeds its walk from their gcthings). Empty before the first
// JS::NightRegisterRoot.
size_t NightAllScriptsLength();
JSScript* NightAllScriptAt(size_t i);

}  // namespace night
}  // namespace js

namespace JS {

// Record `script` as an AOT compilation root for a subsequent snapshot
// transform. Eagerly delazifies the script's function tree. Call during
// wizer initialization, after compilation, before the snapshot.
//
// The addresses this records are a MIRROR of state the GC traces, not roots
// themselves: `roots[]` holds bare `JSScript*`s for a tool that reads this
// process's memory image, and the program's whole top level runs between
// here and the snapshot. The rooted copies are what stay correct across a
// moving GC, so `NightSealSnapshotAddresses` re-derives the mirror from
// them once, at the end of the window. That is what lets compacting GC stay
// ON (docs/TODO 1.4).
// `executedAtInit` states whether the embedding runs the script's top level
// before the snapshot is taken (it affects how global-state caches are armed
// at activation).
extern JS_PUBLIC_API bool NightRegisterRoot(JSContext* cx,
                                            JS::Handle<JSScript*> script,
                                            bool executedAtInit);

// One-time arming after wizer resume; a no-op (returning false) when the
// module was not transformed. Idempotent.
extern JS_PUBLIC_API bool NightActivate(JSContext* cx);

}  // namespace JS

#endif /* night_runtime_NightRegistration_h */
