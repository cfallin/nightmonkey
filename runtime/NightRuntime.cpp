/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80: */

#include "runtime/NightRuntime.h"

#include "mozilla/Assertions.h"  // MOZ_CRASH
#include "mozilla/Utf8.h"        // mozilla::Utf8Unit

#include <algorithm>  // std::lower_bound
#include <deque>      // std::deque (stable addresses for PersistentRooted)
#include <map>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>  // malloc/free (regex matcher table)
#include <string>    // std::string, std::u16string
#include <string.h>  // memcpy
#include <unordered_map>  // the add-placement memo
#include <vector>    // std::vector

#include "jsapi.h"   // JS_NewPlainObject, JS_DefineFunction
#include "jsmath.h"  // js::math_sin_fdlibm_impl, js::ecmaPow (leaf Math arms)
#include "jsnum.h"   // js::ToNumeric

#include "builtin/Array.h"  // js::NewDenseCopiedArray (JSOp::Rest)
#include "builtin/RegExp.h"  // js::RegExpBuiltinExec*FromJit, IsOptimizableRegExpObject
#include "irregexp/imported/regexp-macro-assembler.h"  // CaseInsensitiveCompare*
#include "irregexp/RegExpAPI.h"
#include "jit/InlinableNatives.h"  // js::jit::InlinableNative (pristine getter check)
#include "jit/VMFunctions.h"       // js::jit::GetNativeDataPropertyByValuePure
#include "js/Array.h"              // JS::NewArrayObject
#include "js/CallAndConstruct.h"   // JS::Call
#include "js/CharacterEncoding.h"  // JS_EncodeStringToUTF8
#include "js/Class.h"              // JSClass
#include "js/Conversions.h"        // JS::ToString, JS::ToObject
#include "js/EnvironmentChain.h"   // JS::SupportUnscopables
#include "js/Exception.h"          // JS_ClearPendingException
#include "js/experimental/JitInfo.h"  // JSJitInfo::InlinableNative
#include "js/friend/ErrorMessages.h"  // js::GetErrorMessage, JSMSG_*
#include "js/friend/WindowProxy.h"    // js::ToWindowIfWindowProxy
#include "js/GCAPI.h"               // JS_SetGCParameter, JS::SetGCSliceCallback
#include "js/GCVector.h"            // JS::RootedValueVector
#include "js/Id.h"                  // JS_ValueToId
#include "js/PropertyAndElement.h"  // JS_GetUCProperty, JS_GetPropertyById, ...
#include "js/Realm.h"               // JS::CurrentGlobalOrNull
#include "js/RootingAPI.h"          // JS::Rooted
#include "js/String.h"              // JS_NewUCStringCopyN
#include "js/Value.h"               // JS::Value
#include "runtime/NightContext.h"
#include "runtime/Night.h"  // js::night::NightAddPropCheck, the dyncode fuse
#include "runtime/NightObjectWord.h"
#include "runtime/NightHooks.h"  // js::night::gNightHooks (the vouched-store mask)
#include "runtime/NightRegExp.h"
#include "runtime/NightEntry.h"  // js::night::EnterNightStatus, NightApplyOrCall
#include "runtime/NightEnv.h"  // js::night::NightEnvDesc, night_runtime_install_env
#include "runtime/NightGenerator.h"  // js::night::NightGen* (generator engine half)
#include "runtime/NightHelperList.h"  // js::night::kNightHelpers (compile check)
#include "runtime/NightInlineCaches.h"  // js::night::NightPopulate* (IC populate)
#include "runtime/NightInlineHeap.h"  // js::night::NightAllocCell, the barriers
#include "runtime/NightOps.h"  // js::night::Night* (bytecode-op engine half)
#include "runtime/NightOpsInterp.h"  // js::night::NightDirectEval (baseline)
#include "builtin/MapObject.h"         // MapObject::class_ (the inline map get)
#include "runtime/NightRegionShape.h"   // Night_* region shape constants
#include "runtime/NightRegistration.h"  // js::night::gNightActivated
#include "runtime/NightRuntimeData.h"  // js::night::NightRuntimeData (regex table)
#include "runtime/NightRuntimeSlots.h"  // js::night::NightGet/SetHomeObject (isolated -inl TU)
#include "runtime/NightStack.h"
#include "builtin/Object.h"        // js::obj_toString
#include "builtin/ModuleObject.h"  // js::StartDynamicModuleImport (baseline)
#include "vm/ArgumentsObject.h"     // js::MappedArgumentsObject, Unmapped
#include "vm/ArrayBufferObject.h"   // js::ArrayBufferObject::byteLength
#include "vm/ArrayObject.h"         // js::ArrayObject
#include "vm/AsyncIteration.h"      // js::CreateAsyncFromSyncIterator
#include "vm/BytecodeUtil.h"        // JSDVG_IGNORE_STACK (JSOp::CheckReturn)
#include "vm/CompletionKind.h"      // js::CompletionKind
#include "vm/EnvironmentObject.h"   // js::BlockLexicalEnvironmentObject
#include "vm/EqualityOperations.h"  // js::LooselyEqual, js::StrictlyEqual
#include "vm/FunctionPrefixKind.h"  // js::FunctionPrefixKind (JSOp::SetFunName)
#include "vm/GlobalObject.h"        // GlobalObject::lexicalEnvironment
#include "vm/Interpreter.h"         // js::AddValues, SubValues, LessThan, ...
#include "vm/GeneratorObject.h"  // js::ResumeKindToAtom (JSOp::Resume)
#include "vm/SelfHosting.h"      // js::CallSelfHostedFunction (JSOp::Resume)
#include "vm/Iteration.h"    // js::ValueToIterator, IteratorMore, CloseIterator
#include "vm/JSAtomState.h"  // JSAtomState (cx->names())
#include "vm/JSAtomUtils.h"  // js::AtomizeChars (selfhosted patch arming)
#include "vm/JSContext.h"    // JSContext::nightStack
#include "vm/JSFunction.h"  // JSFunction, js::SetFunctionName, CloneFunctionReuseScript
#include "vm/JSScript.h"          // JSScript, BaseScript::gcthings
#include "gc/GC.h"                // js::gc::AutoSuppressGC
#include "vm/ObjectFuse.h"        // js::ObjectFuse (predicted-method cells)
#include "vm/ObjectOperations.h"  // js::DefineAccessorProperty
#include "vm/RegExpObject.h"      // js::CloneRegExpObject
#include "vm/Shape.h"             // js::BaseShape::offsetOfProto
#include "vm/SharedStencil.h"     // js::GCThingIndex (JSOp::FunWithProto)
#include "vm/StringType.h"        // js::StringEqualsLiteral
#include "vm/SymbolType.h"        // JS::Symbol::new_ (JSOp::NewPrivateName)
#include "vm/ThrowMsgKind.h"      // js::ThrowCondition, ThrowMsgKindToErrNum
#include "vm/TypedArrayObject.h"  // TypedArrayObject::getElementPure
#include "vm/Watchtower.h"        // js::Watchtower::watchesPropertyAdd

#include "vm/ArgumentsObject-inl.h"  // js::ArgumentsObject::setArg/arg
#include "vm/Interpreter-inl.h"      // HasOwnProperty, ToPropertyKeyOperation
#include "vm/JSScript-inl.h"         // JSScript::getRegExp
#include "vm/NativeObject-inl.h"  // initDenseElement, setDenseInitializedLength
#include "vm/ObjectOperations-inl.h"  // js::ClassMayResolveId
#include "vm/JSObject-inl.h"  // js::HasNoToPrimitiveMethodPure, IsNativeFunction

// Defined in vm/Interpreter.cpp (reactor build): resolve a global name exactly
// as the interpreter's CASE(GetGName), against the global lexical environment.

// Reinterpret a linear-memory byte offset as a typed host pointer. The reactor
// identity-maps its linear memory, so the u32 offset IS the host address; this
// centralizes the dozens of offset-to-typed-pointer casts. Taking `uintptr_t`
// matches the original static_cast for any integer offset width (u32 offsets
// widen; already-wide offsets pass through).
template <typename T>
static inline T* LinMem(uintptr_t addr) {
  return reinterpret_cast<T*>(addr);
}

// Little-endian cursor over a merge-embedded byte table. `u32()` reads without
// its own bounds check -- callers gate on `remaining()` exactly as the
// hand-written parsers did; the raw `p`/`end` stay accessible for
// variable-length byte fields.
struct ByteReader {
  const uint8_t* p;
  const uint8_t* end;
  ByteReader(uint32_t base, uint32_t len)
      : p(LinMem<const uint8_t>(base)), end(p + len) {}
  size_t remaining() const { return size_t(end - p); }
  uint32_t u32() {
    uint32_t v;
    memcpy(&v, p, sizeof(v));
    p += sizeof(v);
    return v;
  }
};

// memset a linear-memory region (u32 offset + byte length) to zero, for the GC
// callbacks that blanket-invalidate the pointer-caching caches.
static inline void ZeroRegion(uint32_t base, size_t len) {
  memset(LinMem<void>(base), 0, len);
}

// Direct-mapped cache hash mixing a shape word with an atom id (shared by the
// set-add, init-add, mega-get, mega-set, and guarded-chain tables).
static inline uint32_t CacheHash(uint32_t shape, uint32_t atomId) {
  return (shape >> 3) * 2654435761u ^ (atomId * 0x9e3779b9u);
}

// ===========================================================================
// Runtime state
// ===========================================================================
//
// Everything this file keeps between calls lives in one NightRuntimeState
// (defined at the end of the file, once every member's type is): the region
// table the image published, the interned name and binding tables, the
// pristine engine functions the compiled module's identity cells are armed
// from, the predicted this-layout table, the assorted derived addresses and
// one-way flags, the direct-mapped side caches, and the census. It belongs
// to the context's external-tier state (runtime/NightContext.h); SpiderMonkey
// runs one JSContext per JSRuntime, so state keyed by shapes and atoms (which
// are per runtime) is per runtime too. Each part is reached through an
// accessor taking the context (RtEnv(cx), RtNames(cx), ...): one load more
// than a global's address. Entry points the engine or the compiled module
// call with no context argument (the write barriers, the leaf probes) use
// CurrentNightContext(), the engine's current context for the thread.

static inline JSContext* CurrentNightContext() { return js::TlsContext.get(); }

// The region table `night_runtime_install_env` was handed: every reserved
// linear-memory base and length the helpers address, kept as the one table
// the image published rather than as a global per field. Zero means the
// image left that region out (older tool, or the feature disabled).
static js::night::NightEnvDesc& RtEnv(JSContext* cx);

// Fused constant globals: predicted (atomId -> literal bits), sorted by
// atomId. The fuse-cell region (`RtEnv(cx).fuseCellsPtr`) holds a u32 per
// binding, index == table position: 0 unarmed, 1 armed (compiled reads fold
// to the literal), 2 blown. Armed by the write helpers seeing exactly the
// predicted value; blown by any other write or delete; all blown at startup
// if ANY script stays interpreted, since its global writes would bypass the
// compiled hooks.
struct GnameFuse {
  uint32_t atom;
  uint32_t cell;  // fuse-cell index (== position in the embedded table)
  uint64_t literal;
};

// The name side of the wire: the compiled module names properties and global
// bindings by small integer, and these are the tables those integers index.
struct NightNameTables {
  // Property-name atom table, indexed by `atomId`, built at startup from
  // the merge-embedded table (UTF-16); source for the pre-interned `ids`
  // below and for diagnostic messages. `latin1`/`latin1Ok` are pre-deflated
  // Latin1 copies (index-parallel with `atoms`, valid where `latin1Ok` is
  // nonzero) so the paths that can avoid UTF-16 -- e.g. copying a string
  // literal's bytes -- need not re-scan and deflate the char16 data on
  // every use.
  std::vector<std::u16string> atoms;
  std::vector<std::string> latin1;
  std::vector<uint8_t> latin1Ok;
  // Pre-interned `PropertyKey` per `atomId`: the hot property paths take the
  // key straight out of here instead of re-atomizing per call. A deque for
  // stable element addresses (PersistentRooted registers itself by address).
  std::deque<JS::PersistentRooted<JS::PropertyKey>>* ids = nullptr;

  // The pre-interned global-binding names (binding-id -> PropertyKey), the
  // resolver's keys (mirrors `ids` above), in the order the `RtEnv(cx).gslotsPtr`
  // region the inlined `GetGName` reads uses.
  std::deque<JS::PersistentRooted<JS::PropertyKey>>* bindingKeys = nullptr;
  // atomId -> binding index (UINT32_MAX = none), and its inverse by name:
  // the hot write hooks' O(1) bridge from the atom-keyed helpers (set_name /
  // set_property) to the binding cells.
  std::vector<uint32_t> bindingOfAtom;
  std::unordered_map<std::u16string, uint32_t> bindingIdOfName;
  // Per binding: the address of the script whose function the compiler
  // predicts the binding holds (0 = none), from the binding table. Arming
  // with a compiled function of that script arms the predicted state
  // (Night_bindingFusePredicted), which compiled reads typed as that
  // function test.
  std::vector<uint32_t> bindingPredictedScript;

  std::vector<GnameFuse> fuses;
};
static NightNameTables& RtNames(JSContext* cx);

// The pristine engine functions the compiled module's identity cells are
// armed from. Each is a `PersistentRootedValue` because the cells hold raw
// boxed bits: a compacting major GC moves the function objects, and the
// rearm after each GC reads the current address back out of these.
struct NightPristineFns {
  // String.prototype.charCodeAt / charAt and String.fromCharCode, behind the
  // inline string-method call arms.
  JS::PersistentRootedValue* strCharCodeAt = nullptr;
  JS::PersistentRootedValue* strCharAt = nullptr;
  JS::PersistentRootedValue* strFromCharCode = nullptr;
  // Object.defineProperty / defineProperties / Reflect.defineProperty: the
  // define intercept compares the runtime callee against these.
  JS::PersistentRootedValue* defineProperty = nullptr;
  JS::PersistentRootedValue* defineProperties = nullptr;
  JS::PersistentRootedValue* reflectDefineProperty = nullptr;
  // RegExp.prototype.exec / .test, the self-hosted wrappers the regex arms
  // are allowed to fast-path.
  JS::PersistentRootedValue* regExpExec = nullptr;
  JS::PersistentRootedValue* regExpTest = nullptr;
  // The builtin callee-identity cells in translate::BC_* order; see the
  // arming code for the list. The count positions everything after the cells
  // in the host-constant block, so it is shared, not mirrored.
  static const uint32_t kCount = js::night::Night_builtinCellCount;
  JS::PersistentRootedValue* builtins[kCount] = {};
};
static NightPristineFns& RtFns(JSContext* cx);

// Likely this-layout table, parsed from the merge's data segment at startup:
// per layout id, the predicted field list (atomIds ordered by slot). The
// guard-cell region is `RtEnv(cx).layoutCellsPtr` ([shape u32, gen u32] per
// layout); the validator publishes a shape word (or the INVALID sentinel 1)
// into a cell, and the generation stamp invalidates it across major GCs like
// the property ICs.
struct NightLayoutTable {
  std::vector<std::vector<uint32_t>> rows;
  // Per layout: the longest prefix length over every clump member extending
  // it (self included), parsed from the layout blob; the add check's
  // harmless-append fast path compares assigned slots against it.
  std::vector<uint32_t> extLen;
  // Per layout, per field: its predicted type (`Claim` bits, 0 = none).
  std::vector<std::vector<uint32_t>> claims;
  // Whether TYPES has the any-type meaning, so the claims may keep it.
  bool anyTypes = false;
};
static NightLayoutTable& RtLayouts(JSContext* cx);

// The rest: the embedding's context, the addresses derived from `RtEnv(cx)` at
// install time, and the one-way flags.
struct NightState {
  // The embedding's long-lived context, captured by
  // night_runtime_install_env. Helpers with no context argument
  // (night_runtime_regex_ci_compare, the fuse hooks) resolve theirs here.
  JSContext* cx = nullptr;

  // Per-binding value-fuse cells (u32 per binding, right after the
  // `RtEnv(cx).gslotsPtr` rows).
  uint32_t globalValsBase = 0;
  // Inline string block (mirrors mod.rs strlit_slot): emptyString @0, the
  // string nursery header @4 and its alloc site's count address @8
  // (RefreshStringAlloc).
  uint32_t strLitBase = 0;
  // Inline string-method call guard cells (RtEnv(cx).propicGenPtr + 32/40/48) and
  // the builtin identity cells (+64): the boxed bits of the originals,
  // armed at startup and re-written after every major GC (function objects
  // move under compaction; the PersistentRooted values track them).
  uint32_t strCharCodeAtCell = 0;
  uint32_t strCharAtCell = 0;
  uint32_t strFromCharCodeCell = 0;
  uint32_t builtinCellsBase = 0;
  // Flat mirror of RtFns(cx).builtins[0]'s bits (Array.prototype.push) for the
  // native-dispatch fast-arm compare: one load, no PersistentRooted deref.
  // Rewritten wherever the cells are rearmed.
  uint64_t pushFnBits = 0;

  // Dynamic-code fuse (mirrors mod.rs `dyncode_fuse_word`, the args-metadata
  // block's tail pad). `dynCodeSeen` is the truth and survives the wizer
  // snapshot with the rest of the image; `dynCodeFuseAddr` is the compiled
  // module's copy of it, published at startup and written straight through
  // afterwards so an in-flight compiled frame sees the blow immediately (the
  // compiled read is inline and never hoisted over a call). Registration
  // re-arms: the registered graph is exactly what the analysis scanned.
  bool dynCodeSeen = false;
  uint32_t dynCodeFuseAddr = 0;

  // True when the nursery bump words were published at startup (nursery
  // object allocation live); alloc cells only fill then.
  bool nurseryInlineOK = false;
  // Whether this realm's Math.sin/cos use the fdlibm implementations
  // (captured at startup; the inline arm only fires on the pristine
  // main-realm Math methods, so one capture covers every call).
  bool useFdlibmSinCos = false;
  // Whether any prop-IC trans row currently caches a NURSERY proto pointer:
  // the minor-GC-end callback then zeroes every trans row (moved or reused
  // nursery addresses must never false-hit) and clears the flag. Stays clear
  // on GC-heavy workloads whose protos tenure at the first minor GC.
  bool transRowsHoldNursery = false;
  // Cleared for the process once interpreted code can write globals without
  // going through the compiled hooks; no fuse may be armed after that.
  bool bindingFuseArmingAllowed = true;
  // Binding cells armed with a NURSERY value: re-armed from the binding's
  // (rooted) slot at minor-GC end, when the value has moved. A program
  // that never runs a minor GC keeps the nursery pointer, which is exactly
  // as live as the slot it mirrors.
  std::vector<uint32_t> nurseryArmedBindings;
  // Per-binding count of changed GC-thing stores into an armed cell (the
  // inline store's leaf). Past `kBindingFlipLimit` the cell is blown for
  // good: a global that keeps changing objects is not fuse material.
  std::vector<uint32_t> bindingFlips;

  // The slice callback that was installed before ours (the shell installs
  // one), chained rather than clobbered.
  JS::GCSliceCallback prevSliceCallback = nullptr;

  // What the string-char-ops fuse word points at when the realm has no
  // fuse: never 0, the "fuse unavailable" sentinel.
  size_t poppedWord = 1;
  // The MIR guard-failure stress mode's call count.
  uint32_t stressCount = 0;
  // The stamp-invalidation epoch (NightObjectWord.h). Compiled code reads
  // it through the address published in the strlit block.
  uint64_t stampEpoch = 0;
};
static NightState& RtState(JSContext* cx);

// Dense-append cache region (the inline SetElem append arm's probe table;
// sized through NightRegionShape.h). Rows [shape, protoPtr0, protoShape0,
// protoPtr1, protoShape1, isArray, pad, pad], shape-hashed; primed by the
// generic set-element helper after a successful engine-side dense store on
// a validated receiver; zeroed on major GC (shapes/protos move; protos are
// tenured-only so minor GCs cannot invalidate).
static const uint32_t kAppendCacheRows = js::night::Night_appendCacheRows;
static const uint32_t kAppendCacheRowBytes =
    js::night::Night_appendCacheRowBytes;

// Accessor-call cache (sized through NightRegionShape.h): entries
// [callee u64, recvShape, atomId << 1 | kind, holderPtr, holderShape,
// pad], (recvShape, atom^kind)-hashed, GC-zeroed. The base rides its own
// region-table slot (ABI v5); images from older tools leave it 0 =
// disabled.
static const uint32_t kAccessorCacheRows = js::night::Night_accessorCacheRows;
static const uint32_t kAccessorCacheRowBytes =
    js::night::Night_accessorCacheRowBytes;

static void WriteAccessorEntry(JSContext* cx, uint32_t recvShape, uint32_t atomId,
                               uint32_t kind, uint64_t callee,
                               uint32_t holderPtr, uint32_t holderShape) {
  uint32_t ak = (atomId << 1) | kind;
  uint32_t h = ((recvShape >> 3) * 2654435761u) ^ (ak * 0x9e3779b9u);
  uint32_t idx = h & (kAccessorCacheRows - 1);
  uint32_t* e =
      LinMem<uint32_t>(RtEnv(cx).accessorCachePtr + idx * kAccessorCacheRowBytes);
  e[2] = 0;  // shape word first cleared, last written: validity marker
  memcpy(e, &callee, sizeof(callee));
  e[3] = ak;
  e[4] = holderPtr;
  e[5] = holderShape;
  e[2] = recvShape;
}
// Prime the dense-append cache row for `no`'s shape. Called from the
// generic set-element helper's dense fast path AFTER a successful
// engine-side dense store on this receiver -- so class admissibility
// (Array / hook-free), extensibility, no-own-indexed, and the proto
// consult have all just been validated for exactly this shape; the row
// only lets the inline arm replay what the engine path just did. The
// receiver-side conditions are pinned by the shape word; proto-side
// integrity is pinned by the cached proto shape words, which the inline
// arm re-reads LIVE (a proto gaining plain dense elements does not change
// its shape, but that never blocks a receiver APPEND -- shadowing is
// legal; accessors/non-writable indexed properties require sparsifying or
// freezing, both shape changes). Dictionary shapes mutate in place and
// UsedAsPrototype receivers may need teleport bookkeeping: not cached.
// Tenured protos only (minor GC must not invalidate); shapes are always
// tenured.
static void PrimeAppendRow(JSContext* cx, js::NativeObject* no) {
  js::Shape* shape = no->shape();
  if (!shape->isShared()) {
    return;
  }
  if (shape->objectFlags().hasFlag(js::ObjectFlag::IsUsedAsPrototype)) {
    return;
  }
  uint32_t protos[2][2] = {{0, 0}, {0, 0}};
  JSObject* p = no->staticPrototype();
  for (int i = 0; p; i++) {
    if (i >= 2 || !p->is<js::NativeObject>() || js::gc::IsInsideNursery(p)) {
      return;
    }
    protos[i][0] = uint32_t(reinterpret_cast<uintptr_t>(p));
    protos[i][1] = uint32_t(reinterpret_cast<uintptr_t>(p->shape()));
    p = p->as<js::NativeObject>().staticPrototype();
  }
  uint32_t s = uint32_t(reinterpret_cast<uintptr_t>(shape));
  uint32_t* row =
      LinMem<uint32_t>(RtEnv(cx).appendCachePtr +
                       (((s >> 3) * 2654435761u) & (kAppendCacheRows - 1)) *
                           kAppendCacheRowBytes);
  row[1] = protos[0][0];
  row[2] = protos[0][1];
  row[3] = protos[1][0];
  row[4] = protos[1][1];
  row[5] = no->is<js::ArrayObject>() ? 1 : 0;
  row[0] = s;
}
// Inline property-IC hit path. The GetProp hit path is emitted INLINE in
// the compiled Wasm (a shape + generation + holder-shape guard, then a slot
// load -- no runtime call); only a miss calls `night_runtime_get_prop_ic_miss`,
// which populates this linear-memory cache. Per site there are
// `INLINE_IC_WAYS` ways of 5 `u32` fields: [recvShape, ownFixedOff,
// holderPtr, holderShape, slotEnc] (`recvShape==0` = empty). The cache lives
// in the module's linear memory (reserved by the merge); `RtEnv(cx).propicPtr` is
// its base, `RtEnv(cx).propicGenPtr` a single `u32` generation counter the GC
// callback bumps on every major GC (so a moved/freed shape or holder
// invalidates the way at once -- the cheap blanket-invalidation validity
// model, whose cost stays low when major GCs are infrequent). Both addresses
// are linear-memory offsets, written via raw pointers (like `gGlobalSlots`).
//
// A GET site fills its ways first-come: the inline arm compares the
// receiver's shape against each way in turn and shares one hit tail, so a
// site with up to `INLINE_IC_WAYS` receiver shapes never leaves the body.
// A shape past the last way is served by the linear-memory mega table; the
// ways it has keep serving theirs. A SET site uses way 0 alone plus the
// poly sentinel.
static const uint32_t INLINE_IC_WAYS = js::night::Night_inlineIcWays;
static const uint32_t INLINE_IC_WAY_WORDS =
    5;  // recvShape,ownFixedOff,holderPtr,holderShape,slotEnc
static const uint32_t INLINE_IC_WAY_BYTES = js::night::Night_inlineIcWayBytes;
static_assert(INLINE_IC_WAY_BYTES == INLINE_IC_WAY_WORDS * 4,
              "the way's field list and its byte size disagree");
// Per-site add-transition row appended after the way (size shared through
// NightRegionShape.h): [oldShape, newShape, slotOff, absSlot, then four
// [protoPtr, protoShape] pairs]. slotOff is the fixed-slot byte offset
// (0 = dynamic slot, inline arm punts). GC-zeroed with the way; also zeroed
// at minor-GC end when any row cached a nursery proto.
static const uint32_t INLINE_IC_TRANS_OFF =
    INLINE_IC_WAYS * INLINE_IC_WAY_BYTES;
// FOUR proto hops, matching the global SET-add table. Two is a starvation
// cliff: a receiver whose add needs a third hop can never have its SITE row
// seeded, so its inline add arm never hits and every store calls the helper
// forever. Real class hierarchies routinely sit three or four hops deep.
static const uint32_t INLINE_IC_TRANS_BYTES =
    js::night::Night_inlineIcTransBytes;
static const uint32_t INLINE_IC_STRIDE = js::night::Night_inlineIcStride;
// Whether any trans row currently caches a NURSERY proto pointer: the
// minor-GC-end callback then zeroes every trans row (moved/reused nursery
// addresses must never false-hit) and clears the flag. Stays clear on
// GC-heavy workloads whose protos tenure at the first minor GC.

double night_runtime_math_unary(uint32_t kind, double x) {
  JSContext* cx = CurrentNightContext();
  if (RtState(cx).useFdlibmSinCos) {
    return kind ? js::math_cos_fdlibm_impl(x) : js::math_sin_fdlibm_impl(x);
  }
  return kind ? js::math_cos_native_impl(x) : js::math_sin_native_impl(x);
}

double night_runtime_math_pow(double x, double y) { return js::ecmaPow(x, y); }

double night_runtime_fmod(double x, double y) { return js::NumberMod(x, y); }

static void RearmBuiltinCells() {
  JSContext* cx = CurrentNightContext();
  if (RtFns(cx).builtins[0]) {
    RtState(cx).pushFnBits = RtFns(cx).builtins[0]->get().asRawBits();
  }
  if (!RtState(cx).builtinCellsBase) {
    return;
  }
  for (uint32_t i = 0; i < NightPristineFns::kCount; i++) {
    if (RtFns(cx).builtins[i]) {
      *LinMem<uint64_t>(RtState(cx).builtinCellsBase + 8 * i) =
          RtFns(cx).builtins[i]->get().asRawBits();
    }
  }
}

static void RearmStringMethodCells() {
  JSContext* cx = CurrentNightContext();
  if (RtState(cx).strCharCodeAtCell && RtFns(cx).strCharCodeAt) {
    *LinMem<uint64_t>(RtState(cx).strCharCodeAtCell) =
        RtFns(cx).strCharCodeAt->get().asRawBits();
  }
  if (RtState(cx).strCharAtCell && RtFns(cx).strCharAt) {
    *LinMem<uint64_t>(RtState(cx).strCharAtCell) = RtFns(cx).strCharAt->get().asRawBits();
  }
  if (RtState(cx).strFromCharCodeCell && RtFns(cx).strFromCharCode) {
    *LinMem<uint64_t>(RtState(cx).strFromCharCodeCell) =
        RtFns(cx).strFromCharCode->get().asRawBits();
  }
}

// True when `callee` is the pristine String.prototype.charCodeAt/charAt and
// `recv` is a rope: the call site flattens the rope once (mirrors CacheIR's
// LinearizeForCharAccess) so later calls hit the compiled linear-string arm.
static inline bool IsRopeCharAccess(JSContext* cx, const JS::Value& callee,
                                    const JS::Value& recv) {
  return recv.isString() && !recv.toString()->isLinear() &&
         ((RtFns(cx).strCharCodeAt &&
           callee.asRawBits() == RtFns(cx).strCharCodeAt->get().asRawBits()) ||
          (RtFns(cx).strCharAt &&
           callee.asRawBits() == RtFns(cx).strCharAt->get().asRawBits()));
}

// defineProperty intercept: the ORIGINAL Object.defineProperty /
// Object.defineProperties / Reflect.defineProperty (captured at startup,
// before user code runs). A native call through night_runtime_call whose callee
// is one of these and whose target is the active global redefines a binding
// WITHOUT hitting any compiled write hook -- blow the targeted binding's
// fuse (or all, for defineProperties) before the native runs. (Known
// residual holes, engine-internal invocations that skip night_runtime_call:
// defineProperty.apply/Reflect.apply forwarding of the native itself.)

// Pristine RegExp.prototype.exec/.test: the self-hosted wrappers otherwise run
// interpreted. Captured before user code runs; intercepted by callee identity
// in night_runtime_call to dispatch the engine's JIT exec/test directly.

// SET-side add-transition cache, direct-mapped on (oldShape, atomId): serves
// the poly sites whose single-entry site row ping-pongs between receiver
// shapes (e.g. subclasses funneled through one shared add site).
// Probed when the site row misses; same proto-guard set as the site row.
// Generation-validated against major GCs; zeroed with the trans rows at
// minor-GC end when any cached proto was nursery-resident.
struct SetAddRow {
  uint32_t gen = 0;
  uint32_t oldShape = 0;
  uint32_t atomId = 0;
  uint32_t newShape = 0;
  uint32_t slot = 0;
  uint32_t numProtos = 0;
  uint32_t protoPtrs[4] = {};
  uint32_t protoShapes[4] = {};
  // The transition skips slots (NightPopulateAddTransition): C++ replay
  // only, never copied into a site row.
  bool skip = false;
};
static const uint32_t kSetAddSize = 4096;
static SetAddRow* RtSetAdd(JSContext* cx);
static inline SetAddRow& SetAddAt(JSContext* cx, uint32_t shape, uint32_t atomId) {
  uint32_t h = CacheHash(shape, atomId);
  return RtSetAdd(cx)[h & (kSetAddSize - 1)];
}

// Init-define add-transition cache: direct-mapped on (oldShape, atomId), no
// per-site index (init_prop carries none) and no proto guards (defines never
// consult the chain). Same generation validity model as gAddTransitions.
struct InitAddRow {
  uint32_t gen = 0;
  uint32_t oldShape = 0;
  uint32_t atomId = 0;
  uint32_t newShape = 0;
  uint32_t slot = 0;
  bool skip = false;  // as SetAddRow's
};
static const uint32_t kInitAddSize = 4096;
static InitAddRow* RtInitAdd(JSContext* cx);
static inline InitAddRow& InitAddAt(JSContext* cx, uint32_t shape, uint32_t atomId) {
  uint32_t h = CacheHash(shape, atomId);
  return RtInitAdd(cx)[h & (kInitAddSize - 1)];
}
// Cache of function shapes proven to have the default @@hasInstance (direct
// proto == Function.prototype, no own @@hasInstance). Direct-mapped
// [shape,gen]; `gen` is the inline-IC generation (bumped on major GC) so a
// freed+reused shape pointer can't false-hit. Lets hot instanceof calls skip
// the per-call LookupPropertyPure verification.
static const uint32_t kHasInstCacheN = 64;
static uint32_t* RtHasInst(JSContext* cx);

// Megamorphic secondary GET cache: a global direct-mapped (receiver shape,
// atomId) -> property coordinate table consulted by the miss helper BEFORE the
// full JS_GetPropertyById. Polymorphic/megamorphic sites overflow the 4-way
// inline cache and would otherwise pay the whole generic lookup per read;
// here they pay one hash probe + a slot load. Same
// coordinate encoding and soundness argument as the inline IC ways (pure-
// lookup own/proto data slot; tenured proto holder revalidated by its shape
// word; the shared generation zeroes everything at major GC).
// The mega-GET table lives in LINEAR MEMORY so the compiled poly
// sites (mono way == the sentinel 1) probe it inline; this helper fills it.
// Entry: [shape, atomId, holderPtr, holderShape, slotEnc, pad] (24 bytes,
// translate.rs MEGA_* offsets). No generation field: the GC callback zeroes
// the whole table (and the per-site ways) at every major GC.
struct MegaGetEntry {
  uint32_t shape;  // receiver shape word; 0 = empty
  uint32_t atomId;
  uint32_t holderPtr;  // 0 = own slot (receiver-relative)
  uint32_t holderShape;
  uint32_t slotEnc;  // NightSlotEnc: byte offset | is-dynamic bit
  uint32_t pad;
};
static_assert(sizeof(MegaGetEntry) == js::night::Night_megaGetEntryBytes,
              "must match MEGA_GET_ENTRY_BYTES");
static constexpr size_t kMegaGetSize = js::night::Night_megaGetSize;

static inline size_t MegaGetSlot(uint32_t shape, uint32_t atomId) {
  uint32_t h = CacheHash(shape, atomId);
  return h & (kMegaGetSize - 1);
}
static inline MegaGetEntry* MegaGet(JSContext* cx, uint32_t shape, uint32_t atomId) {
  return LinMem<MegaGetEntry>(RtEnv(cx).megaGetPtr) + MegaGetSlot(shape, atomId);
}
// The poly-site marker in a SET site's way-0 recvShape (wasm/mir/abi.rs
// IC_POLY_SENTINEL); never a valid shape pointer. Get sites have no
// sentinel: their ways fill in turn and the mega table takes the rest.
static constexpr uint32_t kIcPolySentinel = 1;

// Guarded proto-chain GET cache (C++-side): serves reads whose
// chain NightPopulateInlineGetIC refuses (invalidated teleporting -- e.g. a
// deep prototype hierarchy that would otherwise take full engine lookups per
// read). Direct-mapped on (receiver shape, atomId) like the mega table; a hit
// re-validates EVERY hop's live shape (CacheIR non-teleporting semantics)
// then serves the holder slot. Chain pointers are tenured-only and the
// whole table is zeroed on major GC.
// The compiled get probe reads it too (its address is in the strlit block;
// the layout is shared through NightRegionShape.h).
struct GChainEntry {
  uint32_t shape;  // receiver shape word; 0 = empty
  uint32_t atomId;
  uint32_t nHops;  // 1..kGChainMaxHops; protoPtr[nHops-1] is the holder
  uint32_t slotEnc;
  uint32_t protoPtr[4];
  uint32_t protoShape[4];
};
static constexpr uint32_t kGChainMaxHops = js::night::Night_gchainMaxHops;
static constexpr size_t kGChainSize = js::night::Night_gchainSize;
static_assert((kGChainSize & (kGChainSize - 1)) == 0, "a power of two");
static_assert(sizeof(GChainEntry) == js::night::Night_gchainEntryBytes &&
                  offsetof(GChainEntry, nHops) == js::night::Night_gchainNhopsOff &&
                  offsetof(GChainEntry, slotEnc) ==
                      js::night::Night_gchainSlotEncOff &&
                  offsetof(GChainEntry, protoPtr) ==
                      js::night::Night_gchainProtoPtrOff &&
                  offsetof(GChainEntry, protoShape) ==
                      js::night::Night_gchainProtoShapeOff &&
                  kGChainMaxHops == 4,
              "GChainEntry must match NightRegionShape.h");
static_assert(js::night::kNightSlotEncAbsent ==
                  js::night::Night_icSlotEncAbsent,
              "the absent slotEnc");
static GChainEntry* RtGChain(JSContext* cx);

static inline GChainEntry* GChainSlot(JSContext* cx, uint32_t shape, uint32_t atomId) {
  uint32_t h = CacheHash(shape, atomId);
  return &RtGChain(cx)[h & (kGChainSize - 1)];
}

// Megamorphic secondary SET cache: the write-side mirror of `gMegaGet`.
// (receiver shape, atomId) -> own writable data slot, consulted by the set
// miss helper after the add-transition row but before the full
// JS_SetPropertyById. A hit is a hash probe + `setSlot` (which runs the
// pre/post write barriers). Same soundness as the inline set ways: a shape
// match implies the same own-slot layout, and the generation guard
// invalidates across major GCs.
// The SET-side megamorphic table lives in linear memory (the inline poly-set
// probe reads it; the size and field offsets are shared through
// NightRegionShape.h): [shape @0,
// atomId @4, slotEnc @8, absSlot @12]; zero = empty; GC-zeroed (shapes move
// only under a compacting major GC).
struct MegaSetEntry {
  uint32_t shape;  // receiver shape word; 0 = empty
  uint32_t atomId;
  uint32_t slotEnc;  // NightSlotEnc: byte offset | is-dynamic bit
  uint32_t absSlot;  // absolute slot for setSlot
};
static_assert(sizeof(MegaSetEntry) == js::night::Night_megaSetEntryBytes,
              "must match MEGA_SET_ENTRY_BYTES");
static const uint32_t kMegaSetSize = js::night::Night_megaSetSize;
static inline MegaSetEntry* MegaSet(JSContext* cx, uint32_t shape, uint32_t atomId) {
  uint32_t h = CacheHash(shape, atomId);
  return LinMem<MegaSetEntry>(RtEnv(cx).megaSetPtr) + (h & (kMegaSetSize - 1));
}
// Likely this-layout table (parsed from the merge's data segment at
// startup): per layout id, the predicted (atomId ordered by slot) field
// list; `RtEnv(cx).layoutCellsPtr` is the guard-cell region ([shape u32, gen u32]
// per layout). The validator publishes a shape word (or the INVALID
// sentinel 1) into a cell; the generation stamp invalidates across major
// GCs like the property ICs.
// Per layout: the longest prefix length over every clump member extending
// it (self included), parsed from the layout blob; the add check's
// harmless-append fast path compares assigned slots against it.

// Fused constant globals: predicted (atomId -> literal bits), sorted by
// atomId, plus the fuse-cell region base (u32 per binding, index == table
// position; 0 unarmed, 1 armed == compiled reads fold to the literal,
// 2 blown). Armed by the write helpers seeing exactly the predicted value;
// blown by any other write/delete; all blown at startup if ANY script stays
// interpreted (its global writes would bypass the compiled hooks).

static uint32_t* GnameFuseCell(JSContext* cx, uint32_t idx) {
  return LinMem<uint32_t>(RtEnv(cx).fuseCellsPtr + 4 * idx);
}

static const GnameFuse* FindGnameFuse(JSContext* cx, uint32_t atomId) {
  if (RtNames(cx).fuses.empty() || !RtEnv(cx).fuseCellsPtr) {
    return nullptr;
  }
  auto it = std::lower_bound(
      RtNames(cx).fuses.begin(), RtNames(cx).fuses.end(), atomId,
      [](const GnameFuse& f, uint32_t a) { return f.atom < a; });
  if (it == RtNames(cx).fuses.end() || it->atom != atomId) {
    return nullptr;
  }
  return &*it;
}

// The gname-fuse write handshake is split around the store: the blow half
// runs BEFORE the store (blowing early is conservative -- a fuse that could
// have stayed armed just disarms), and the arm half runs only AFTER a
// successful store. Arming before the store is unsound: a throwing write
// (non-writable binding under strict mode, throwing setter) leaves the
// binding holding its old value while an armed fuse would fold reads to the
// literal.
static void MaybeGnameFuseBlow(uint32_t atomId, uint64_t valueBits) {
  JSContext* cx = CurrentNightContext();
  if (const GnameFuse* f = FindGnameFuse(cx, atomId)) {
    if (valueBits != f->literal) {
      *GnameFuseCell(cx, f->cell) = 2;
    }
  }
}

static void BlowGnameFuse(uint32_t atomId) {
  JSContext* cx = CurrentNightContext();
  if (const GnameFuse* f = FindGnameFuse(cx, atomId)) {
    *GnameFuseCell(cx, f->cell) = 2;
  }
}

static void BlowAllGnameFuses() {
  JSContext* cx = CurrentNightContext();
  if (!RtEnv(cx).fuseCellsPtr) {
    return;
  }
  for (const GnameFuse& f : RtNames(cx).fuses) {
    *GnameFuseCell(cx, f.cell) = 2;
  }
}

// Whether `obj` is the active global (fused-global write detection).
// A `globalThis` receiver may be the global's WindowProxy (the shell's main
// global has one); writes through it land on the global, so unwrap before
// the identity check.
static bool IsActiveGlobal(JSObject* obj) {
  JSContext* cx = CurrentNightContext();
  if (!RtState(cx).cx) {
    return false;
  }
  JSObject* global = JS::CurrentGlobalOrNull(RtState(cx).cx);
  return global && js::ToWindowIfWindowProxy(obj) == global;
}

// Per-binding value fuses (definitions after the gGlobalVals globals
// below): fuseWord 0 = unarmed, 1 = armed, 2 = blown, 3 = armed with the
// binding's predicted function (NightRegionShape.h). Armed is bit 0.
static void MaybeBlowBindingFuseAtom(uint32_t atomId, uint64_t newBits);
static void BlowBindingFuseAtom(uint32_t atomId);
static void BlowBindingFuseKey(JS::PropertyKey id);
static void BlowAllBindingFuses();

extern "C" void night_runtime_distrust_global_fuses() {
  JSContext* cx = CurrentNightContext();
  BlowAllGnameFuses();
  BlowAllBindingFuses();
  RtState(cx).bindingFuseArmingAllowed = false;
}

// Pointer to way `way`'s first field for site `cacheIdx` in the linear-memory
// inline cache.
static inline uint32_t* InlineWay(JSContext* cx, uint32_t cacheIdx, uint32_t way) {
  uintptr_t addr = static_cast<uintptr_t>(RtEnv(cx).propicPtr) +
                   static_cast<uintptr_t>(cacheIdx) * INLINE_IC_STRIDE +
                   way * INLINE_IC_WAY_BYTES;
  return reinterpret_cast<uint32_t*>(addr);
}

// Pointer to site `cacheIdx`'s add-transition row.
static inline uint32_t* InlineTransRow(JSContext* cx, uint32_t cacheIdx) {
  uintptr_t addr = static_cast<uintptr_t>(RtEnv(cx).propicPtr) +
                   static_cast<uintptr_t>(cacheIdx) * INLINE_IC_STRIDE +
                   INLINE_IC_TRANS_OFF;
  return reinterpret_cast<uint32_t*>(addr);
}
static inline uint32_t InlineGen(JSContext* cx) {
  return *LinMem<uint32_t>(RtEnv(cx).propicGenPtr + js::night::Night_hostGenOff);
}

// The slot a cache row names, read off its holder.
static inline const JS::Value& SlotEncRead(const js::NativeObject* holder,
                                           uint32_t slotEnc) {
  uint32_t idx = js::night::NightSlotEncIndex(slotEnc);
  return js::night::NightSlotEncIsDynamic(slotEnc) ? holder->getDynamicSlot(idx)
                                                   : holder->getFixedSlot(idx);
}

// Record a receiver shape's coordinate in GET site `cacheIdx`'s inline ways:
// the way already holding this shape is refilled (a stale holder or slot),
// else the first empty way is taken, else nothing -- the mega table serves
// the shapes a site has outgrown its ways for. Word 1 is the pre-decoded
// own-fixed-slot byte offset the inline fast way loads through with no
// holder re-check (0 = proto holder or dynamic slot: the shared hit tail).
static void NoteGetWay(uint32_t cacheIdx, uint32_t recvShape,
                       uint32_t holderPtr, uint32_t holderShape,
                       uint32_t slotEnc) {
  JSContext* cx = CurrentNightContext();
  uint32_t* way = nullptr;
  for (uint32_t w = 0; w < INLINE_IC_WAYS; w++) {
    uint32_t* cand = InlineWay(cx, cacheIdx, w);
    if (cand[0] == recvShape) {
      way = cand;
      break;
    }
    if (cand[0] == 0 && !way) {
      way = cand;
    }
  }
  if (!way) {
    return;
  }
  way[1] = (holderPtr == 0 && !js::night::NightSlotEncIsDynamic(slotEnc))
               ? slotEnc
               : 0;
  way[2] = holderPtr;
  way[3] = holderShape;
  way[4] = slotEnc;
  way[0] = recvShape;  // shape last: the way's validity marker.
}

// Validated "no extra indexed properties" cache over the proto chain, for
// the dense-append paths (push arm leaf + set_element append), which
// otherwise pay the full ObjectMayHaveExtraIndexedProperties walk
// (class-hook + isIndexed + dense checks per proto) on EVERY element.
// Cacheable case: chains of depth <= 2 ending at null (Array.prototype ->
// Object.prototype). Shape identity pins a proto's class, object flags
// (isIndexed), and own [[Prototype]]; the dense initializedLength is NOT
// shape-pinned, so it is rechecked per hit. The generation stamp (bumped
// on major GC) guards freed-pointer reuse.
static const uint32_t kNoExtraCacheN = 16;
// p0, s0, p1, s1, gen per entry.
static uintptr_t* RtNoExtra(JSContext* cx);

static bool NoExtraIndexedFast(JSContext* cx, JSObject* o) {
  if (js::ObjectMayHaveExtraIndexedOwnProperties(o)) {
    return false;
  }
  js::NativeObject* no = &o->as<js::NativeObject>();
  JSObject* p0 = no->staticPrototype();
  if (!p0) {
    return true;
  }
  uint32_t gen = InlineGen(cx);
  uintptr_t* e =
      &RtNoExtra(cx)[((uintptr_t(p0) >> 4) & (kNoExtraCacheN - 1)) * 5];
  if (e[0] == uintptr_t(p0) && e[4] == uintptr_t(gen) &&
      uintptr_t(p0->shape()) == e[1]) {
    js::NativeObject* n0 = &p0->as<js::NativeObject>();
    if (n0->getDenseInitializedLength() == 0) {
      JSObject* p1 = n0->staticPrototype();
      if (uintptr_t(p1) == e[2] &&
          (!p1 ||
           (uintptr_t(p1->shape()) == e[3] &&
            p1->as<js::NativeObject>().getDenseInitializedLength() == 0))) {
        return true;
      }
    }
  }
  if (js::PrototypeMayHaveIndexedProperties(no)) {
    return false;
  }
  // Chain is clean; record it when it has depth <= 2 (both levels native,
  // ending at null -- guaranteed by the walk above reaching the end).
  JSObject* p1 = p0->as<js::NativeObject>().staticPrototype();
  if (!p1 || !p1->as<js::NativeObject>().staticPrototype()) {
    e[0] = uintptr_t(p0);
    e[1] = uintptr_t(p0->shape());
    e[2] = uintptr_t(p1);
    e[3] = p1 ? uintptr_t(p1->shape()) : 0;
    e[4] = uintptr_t(gen);
  }
  return true;
}

// Populate a per-site add-transition row (INLINE_IC_TRANS layout): newShape,
// the fixed-slot byte offset (0 = dynamic slot), the absolute slot, up to two
// proto [ptr, shape] guard pairs, then the old shape word LAST as the row's
// validity marker.
static inline void FillTransRow(uint32_t* row, uint32_t oldShape,
                                uint32_t newShape, uint32_t slot,
                                uint32_t nfixed, const uint32_t* protoPtrs,
                                const uint32_t* protoShapes,
                                uint32_t numProtos) {
  row[1] = newShape;
  row[2] = slot < nfixed
               ? uint32_t(sizeof(js::NativeObject) + slot * sizeof(JS::Value))
               : 0;
  row[3] = slot;
  for (uint32_t i = 0; i < 4; i++) {
    row[4 + 2 * i] = i < numProtos ? protoPtrs[i] : 0;
    row[5 + 2 * i] = i < numProtos ? protoShapes[i] : 0;
  }
  row[0] = oldShape;  // validity marker last
}

// MIR's element-add arm's row for a SetAddRow (Night_strlitElemAddOff):
// the transition in a site row's layout, then its key. A transition that
// skips slots is the C++ replay's alone.
static void SeedElemAddRow(JSContext* cx, const SetAddRow& t, uint32_t nfixed) {
  if (t.skip) {
    return;
  }
  uint32_t h = CacheHash(t.oldShape, t.atomId) & (js::night::Night_elemAddRows - 1);
  uint32_t* row = js::night::NightData(cx).elemAdd +
                  h * (js::night::Night_elemAddRowBytes / 4);
  row[0] = 0;
  row[js::night::Night_elemAddKeyOff / 4] = t.atomId;
  FillTransRow(row, t.oldShape, t.newShape, t.slot, nfixed, t.protoPtrs,
               t.protoShapes, t.numProtos);
}
static void NightGcSliceCallback(JSContext* cx, JS::GCProgress progress,
                                 const JS::GCDescription& desc);

// Pre-interned `PropertyKey` per `atomId`: the hot property
// helpers (`get_property`/`set_property`) index this instead of re-atomizing
// the UTF-16 chars on every access (the dominant generic-helper cost the call
// scoreboard surfaced). `PersistentRooted` self-registers as a GC root and is
// not movable, so a `std::deque` (stable element addresses) holds them.
// Populated by `BuildAtomIds`.

// Arm half of the gname-fuse write handshake (blow half above): the cell arms
// only when the global binding verifiably holds the literal as a plain own
// data slot right now. The read-back (pure lookup, no allocation) also covers
// accessor bindings, whose setter may have stored something other than the
// written value, and writes that resolved to a non-global binding of the same
// name.
static void MaybeGnameFuseArmAfterStore(JSContext* cx, uint32_t atomId,
                                        uint64_t valueBits) {
  const GnameFuse* f = FindGnameFuse(cx, atomId);
  if (!f || valueBits != f->literal) {
    return;
  }
  uint32_t* cell = GnameFuseCell(cx, f->cell);
  if (*cell != 0) {
    return;
  }
  JSObject* global = JS::CurrentGlobalOrNull(cx);
  if (!global || !RtNames(cx).ids || atomId >= RtNames(cx).ids->size()) {
    return;
  }
  JS::PropertyKey id = (*RtNames(cx).ids)[atomId].get();
  js::NativeObject* holder = nullptr;
  js::PropertyResult prop;
  if (js::LookupPropertyPure(cx, global, id, &holder, &prop) &&
      prop.isNativeProperty() && holder == global &&
      prop.propertyInfo().isDataProperty() &&
      holder->getSlot(prop.propertyInfo().slot()).asRawBits() == f->literal) {
    *cell = 1;
  }
}

// Cold (defineProperty intercept, and the computed-key `global[k] = v` /
// `delete global[k]` paths): blow a literal gname fuse by runtime jsid
// rather than every fuse (the fuse table is atomId-keyed; compare against
// the pre-interned keys). A blown fuse's read arm is a slower continuation,
// so a program that writes many computed-key globals at startup would
// otherwise pay that cost everywhere.
static void BlowGnameFuseKey(JS::PropertyKey id) {
  JSContext* cx = CurrentNightContext();
  if (!RtNames(cx).ids) {
    return;
  }
  for (const GnameFuse& f : RtNames(cx).fuses) {
    if ((*RtNames(cx).ids)[f.atom] == id) {
      *GnameFuseCell(cx, f.cell) = 2;
      return;
    }
  }
}

// Report a pending exception to stderr (best-effort; ToString of the value).
static void ReportPending(JSContext* cx) {
  if (!JS_IsExceptionPending(cx)) {
    return;
  }
  JS::RootedValue exc(cx);
  if (!JS_GetPendingException(cx, &exc)) {
    return;
  }
  JS_ClearPendingException(cx);
  JS::RootedString str(cx, JS::ToString(cx, exc));
  if (str) {
    JS::UniqueChars bytes = JS_EncodeStringToUTF8(cx, str);
    if (bytes) {
      fprintf(stderr, "night-rt: uncaught exception: %s\n", bytes.get());
      fflush(stderr);
      return;
    }
  }
  JS_ClearPendingException(cx);
  fputs("night-rt: uncaught exception (unprintable)\n", stderr);
}

extern "C" {

// Static fixed-slot store post-write (generational) barrier slow path: the
// driver inlines the raw store + the is-GC-thing/is-nursery check, and calls
// this only to record the (owner, slot) edge (forward to Interpreter.cpp, where
// the store buffer is visible). A leaf; no rooting/err handshake.
void night_runtime_post_write_barrier(uint64_t ownerBits, uint32_t slot,
                                      uint64_t valBits) {
#ifdef ENABLE_JS_NIGHTMONKEY
  js::night::NightPostWriteBarrier(ownerBits, slot, valBits);
#else
  (void)ownerBits;
  (void)slot;
  (void)valBits;
#endif
}

// Element variant of the post-write barrier behind the inlined dense `SetElem`
// store: records the `HeapSlot::Element` store-buffer edge (forward to
// Interpreter.cpp, which converts `index` to the unshifted store-buffer index
// from the owner). A leaf; no rooting/err handshake.
void night_runtime_post_write_barrier_elem(uint64_t ownerBits, uint32_t index,
                                           uint64_t valBits) {
#ifdef ENABLE_JS_NIGHTMONKEY
  js::night::NightPostWriteBarrierElem(ownerBits, index, valBits);
#else
  (void)ownerBits;
  (void)index;
  (void)valBits;
#endif
}

// Static fixed-slot store pre-write (incremental-marking) barrier slow
// path. The driver inlines the gate (reads the old value and the zone flag) and
// calls this only during active incremental marking, to mark the overwritten
// value (forward to Interpreter.cpp). A leaf; no rooting/err handshake.
void night_runtime_pre_write_barrier(uint64_t valBits) {
#ifdef ENABLE_JS_NIGHTMONKEY
  js::night::NightPreWriteBarrier(valBits);
#else
  (void)valBits;
#endif
}

void night_runtime_print(JSContext* cx, uint64_t val) {
  JS::RootedValue v(cx, JS::Value::fromRawBits(val));
  JS::RootedString str(cx, JS::ToString(cx, v));
  if (!str) {
    JS_ClearPendingException(cx);
    fputs("<night_runtime_print: ToString failed>\n", stdout);
    return;
  }
  JS::UniqueChars bytes = JS_EncodeStringToUTF8(cx, str);
  if (!bytes) {
    JS_ClearPendingException(cx);
    fputs("<night_runtime_print: encode failed>\n", stdout);
    return;
  }
  fputs(bytes.get(), stdout);
  fputc('\n', stdout);
  fflush(stdout);
}

#ifdef ENABLE_JS_NIGHTMONKEY
// "@@name" -> well-known-symbol property key (the few the selfhosted
// allowlist uses).
static bool ResolveWellKnownSymbolId(JSContext* cx, const std::string& name,
                                     JS::MutableHandleId id) {
  static const struct {
    const char* name;
    JS::SymbolCode code;
  } kSyms[] = {
      {"replace", JS::SymbolCode::replace},
      {"split", JS::SymbolCode::split},
      {"match", JS::SymbolCode::match},
      {"search", JS::SymbolCode::search},
      {"iterator", JS::SymbolCode::iterator},
  };
  for (const auto& e : kSyms) {
    if (name == e.name) {
      JS::Symbol* sym = cx->wellKnownSymbols().get(size_t(e.code));
      id.set(JS::PropertyKey::Symbol(sym));
      return true;
    }
  }
  return false;
}

// Resolve a dotted global path ("Array.prototype.forEach") to a JSFunction.
// A final "@@name" component is a well-known-symbol key (e.g.
// "RegExp.prototype.@@replace"); a "%Name%" path is a self-hosting intrinsic.
extern "C++" JSFunction* js::night::ResolveGlobalPath(JSContext* cx,
                                                      const char* path,
                                                      size_t len) {
  std::string s(path, len);
  JS::RootedValue v(cx);
  if (s.size() > 2 && s.front() == '%' && s.back() == '%') {
    std::u16string name16(s.begin() + 1, s.end() - 1);
    JSAtom* atom = js::AtomizeChars(cx, name16.data(), name16.size());
    if (!atom) {
      JS_ClearPendingException(cx);
      return nullptr;
    }
    JS::Rooted<js::PropertyName*> name(cx, atom->asPropertyName());
    if (!js::GlobalObject::getIntrinsicValue(cx, cx->global(), name, &v)) {
      JS_ClearPendingException(cx);
      return nullptr;
    }
  } else {
    v = JS::ObjectValue(*cx->global());
    size_t start = 0;
    for (;;) {
      size_t dot = s.find('.', start);
      std::string part = dot == std::string::npos
                             ? s.substr(start)
                             : s.substr(start, dot - start);
      if (!v.isObject()) {
        return nullptr;
      }
      JS::RootedObject obj(cx, &v.toObject());
      bool ok;
      if (part.rfind("@@", 0) == 0) {
        JS::RootedId id(cx);
        if (!ResolveWellKnownSymbolId(cx, part.substr(2), &id)) {
          return nullptr;
        }
        ok = JS_GetPropertyById(cx, obj, id, &v);
      } else {
        ok = JS_GetProperty(cx, obj, part.c_str(), &v);
      }
      if (!ok) {
        JS_ClearPendingException(cx);
        return nullptr;
      }
      if (dot == std::string::npos) {
        break;
      }
      start = dot + 1;
    }
  }
  if (!v.isObject() || !v.toObject().is<JSFunction>()) {
    return nullptr;
  }
  return &v.toObject().as<JSFunction>();
}

#endif  // ENABLE_JS_NIGHTMONKEY

// Bounds-checked atomId -> pre-interned PropertyKey. An out-of-range id
// is a merge/compiler invariant violation, so it aborts. The returned HandleId
// wraps the stable PersistentRooted in `RtNames(cx).ids`, so it stays valid across
// GC.
static inline JS::HandleId AtomIdChecked(JSContext* cx, uint32_t atomId) {
  if (atomId >= RtNames(cx).atoms.size()) {
    MOZ_CRASH("night-rt: atomId out of range");
  }
  return (*RtNames(cx).ids)[atomId];
}

// Intern each atom-table name to a `PropertyKey` once, after the realm is
// entered. Must run with `cx` in a realm (atomization needs one).
static bool BuildAtomIds(JSContext* cx) {
  RtNames(cx).ids = new std::deque<JS::PersistentRooted<JS::PropertyKey>>();
  for (const std::u16string& s : RtNames(cx).atoms) {
    JS::RootedId id(cx);
    JS::TwoByteChars chars(s.data(), s.size());
    if (!JS_CharsToId(cx, chars, &id)) {
      return false;
    }
    RtNames(cx).ids->emplace_back(cx, id);
  }
  return true;
}

// Fill the literal-atom table: a linear-memory array of `JSAtom*` indexed
// by atom-table id, its address written to the host slot at `slotAddr`.
static bool BuildAtomTable(JSContext* cx, uint32_t slotAddr) {
  size_t n = RtNames(cx).atoms.size();
  uint32_t* tbl = static_cast<uint32_t*>(malloc(n * sizeof(uint32_t)));
  if (!tbl) {
    return false;
  }
  for (size_t i = 0; i < n; i++) {
    const std::u16string& s = RtNames(cx).atoms[i];
    JSAtom* atom = js::AtomizeChars(cx, s.data(), s.size());
    if (!atom || !js::PinAtom(cx, atom)) {
      return false;
    }
    tbl[i] = static_cast<uint32_t>(reinterpret_cast<uintptr_t>(atom));
  }
  *LinMem<uint32_t>(slotAddr) =
      static_cast<uint32_t>(reinterpret_cast<uintptr_t>(tbl));
  return true;
}

static void NightNurseryEndCallback(JSContext* cx,
                                    JS::GCNurseryProgress progress,
                                    JS::GCReason reason, void* data);

// Inline string allocation (the strlit block's header and count words): the
// nursery cell header of a string allocated at the zone's catch-all string
// site, and the address of that site's allocation count, which the compiled
// allocation bumps as the engine's own does (the count is what the
// pretenuring heuristics weigh). Both 0 -- the compiled arms take their
// helper -- unless the zone allocates strings in the nursery. That flag moves
// only inside a GC, so a refresh at startup, after every minor GC and at the
// end of every cycle tracks it the way discarding JIT code does for Ion.
static void RefreshStringAlloc(JSContext* cx) {
  if (!RtState(cx).strLitBase) {
    return;
  }
  uint32_t header = 0;
  uint32_t countAddr = 0;
  if (RtState(cx).nurseryInlineOK) {
    js::night::NightNurseryStringAlloc(cx, &header, &countAddr);
  }
  *LinMem<uint32_t>(RtState(cx).strLitBase +
                    js::night::Night_strlitStrCountAddrOff) = countAddr;
  *LinMem<uint32_t>(RtState(cx).strLitBase + js::night::Night_strlitStrHeaderOff) =
      header;
}

static void NightStringAllocNurseryCallback(JSContext* cx,
                                            JS::GCNurseryProgress progress,
                                            JS::GCReason reason, void* data) {
  if (progress == JS::GCNurseryProgress::GC_NURSERY_COLLECTION_END) {
    RefreshStringAlloc(cx);
  }
}

// Per-binding value-fuse cells ([bits u64][fuseWord u32][pad], 16 bytes
// per binding, right after the gGlobalSlots rows). fuseWord 1 (armed) means
// bits IS the binding's current value -- the compiled read/call arms serve
// it on one load+compare. Armed at resolve when the value is tenured; blown
// (2, sticky) by every compiled global write path on a value CHANGE
// (rewriting the same bits keeps it armed) and unconditionally by deletes /
// defineProperty. The major-GC zero resets cells to 0 (unarmed) and the next
// resolve re-arms with the then-current value. No engine ObjectFuse, no
// Watchtower slow path on global writes. GC-zeroed with the rows.
static uint32_t* BindingFuseCell(JSContext* cx, uint32_t bindingId) {
  return LinMem<uint32_t>(RtState(cx).globalValsBase + 16 * bindingId);
}

static void BlowBindingFuseId(uint32_t bindingId) {
  JSContext* cx = CurrentNightContext();
  if (!RtState(cx).globalValsBase) {
    return;
  }
  uint32_t* cell = BindingFuseCell(cx, bindingId);
  if (cell[2] & 1) {
    cell[2] = js::night::Night_bindingFuseBlown;
  }
}

// A value CHANGE unarms the cell (0) rather than blowing it (2): the
// binding is still a plain data slot, only its value moved, so the next
// store's re-arm (`MaybeRearmBindingFuseAtom`) or the minor-GC-end retry
// caches the new value. Blown (2) is reserved for bindings that stop being
// plain data slots: a program that re-creates its heap-view globals on
// every run would otherwise put every one of its global reads on the
// slower slot prologue instead of the fuse arm.
static void MaybeBlowBindingFuseId(uint32_t bindingId, uint64_t newBits) {
  JSContext* cx = CurrentNightContext();
  if (!RtState(cx).globalValsBase) {
    return;
  }
  uint32_t* cell = BindingFuseCell(cx, bindingId);
  if ((cell[2] & 1) && *reinterpret_cast<uint64_t*>(cell) != newBits) {
    cell[2] = 0;
  }
}

static void MaybeArmBindingFuse(JSContext* cx, uint32_t bindingId,
                                JS::PropertyKey id);

// After a successful global store through a generic helper: re-arm the
// binding's cell from the stored (rooted) value.
static void MaybeRearmBindingFuseAtom(JSContext* cx, uint32_t atomId) {
  if (atomId < RtNames(cx).bindingOfAtom.size() &&
      RtNames(cx).bindingOfAtom[atomId] != UINT32_MAX && RtNames(cx).bindingKeys) {
    uint32_t bid = RtNames(cx).bindingOfAtom[atomId];
    MaybeArmBindingFuse(cx, bid, (*RtNames(cx).bindingKeys)[bid].get());
  }
}

static void MaybeBlowBindingFuseAtom(uint32_t atomId, uint64_t newBits) {
  JSContext* cx = CurrentNightContext();
  if (atomId < RtNames(cx).bindingOfAtom.size() &&
      RtNames(cx).bindingOfAtom[atomId] != UINT32_MAX) {
    MaybeBlowBindingFuseId(RtNames(cx).bindingOfAtom[atomId], newBits);
  }
}

static void BlowBindingFuseAtom(uint32_t atomId) {
  JSContext* cx = CurrentNightContext();
  if (atomId < RtNames(cx).bindingOfAtom.size() &&
      RtNames(cx).bindingOfAtom[atomId] != UINT32_MAX) {
    BlowBindingFuseId(RtNames(cx).bindingOfAtom[atomId]);
  }
}

// Cold (defineProperty intercept): match a runtime jsid against the
// pre-interned binding keys.
static void BlowBindingFuseKey(JS::PropertyKey id) {
  JSContext* cx = CurrentNightContext();
  if (!RtState(cx).globalValsBase || !RtNames(cx).bindingKeys) {
    return;
  }
  for (size_t i = 0; i < RtNames(cx).bindingKeys->size(); i++) {
    if ((*RtNames(cx).bindingKeys)[i].get() == id) {
      BlowBindingFuseId(uint32_t(i));
      return;
    }
  }
}

static void BlowAllBindingFuses() {
  JSContext* cx = CurrentNightContext();
  if (!RtState(cx).globalValsBase || !RtNames(cx).bindingKeys) {
    return;
  }
  for (size_t i = 0; i < RtNames(cx).bindingKeys->size(); i++) {
    BlowBindingFuseId(uint32_t(i));
  }
}

// Build `RtNames(cx).bindingKeys` from the merge-embedded binding table: per
// entry the UTF-16 name (like the atom table) plus a u32 predicted-script
// word. Must run with `cx` in a realm.
static bool BuildGlobalBindingKeys(JSContext* cx, uint32_t gbind_ptr,
                                   uint32_t gbind_len) {
  RtNames(cx).bindingKeys = new std::deque<JS::PersistentRooted<JS::PropertyKey>>();
  if (gbind_len < sizeof(uint32_t)) {
    return true;
  }
  ByteReader br(gbind_ptr, gbind_len);
  uint32_t count = br.u32();
  for (uint32_t i = 0; i < count; i++) {
    if (br.remaining() < sizeof(uint32_t)) {
      return false;
    }
    uint32_t clen = br.u32();
    if (br.remaining() < size_t(clen) * 2 + sizeof(uint32_t)) {
      return false;
    }
    std::u16string s;
    s.resize(clen);
    memcpy(s.data(), br.p, size_t(clen) * 2);
    br.p += size_t(clen) * 2;
    uint32_t predicted = br.u32();
    JS::RootedId id(cx);
    JS::TwoByteChars chars(s.data(), s.size());
    if (!JS_CharsToId(cx, chars, &id)) {
      return false;
    }
    RtNames(cx).bindingIdOfName.emplace(std::move(s), i);
    RtNames(cx).bindingPredictedScript.push_back(predicted);
    RtNames(cx).bindingKeys->emplace_back(cx, id);
  }
  return true;
}

// Fill `RtNames(cx).bindingOfAtom` (atomId -> bindingId) once both name tables
// exist.
static void BuildBindingOfAtom() {
  JSContext* cx = CurrentNightContext();
  RtNames(cx).bindingOfAtom.assign(RtNames(cx).atoms.size(), UINT32_MAX);
  for (size_t a = 0; a < RtNames(cx).atoms.size(); a++) {
    auto it = RtNames(cx).bindingIdOfName.find(RtNames(cx).atoms[a]);
    if (it != RtNames(cx).bindingIdOfName.end()) {
      RtNames(cx).bindingOfAtom[a] = it->second;
    }
  }
}

// Build the property-name atom table from the merge-embedded data (`u32 count`,
// then `count` x (`u32 char_len`, `char_len` x LE `u16`)).
static void BuildAtoms(uint32_t atom_ptr, uint32_t atom_len) {
  JSContext* cx = CurrentNightContext();
  RtNames(cx).atoms.clear();
  RtNames(cx).latin1.clear();
  RtNames(cx).latin1Ok.clear();
  if (atom_len < sizeof(uint32_t)) {
    return;
  }
  ByteReader br(atom_ptr, atom_len);
  uint32_t count = br.u32();
  RtNames(cx).atoms.reserve(count);
  for (uint32_t i = 0; i < count; i++) {
    if (br.remaining() < sizeof(uint32_t)) {
      return;
    }
    uint32_t clen = br.u32();
    if (br.remaining() < size_t(clen) * 2) {
      return;
    }
    std::u16string s;
    s.resize(clen);
    memcpy(s.data(), br.p, size_t(clen) * 2);  // LE u16 == char16_t on LE
    br.p += size_t(clen) * 2;
    bool latin1 = true;
    for (char16_t c : s) {
      if (c > 0xFF) {
        latin1 = false;
        break;
      }
    }
    std::string l;
    if (latin1) {
      l.reserve(s.size());
      for (char16_t c : s) {
        l.push_back(char(c));
      }
    }
    RtNames(cx).latin1Ok.push_back(latin1 ? 1 : 0);
    RtNames(cx).latin1.push_back(std::move(l));
    RtNames(cx).atoms.push_back(std::move(s));
  }
}

int32_t night_runtime_regex_ci_compare(uint32_t a_ptr, uint32_t b_ptr,
                                       uint32_t byte_len, uint32_t unicode) {
  JSContext* cx = CurrentNightContext();
  using MA = v8::internal::RegExpMacroAssembler;
  js::irregexp::Isolate* iso = RtState(cx).cx->isolate;
  auto a = static_cast<v8::Address>(a_ptr);
  auto b = static_cast<v8::Address>(b_ptr);
  return unicode ? MA::CaseInsensitiveCompareUnicode(a, b, byte_len, iso)
                 : MA::CaseInsensitiveCompareNonUnicode(a, b, byte_len, iso);
}

// Snapshot activation (executedAtInit): the top level ran before the
// compiled write hooks existed, so no write ever armed the gname fuses. Arm
// each fuse whose binding currently holds exactly the predicted literal;
// blown (2) cells stay blown. Requires BuildAtomIds
// (night_runtime_install_env).
extern "C" void night_runtime_arm_gname_fuses_from_live(JSContext* cx) {
  if (!RtEnv(cx).fuseCellsPtr || !RtNames(cx).ids) {
    return;
  }
  for (const GnameFuse& f : RtNames(cx).fuses) {
    uint32_t* cell = GnameFuseCell(cx, f.cell);
    if (*cell != 0) {
      continue;
    }
    uint64_t bits;
    if (js::night::NightTryBindingValue(cx, AtomIdChecked(cx, f.atom), &bits) &&
        bits == f.literal) {
      *cell = 1;
    }
  }
}

bool night_runtime_install_env(JSContext* cx,
                               const js::night::NightEnvDesc& env) {
  // Everything the image published about its reserved regions, taken as
  // one table rather than a global per field. Helpers with no context
  // argument resolve theirs through RtState(cx).cx.
  RtEnv(cx) = env;
  if (!RtState(cx).cx) {
    RtState(cx).cx = cx;
  }
#ifdef ENABLE_JS_NIGHTMONKEY
  // The inline instanceof proto-walk reads BaseShape::proto_ at a baked offset
  // (translate.rs BASESHAPE_PROTO_OFFSET = 8); assert no layout drift.
  MOZ_RELEASE_ASSERT(js::BaseShape::offsetOfProto() == 8,
                     "BaseShape::proto_ offset drift (instanceof inline)");
  // Generated code bakes fixed slots at object+16 with an 8-byte stride
  // (translate.rs FIXED_SLOTS_BASE / SLOT_SIZE); the pre-decoded IC way
  // offsets computed in this file assume the same layout.
  MOZ_RELEASE_ASSERT(sizeof(js::NativeObject) == 16 && sizeof(JS::Value) == 8,
                     "NativeObject fixed-slot layout drift (baked offsets)");
#endif
  BuildAtoms(env.atomPtr, env.atomLen);
  // AOT regex matcher table -> runtime nightData().regexTable (see
  // NightRuntime.h for the wire format). Pattern chars point directly into the
  // embedded segment (it is never reused).
  if (env.regexLen >= 4) {
    const uint8_t* p = LinMem<const uint8_t>(env.regexPtr);
    const uint8_t* end = p + env.regexLen;
    uint32_t count;
    memcpy(&count, p, 4);
    p += 4;
    auto* table = static_cast<js::night::NightRegexEntry*>(
        count ? malloc(sizeof(js::night::NightRegexEntry) * count) : nullptr);
    uint32_t n = 0;
    while (table && n < count && p + 24 <= end) {
      js::night::NightRegexEntry e;
      memcpy(&e.flags, p, 4);
      memcpy(&e.latin1Idx, p + 4, 4);
      memcpy(&e.twobyteIdx, p + 8, 4);
      memcpy(&e.numRegisters, p + 12, 4);
      memcpy(&e.pairCount, p + 16, 4);
      uint32_t plen;
      memcpy(&plen, p + 20, 4);
      p += 24;
      if (p + 2 * size_t(plen) > end) {
        break;
      }
      e.pattern = reinterpret_cast<const char16_t*>(p);
      e.patternLen = plen;
      p += 2 * size_t(plen);
      table[n++] = e;
    }
    js::night::NightRuntimeData& aot = js::night::NightData(cx);
    bool installed = false;
    if (n > 0) {
      constexpr uint32_t kBtElems = 1u << 20;  // 4 MB backtrack scratch
      aot.regexBtStack = static_cast<int32_t*>(malloc(kBtElems * 4));
      if (aot.regexBtStack) {
        aot.regexBtStackElems = kBtElems;
        aot.regexTable = table;
        aot.regexTableCount = n;
        installed = true;
      }
    }
    if (!installed) {
      free(table);
    }
  }
  // Gname fuse table: u32 count, then per binding u32 atomId + u64 literal
  // bits; the fuse-cell index is the table position.
  {
    const uint8_t* p = LinMem<const uint8_t>(env.fusePtr);
    const uint8_t* end = p + env.fuseLen;
    if (env.fuseLen >= 4) {
      uint32_t count;
      memcpy(&count, p, 4);
      p += 4;
      for (uint32_t i = 0; i < count && p + 12 <= end; i++) {
        GnameFuse f;
        f.cell = i;
        memcpy(&f.atom, p, 4);
        memcpy(&f.literal, p + 4, 8);
        p += 12;
        RtNames(cx).fuses.push_back(f);
      }
      std::sort(RtNames(cx).fuses.begin(), RtNames(cx).fuses.end(),
                [](const GnameFuse& a, const GnameFuse& b) {
                  return a.atom < b.atom;
                });
    }
  }
  // Likely this-layout table: u32 count, then per layout u32 nfields +
  // nfields x u32 atomId (predicted slot == position).
  {
    ByteReader br(env.layoutPtr, env.layoutLen);
    if (env.layoutLen >= 8) {
      // Flags: bit 8, the field claims may keep TYPES (the any-type
      // meaning of the MIR and baseline tiers).
      RtLayouts(cx).anyTypes = (br.u32() & 0x100) != 0;
      uint32_t count = br.u32();
      for (uint32_t i = 0; i < count && br.p + 4 <= br.end; i++) {
        uint32_t nf = br.u32();
        std::vector<uint32_t> fields;
        for (uint32_t j = 0; j < nf && br.p + 4 <= br.end; j++) {
          fields.push_back(br.u32());
        }
        // The per-layout add-check bound (byte-offset form): fill the
        // static bound table (read by the compiled unknown-receiver add
        // arms) and keep the slot-index form for the engine hook's fast
        // path.
        uint32_t bound = br.p + 4 <= br.end ? br.u32() : 0;
        if (RtEnv(cx).layoutCellsPtr) {
          *LinMem<uint32_t>(RtEnv(cx).layoutCellsPtr + 8 * i) = bound;
          // The row's second word: the layout's OWN byte bound, for the
          // add checks' clear-vs-advance-ineligible split.
          *LinMem<uint32_t>(RtEnv(cx).layoutCellsPtr + 8 * i + 4) =
              16 + 8 * uint32_t(fields.size());
        }
        RtLayouts(cx).extLen.push_back(bound >= 16 ? (bound - 16) / 8
                                              : uint32_t(fields.size()));
        std::vector<uint32_t> claims;
        for (uint32_t j = 0; j < nf && br.p + 4 <= br.end; j++) {
          claims.push_back(br.u32());
        }
        RtLayouts(cx).claims.push_back(std::move(claims));
        RtLayouts(cx).rows.push_back(std::move(fields));
      }
    }
  }
  JS::RootedObject global(cx, JS::CurrentGlobalOrNull(cx));
  if (!global) {
    fputs("night_runtime_install_env: no current global\n", stderr);
    return false;
  }
  // Pre-intern property keys now that we are in a realm.
  if (!BuildAtomIds(cx)) {
    ReportPending(cx);
    return false;
  }
  // Pre-intern the global-binding names and record the slot-cache base.
  // The bindings themselves do not exist yet (GlobalOrEvalDeclInstantiation is
  // the global script's first op, run inside JS_ExecuteScript below), so the
  // slots are resolved lazily on first access; the region stays zero (==
  // unresolved) until then.
  if (!BuildGlobalBindingKeys(cx, env.gbindPtr, env.gbindLen)) {
    ReportPending(cx);
    return false;
  }
  BuildBindingOfAtom();

  // Record the inline property-IC region bases (the merge reserved both,
  // zero-initialized) and install the major-GC generation-bump callback. The
  // region stays all-zero (every way empty) until the miss helper populates it.
  RtState(cx).prevSliceCallback = JS::SetGCSliceCallback(cx, NightGcSliceCallback);
  js::nightrt::NightStateOf(cx)->propIcBase = env.propicPtr;
  // Startup-written host constants the AOT'd module cannot embed (the merge
  // reserved u32 slots at +8/+12/+16; layout mirrored in wasm/mod.rs): the two
  // JSFunction class addresses for the inline callee classify's clasp
  // compares, and the StaticStrings unit-string table base for the inline
  // string s[i] element path.
  *LinMem<uint32_t>(env.propicGenPtr + js::night::Night_hostFnClassOff) =
      static_cast<uint32_t>(reinterpret_cast<uintptr_t>(&js::FunctionClass));
  *LinMem<uint32_t>(env.propicGenPtr + js::night::Night_hostFnClassOff + 4) =
      static_cast<uint32_t>(
          reinterpret_cast<uintptr_t>(&js::ExtendedFunctionClass));
  *LinMem<uint32_t>(env.propicGenPtr + js::night::Night_hostStaticStringsOff) =
      static_cast<uint32_t>(reinterpret_cast<uintptr_t>(
          cx->staticStrings().unitStaticTableBase()));
  // The literal-atom table (+20): one JSAtom* per atom-table id, the value
  // `JSOp::String` pushes. Pinned, so the atoms live as long as the runtime
  // and, being in the atoms zone, never move: the compiled read is a load
  // off this table and a tag, the same value the interpreter pushes.
  if (!BuildAtomTable(cx,
                      env.propicGenPtr + js::night::Night_hostAtomTableOff)) {
    ReportPending(cx);
    return false;
  }
  // Inline string-method call guard cells (+32/+40/+48): the boxed bits of
  // the PRISTINE String.prototype.charCodeAt / charAt / String.fromCharCode
  // (user code has not run yet, so these are the originals whose behavior
  // the inline arms mirror). +56 holds the ADDRESS of the engine's
  // OptimizeStringCharOpsFuse guard word: Watchtower pops it on any mutation
  // of those properties, so `word == 0` proves a GetProp of them on a string
  // receiver yields the cached original -- the lookup is elided entirely.
  RtState(cx).strCharCodeAtCell =
      env.propicGenPtr + js::night::Night_hostStrCharCodeAtOff;
  RtState(cx).strCharAtCell = env.propicGenPtr + js::night::Night_hostStrCharAtOff;
  RtState(cx).strFromCharCodeCell =
      env.propicGenPtr + js::night::Night_hostStrFromCharCodeOff;
  {
    size_t* fuseWord = js::night::NightStringCharOpsFuseWord(cx);
    *LinMem<uint32_t>(env.propicGenPtr +
                      js::night::Night_hostStrCharOpsFuseOff) =
        static_cast<uint32_t>(
            reinterpret_cast<uintptr_t>(fuseWord ? fuseWord
                                                : &RtState(cx).poppedWord));
    // +60: &js::ArrayObject::class_ -- the inline array-length arm's clasp
    // identity compare (was the global ObjectFuse word).
    *LinMem<uint32_t>(env.propicGenPtr + js::night::Night_hostArrayClassOff) =
        static_cast<uint32_t>(
            reinterpret_cast<uintptr_t>(&js::ArrayObject::class_));
    // TA-clasp table, right after the builtin cells (NightTaClassBase,
    // shared with mod.rs `ta_class_base` through NightRegionShape.h): the
    // fixed-length typed-array class pointer for element kind 1..=9 at index
    // kind-1, guarding the inline TA read arm.
    {
      uint32_t taBase = js::night::NightTaClassBase(env.propicGenPtr);
      static const js::Scalar::Type kKindType[9] = {
          js::Scalar::Int8,   js::Scalar::Uint8,   js::Scalar::Uint8Clamped,
          js::Scalar::Int16,  js::Scalar::Uint16,  js::Scalar::Int32,
          js::Scalar::Uint32, js::Scalar::Float32, js::Scalar::Float64};
      for (int i = 0; i < 9; i++) {
        const JSClass* c =
            &js::TypedArrayObject::fixedLengthClasses[kKindType[i]];
        *LinMem<uint32_t>(taBase + 4 * i) =
            static_cast<uint32_t>(reinterpret_cast<uintptr_t>(c));
      }
      // The table's alignment pad (Night_taClassDdaFuseOff, shared with
      // mod.rs dda_fuse_addr_slot) holds the ADDRESS of the runtime's
      // HasSeenObjectEmulateUndefinedFuse guard word: while the word is 0
      // (intact), no object anywhere emulates undefined, so the compiled
      // loose-eq nullish and truthiness arms skip the per-operand clasp walk.
      *LinMem<uint32_t>(taBase + js::night::Night_taClassDdaFuseOff) =
          static_cast<uint32_t>(reinterpret_cast<uintptr_t>(
              js::night::NightEmulatesUndefinedFuseWord(cx)));
      // args-object inline metadata right after the TA table
      // (NightArgsClassBase, shared with mod.rs `args_class_base`): [mapped @0,
      // unmapped @4, ArgumentsData::offsetOfArgs() @8, pad @12]. The clasp pair
      // guards the inline `arguments.length` / `arguments[i]` arms; the offset
      // (engine constexpr, no layout-drift risk) locates the element Value
      // array off `data()` (DATA_SLOT payload).
      uint32_t argsBase = js::night::NightArgsClassBase(env.propicGenPtr);
      *LinMem<uint32_t>(argsBase + js::night::Night_argsClassMappedOff) =
          static_cast<uint32_t>(
              reinterpret_cast<uintptr_t>(&js::MappedArgumentsObject::class_));
      *LinMem<uint32_t>(argsBase + js::night::Night_argsClassUnmappedOff) =
          static_cast<uint32_t>(reinterpret_cast<uintptr_t>(
              &js::UnmappedArgumentsObject::class_));
      *LinMem<uint32_t>(argsBase + js::night::Night_argsClassDataArgsOff) =
          static_cast<uint32_t>(js::ArgumentsData::offsetOfArgs());
      // The block's tail pad (Night_argsDynCodeFuseOff, shared with mod.rs
      // `dyncode_fuse_word`) is
      // the dynamic-code fuse WORD itself, not an address: the engine has
      // no such word to point at, so night owns it and the compiled guard
      // is one load and one test. Seeded from the truth flag, which is
      // already set if source was compiled after registration but before
      // the snapshot.
      RtState(cx).dynCodeFuseAddr = argsBase + js::night::Night_argsDynCodeFuseOff;
      *LinMem<uint32_t>(RtState(cx).dynCodeFuseAddr) = RtState(cx).dynCodeSeen ? 1u : 0u;
      // Inline string-literal block right after the args metadata
      // (NightStrLitBase, shared with mod.rs strlit_slot): [emptyString @0]
      // (permanent atom, armed here, never zeroed) + the thin/fat replay
      // triples [hdr, flags, total] the slow night_runtime_string fills (zeroed
      // on major GC
      // -- the header word embeds zone/alloc-site pointers).
      RtState(cx).strLitBase = js::night::NightStrLitBase(env.propicGenPtr);
      *LinMem<uint32_t>(RtState(cx).strLitBase) =
          static_cast<uint32_t>(reinterpret_cast<uintptr_t>(cx->emptyString()));
      // The MapObject class: the inline map lookup's receiver check.
      *LinMem<uint32_t>(RtState(cx).strLitBase +
                        js::night::Night_strlitMapClassOff) =
          static_cast<uint32_t>(reinterpret_cast<uintptr_t>(&js::MapObject::class_));
      // The guarded-chain GET table, which the compiled get probe reads.
      *LinMem<uint32_t>(RtState(cx).strLitBase +
                        js::night::Night_strlitGchainAddrOff) =
          static_cast<uint32_t>(reinterpret_cast<uintptr_t>(RtGChain(cx)));
      // The strlit block's tail pad (Night_strlitStampEpochAddrOff)
      // publishes the address of the
      // stamp-invalidation epoch (vm/JSObject.h): compiled code compares
      // its low word around non-quiet helper calls so a helper that ran
      // but demoted nothing keeps FLAG_STAMPS clear -- the runtime-precise
      // replacement for saturating the bit at every helper site.
      *LinMem<uint32_t>(RtState(cx).strLitBase +
                        js::night::Night_strlitStampEpochAddrOff) =
          static_cast<uint32_t>(
              reinterpret_cast<uintptr_t>(&RtState(cx).stampEpoch));
      // The compartment's active-iterator list, which a for-in started in
      // compiled code joins (as the JIT's registerIterator, whose IC embeds
      // the same address).
      *LinMem<uint32_t>(RtState(cx).strLitBase +
                        js::night::Night_strlitEnumeratorsOff) =
          static_cast<uint32_t>(
              reinterpret_cast<uintptr_t>(cx->compartment()->enumeratorsAddr()));
      // MIR's regexp arm: the realm's RegExp.prototype fuse word, the
      // regex-leaf block (with the matchers' backtrack scratch), and the
      // optimizable shape, unarmed.
      {
        js::night::NightRuntimeData& aot = js::night::NightData(cx);
        aot.regexLeaf.btStack = aot.regexBtStack;
        aot.regexLeaf.btElems = aot.regexBtStackElems;
        *LinMem<uint32_t>(RtState(cx).strLitBase +
                          js::night::Night_strlitRegExpFuseAddrOff) =
            static_cast<uint32_t>(reinterpret_cast<uintptr_t>(
                cx->realm()->realmFuses.optimizeRegExpPrototypeFuse.fuseRef()));
        *LinMem<uint32_t>(RtState(cx).strLitBase +
                          js::night::Night_strlitRegexLeafOff) =
            static_cast<uint32_t>(reinterpret_cast<uintptr_t>(&aot.regexLeaf));
        *LinMem<uint32_t>(RtState(cx).strLitBase +
                          js::night::Night_strlitRegExpShapeOff) = 0;
        *LinMem<uint32_t>(RtState(cx).strLitBase +
                          js::night::Night_strlitElemAddOff) =
            static_cast<uint32_t>(reinterpret_cast<uintptr_t>(aot.elemAdd));
      }
      // The plain-object class: MIR's `guard.kind Plain` compares a
      // receiver's clasp against it.
      *LinMem<uint32_t>(RtState(cx).strLitBase +
                        js::night::Night_strlitPlainClassOff) =
          static_cast<uint32_t>(
              reinterpret_cast<uintptr_t>(&js::PlainObject::class_));
      MOZ_RELEASE_ASSERT(JSString::offsetOfFlags() == 0);
      MOZ_RELEASE_ASSERT(JSString::offsetOfLength() == 4);
      MOZ_RELEASE_ASSERT(JSThinInlineString::MAX_LENGTH_LATIN1 == 8);
      MOZ_RELEASE_ASSERT(JSFatInlineString::MAX_LENGTH_LATIN1 == 24);
      MOZ_RELEASE_ASSERT(sizeof(JSString) == 16);
      MOZ_RELEASE_ASSERT(sizeof(JSFatInlineString) == 32);
      MOZ_RELEASE_ASSERT(js::night::NightCheckRopeLayout(cx));
      MOZ_RELEASE_ASSERT(js::night::NightCheckIteratorLayout());
    }
    // Per-binding value fuses: enable the cells (right after the
    // gGlobalSlots rows) unless the kill switch is set; the nursery-end
    // callback re-tries cells whose value was nursery-young at resolve.
    if (RtNames(cx).bindingKeys) {
      RtState(cx).globalValsBase =
          env.gslotsPtr + uint32_t(RtNames(cx).bindingKeys->size()) * 8;
      JS::AddGCNurseryCollectionCallback(cx, NightNurseryEndCallback, nullptr);
    }
  }
  {
    JS::RootedObject strProto(cx);
    JS::RootedValue ccat(cx), cat(cx), fcc(cx);
    JS::RootedValue strCtor(cx);
    if (JS_GetClassPrototype(cx, JSProto_String, &strProto) && strProto &&
        JS_GetProperty(cx, strProto, "charCodeAt", &ccat) &&
        JS_GetProperty(cx, strProto, "charAt", &cat) &&
        JS_GetProperty(cx, strProto, "constructor", &strCtor) &&
        ccat.isObject() && cat.isObject() && strCtor.isObject()) {
      RtFns(cx).strCharCodeAt = new JS::PersistentRootedValue(cx, ccat);
      RtFns(cx).strCharAt = new JS::PersistentRootedValue(cx, cat);
      JS::RootedObject ctorObj(cx, &strCtor.toObject());
      if (JS_GetProperty(cx, ctorObj, "fromCharCode", &fcc) && fcc.isObject()) {
        RtFns(cx).strFromCharCode = new JS::PersistentRootedValue(cx, fcc);
      }
      RearmStringMethodCells();
    } else {
      JS_ClearPendingException(cx);
    }
  }
  // Builtin callee-identity cells (Night_hostBuiltinCellsOff,
  // Night_builtinCellCount u64 cells in translate::BC_* order: push, pop,
  // sqrt, abs, floor, min, max, sin, cos, pow, parseInt, clz32, imul, then
  // the String.prototype direct-dispatch methods indexOf, lastIndexOf,
  // slice, substring, toLowerCase, toUpperCase, trim, startsWith, endsWith,
  // includes, then the Array constructor, Function.prototype.apply,
  // Function.prototype.call, Object.prototype.hasOwnProperty, and
  // RegExp.prototype.exec and .test, armed with their capture below): capture
  // the pristine builtins (user code has not run yet); the boxed bits of
  // each are re-written after every GC (functions move under compaction and
  // tenure out of the nursery; the PersistentRooted values track them).
  // Keep in sync with translate::BC_COUNT. A fetch failure just leaves that
  // cell unarmed.
  {
    RtState(cx).builtinCellsBase =
        env.propicGenPtr + js::night::Night_hostBuiltinCellsOff;
    JS::RootedValue v(cx);
    // Only arm cells whose pristine value is a genuine C++ native: the
    // direct-dispatch arm calls `fun->native()` in place, which would trap for
    // a self-hosted builtin (e.g. some String.prototype methods). A skipped
    // (unarmed, 0) cell can never match a runtime callee, so those calls take
    // the generic path -- correct, just not inlined.
    // Self-hosted builtins count (`Object.prototype.hasOwnProperty`): the
    // cells compare value identity, not the implementation.
    auto arm = [&](int idx) {
      if (v.isObject() && v.toObject().is<JSFunction>() &&
          (v.toObject().as<JSFunction>().isNativeFun() ||
           v.toObject().as<JSFunction>().isSelfHostedBuiltin())) {
        RtFns(cx).builtins[idx] = new JS::PersistentRootedValue(cx, v);
      }
    };
    JS::RootedObject g(cx, JS::CurrentGlobalOrNull(cx));
    {
      JS::RootedObject arrProto(cx);
      if (JS_GetClassPrototype(cx, JSProto_Array, &arrProto) && arrProto &&
          JS_GetProperty(cx, arrProto, "push", &v)) {
        arm(0);
        if (JS_GetProperty(cx, arrProto, "pop", &v)) {
          arm(1);
        }
        // The pristine Array CONSTRUCTOR (BC_ARRAY_CTOR = 23): the compiled
        // `new Array()` arm matches the construct callee by value identity
        // against this cell and nursery-bumps an empty dense array in
        // place; a shadowed/monkeypatched Array is a different value, the
        // compare self-misses, and the site takes the generic construct.
        if (JS_GetProperty(cx, arrProto, "constructor", &v)) {
          arm(23);
        } else {
          JS_ClearPendingException(cx);
        }
      } else {
        JS_ClearPendingException(cx);
      }
    }
    {
      // `Function.prototype.apply` (BC_FUN_APPLY = 24). The apply-forward
      // fast arm calls the resolved target DIRECTLY instead of going through
      // `night_runtime_apply_fwd`, which is only correct if the `.apply` the
      // site actually reached is the pristine one -- the helper's own
      // `native() == js::fun_apply` test, hoisted into compiled code as a
      // value-identity compare against this cell. A monkeypatched or
      // shadowed apply is a different value, the compare self-misses, and
      // the site takes the helper.
      JS::RootedObject funProto(cx);
      if (JS_GetClassPrototype(cx, JSProto_Function, &funProto) && funProto &&
          JS_GetProperty(cx, funProto, "apply", &v)) {
        arm(24);
        // `Function.prototype.call` (BC_FUN_CALL = 25), the `.call` half of
        // the `hasOwnProperty.call(o, k)` arm's identity guard.
        if (JS_GetProperty(cx, funProto, "call", &v)) {
          arm(25);
        } else {
          JS_ClearPendingException(cx);
        }
      } else {
        JS_ClearPendingException(cx);
      }
    }
    {
      // `Object.prototype.hasOwnProperty` (BC_OBJ_HASOWN = 26): the target
      // half of the same guard.
      JS::RootedObject objProto(cx);
      if (JS_GetClassPrototype(cx, JSProto_Object, &objProto) && objProto &&
          JS_GetProperty(cx, objProto, "hasOwnProperty", &v)) {
        arm(26);
      } else {
        JS_ClearPendingException(cx);
      }
    }
    if (g) {
      JS::Realm* realm = JS::GetCurrentRealmOrNull(cx);
      RtState(cx).useFdlibmSinCos =
          js::math_use_fdlibm_for_sin_cos_tan() ||
          (realm && JS::RealmCreationOptionsRef(realm).alwaysUseFdlibm());
      JS::RootedValue mathv(cx);
      if (JS_GetProperty(cx, g, "Math", &mathv) && mathv.isObject()) {
        JS::RootedObject math(cx, &mathv.toObject());
        // Math native-pointer slots: the compiled math arms compare a
        // classified-native callee's JSNative against these, which matches
        // BOTH the Math.* property functions and the std_Math_* intrinsic
        // clones (same native, different JSFunction objects). Order matches
        // translate::MN_*.
        if (RtEnv(cx).mathNativesPtr) {
          static const char* const kMnNames[13] = {
              "max",   "min",    "pow",  "sqrt",  "abs", "floor", "ceil",
              "trunc", "fround", "imul", "clz32", "sin", "cos"};
          static_assert(sizeof(kMnNames) / sizeof(kMnNames[0]) <=
                            js::night::Night_mathNativeSlots,
                        "more MN_* names than the region reserves slots for");
          auto* slots = LinMem<uint32_t>(RtEnv(cx).mathNativesPtr);
          for (int i = 0; i < 13; i++) {
            if (JS_GetProperty(cx, math, kMnNames[i], &v) && v.isObject() &&
                v.toObject().is<JSFunction>() &&
                v.toObject().as<JSFunction>().isNativeFun()) {
              slots[i] = static_cast<uint32_t>(reinterpret_cast<uintptr_t>(
                  v.toObject().as<JSFunction>().native()));
            } else {
              JS_ClearPendingException(cx);
            }
          }
        }
        static const char* const kMathNames[8] = {
            "sqrt", "abs", "floor", "min", "max", "sin", "cos", "pow"};
        for (int i = 0; i < 8; i++) {
          if (JS_GetProperty(cx, math, kMathNames[i], &v)) {
            arm(2 + i);
          } else {
            JS_ClearPendingException(cx);
          }
        }
        // clz32 -> BC_MATH_CLZ32 (11), imul -> BC_MATH_IMUL (12).
        if (JS_GetProperty(cx, math, "clz32", &v)) {
          arm(11);
        } else {
          JS_ClearPendingException(cx);
        }
        if (JS_GetProperty(cx, math, "imul", &v)) {
          arm(12);
        } else {
          JS_ClearPendingException(cx);
        }
      } else {
        JS_ClearPendingException(cx);
      }
    }
    if (g && JS_GetProperty(cx, g, "parseInt", &v)) {
      arm(10);
    } else {
      JS_ClearPendingException(cx);
    }
    // String.prototype direct-dispatch identity cells (Part B): BC_STR_*
    // (13..22). Each cell holds the pristine native; the inline arm compares
    // the runtime callee against it (an override self-misses) and, on a string
    // receiver, invokes the native directly via night_runtime_native_dispatch.
    {
      JS::RootedObject strProto(cx);
      if (JS_GetClassPrototype(cx, JSProto_String, &strProto) && strProto) {
        static const char* const kStrNames[10] = {
            "indexOf",     "lastIndexOf", "slice", "substring",
            "toLowerCase", "toUpperCase", "trim",  "startsWith",
            "endsWith",    "includes"};
        for (int i = 0; i < 10; i++) {
          if (JS_GetProperty(cx, strProto, kStrNames[i], &v)) {
            arm(13 + i);
          } else {
            JS_ClearPendingException(cx);
          }
        }
      } else {
        JS_ClearPendingException(cx);
      }
    }
    RearmBuiltinCells();
  }
  // Inline nursery allocation (+24/+28 = addresses of the nursery's position
  // and currentEnd words; 0 = disabled). Also record the alloc-cell region
  // for GC zeroing. (Every baked layout offset is static_asserted in
  // NightInlineHeap.cpp.)
  {
    uint32_t posAddr = 0;
    uint32_t endAddr = 0;
    if (js::night::NightNurseryAddresses(cx, &posAddr, &endAddr)) {
      RtState(cx).nurseryInlineOK = true;
    }
    *LinMem<uint32_t>(env.propicGenPtr + js::night::Night_hostNurseryPosOff) =
        posAddr;
    *LinMem<uint32_t>(env.propicGenPtr + js::night::Night_hostNurseryEndOff) =
        endAddr;
    RefreshStringAlloc(cx);
    JS::AddGCNurseryCollectionCallback(cx, NightStringAllocNurseryCallback,
                                       nullptr);
  }

  // Capture the pristine defineProperty family for the binding-fuse
  // intercept in night_runtime_call (user code has not run yet).
  {
    JS::RootedValue objCtor(cx), reflect(cx), dp(cx), dps(cx), rdp(cx);
    JS::RootedObject globalObj(cx, JS::CurrentGlobalOrNull(cx));
    if (globalObj && JS_GetProperty(cx, globalObj, "Object", &objCtor) &&
        objCtor.isObject()) {
      JS::RootedObject octor(cx, &objCtor.toObject());
      if (JS_GetProperty(cx, octor, "defineProperty", &dp) && dp.isObject()) {
        RtFns(cx).defineProperty = new JS::PersistentRootedValue(cx, dp);
      }
      if (JS_GetProperty(cx, octor, "defineProperties", &dps) &&
          dps.isObject()) {
        RtFns(cx).defineProperties = new JS::PersistentRootedValue(cx, dps);
      }
    }
    if (globalObj && JS_GetProperty(cx, globalObj, "Reflect", &reflect) &&
        reflect.isObject()) {
      JS::RootedObject robj(cx, &reflect.toObject());
      if (JS_GetProperty(cx, robj, "defineProperty", &rdp) && rdp.isObject()) {
        RtFns(cx).reflectDefineProperty = new JS::PersistentRootedValue(cx, rdp);
      }
    }
    if (JS_IsExceptionPending(cx)) {
      JS_ClearPendingException(cx);
    }
  }

  // Capture the pristine RegExp.prototype.exec/.test for the night_runtime_call
  // intercept (self-hosted wrappers otherwise run interpreted).
  {
    JS::RootedObject reProto(cx);
    JS::RootedValue ex(cx), te(cx);
    if (JS_GetClassPrototype(cx, JSProto_RegExp, &reProto) && reProto) {
      if (JS_GetProperty(cx, reProto, "exec", &ex) && ex.isObject()) {
        RtFns(cx).regExpExec = new JS::PersistentRootedValue(cx, ex);
      }
      if (JS_GetProperty(cx, reProto, "test", &te) && te.isObject()) {
        RtFns(cx).regExpTest = new JS::PersistentRootedValue(cx, te);
      }
    }
    if (JS_IsExceptionPending(cx)) {
      JS_ClearPendingException(cx);
    }
    // The same two as builtin cells (BC_REGEXP_EXEC = 27, BC_REGEXP_TEST =
    // 28): the compiled call's regexp arm matches its callee against them.
    RtFns(cx).builtins[27] = RtFns(cx).regExpExec;
    RtFns(cx).builtins[28] = RtFns(cx).regExpTest;
    // `Map.prototype.get` (BC_MAP_GET = 29): the inline map lookup's callee.
    JS::RootedObject mapProto(cx);
    JS::RootedValue mg(cx);
    if (JS_GetClassPrototype(cx, JSProto_Map, &mapProto) && mapProto &&
        JS_GetProperty(cx, mapProto, "get", &mg) && mg.isObject()) {
      RtFns(cx).builtins[29] = new JS::PersistentRootedValue(cx, mg);
    }
    if (JS_IsExceptionPending(cx)) {
      JS_ClearPendingException(cx);
    }
    RearmBuiltinCells();
  }

  return true;
}

// Resolve `recv` to the object whose property is accessed (boxing primitives;
// null/undefined throws a TypeError, matching JS semantics).
static JSObject* ReceiverObject(JSContext* cx, uint64_t recv) {
  JS::RootedValue recvVal(cx, JS::Value::fromRawBits(recv));
  JS::RootedObject obj(cx);
  if (!JS_ValueToObject(cx, recvVal, &obj)) {
    return nullptr;
  }
  if (!obj) {
    js::ReportIsNullOrUndefinedForPropertyAccess(cx, recvVal,
                                                 JSDVG_IGNORE_STACK);
    return nullptr;
  }
  return obj;
}

// Hot-path variant: builds the atom-name error string only on failure.
static JSObject* ReceiverObjectAtom(JSContext* cx, uint64_t recv,
                                    const char* prefix, uint32_t atomId) {
  JS::RootedValue recvVal(cx, JS::Value::fromRawBits(recv));
  JS::RootedObject obj(cx);
  if (!JS_ValueToObject(cx, recvVal, &obj)) {
    return nullptr;
  }
  if (MOZ_UNLIKELY(!obj)) {
    JS::Rooted<jsid> id(cx, AtomIdChecked(cx, atomId));
    js::ReportIsNullOrUndefinedForPropertyAccess(cx, recvVal,
                                                 JSDVG_IGNORE_STACK, id);
    return nullptr;
  }
  return obj;
}

// Install the GC scan limit `top` (a linear-memory address one past the last
// live rooted Value) on the context, before any may-GC work.
// Every may-GC helper takes `top` as its second parameter and calls this on
// entry, rather than through a separate set-top round-trip.
static inline void SetNightTop(JSContext* cx, uint32_t top) {
  js::nightrt::TheNightStackInline(cx).setTop(LinMem<JS::Value>(top));
}

// Write a boxed result to the scratch out-slot, which sits exactly at `top`
// (the scan boundary, excluded from the rooted region [base, top)).
static inline void WriteNightOut(uint32_t top, uint64_t bits) {
  *LinMem<uint64_t>(top) = bits;
}

// Generic receiver-aware set with the interpreter's SetPropertyOperation
// semantics: the original (possibly primitive) receiver flows through, and a
// refused write throws in strict mode / is silently ignored otherwise.
static bool GenericSetWithStrict(JSContext* cx, JS::HandleObject obj,
                                 JS::HandleId id, uint64_t val, uint64_t recv,
                                 uint32_t strict) {
  JS::RootedValue v(cx, JS::Value::fromRawBits(val));
  JS::RootedValue receiver(cx, JS::Value::fromRawBits(recv));
  JS::ObjectOpResult result;
  if (!js::SetProperty(cx, obj, id, v, receiver, result)) {
    return false;
  }
  return result.checkStrictModeError(cx, obj, id, strict != 0);
}

// While in scope, and `vouched`, the engine's store choke drops RANGES but
// keeps TYPES: the one store made inside is of a conforming value.
static void NightCensusTraceSet(uint32_t atomId, uint32_t word,
                                uint32_t flags);

// Whether a store of `v` to property `atomId` of `obj` keeps the TYPES claim
// of `obj`'s class (its stamp's identity, or its early key while it is
// constructed): the field its layout predicts under that name is of the
// field's predicted type, or its layout has no such typed field. The check
// a compiled store to a known field makes (`field_types`), made here for
// the set helpers' stores, which know the field. (The engine's store choke
// knows no field and drops the bit.)
static bool NightStoreConforms(JSContext* cx, JSObject* obj, uint32_t atomId, JS::Value v) {
  if (!RtLayouts(cx).anyTypes) {
    return false;
  }
  uint32_t w = obj->externalWord();
  uint32_t k = (w & js::night::kWordConstructing) ? (w >> 18) & 0x0FFF
                                                  : w & 0xFFFF;
  if (k == 0 || k - 1 >= RtLayouts(cx).rows.size() ||
      k - 1 >= RtLayouts(cx).claims.size()) {
    return false;
  }
  const std::vector<uint32_t>& row = RtLayouts(cx).rows[k - 1];
  const std::vector<uint32_t>& claims = RtLayouts(cx).claims[k - 1];
  for (size_t i = 0; i < row.size(); i++) {
    if (row[i] != atomId) {
      continue;
    }
    uint32_t c = i < claims.size() ? claims[i] : 0;
    if (c == 0) {
      return true;
    }
    if (c & 0x0F00) {
      return false;  // a typed-array claim: its kind is not checked here
    }
    uint32_t bit = v.isInt32()       ? 0x01
                   : v.isDouble()    ? 0x02
                   : v.isString()    ? 0x04
                   : v.isUndefined() ? 0x08
                   : v.isNull()      ? 0x10
                   : v.isBoolean()   ? 0x20
                   : v.isBigInt()    ? 0x40
                   : v.isSymbol()    ? 0x80
                   : v.isObject()    ? 0x8000
                                     : 0;
    return (c & bit) != 0;
  }
  return true;
}

class MOZ_RAII AutoVouchedStore {
  bool on_;

 public:
  explicit AutoVouchedStore(bool vouched) : on_(vouched) {
    if (on_) {
      js::night::gNightHooks.storeClearMask = js::night::kWordRanges;
      js::night::gNightHooks.storeNonNumberClearMask = 0;
    }
  }
  ~AutoVouchedStore() {
    if (on_) {
      js::night::gNightHooks.storeClearMask = js::night::kStoreClearMask;
      js::night::gNightHooks.storeNonNumberClearMask =
          js::night::kStoreNonNumberClearMask;
    }
  }
};

// Whether a set of `id` on `obj` is a plain slot write or a plain add, which
// run no JS: `obj` a plain object with `id` an own writable data property;
// or extensible, and `id` on neither it nor any prototype, each an ordinary
// native object with no resolve hook (nothing to shadow, no setter, no
// proxy trap to run).
static bool PlainStore(JSObject* obj, JS::HandleId id) {
  if (!obj->is<js::PlainObject>()) {
    return false;
  }
  js::NativeObject* nobj = &obj->as<js::NativeObject>();
  mozilla::Maybe<js::PropertyInfo> prop = nobj->lookupPure(id);
  if (prop.isSome()) {
    return prop->isDataProperty() && prop->writable();
  }
  if (!nobj->isExtensible()) {
    return false;
  }
  for (JSObject* p = nobj->staticPrototype(); p; p = p->staticPrototype()) {
    if (!p->is<js::NativeObject>() || p->getClass()->getResolve() ||
        p->getClass()->getAddProperty()) {
      return false;
    }
    // The first holder on the chain decides: a writable data property is
    // shadowed by a plain add (a prototype's defaults, `x: 0.0`); a setter
    // or a read-only one is not a plain store.
    mozilla::Maybe<js::PropertyInfo> pp = p->as<js::NativeObject>().lookupPure(id);
    if (pp.isSome()) {
      if (!pp->isDataProperty() || !pp->writable()) {
        return false;
      }
      break;
    }
  }
  return !nobj->getClass()->getAddProperty();
}

// Whether `Object.defineProperty(obj, id, desc)` may run under
// AutoVouchedStore: the define touches no field the object's TYPES claim
// covers, and runs no JS (the vouch is process-wide while it is up, so a
// store made by a getter it ran would be vouched too).
//
// - `id` is not in the stamped layout's row: the masked fields are
//   untouched. (Redefining a masked field as an accessor is a structural
//   change the engine reports anyway.)
// - `obj` is an ordinary native object: no proxy trap, resolve or
//   addProperty hook.
// - `desc` is a plain object whose descriptor fields are absent or own
//   data properties, none of them inherited: ToPropertyDescriptor then
//   calls no getter.
//
// pdfjs's `addContextCurrentTransform` defines two accessors on the canvas
// context once per context; through the engine each cleared the context's
// TYPES, and every method call on it after that failed its entry guard.
static bool DefineKeepsTypes(JSContext* cx, JSObject* obj, JS::PropertyKey id,
                             JS::Value desc) {
  if (!RtLayouts(cx).anyTypes || !RtNames(cx).ids || !desc.isObject()) {
    return false;
  }
  uint32_t w = obj->externalWord();
  if (!(w & js::night::kWordTypes)) {
    return false;
  }
  uint32_t k = (w & js::night::kWordConstructing) ? (w >> 18) & 0x0FFF
                                                  : w & 0xFFFF;
  if (k == 0 || k - 1 >= RtLayouts(cx).rows.size()) {
    return false;
  }
  for (uint32_t atom : RtLayouts(cx).rows[k - 1]) {
    if (atom < RtNames(cx).ids->size() && (*RtNames(cx).ids)[atom].get() == id) {
      return false;
    }
  }
  if (!obj->is<js::NativeObject>() || obj->getOpsDefineProperty() ||
      obj->getClass()->getResolve() || obj->getClass()->getAddProperty()) {
    return false;
  }
  JSObject* d = &desc.toObject();
  if (!d->is<js::PlainObject>()) {
    return false;
  }
  js::NativeObject* nd = &d->as<js::NativeObject>();
  const js::ImmutableTenuredPtr<js::PropertyName*>* kFields[] = {
      &cx->names().enumerable, &cx->names().configurable, &cx->names().value,
      &cx->names().writable,   &cx->names().get,          &cx->names().set};
  for (auto* f : kFields) {
    JS::PropertyKey fid = js::NameToId(*f);
    mozilla::Maybe<js::PropertyInfo> own = nd->lookupPure(fid);
    if (own.isSome()) {
      if (!own->isDataProperty()) {
        return false;
      }
      continue;
    }
    for (JSObject* p = nd->staticPrototype(); p; p = p->staticPrototype()) {
      if (!p->is<js::NativeObject>() || p->getClass()->getResolve() ||
          p->as<js::NativeObject>().lookupPure(fid).isSome()) {
        return false;
      }
    }
  }
  return true;
}

// `flags`: bit 0 strict; bit 1 the compiled caller vouches that `val` is of
// the field's predicted type for the object's class (the baseline tier's
// stores, `night_runtime_set_prop_ic_miss`'s rule): a plain slot write or
// add then keeps TYPES.
bool night_runtime_set_property(JSContext* cx, uint32_t top, uint64_t recv,
                                uint32_t atomId, uint64_t val,
                                uint32_t flags) {
  bool strict = flags & 1;
  SetNightTop(cx, top);
  if (JS::Value::fromRawBits(recv).isObject()) {
    NightCensusTraceSet(atomId,
                        JS::Value::fromRawBits(recv).toObject().externalWord(),
                        flags | 4);
  }
  JS::HandleId id = AtomIdChecked(cx, atomId);
  JS::RootedObject obj(cx, ReceiverObject(cx, recv));
  if (!obj) {
    return false;
  }
  // Fused globals: a qualified write to the global (`globalThis.X = ...`).
  bool activeGlobal = IsActiveGlobal(obj);
  if (activeGlobal) {
    MaybeGnameFuseBlow(atomId, val);
    MaybeBlowBindingFuseAtom(atomId, val);
  }
  {
    bool vouched = (flags & 2) ||
                   NightStoreConforms(cx, obj, atomId, JS::Value::fromRawBits(val));
    AutoVouchedStore v(vouched && !activeGlobal && PlainStore(obj, id));
    if (!GenericSetWithStrict(cx, obj, id, val, recv, strict)) {
      return false;
    }
  }
  if (activeGlobal) {
    MaybeGnameFuseArmAfterStore(cx, atomId, val);
    MaybeRearmBindingFuseAtom(cx, atomId);
  }
  return true;
}

// Leaf GET probes (the linmem mega table and the guarded chain): pure loads, no
// GC, no rooting. `shape` is the rows' receiver key: the receiver's shape, or
// a primitive's pseudo shape (whose rows always name a prototype holder;
// `robj` is then null). Writes the result to `out` and returns true on a hit;
// a mega hit also fills a free inline way for the key.
static bool TryLeafGetProbesShape(JSObject* robj, uint32_t shape,
                                  uint32_t atomId, uint32_t cacheIdx,
                                  JS::Value* out) {
  JSContext* cx = CurrentNightContext();
  MegaGetEntry& e = *MegaGet(cx, shape, atomId);
  if (e.shape == shape && e.atomId == atomId && (e.holderPtr || robj)) {
    js::NativeObject* holder;
    bool holderOk = true;
    if (e.holderPtr) {
      holder = LinMem<js::NativeObject>(e.holderPtr);
      holderOk = js::night::NightObjectShape(holder) == e.holderShape;
    } else {
      // Same shape => same clasp => still a NativeObject.
      holder = &robj->as<js::NativeObject>();
    }
    if (holderOk) {
      *out = e.slotEnc == js::night::kNightSlotEncAbsent
                 ? JS::UndefinedValue()
                 : SlotEncRead(holder, e.slotEnc);
      NoteGetWay(cacheIdx, e.shape, e.holderPtr, e.holderShape, e.slotEnc);
      return true;
    }
  }
  // Guarded-chain probe: validates every hop's live shape, then
  // serves the holder slot or the proven-ABSENT undefined.
  GChainEntry& g = *GChainSlot(cx, shape, atomId);
  if (g.shape == shape && g.atomId == atomId) {
    bool ok = true;
    for (uint32_t h = 0; h < g.nHops; h++) {
      js::NativeObject* p = LinMem<js::NativeObject>(g.protoPtr[h]);
      if (js::night::NightObjectShape(p) != g.protoShape[h]) {
        ok = false;
        break;
      }
    }
    if (ok) {
      if (g.slotEnc == js::night::kNightSlotEncAbsent) {
        *out = JS::UndefinedValue();
        return true;
      }
      js::NativeObject* holder =
          LinMem<js::NativeObject>(g.protoPtr[g.nHops - 1]);
      *out = SlotEncRead(holder, g.slotEnc);
      return true;
    }
  }
  return false;
}

static bool TryLeafGetProbesV(JSObject* robj, uint32_t atomId,
                              uint32_t cacheIdx, JS::Value* out) {
  return TryLeafGetProbesShape(robj, js::night::NightObjectShape(robj), atomId,
                               cacheIdx, out);
}

// A primitive's pseudo shape (the get rows' receiver key) and the prototype
// its lookup starts at; false for a kind without one.
static bool PrimGetKey(JSContext* cx, const JS::Value& v, uint32_t* shapeOut,
                       JSObject** protoOut) {
  JSProtoKey key;
  if (v.isString()) {
    key = JSProto_String;
    *shapeOut = js::night::Night_icPrimStringShape;
  } else if (v.isNumber()) {
    key = JSProto_Number;
    *shapeOut = js::night::Night_icPrimNumberShape;
  } else if (v.isBoolean()) {
    key = JSProto_Boolean;
    *shapeOut = js::night::Night_icPrimBooleanShape;
  } else {
    return false;
  }
  *protoOut = cx->global()->maybeGetPrototype(key);
  return *protoOut != nullptr;
}

static bool TryLeafGetProbes(JSObject* robj, uint32_t atomId, uint32_t cacheIdx,
                             uint32_t top) {
  JS::Value v;
  if (!TryLeafGetProbesV(robj, atomId, cacheIdx, &v)) {
    return false;
  }
  WriteNightOut(top, v.asRawBits());
  return true;
}

// The property-IC miss result bitset (see NightRuntime.h). CLEAN is the
// second-chance signal: the miss was served without running user code and
// without GC, so nothing the compiled caller had proven about any value can
// have been invalidated. Claimed on the pure slot lookups AND on the cached
// add-transition replays -- an add reshapes the receiver, but the caller
// never remembers a shape (its guards re-load them) and the class-idx word
// its `cls` facts name is untouched.
static constexpr uint32_t kMissErr = 0;
static constexpr uint32_t kMissOk = 1;
static constexpr uint32_t kMissClean = 3;

// Whether `id` on `obj` resolves (pure lookup up the static proto chain) to
// an accessor whose getter is the engine's own inlinable native `want` --
// the `length`/`byteLength` getters of typed arrays and array buffers, which
// user code can shadow or redefine, and which are then no longer pure reads.
static bool PristineGetterIs(JSObject* obj, JS::HandleId id,
                             js::jit::InlinableNative want) {
  JSObject* holder = obj;
  for (;;) {
    if (!holder->is<js::NativeObject>()) {
      return false;
    }
    js::NativeObject* nh = &holder->as<js::NativeObject>();
    mozilla::Maybe<js::PropertyInfo> prop = nh->lookupPure(id);
    if (prop.isSome()) {
      if (!prop->isAccessorProperty()) {
        return false;
      }
      JSObject* g = nh->getGetter(*prop);
      if (!g || !g->is<JSFunction>()) {
        return false;
      }
      JSFunction* f = &g->as<JSFunction>();
      return f->isNativeFun() && f->hasJitInfo() &&
             f->jitInfo()->type() == JSJitInfo::InlinableNative &&
             f->jitInfo()->inlinableNative == want;
    }
    if (!holder->hasStaticPrototype()) {
      return false;
    }
    holder = holder->staticPrototype();
    if (!holder) {
      return false;
    }
  }
}

// The `length`/`byteLength` reads the IC cannot cache, as the pure reads
// they are: a string value's, an array's (a custom data property), an
// unmodified arguments object's (reified on demand), and the typed-array
// and array-buffer prototype getters while still the engine's own. Leaf.
static bool PureLengthRead(JSContext* cx, JS::Value rv, JS::HandleId id,
                           JS::Value* out) {
  const bool wantLength = id == js::NameToId(cx->names().length);
  const bool wantByteLength = id == js::NameToId(cx->names().byteLength);
  if (!wantLength && !wantByteLength) {
    return false;
  }
  if (rv.isString() && wantLength) {
    *out = JS::Int32Value(int32_t(rv.toString()->length()));
    return true;
  }
  if (!rv.isObject()) {
    return false;
  }
  JSObject* ro = &rv.toObject();
  uint64_t len = 0;
  bool have = false;
  if (wantLength && ro->is<js::ArrayObject>()) {
    len = ro->as<js::ArrayObject>().length();
    have = true;
  } else if (wantLength && ro->is<js::ArgumentsObject>() &&
             !ro->as<js::ArgumentsObject>().hasOverriddenLength()) {
    len = ro->as<js::ArgumentsObject>().initialLength();
    have = true;
  } else if (ro->is<js::TypedArrayObject>()) {
    auto* ta = &ro->as<js::TypedArrayObject>();
    if (wantLength &&
        PristineGetterIs(ro, id, js::jit::InlinableNative::TypedArrayLength)) {
      len = ta->length().valueOr(0);
      have = true;
    } else if (wantByteLength &&
               PristineGetterIs(
                   ro, id, js::jit::InlinableNative::TypedArrayByteLength)) {
      len = ta->byteLength().valueOr(0);
      have = true;
    }
  } else if (wantByteLength && ro->is<js::ArrayBufferObject>() &&
             PristineGetterIs(ro, id,
                              js::jit::InlinableNative::ArrayBufferByteLength)) {
    len = ro->as<js::ArrayBufferObject>().byteLength();
    have = true;
  }
  if (!have) {
    return false;
  }
  *out = len <= uint64_t(INT32_MAX) ? JS::Int32Value(int32_t(len))
                                    : JS::DoubleValue(double(len));
  return true;
}

// Record a coordinate (or a proven absence) in the site's inline ways and
// the mega table.
static void NoteGetRow(uint32_t cacheIdx, uint32_t atomId, uint32_t recvShape,
                       uint32_t holderPtr, uint32_t holderShape,
                       uint32_t slotEnc) {
  JSContext* cx = CurrentNightContext();
  NoteGetWay(cacheIdx, recvShape, holderPtr, holderShape, slotEnc);
  // Fill the linmem mega entry unconditionally (direct-mapped overwrite).
  MegaGetEntry& e = *MegaGet(cx, recvShape, atomId);
  e.atomId = atomId;
  e.holderPtr = holderPtr;
  e.holderShape = holderShape;
  e.slotEnc = slotEnc;
  e.pad = 0;
  e.shape = recvShape;
}

// Record a guarded chain keyed by `shape`.
static void NoteGChain(uint32_t shape, uint32_t atomId, uint32_t nHops,
                       uint32_t slotEnc, const uint32_t* pp,
                       const uint32_t* ps) {
  JSContext* cx = CurrentNightContext();
  GChainEntry& g = *GChainSlot(cx, shape, atomId);
  g.shape = 0;
  g.atomId = atomId;
  g.nHops = nHops;
  g.slotEnc = slotEnc;
  for (uint32_t h = 0; h < kGChainMaxHops; h++) {
    g.protoPtr[h] = h < nHops ? pp[h] : 0;
    g.protoShape[h] = h < nHops ? ps[h] : 0;
  }
  g.shape = shape;  // validity marker last
}

// Fill the site's inline ways and the mega table (or the guarded-chain
// table) for `id` on native `obj`, where it resolves to a plain data slot
// (or a proven absence). Leaf. False where neither populate applies.
static bool PopulateGetCaches(JSContext* cx, JSObject* obj, jsid id,
                              uint32_t atomId, uint32_t cacheIdx) {
  uint32_t recvShape, holderPtr, holderShape, slotEnc;
  if (js::night::NightPopulateInlineGetIC(cx, obj, id, &recvShape, &holderPtr,
                                          &holderShape, &slotEnc)) {
    NoteGetRow(cacheIdx, atomId, recvShape, holderPtr, holderShape, slotEnc);
    return true;
  }
  if (!obj->is<js::NativeObject>()) {
    return false;
  }
  // Guarded-chain populate: the plain coordinate was refused (invalidated
  // teleporting / deep chain) -- record the per-hop guarded chain.
  uint32_t nHops = 0;
  uint32_t gSlotEnc = 0;
  uint32_t pp[kGChainMaxHops];
  uint32_t ps[kGChainMaxHops];
  if (!js::night::NightPopulateGuardedChain(cx, obj, id, kGChainMaxHops, &nHops,
                                            pp, ps, &gSlotEnc)) {
    return false;
  }
  NoteGChain(js::night::NightObjectShape(obj), atomId, nHops, gSlotEnc, pp, ps);
  return true;
}

// The same for a primitive receiver keyed by `pseudoShape`, whose lookup
// starts at `proto`.
static bool PopulatePrimGetCaches(JSContext* cx, JSObject* proto,
                                  uint32_t pseudoShape, jsid id,
                                  uint32_t atomId, uint32_t cacheIdx) {
  uint32_t recvShape, holderPtr, holderShape, slotEnc;
  if (js::night::NightPopulateInlineGetICPrim(cx, proto, pseudoShape, id,
                                              &recvShape, &holderPtr,
                                              &holderShape, &slotEnc)) {
    NoteGetRow(cacheIdx, atomId, recvShape, holderPtr, holderShape, slotEnc);
    return true;
  }
  uint32_t nHops = 0;
  uint32_t gSlotEnc = 0;
  uint32_t pp[kGChainMaxHops];
  uint32_t ps[kGChainMaxHops];
  if (!js::night::NightPopulateGuardedChainPrim(cx, proto, id, kGChainMaxHops,
                                                &nHops, pp, ps, &gSlotEnc)) {
    return false;
  }
  NoteGChain(pseudoShape, atomId, nHops, gSlotEnc, pp, ps);
  return true;
}

uint64_t night_runtime_get_prop_pure(JSContext* cx, uint64_t recv,
                                     uint32_t atomId, uint32_t cacheIdx) {
  JS::AutoCheckCannotGC nogc;
  const uint64_t fail = JS::MagicValue(JS_GENERIC_MAGIC).asRawBits();
  JS::HandleId id = AtomIdChecked(cx, atomId);
  if (!id.isAtom()) {
    return fail;
  }
  JS::Value rv = JS::Value::fromRawBits(recv);
  JS::Value out;
  if (PureLengthRead(cx, rv, id, &out)) {
    return out.asRawBits();
  }
  if (rv.isObject()) {
    JSObject* obj = &rv.toObject();
    if (TryLeafGetProbesV(obj, atomId, cacheIdx, &out)) {
      return out.asRawBits();
    }
    if (!js::GetPropertyPure(cx, obj, id, &out)) {
      return fail;
    }
    PopulateGetCaches(cx, obj, id, atomId, cacheIdx);
    return out.asRawBits();
  }
  // A primitive's own properties are its length and indices (a string
  // wrapper's), which the arms above and the atom check rule out: the
  // lookup starts at its prototype, and the rows key on the primitive's
  // pseudo shape.
  uint32_t pseudo;
  JSObject* proto;
  if (PrimGetKey(cx, rv, &pseudo, &proto)) {
    if (TryLeafGetProbesShape(nullptr, pseudo, atomId, cacheIdx, &out)) {
      return out.asRawBits();
    }
    if (!js::GetPropertyPure(cx, proto, id, &out)) {
      return fail;
    }
    PopulatePrimGetCaches(cx, proto, pseudo, id, atomId, cacheIdx);
    return out.asRawBits();
  }
  JSProtoKey key = rv.isSymbol()   ? JSProto_Symbol
                   : rv.isBigInt() ? JSProto_BigInt
                                   : JSProto_Null;
  if (key == JSProto_Null) {
    return fail;
  }
  JSObject* obj = cx->global()->maybeGetPrototype(key);
  if (!obj || !js::GetPropertyPure(cx, obj, id, &out)) {
    return fail;
  }
  return out.asRawBits();
}

int32_t night_runtime_to_primitive_pure(JSContext* cx, uint64_t bits) {
  JS::AutoCheckCannotGC nogc;
  JS::Value v = JS::Value::fromRawBits(bits);
  if (!v.isObject()) {
    return 1;
  }
  JSObject* obj = &v.toObject();
  // Object.prototype's own conversion, found by pure lookups: no
  // @@toPrimitive, `valueOf` the self-hosted Object_valueOf (ToObject),
  // `toString` the native obj_toString, whose @@toStringTag read finds a
  // data property or nothing.
  if (!js::HasNoToPrimitiveMethodPure(obj, cx)) {
    return 0;
  }
  JS::Value f;
  if (!js::GetPropertyPure(cx, obj, js::NameToId(cx->names().valueOf), &f) ||
      !js::IsSelfHostedFunctionWithName(f, cx->names().Object_valueOf)) {
    return 0;
  }
  if (!js::GetPropertyPure(cx, obj, js::NameToId(cx->names().toString), &f) ||
      !js::IsNativeFunction(f, js::obj_toString)) {
    return 0;
  }
  JS::Value tag;
  return js::GetPropertyPure(
             cx, obj,
             JS::PropertyKey::Symbol(cx->wellKnownSymbols().toStringTag), &tag)
             ? 1
             : 0;
}

// The "no GC, no stamp moved" proof for an IC-miss path that ran the
// engine's generic operation: the two counters are what a getter/setter
// that ran user code, or a resolve hook that allocated, would have moved.
struct MissQuiet {
  uint64_t gc;
  uint64_t epoch;
  explicit MissQuiet(JSContext* cx)
      : gc(cx->runtime()->gc.gcNumber()), epoch(RtState(cx).stampEpoch) {}
  bool still(JSContext* cx) const {
    return cx->runtime()->gc.gcNumber() == gc &&
           RtState(cx).stampEpoch == epoch;
  }
};

// Inline get-IC miss helper. Reached only when the compiled body's inline
// shape/generation/holder guards all miss (an unseen receiver shape, a stale
// generation after a major GC, or a non-cacheable site). Does the generic by-id
// get and, if the property resolves to a cacheable proto-holder coordinate,
// populates a free/victim way of the linear-memory inline cache so subsequent
// reads hit inline with no call. May GC (the generic get can run getters), so
// the rooting handshake (driver spills before, reloads after) applies; the
// result is written to the out-slot `*top`.
uint32_t night_runtime_get_prop_ic_miss(JSContext* cx, uint32_t top,
                                        uint64_t recv, uint32_t atomId,
                                        uint32_t cacheIdx) {
  SetNightTop(cx, top);
  JS::HandleId id = AtomIdChecked(cx, atomId);
  {
    JS::Value out;
    if (PureLengthRead(cx, JS::Value::fromRawBits(recv), id, &out)) {
      WriteNightOut(top, out.asRawBits());
      return kMissClean;
    }
  }
  // The mega and guarded-chain probes hoisted ABOVE the receiver rooting: both
  // are leaf (pure loads, no GC), and together they serve the vast majority of
  // the helper's calls -- the Rooted construction and ReceiverObjectAtom call
  // below are pure waste for them. A raw JSObject* is safe here: nothing
  // between entry and these probes can GC. A primitive receiver's rows are
  // keyed by its pseudo shape.
  uint32_t pseudo = 0;
  JSObject* primProto = nullptr;
  {
    JS::Value rv = JS::Value::fromRawBits(recv);
    if (rv.isObject()) {
      if (TryLeafGetProbes(&rv.toObject(), atomId, cacheIdx, top)) {
        return kMissClean;
      }
    } else if (PrimGetKey(cx, rv, &pseudo, &primProto)) {
      JS::Value out;
      if (TryLeafGetProbesShape(nullptr, pseudo, atomId, cacheIdx, &out)) {
        WriteNightOut(top, out.asRawBits());
        return kMissClean;
      }
    }
  }
  // (Not a pointer held across the generic get below, which may GC.)
  const bool primitive = primProto != nullptr;
  primProto = nullptr;
  // Everything below may allocate (wrapping a primitive receiver) or run
  // the engine's generic get: the counters decide whether the caller's
  // raw carriers and stamp-guarded facts survived (`MissQuiet`). Without
  // this, every first miss at a hot site, and every method read on a
  // string receiver, would step the caller off the Opt track for the rest
  // of its body.
  const MissQuiet quiet(cx);
  JS::RootedObject obj(cx, ReceiverObjectAtom(cx, recv, "ic-get ", atomId));
  if (!obj) {
    return kMissErr;
  }
  // The leaf mega/gchain probes ran pre-rooting above; reaching here means
  // both missed, so the site takes the generic get + populate path.

  // Forward the ORIGINAL (possibly primitive) receiver: a scripted getter's
  // `this` must be the primitive, not its wrapper.
  JS::RootedValue recvv(cx, JS::Value::fromRawBits(recv));
  JS::RootedValue res(cx);
  if (!JS_ForwardGetPropertyTo(cx, obj, id, recvv, &res)) {
    return kMissErr;
  }
  // The populate paths' clean proof: a plain data slot on a native holder
  // (populate succeeds only for those) and the counters unmoved. A
  // primitive's rows start at its prototype, keyed by its pseudo shape (the
  // prototype re-read: the get above may have run code and GC'd).
  if (primitive ? PrimGetKey(cx, recvv, &pseudo, &primProto) &&
                      PopulatePrimGetCaches(cx, primProto, pseudo, id, atomId,
                                            cacheIdx)
                : PopulateGetCaches(cx, obj, id, atomId, cacheIdx)) {
    if (quiet.still(cx)) {
      WriteNightOut(top, res.asRawBits());
      return kMissClean;
    }
  } else if (obj->is<js::NativeObject>() && RtEnv(cx).accessorCachePtr) {
    // BOTH slot populates refused: likely a proto-chain GETTER --
    // prime the accessor-call cache for the compiled accessor arm.
    uint64_t callee;
    uint32_t rs, hp, hs;
    if (js::night::NightPrimeAccessor(cx, obj, id, /*wantSetter=*/false,
                                      &callee, &rs, &hp, &hs)) {
      WriteAccessorEntry(cx, rs, atomId, /*kind=*/0, callee, hp, hs);
    }
  }
  WriteNightOut(top, res.get().asRawBits());
  return kMissOk;
}

static uint32_t SetPropIcMiss(JSContext* cx, uint32_t top, uint64_t recv,
                              uint32_t atomId, uint64_t val, uint32_t cacheIdx,
                              bool strict, bool vouched,
                              bool skipRows = false);
static void NightCensusTraceSet(uint32_t atomId, uint32_t word,
                                uint32_t flags);

// Inline SetProp IC miss helper. Reached only when the body's inline
// shape/generation guards miss (an unseen receiver shape, a stale generation,
// or a non-cacheable site -- proto/accessor/new property). Does the generic
// by-id set and, if the property is an own writable data slot, populates a
// free/victim inline way so subsequent writes hit inline. The value stays on
// the operand stack (the body re-pushes it, as in the generic set). May GC.
//
// `flags`: bit 0 strict; bit 1 (kSetVouchTypes) the compiled caller vouches
// that `val` is of the field's predicted type for the object's class (its
// stamp's, or its early key's while constructed), as its inline arms check
// before they store. Then the helper's own stores that run no JS (the
// add-transition replays and the mega-set probe: this one store, to this
// field) keep TYPES, as the inline arms do (`AutoVouchedStore`); the
// generic set, which may run setters, still drops it.
static constexpr uint32_t kSetVouchTypes = 2;
uint32_t night_runtime_set_prop_ic_miss(JSContext* cx, uint32_t top,
                                        uint64_t recv, uint32_t atomId,
                                        uint64_t val, uint32_t cacheIdx,
                                        uint32_t flags) {
  JS::Value rv = JS::Value::fromRawBits(recv);
  if (rv.isObject()) {
    NightCensusTraceSet(atomId, rv.toObject().externalWord(), flags);
  }
  bool vouched = (flags & kSetVouchTypes) ||
                 (rv.isObject() && NightStoreConforms(cx, &rv.toObject(), atomId,
                                                      JS::Value::fromRawBits(val)));
  return SetPropIcMiss(cx, top, recv, atomId, val, cacheIdx, flags & 1,
                       vouched);
}

// Whether a set of `id` on `obj` runs no code and calls back into nothing:
// a native object (not the global, not a typed array, no Watchtower
// watch: a prototype, a fuse's holder) with `id` an own writable data
// property (or a writable array length); or extensible, with no hook that could resolve or observe the
// add, and `id` on no prototype but as a writable data property of an
// ordinary native object (`PlainStore`, beyond plain objects).
static bool NoCodeStore(JSContext* cx, JSObject* obj, JS::HandleId id) {
  if (!obj->is<js::NativeObject>() || obj->is<js::GlobalObject>() ||
      obj->is<js::TypedArrayObject>() || obj->getOpsSetProperty() ||
      obj->getOpsLookupProperty()) {
    return false;
  }
  js::NativeObject* nobj = &obj->as<js::NativeObject>();
  if (js::Watchtower::watchesPropertyAdd(nobj) ||
      js::Watchtower::watchesPropertyValueChange(nobj)) {
    return false;
  }
  mozilla::Maybe<js::PropertyInfo> prop = nobj->lookupPure(id);
  if (prop.isSome()) {
    // An array's length (a custom data property): a truncation or an
    // extension, which runs no code, and succeeds where every element is
    // a configurable dense one (not sealed, nothing sparse).
    if (nobj->is<js::ArrayObject>() && id == js::NameToId(cx->names().length)) {
      return nobj->as<js::ArrayObject>().lengthIsWritable() &&
             !nobj->denseElementsAreSealed() && !nobj->isIndexed();
    }
    return prop->isDataProperty() && prop->writable();
  }
  // An array's addProperty hook is the engine's own length bookkeeping.
  if (!nobj->isExtensible() ||
      (nobj->getClass()->getAddProperty() && !nobj->is<js::ArrayObject>()) ||
      js::ClassMayResolveId(cx->names(), nobj->getClass(), id, nobj)) {
    return false;
  }
  for (JSObject* p = nobj->staticPrototype(); p; p = p->staticPrototype()) {
    if (!p->is<js::NativeObject>() || p->getOpsLookupProperty() ||
        js::ClassMayResolveId(cx->names(), p->getClass(), id, p)) {
      return false;
    }
    mozilla::Maybe<js::PropertyInfo> pp =
        p->as<js::NativeObject>().lookupPure(id);
    if (pp.isSome()) {
      return pp->isDataProperty() && pp->writable();
    }
  }
  return true;
}

static bool TryPureElementRead(JSContext* cx, uint32_t top, uint64_t recv,
                               uint64_t key);
static bool SetPropCached(JSContext* cx, uint32_t top, uint64_t recv,
                          uint32_t atomId, uint64_t val, uint32_t cacheIdx,
                          bool vouched, bool skipRows = false);

// Whether a store that changed `obj`'s word from `before` to `after`
// demoted a claim of its published class MIR reads: TYPES, SLOTS or CLOSED,
// or the class itself. RANGES, which no MIR claim reads, may drop as on every
// engine store; a word under construction backs no fact past a generic op
// (the builder demotes its `Ctor` slots).
static bool DemotedForMir(uint32_t before, uint32_t after) {
  constexpr uint32_t claims = js::night::kWordTypes | js::night::kWordSlots |
                               js::night::kWordClosed;
  return !(before & js::night::kWordConstructing) &&
         (((before & claims) & ~after) != 0 ||
          ((before & 0xFFFF) != 0 && (after & 0xFFFF) == 0));
}

uint32_t night_runtime_get_elem_pure(JSContext* cx, uint32_t top,
                                     uint64_t recv, uint64_t key) {
  SetNightTop(cx, top);
  if (TryPureElementRead(cx, top, recv, key)) {
    return 1;
  }
  JS::RootedValue rv(cx, JS::Value::fromRawBits(recv));
  JS::RootedValue kv(cx, JS::Value::fromRawBits(key));
  // An object key's ToPropertyKey may call user code; null and undefined
  // throw.
  if (kv.isObject() || rv.isNullOrUndefined()) {
    return 0;
  }
  JS::RootedId id(cx);
  if (!js::ToPropertyKey(cx, kv, &id)) {
    return 2;
  }
  if (rv.isString()) {
    JS::RootedString str(cx, rv.toString());
    if (id.isInt() && uint32_t(id.toInt()) < str->length()) {
      // Flattened, as the engine's element read does: a rope built by
      // `+=` then serves the inline char arm instead of being walked here
      // on every read.
      JSLinearString* linear = str->ensureLinear(cx);
      if (!linear) {
        return 2;
      }
      JSString* c =
          cx->staticStrings().getUnitStringForElement(cx, linear, id.toInt());
      if (!c) {
        return 2;
      }
      WriteNightOut(top, JS::StringValue(c).asRawBits());
      return 1;
    }
    if (id == js::NameToId(cx->names().length)) {
      WriteNightOut(top, JS::Int32Value(int32_t(str->length())).asRawBits());
      return 1;
    }
    if (id.isInt()) {
      // Out of range: String.prototype is the empty String object, whose
      // resolve hook (which the pure lookup refuses for any index)
      // defines none; past it, Object.prototype and up.
      JS::AutoCheckCannotGC nogc;
      JSObject* sp = cx->global()->maybeGetPrototype(JSProto_String);
      if (!sp || !sp->is<js::NativeObject>() ||
          sp->as<js::NativeObject>().lookupPure(id).isSome() ||
          sp->as<js::NativeObject>().getDenseInitializedLength() != 0) {
        return 0;
      }
      JS::Value v = JS::UndefinedValue();
      JSObject* op = sp->staticPrototype();
      if (op && !js::GetPropertyPure(cx, op, id, &v)) {
        return 0;
      }
      WriteNightOut(top, v.asRawBits());
      return 1;
    }
  }
  JS::AutoCheckCannotGC nogc;
  JSObject* obj;
  if (rv.isObject()) {
    obj = &rv.toObject();
    if (obj->is<js::ArgumentsObject>() && id.isInt()) {
      JS::Value v = JS::UndefinedValue();
      JS::MutableHandleValue mv = JS::MutableHandleValue::fromMarkedLocation(&v);
      if (!obj->as<js::ArgumentsObject>().maybeGetElement(id.toInt(), mv)) {
        return 0;
      }
      WriteNightOut(top, v.asRawBits());
      return 1;
    }
  } else {
    // As `night_runtime_get_prop_pure`: a primitive's own properties are
    // a string's length and chars, taken above.
    JSProtoKey pk = rv.isString()    ? JSProto_String
                    : rv.isNumber()  ? JSProto_Number
                    : rv.isBoolean() ? JSProto_Boolean
                    : rv.isSymbol()  ? JSProto_Symbol
                    : rv.isBigInt()  ? JSProto_BigInt
                                     : JSProto_Null;
    if (pk == JSProto_Null) {
      return 0;
    }
    obj = cx->global()->maybeGetPrototype(pk);
    if (!obj) {
      return 0;
    }
  }
  JS::Value v;
  if (!js::GetPropertyPure(cx, obj, id, &v)) {
    return 0;
  }
  WriteNightOut(top, v.asRawBits());
  return 1;
}

uint32_t night_runtime_set_elem_pure(JSContext* cx, uint32_t top,
                                     uint64_t recv, uint64_t key,
                                     uint64_t val) {
  SetNightTop(cx, top);
  JS::Value rv = JS::Value::fromRawBits(recv);
  JS::Value kv = JS::Value::fromRawBits(key);
  JS::Value v = JS::Value::fromRawBits(val);
  // An element by an int32 key (no conversion), of a native object the
  // engine calls back into nothing for (not the global, an arguments
  // object, a prototype or a fuse's holder).
  if (!rv.isObject() || !kv.isInt32() || kv.toInt32() < 0 ||
      !rv.toObject().is<js::NativeObject>()) {
    return 0;
  }
  js::NativeObject* nobj = &rv.toObject().as<js::NativeObject>();
  JS::PropertyKey id = JS::PropertyKey::Int(kv.toInt32());
  if (nobj->is<js::GlobalObject>() || nobj->is<js::ArgumentsObject>() ||
      nobj->getOpsSetProperty() || nobj->getOpsLookupProperty() ||
      js::Watchtower::watchesPropertyAdd(nobj) ||
      js::Watchtower::watchesPropertyValueChange(nobj)) {
    return 0;
  }
  if (nobj->is<js::TypedArrayObject>()) {
    // A number to a number array (an out-of-range index is ignored).
    if (!v.isNumber() ||
        js::Scalar::isBigIntType(nobj->as<js::TypedArrayObject>().type())) {
      return 0;
    }
  } else {
    js::PropertyResult prop;
    if (!js::LookupOwnPropertyPure(cx, nobj, id, &prop)) {
      return 0;
    }
    if (prop.isDenseElement()) {
      if (nobj->denseElementsAreFrozen()) {
        return 0;
      }
    } else if (prop.isNativeProperty()) {
      if (!prop.propertyInfo().isDataProperty() ||
          !prop.propertyInfo().writable()) {
        return 0;
      }
    } else if (prop.isFound()) {
      return 0;
    } else {
      // An add: nothing on the chain to run or refuse it (an array's
      // addProperty hook is the engine's own length bookkeeping).
      if (!nobj->isExtensible() ||
          (nobj->getClass()->getAddProperty() && !nobj->is<js::ArrayObject>())) {
        return 0;
      }
      if (nobj->is<js::ArrayObject>() &&
          uint32_t(kv.toInt32()) >= nobj->as<js::ArrayObject>().length() &&
          !nobj->as<js::ArrayObject>().lengthIsWritable()) {
        return 0;
      }
      if (JSObject* proto = nobj->staticPrototype()) {
        js::NativeObject* holder;
        js::PropertyResult pp;
        if (!js::LookupPropertyPure(cx, proto, id, &holder, &pp)) {
          return 0;
        }
        if (pp.isFound() &&
            !(pp.isDenseElement() ||
              (pp.isNativeProperty() && pp.propertyInfo().isDataProperty() &&
               pp.propertyInfo().writable()))) {
          return 0;
        }
      }
    }
  }
  uint32_t before = nobj->externalWord();
  JS::RootedObject obj(cx, nobj);
  JS::RootedValue rval(cx, v);
  JS::RootedValue receiver(cx, rv);
  JS::RootedId rid(cx, id);
  JS::ObjectOpResult result;
  if (!js::SetProperty(cx, obj, rid, rval, receiver, result)) {
    return 3;
  }
  if (!result.ok()) {
    // Nothing the checks above let through refuses; be exact anyway.
    return 0;
  }
  return DemotedForMir(before, obj->externalWord()) ? 2 : 1;
}

uint32_t night_runtime_set_prop_pure(JSContext* cx, uint32_t top,
                                     uint64_t recv, uint32_t atomId,
                                     uint64_t val, uint32_t cacheIdx,
                                     uint32_t flags) {
  SetNightTop(cx, top);
  JS::Value rv = JS::Value::fromRawBits(recv);
  if (!rv.isObject() || rv.toObject().is<js::GlobalObject>()) {
    return 0;
  }
  JS::RootedObject robj(cx, &rv.toObject());
  bool vouched = (flags & kSetVouchTypes) ||
                 NightStoreConforms(cx, robj, atomId, JS::Value::fromRawBits(val));
  // The IC's cached replays first: populated only from plain data stores,
  // they run no code (and need no lookup here).
  uint32_t before = robj->externalWord();
  if (SetPropCached(cx, top, recv, atomId, val, cacheIdx, vouched)) {
    return DemotedForMir(before, robj->externalWord()) ? 2 : 1;
  }
  JSObject* obj = robj;
  JS::HandleId id = AtomIdChecked(cx, atomId);
  if (!id.isAtom() || !NoCodeStore(cx, obj, id)) {
    return 0;
  }
  // The claims MIR reads of the object's published class: TYPES (kept
  // for a conforming value, the vouched store) and SLOTS (an add off the
  // class's slots drops it), and the class itself. RANGES, which no MIR
  // claim reads, drops as on every engine store; a word under
  // construction backs no fact past a generic op (the builder demotes
  // its `Ctor` slots).
  uint32_t r = SetPropIcMiss(cx, top, recv, atomId, val, cacheIdx,
                             /*strict=*/false, vouched);
  if (r == kMissErr) {
    return 3;
  }
  return DemotedForMir(before, robj->externalWord()) ? 2 : 1;
}

// Mega-table state machine (write side): way0 is the MONO way ([recvShape, 0,
// slotEnc, absSlot]); a second shape sentinels it and the site is served
// by the C++ mega-SET cache from here on.
static void NoteSetShape(uint32_t cacheIdx, uint32_t recvShape,
                         uint32_t slotEnc, uint32_t absSlot) {
  JSContext* cx = CurrentNightContext();
  uint32_t* way0 = InlineWay(cx, cacheIdx, 0);
  if (way0[0] == 0 || way0[0] == recvShape) {
    way0[1] = 0;
    way0[2] = slotEnc;
    way0[3] = absSlot;
    way0[0] = recvShape;  // shape last: the way's validity marker.
  } else if (way0[0] != kIcPolySentinel) {
    way0[0] = kIcPolySentinel;
  }
}

// The set IC's cached replays (no lookup, no JS): the site's add-transition
// row, the global (shape, atom) add table, the mega-SET probe. True when
// one served the store.
static bool SetPropCached(JSContext* cx, uint32_t top, uint64_t recv,
                          uint32_t atomId, uint64_t val, uint32_t cacheIdx,
                          bool vouched, bool skipRows) {
  SetNightTop(cx, top);
  // Add-transition row (linear-memory, after the site's ways; the
  // compiled body replays fixed-slot adds inline and only falls here for
  // dynamic slots, barrier-needing stores to tenured receivers, or a proto
  // mismatch). Replay in C++ (no lookup, no JS_SetPropertyById machinery);
  // the region is GC-zeroed so every cached word is a live pointer.
  {
    uint32_t* row = InlineTransRow(cx, cacheIdx);
    if (row[0]) {
      uint32_t protoPtrs[4] = {row[4], row[6], row[8], row[10]};
      uint32_t protoShapes[4] = {row[5], row[7], row[9], row[11]};
      uint32_t numProtos = 0;
      while (numProtos < 4 && protoPtrs[numProtos]) numProtos++;
      AutoVouchedStore v(vouched);
      if (js::night::NightTryAddPropTransition(cx, recv, row[0], row[1], row[3],
                                               protoPtrs, protoShapes,
                                               numProtos, val)) {
        return true;
      }
    }
  }
  // Global (oldShape, atomId) SET-add table: catches the poly sites whose
  // single site row alternates between receiver shapes.
  if (JS::Value::fromRawBits(recv).isObject()) {
    uint32_t shapeW =
        js::night::NightObjectShape(&JS::Value::fromRawBits(recv).toObject());
    SetAddRow& trow = SetAddAt(cx, shapeW, atomId);
    AutoVouchedStore v(vouched);
    if (trow.gen == InlineGen(cx) && trow.oldShape == shapeW &&
        trow.atomId == atomId &&
        js::night::NightTryAddPropTransition(
            cx, recv, trow.oldShape, trow.newShape, trow.slot, trow.protoPtrs,
            trow.protoShapes, trow.numProtos, val)) {
      // Seed the SITE row too (same rule as the init-add path above).
      // Without it this early return starves every site but the one that
      // populated the table -- and a spliced ctor has one site per splice,
      // so nearly every execution of the inline add arm finds an empty row
      // and lands here instead. The site row replays two proto hops; deeper
      // chains stay on the table alone.
      if (trow.numProtos <= 4 && (!trow.skip || skipRows)) {
        uint32_t* srow = InlineTransRow(cx, cacheIdx);
        uint32_t nfixed = JS::Value::fromRawBits(recv)
                              .toObject()
                              .as<js::NativeObject>()
                              .numFixedSlots();
        FillTransRow(srow, trow.oldShape, trow.newShape, trow.slot, nfixed,
                     trow.protoPtrs, trow.protoShapes, trow.numProtos);
      }
      return true;
    }
  }
  // Megamorphic secondary SET probe (leaf: pure loads + a barriered store).
  if (JS::Value::fromRawBits(recv).isObject()) {
    js::NativeObject* nobj = static_cast<js::NativeObject*>(
        &JS::Value::fromRawBits(recv).toObject());
    uint32_t shape = js::night::NightObjectShape(nobj);
    MegaSetEntry& e = *MegaSet(cx, shape, atomId);
    if (e.shape == shape && e.atomId == atomId) {
      AutoVouchedStore v(vouched);
      nobj->setSlot(e.absSlot, JS::Value::fromRawBits(val));
      NoteSetShape(cacheIdx, e.shape, e.slotEnc, e.absSlot);
      return true;
    }
  }
  return false;
}

// `skipRows`: the site's row may hold a transition that skips slots (an
// `init_field` site, whose compiled replay initializes them; MIR.md §2.3).
static uint32_t SetPropIcMiss(JSContext* cx, uint32_t top, uint64_t recv,
                              uint32_t atomId, uint64_t val, uint32_t cacheIdx,
                              bool strict, bool vouched, bool skipRows) {
  SetNightTop(cx, top);
  JS::HandleId id = AtomIdChecked(cx, atomId);
  // Fused globals: a fused global's write must never be served by the
  // inline/mega set caches (their hits bypass this helper): do the write
  // generically, arm or blow the fuses, and cache nothing for this (shape,
  // atom).
  if (JS::Value::fromRawBits(recv).isObject() &&
      IsActiveGlobal(&JS::Value::fromRawBits(recv).toObject())) {
    MaybeBlowBindingFuseAtom(atomId, val);
    if (FindGnameFuse(cx, atomId)) {
      MaybeGnameFuseBlow(atomId, val);
      JS::RootedObject gobj(cx, &JS::Value::fromRawBits(recv).toObject());
      if (!GenericSetWithStrict(cx, gobj, id, val, recv, strict)) {
        return kMissErr;
      }
      MaybeGnameFuseArmAfterStore(cx, atomId, val);
      MaybeRearmBindingFuseAtom(cx, atomId);
      return kMissOk;
    }
  }
  if (SetPropCached(cx, top, recv, atomId, val, cacheIdx, vouched, skipRows)) {
    return kMissClean;
  }
  const MissQuiet quiet(cx);
  bool populated = false;
  JS::RootedObject obj(cx, ReceiverObjectAtom(cx, recv, "ic-set ", atomId));
  if (!obj) {
    return kMissErr;
  }
  // Never cache the GLOBAL OBJECT as a set receiver: our inline set-IC /
  // mega / trans-add hits do raw stores that bypass Watchtower, which the
  // constant-gname ObjectFuse arm depends on. Global-receiver sets stay on
  // the generic path (engine setters run the Watchtower hooks).
  if (IsActiveGlobal(obj)) {
    return GenericSetWithStrict(cx, obj, id, val, recv, strict);
  }
  uint32_t shapeBefore = js::night::NightObjectShape(obj);
  uint32_t spanBefore = js::night::NightObjectSlotSpanIfShared(obj);
  // A vouched store that is a plain slot write or add runs no JS and makes
  // this one store, so it keeps TYPES too (`PlainStore`).
  bool plainWrite = vouched && PlainStore(obj, id);
  {
    AutoVouchedStore v(plainWrite);
    if (!GenericSetWithStrict(cx, obj, id, val, recv, strict)) {
      return kMissErr;
    }
  }
  if (js::night::NightObjectShape(obj) != shapeBefore) {
    // The set ADDED a property (or otherwise reshaped): try to cache the
    // transition in the site's linear-memory row. (A GC during the set may
    // have moved the old shape, making `shapeBefore` stale -- then the row
    // simply never hits until repopulated; the GC callback zeroes the
    // region on major GC.)
    uint32_t newShape, slot, protoPtrs[4], protoShapes[4], numProtos;
    bool nurseryProto = false;
    bool skip = false;
    if (js::night::NightPopulateAddTransition(
            cx, obj, id, spanBefore, &newShape, &slot, protoPtrs, protoShapes,
            &numProtos, &nurseryProto, &skip)) {
      populated = true;
      if (nurseryProto) {
        RtState(cx).transRowsHoldNursery = true;
      }
      // The site row replays two proto hops at most; deeper chains are
      // served by the global table alone (its rows carry four hops), and so
      // is a transition that skips slots (the compiled replays do not
      // initialize them).
      if (numProtos <= 4 && (!skip || skipRows)) {
        uint32_t* row = InlineTransRow(cx, cacheIdx);
        uint32_t nfixed = obj->as<js::NativeObject>().numFixedSlots();
        FillTransRow(row, shapeBefore, newShape, slot, nfixed, protoPtrs,
                     protoShapes, numProtos);
      }
      SetAddRow& trow = SetAddAt(cx, shapeBefore, atomId);
      trow.gen = InlineGen(cx);
      trow.oldShape = shapeBefore;
      trow.atomId = atomId;
      trow.newShape = newShape;
      trow.slot = slot;
      trow.skip = skip;
      trow.numProtos = numProtos;
      for (uint32_t i = 0; i < 4; i++) {
        trow.protoPtrs[i] = i < numProtos ? protoPtrs[i] : 0;
        trow.protoShapes[i] = i < numProtos ? protoShapes[i] : 0;
      }
    }
  } else {
    uint32_t recvShape, slotEnc, absSlot;
    uint32_t reason = 0;
    if (js::night::NightPopulateInlineSetIC(cx, obj, id, &recvShape, &slotEnc,
                                            &absSlot, &reason)) {
      populated = true;
      NoteSetShape(cacheIdx, recvShape, slotEnc, absSlot);
      // Fill the mega cache unconditionally (global, direct-mapped
      // overwrite).
      MegaSetEntry& e = *MegaSet(cx, recvShape, atomId);
      e.atomId = atomId;
      e.slotEnc = slotEnc;
      e.absSlot = absSlot;
      e.shape = recvShape;
    } else if (RtEnv(cx).accessorCachePtr && reason == 3) {
      // Populate refused with "no own property": the set may have run a
      // proto-chain SETTER -- prime the accessor-call cache so the
      // compiled accessor arm dispatches it directly from here on.
      uint64_t callee;
      uint32_t rs, hp, hs;
      if (js::night::NightPrimeAccessor(cx, obj, id, /*wantSetter=*/true,
                                        &callee, &rs, &hp, &hs)) {
        WriteAccessorEntry(cx, rs, atomId, /*kind=*/1, callee, hp, hs);
      }
    }
  }
  // A store the engine served as a plain slot write or a cached add
  // transition (populate succeeded), with no GC and no stamp moved: the
  // caller's facts hold.
  return populated && JS::Value::fromRawBits(recv).isObject() && quiet.still(cx)
             ? kMissClean
             : kMissOk;
}

// MIR's `init_field` slow path (MIR.md §2.3): add field `atomId` (the next
// one its layout predicts) to `recv`, an object under construction, when
// the add is a plain one (`PlainStore`: runs no JS), keeping TYPES (the
// value is of the field's type by the caller's type) and filling the
// site's add-transition row so the inline replay hits next time. The
// object (a GC may have moved it) goes to the out-slot. Returns 1 iff the
// object is still under construction with the caller's early key, with
// `wantBits` (SLOTS, TYPES) set and exactly the fields `expectSet`: the
// constructing type the caller continues with. 0 leaves the rest of the
// constructor to baseline (an add not done is done there; one done
// becomes an overwrite). May GC.
uint32_t night_runtime_elem_grow(JSContext* cx, uint32_t top, uint64_t recv,
                                 uint32_t idx, uint64_t val) {
  SetNightTop(cx, top);
  WriteNightOut(top, recv);
  JS::Value rv = JS::Value::fromRawBits(recv);
  if (!rv.isObject() || !rv.toObject().is<js::NativeObject>()) {
    return 0;
  }
  JS::Rooted<js::NativeObject*> obj(cx, &rv.toObject().as<js::NativeObject>());
  JS::RootedValue v(cx, JS::Value::fromRawBits(val));
  if (idx != obj->getDenseInitializedLength() || idx == UINT32_MAX ||
      !obj->isExtensible() || obj->denseElementsAreFrozen() ||
      !NoExtraIndexedFast(cx, obj)) {
    return 0;
  }
  bool isArray = obj->is<js::ArrayObject>();
  if (isArray && !obj->as<js::ArrayObject>().lengthIsWritable() &&
      idx >= obj->as<js::ArrayObject>().length()) {
    return 0;
  }
  if (!obj->ensureElements(cx, idx + 1)) {
    cx->clearPendingException();
    return 0;
  }
  obj->setDenseInitializedLength(idx + 1);
  obj->initDenseElement(idx, v);
  if (isArray && idx >= obj->as<js::ArrayObject>().length()) {
    obj->as<js::ArrayObject>().setLength(cx, idx + 1);
  }
  WriteNightOut(top, JS::ObjectValue(*obj).asRawBits());
  return 1;
}

// Whether `obj`, under construction with word `w`, has exactly the fields
// `set` of its layout (bit i: field i, at slot i): the word's set and the
// span of the fields (any other property would raise it), as MIR's
// `guard.ctor`.
static bool NightHasExactlyFields(js::NativeObject* obj, uint32_t w,
                                  uint32_t set) {
  uint32_t span = set ? 32 - mozilla::CountLeadingZeroes32(set) : 0;
  return (w & ((1u << js::night::kCtorSetBits) - 1)) ==
             (set & ((1u << js::night::kCtorSetBits) - 1)) &&
         obj->slotSpan() == span;
}

uint32_t night_runtime_init_field(JSContext* cx, uint32_t top, uint64_t recv,
                                  uint32_t atomId, uint64_t val,
                                  uint32_t cacheIdx, uint32_t expectSet,
                                  uint32_t wantBits) {
  SetNightTop(cx, top);
  WriteNightOut(top, recv);
  JS::Value rv = JS::Value::fromRawBits(recv);
  if (!rv.isObject() || !rv.toObject().is<js::NativeObject>()) {
    return 0;
  }
  JS::RootedObject obj(cx, &rv.toObject());
  JS::HandleId id = AtomIdChecked(cx, atomId);
  uint32_t key = obj->externalWord() & (js::night::kWordConstructing | 0x3FFC0000u);
  if (!PlainStore(obj, id) || obj->as<js::NativeObject>().lookupPure(id).isSome()) {
    return 0;
  }
  uint32_t r =
      SetPropIcMiss(cx, top, recv, atomId, val, cacheIdx, false, true, true);
  WriteNightOut(top, JS::ObjectValue(*obj).asRawBits());
  if (r == kMissErr) {
    cx->clearPendingException();
    return 0;
  }
  uint32_t w = obj->externalWord();
  return (w & (js::night::kWordConstructing | 0x3FFC0000u)) == key &&
                 (w & wantBits) == wantBits &&
                 NightHasExactlyFields(&obj->as<js::NativeObject>(), w,
                                       expectSet)
             ? 1
             : 0;
}

// Major-GC callback: bump the inline-IC generation counter and zero every
// linear-memory cache region that holds raw shape/function/value words, so a
// cached (possibly moved or freed-and-reused) pointer can never false-hit
// against the live heap. Runs at BOTH ends of a *major* GC (minor/nursery
// collections use a separate callback and never move the tenured things we
// cache):
//  - at JSGC_BEGIN, so that under an INCREMENTAL major GC no pre-GC entry
//    survives into an inter-slice mutator window -- a sweep slice can free a
//    cached-but-otherwise-dead Shape/function whose address the mutator then
//    reuses before the collection ends, which would false-hit a guard with
//    no generation field. Entries refilled between slices reference values
//    the mutator just loaded (kept live by allocate-black + barriers), so
//    they stay valid for the rest of the collection.
//  - at JSGC_END, so entries refilled mid-GC that a final compacting phase
//    moved are also dropped.
// Every linear-memory row that caches a raw GC-thing address, dropped in one
// sweep. A compacting GC moves live cells, and a sweeping one frees dead ones
// whose address can be reused, so a row that survives either is a false hit
// waiting to happen. Nothing here is traced -- the rows are u32s in the
// module's own memory with no type tag -- so dropping them is the whole
// invalidation strategy, and every populate path refills lazily.
// The binding value cells (n*16, after the rows) cache raw value bits a
// compacting GC can move. The values themselves outlive any GC (the binding
// keeps each alive) and a write disarms its cell, so an armed cell is
// refreshed from the global in place, keeping its state: compiled code that
// tested a cell before the GC (a `check.binding.fn` whose `load_gname`
// follows a may-GC op) reads the value there after it. Outside a realm (no
// compiled frame is running) the cells are zeroed and re-arm at resolve.
static void RefreshBindingCells() {
  JSContext* cx = CurrentNightContext();
  if (!RtState(cx).globalValsBase || !RtNames(cx).bindingKeys) {
    return;
  }
  size_t n = RtNames(cx).bindingKeys->size();
  if (!cx || !JS::CurrentGlobalOrNull(cx)) {
    ZeroRegion(RtState(cx).globalValsBase, n * 16);
    return;
  }
  for (size_t i = 0; i < n; i++) {
    uint32_t* cell = BindingFuseCell(cx, uint32_t(i));
    if (!(cell[2] & 1)) {
      // Unarmed or blown: reset, as the zeroing this replaces did, so the
      // next resolve may arm it again.
      ZeroRegion(RtState(cx).globalValsBase + 16 * uint32_t(i), 16);
      continue;
    }
    // A nursery value (armed so, and listed for the nursery's end, which
    // re-arms it once moved) is kept as it is.
    uint64_t bits;
    bool nursery = false;
    if (js::night::NightTryBindingValue(cx, (*RtNames(cx).bindingKeys)[i].get(),
                                        &bits, &nursery)) {
      *reinterpret_cast<uint64_t*>(cell) = bits;
    } else {
      cell[2] = 0;
    }
  }
}

// --- Predicted-method cells ------------------------------------------------
//
// A method load whose name the analysis resolves through the receiver's
// prototype chain to one script (`method.load`) reads its function from a
// cell (RtEnv(cx).methodCellsPtr, Night_methodCell*): armed, the cell holds the
// receivers' prototype P and the function, which a property of a holder H
// (P or above it) holds. The receiver is CLOSED (no own property outside
// its row), so the name is not its own, and P is its prototype, so the
// lookup starts there. What keeps the rest true is the holder's ObjectFuse:
// H's property is marked constant, and whatever the engine invalidates
// constant-property assumptions for -- a write, a delete or a redefinition
// of it, the name added to a prototype below it (shape teleporting's
// shadowing), a prototype change on the chain, a swap -- reaches
// `NightObjectFuseInvalidated`, which unarms the cells that
// depend on it. A major GC zeroes every cell (P or the function may die).
struct MethodDep {
  js::ObjectFuse* fuse;
  uint32_t slot;
  uint32_t cell;
};
static std::vector<MethodDep>& RtMethodDeps(JSContext* cx);

static void ZeroMethodCells() {
  JSContext* cx = CurrentNightContext();
  if (RtEnv(cx).methodCellsPtr && RtEnv(cx).methodCellsLen) {
    ZeroRegion(RtEnv(cx).methodCellsPtr, RtEnv(cx).methodCellsLen);
  }
  RtMethodDeps(cx).clear();
}

// A cell found not armable stays so (poisoned) until the next GC: one
// that tenures a function or prototype may make it armable.
static void UnpoisonMethodCells() {
  JSContext* cx = CurrentNightContext();
  if (!RtEnv(cx).methodCellsPtr) {
    return;
  }
  for (uint32_t off = 0; off < RtEnv(cx).methodCellsLen;
       off += js::night::Night_methodCellBytes) {
    uint32_t* c = LinMem<uint32_t>(RtEnv(cx).methodCellsPtr + off);
    if (c[0] == js::night::Night_methodCellPoison) {
      c[0] = 0;
    }
  }
}

// Arm the method cell at `cellAddr` for receiver `recvBits` (an object of a
// CLOSED layout, which compiled code has guarded): name `atomId` resolves
// from its prototype, through native, tenured, resolve-free objects, to a
// data property holding a compiled function of `scriptAddr`'s script,
// tenured, which the holder's ObjectFuse can track as constant. 1 when
// armed (the cell then matches this receiver's prototype); else 0, the
// cell poisoned. A leaf: the holder's fuse flag is set with GC suppressed.
int32_t night_runtime_method_arm(uint64_t recvBits, uint32_t cellAddr,
                                 uint32_t atomId, uint32_t scriptAddr) {
  JSContext* cx = CurrentNightContext();
  uint32_t* c = LinMem<uint32_t>(cellAddr);
  if (!cx || !RtNames(cx).ids || atomId >= RtNames(cx).ids->size() || c[0] != 0) {
    return 0;
  }
  c[0] = js::night::Night_methodCellPoison;
  JS::Value rv = JS::Value::fromRawBits(recvBits);
  if (!rv.isObject()) {
    return 0;
  }
  JS::PropertyKey id = (*RtNames(cx).ids)[atomId].get();
  JSObject* proto = rv.toObject().staticPrototype();
  js::NativeObject* holder = nullptr;
  mozilla::Maybe<js::PropertyInfo> prop;
  for (JSObject* o = proto; o; o = o->staticPrototype()) {
    if (!o->is<js::NativeObject>() || js::gc::IsInsideNursery(o) ||
        o->hasDynamicPrototype()) {
      return 0;
    }
    js::NativeObject* n = &o->as<js::NativeObject>();
    if (js::ClassMayResolveId(cx->names(), n->getClass(), id, n)) {
      return 0;
    }
    prop = n->lookupPure(id);
    if (prop) {
      holder = n;
      break;
    }
  }
  if (!holder || !prop->isDataProperty()) {
    return 0;
  }
  JS::Value fv = holder->getSlot(prop->slot());
  if (!js::night::NightIsCompiledFunctionOf(fv.asRawBits(), scriptAddr) ||
      js::gc::IsInsideNursery(&fv.toObject())) {
    return 0;
  }
  js::ObjectFuse* fuse = nullptr;
  {
    js::gc::AutoSuppressGC nogc(cx);
    JS::Rooted<js::NativeObject*> h(cx, holder);
    if (!h->hasObjectFuse() && !js::NativeObject::setHasObjectFuse(cx, h)) {
      cx->recoverFromOutOfMemory();
      return 0;
    }
    fuse = cx->zone()->objectFuses.getOrCreate(cx, h);
    if (!fuse) {
      cx->recoverFromOutOfMemory();
      return 0;
    }
    // The flag reshaped the holder; its properties are the same.
    prop = h->lookupPure(id);
    if (!prop || !fuse->tryOptimizeConstantProperty(*prop)) {
      return 0;
    }
  }
  RtMethodDeps(cx).push_back({fuse, prop->slot(), cellAddr});
  *reinterpret_cast<uint64_t*>(c + js::night::Night_methodCellFnOff / 4) =
      fv.asRawBits();
  c[0] = uint32_t(reinterpret_cast<uintptr_t>(proto));
  return 1;
}

// The engine invalidated constant-property assumptions about `fuse`'s
// object: the property in `slot`, or every one (UINT32_MAX). Unarm the
// cells resting on them; they re-arm at their next miss if they still can.
extern "C++" {
void js::night::NightObjectFuseInvalidated(js::ObjectFuse* fuse,
                                           uint32_t slot) {
  JSContext* cx = CurrentNightContext();
  for (size_t i = 0; i < RtMethodDeps(cx).size();) {
    const MethodDep& d = RtMethodDeps(cx)[i];
    if (d.fuse == fuse && (slot == UINT32_MAX || d.slot == slot)) {
      ZeroRegion(d.cell, js::night::Night_methodCellBytes);
      RtMethodDeps(cx)[i] = RtMethodDeps(cx).back();
      RtMethodDeps(cx).pop_back();
    } else {
      i++;
    }
  }
}
}  // extern "C++"

static void NightPurgeMovableCaches() {
  JSContext* cx = CurrentNightContext();
  if (RtEnv(cx).propicGenPtr) {
    *LinMem<uint32_t>(RtEnv(cx).propicGenPtr + js::night::Night_hostGenOff) += 1;
  }
  // The per-site ways and the linmem mega-GET table cache raw shape /
  // holder pointers with NO generation field; zero them so a compacting GC
  // can never leave a false-hittable stale pointer. (Way sentinels are
  // cleared too: a poly site re-learns, costing one extra miss round.)
  if (RtEnv(cx).propicPtr && RtEnv(cx).propicLen) {
    ZeroRegion(RtEnv(cx).propicPtr, RtEnv(cx).propicLen);
  }
  if (RtEnv(cx).megaGetPtr) {
    ZeroRegion(RtEnv(cx).megaGetPtr, kMegaGetSize * sizeof(MegaGetEntry));
  }
  // Guarded-chain table: caches tenured proto pointers + shape words.
  memset(RtGChain(cx), 0, sizeof(GChainEntry) * kGChainSize);
  // Dense-append cache rows pin receiver shape + proto (ptr, shape) pairs; a
  // compacting major GC can move any of them, so zero the region (the prime
  // path refills).
  if (RtEnv(cx).appendCachePtr) {
    ZeroRegion(RtEnv(cx).appendCachePtr, kAppendCacheRows * kAppendCacheRowBytes);
  }
  // The accessor-call cache holds raw callee/holder/shape pointers.
  if (RtEnv(cx).accessorCachePtr) {
    ZeroRegion(RtEnv(cx).accessorCachePtr,
               kAccessorCacheRows * kAccessorCacheRowBytes);
  }
  if (RtEnv(cx).megaSetPtr) {
    ZeroRegion(RtEnv(cx).megaSetPtr, kMegaSetSize * sizeof(MegaSetEntry));
  }
  // The guarded gname entries cache a raw shape pointer; a major (compacting)
  // GC can move shapes, and a freed-then-reused shape address would FALSE-HIT
  // the guard. Zero the whole region: every entry re-resolves on next read
  // (the TI-proven entries re-resolve too -- harmless, one leaf call each).
  if (RtEnv(cx).gslotsPtr && RtNames(cx).bindingKeys) {
    // The rows (n*8) cache raw shape pointers: zeroed, re-resolved on use.
    ZeroRegion(RtEnv(cx).gslotsPtr, RtNames(cx).bindingKeys->size() * 8);
    RefreshBindingCells();
  }
  // This region holds the STATIC per-layout add-check bound table (filled
  // at install): it must survive GC, so no zeroing here.
  // Per-site callee value cells (16-byte rows [callee_bits u64][funcidx
  // u32][script u32]; zero == empty), populated inline by compiled code.
  // They cache raw function-value bits and a script pointer; a major GC can
  // move or free either (compact/sweep), and a reused address must never
  // false-hit, so zero the region. (The store path caches tenured callees
  // only, so minor GCs cannot invalidate a row.)
  if (RtEnv(cx).callCellsPtr && RtEnv(cx).callCellsLen) {
    ZeroRegion(RtEnv(cx).callCellsPtr, RtEnv(cx).callCellsLen);
  }
  // Inline-alloc cells (32-byte rows; see translate.rs ALLOC_CELL_BYTES)
  // cache shape and alloc-site pointers; zero so a compacting major GC can
  // never leave a stale replayable row.
  if (RtEnv(cx).allocCellsPtr && RtEnv(cx).allocCellsLen) {
    ZeroRegion(RtEnv(cx).allocCellsPtr, RtEnv(cx).allocCellsLen);
  }
  // Intrinsic value cells cache boxed Value bits (functions, mostly); a
  // compacting major GC can move them, so zero and re-resolve. (The fill
  // helper caches tenured values only, so minor GCs cannot invalidate.)
  if (RtEnv(cx).intrinsicCellsPtr && RtEnv(cx).intrinsicCellsLen) {
    ZeroRegion(RtEnv(cx).intrinsicCellsPtr, RtEnv(cx).intrinsicCellsLen);
  }
  js::night::NightPurgeAddMemo();
  // MIR's element-add arm's rows hold shape and prototype pointers.
  memset(js::night::NightData(cx).elemAdd, 0,
         sizeof(js::night::NightData(cx).elemAdd));
  // MIR's regexp arm caches a shape and RegExpShared pointers.
  if (RtState(cx).strLitBase) {
    *LinMem<uint32_t>(RtState(cx).strLitBase +
                      js::night::Night_strlitRegExpShapeOff) = 0;
    memset(js::night::NightData(cx).regexLeaf.rows, 0,
           sizeof(js::night::NightData(cx).regexLeaf.rows));
  }
  // The string-method and builtin guard cells hold raw function bits;
  // compaction moves functions, so re-write them from the rooted
  // (auto-updated) values.
  RearmStringMethodCells();
  RearmBuiltinCells();
  ZeroMethodCells();
}

// Every row and cell that caches a pointer, a value or a decision about
// this context's heap, emptied: what NightPurgeMovableCaches zeroes, and
// the cells it re-arms from the context's live values (the builtin and
// string-method identity cells, the binding value cells, the method cells,
// the global literal fuses) zeroed instead, which is their unarmed state.
// The generation word moves, so every generation-checked cell misses too.
// Install-time tables (the layout add-check bounds, the region table) and
// the dynamic-code fuse are kept: zero means something else there.
extern "C++" void js::night::NightClearCaches(JSContext* cx) {
  NightPurgeMovableCaches();
  RtState(cx).pushFnBits = 0;
  if (RtState(cx).builtinCellsBase) {
    ZeroRegion(RtState(cx).builtinCellsBase, 8 * NightPristineFns::kCount);
  }
  for (uint32_t cell : {RtState(cx).strCharCodeAtCell, RtState(cx).strCharAtCell,
                        RtState(cx).strFromCharCodeCell}) {
    if (cell) {
      ZeroRegion(cell, 8);
    }
  }
  if (RtState(cx).globalValsBase && RtNames(cx).bindingKeys) {
    ZeroRegion(RtState(cx).globalValsBase, RtNames(cx).bindingKeys->size() * 16);
  }
  RtState(cx).nurseryArmedBindings.clear();
  if (RtEnv(cx).fuseCellsPtr) {
    ZeroRegion(RtEnv(cx).fuseCellsPtr, 4 * RtNames(cx).fuses.size());
  }
  ZeroMethodCells();
  memset(RtSetAdd(cx), 0, sizeof(SetAddRow) * kSetAddSize);
  memset(RtInitAdd(cx), 0, sizeof(InitAddRow) * kInitAddSize);
  memset(RtHasInst(cx), 0, sizeof(uint32_t) * kHasInstCacheN * 2);
  memset(RtNoExtra(cx), 0, sizeof(uintptr_t) * kNoExtraCacheN * 5);
  RtState(cx).transRowsHoldNursery = false;
}

// The purge points, all on the slice callback: `GC_CYCLE_BEGIN`/`GC_CYCLE_END`
// bracket a whole collection (the single-slot `JS_SetGCCallback` is not used
// here because an embedding or the shell's testing functions replace it, which
// would silently drop the purge and leave freed shape pointers in the caches).
// An incremental collection runs JS between its slices -- so a row cached in
// one slice, whose target a LATER slice relocates, would be read stale before
// the cycle ends. Only a SHRINKING GC compacts (`GCRuntime::shouldCompact`),
// so purging at the end of each of its slices closes that window exactly, and
// every other GC keeps the cheaper begin/end pair. The shell installs a slice
// callback of its own; chain it.
static void NightGcSliceCallback(JSContext* cx, JS::GCProgress progress,
                                 const JS::GCDescription& desc) {
  if (progress == JS::GC_CYCLE_BEGIN || progress == JS::GC_CYCLE_END ||
      (progress == JS::GC_SLICE_END &&
       desc.options_ == JS::GCOptions::Shrink)) {
    NightPurgeMovableCaches();
  }
  if (progress == JS::GC_CYCLE_END) {
    RefreshStringAlloc(cx);
  }
  if (RtState(cx).prevSliceCallback) {
    RtState(cx).prevSliceCallback(cx, progress, desc);
  }
}

static void MaybeArmBindingFuse(JSContext* cx, uint32_t bindingId,
                                JS::PropertyKey id);

// Minor-GC-end callback: retry the binding-fuse arm for resolved bindings
// whose cells are still unarmed -- typically because the value was in the
// nursery at resolve time (toplevel functions are nursery-born; they tenure
// at the first minor GC, after which the cache is safe).
static void NightNurseryEndCallback(JSContext* cx,
                                    JS::GCNurseryProgress progress,
                                    JS::GCReason reason, void* data) {
  if (progress != JS::GCNurseryProgress::GC_NURSERY_COLLECTION_END) {
    return;
  }
  // Method/builtin cells arm at startup, when a lazily-materialized builtin
  // can still be nursery-born; the first minor GC moves it and would leave
  // the cell stale (sound but permanently missing). Re-write from the
  // rooted values.
  RearmStringMethodCells();
  RearmBuiltinCells();
  UnpoisonMethodCells();
  // Binding cells armed with a nursery value: the value moved, the slot is
  // the truth. Unarm and re-arm from it (a program that re-creates its
  // heap-view globals on every run never lets that view tenure, so it
  // never arms and every read of it pays the slot prologue).
  if (!RtState(cx).nurseryArmedBindings.empty() && RtNames(cx).bindingKeys) {
    std::vector<uint32_t> pending;
    pending.swap(RtState(cx).nurseryArmedBindings);
    for (uint32_t bid : pending) {
      uint32_t* cell = BindingFuseCell(cx, bid);
      if (cell[2] & 1) {
        cell[2] = 0;
        MaybeArmBindingFuse(cx, bid, (*RtNames(cx).bindingKeys)[bid].get());
      }
    }
  }
  // Trans rows / the SET-add table that cached nursery proto pointers die
  // with this minor GC.
  if (RtState(cx).transRowsHoldNursery) {
    if (RtEnv(cx).propicPtr && RtEnv(cx).propicLen) {
      for (uint32_t off = INLINE_IC_TRANS_OFF; off < RtEnv(cx).propicLen;
           off += INLINE_IC_STRIDE) {
        ZeroRegion(RtEnv(cx).propicPtr + off, INLINE_IC_TRANS_BYTES);
      }
    }
    memset(RtSetAdd(cx), 0, sizeof(SetAddRow) * kSetAddSize);
    RtState(cx).transRowsHoldNursery = false;
  }
  if (!RtEnv(cx).gslotsPtr || !RtState(cx).globalValsBase || !RtNames(cx).bindingKeys) {
    return;
  }
  for (size_t i = 0; i < RtNames(cx).bindingKeys->size(); i++) {
    uint32_t row = *LinMem<uint32_t>(RtEnv(cx).gslotsPtr + 8 * i);
    uint32_t* cell = LinMem<uint32_t>(RtState(cx).globalValsBase + 16 * i);
    if ((row & 1) && !cell[2]) {
      MaybeArmBindingFuse(cx, uint32_t(i), (*RtNames(cx).bindingKeys)[i].get());
    }
  }
}

// A global lexical binding now shadows `id`: zero the binding's resolved
// gGlobalSlots row (entry + shape guard word; the next read/write
// re-resolves, sees the shadow via the lexical lookup in NightResolveGlobal-
// Slot*, and stays generic) and blow the name's value/gname fuses. Rare
// (global-script declaration instantiation), so linear scans are fine.
extern "C" void night_runtime_global_lexical_shadow_added(uintptr_t idBits) {
  JSContext* cx = CurrentNightContext();
  JS::PropertyKey id = JS::PropertyKey::fromRawBits(idBits);
  if (RtEnv(cx).gslotsPtr && RtNames(cx).bindingKeys) {
    for (size_t i = 0; i < RtNames(cx).bindingKeys->size(); i++) {
      if ((*RtNames(cx).bindingKeys)[i].get() == id) {
        ZeroRegion(RtEnv(cx).gslotsPtr + 8 * i, 8);
      }
    }
  }
  BlowBindingFuseKey(id);
  if (RtNames(cx).ids) {
    for (size_t i = 0; i < RtNames(cx).ids->size(); i++) {
      if ((*RtNames(cx).ids)[i].get() == id) {
        BlowGnameFuse(uint32_t(i));
      }
    }
  }
}

bool night_runtime_get_gname(JSContext* cx, uint32_t top, uint32_t atomId,
                             uint32_t forTypeof) {
  SetNightTop(cx, top);
  JS::HandleId id = AtomIdChecked(cx, atomId);
  JS::RootedValue res(cx);
  if (!js::night::NightGetGName(cx, id, forTypeof != 0, &res)) {
    return false;
  }
  WriteNightOut(top, res.get().asRawBits());
  return true;
}

// Arm the binding's value fuse: cache the current (tenured) value in the
// gGlobalVals cell (bits first, fuse word last). Never re-arms a blown (2)
// cell inside a GC cycle; the major-GC zero resets everything and the next
// resolve re-arms with the then-current value.
static void MaybeArmBindingFuse(JSContext* cx, uint32_t bindingId,
                                JS::PropertyKey id) {
  if (!RtState(cx).globalValsBase || !RtState(cx).bindingFuseArmingAllowed) {
    return;
  }
  uint32_t* cell = BindingFuseCell(cx, bindingId);
  if (cell[2] != 0) {
    return;
  }
  uint64_t bits;
  bool nursery = false;
  if (!js::night::NightTryBindingValue(cx, id, &bits, &nursery)) {
    return;
  }
  // A compiled function of the predicted script arms the predicted state,
  // which compiled reads typed as that function test; anything else arms
  // plainly.
  uint32_t predicted = bindingId < RtNames(cx).bindingPredictedScript.size()
                           ? RtNames(cx).bindingPredictedScript[bindingId]
                           : 0;
  bool isPredicted =
      predicted && js::night::NightIsCompiledFunctionOf(bits, predicted);
  *reinterpret_cast<uint64_t*>(cell) = bits;
  cell[2] = isPredicted ? js::night::Night_bindingFusePredicted : js::night::Night_bindingFuseArmed;
  if (nursery) {
    RtState(cx).nurseryArmedBindings.push_back(bindingId);
  }
}

// The inline `SetGName` store's fuse maintenance: the compiled store has
// unarmed the binding's cell (an armed cell whose value changed); re-arm it
// from the stored value with every check the resolve-time arm makes
// (tenured or nursery-listed, expected callee for call bindings). A leaf.
static constexpr uint32_t kBindingFlipLimit = 1024;

void night_runtime_binding_written(uint32_t bindingId) {
  JSContext* cx = CurrentNightContext();
  if (!RtState(cx).cx || !RtNames(cx).bindingKeys ||
      bindingId >= RtNames(cx).bindingKeys->size()) {
    return;
  }
  if (RtState(cx).bindingFlips.size() < RtNames(cx).bindingKeys->size()) {
    RtState(cx).bindingFlips.resize(RtNames(cx).bindingKeys->size(), 0);
  }
  if (++RtState(cx).bindingFlips[bindingId] > kBindingFlipLimit) {
    uint32_t* cell = BindingFuseCell(cx, bindingId);
    if (cell[2] == 0) {
      cell[2] = 2;
    }
    return;
  }
  MaybeArmBindingFuse(RtState(cx).cx, bindingId,
                      (*RtNames(cx).bindingKeys)[bindingId].get());
}

// The guarded (no-TI) resolve: cache [entry, globalShape] for an own plain
// data slot of the global object (not lexically shadowed); return 0 when not
// cacheable so the inline read falls back to the generic char-based helper.
// A leaf (lookupPure + shape read; no allocation, no GC).
uint32_t night_runtime_resolve_global_slot_guarded(JSContext* cx,
                                                   uint32_t bindingId) {
  if (!RtNames(cx).bindingKeys || bindingId >= RtNames(cx).bindingKeys->size()) {
    MOZ_CRASH(
        "night_runtime_resolve_global_slot_guarded: bindingId out of range");
  }
  JS::PropertyKey id = (*RtNames(cx).bindingKeys)[bindingId].get();
  uint32_t shape = 0;
  uint32_t entry = js::night::NightResolveGlobalSlotGuarded(cx, id, &shape);
  uint32_t* row = LinMem<uint32_t>(RtEnv(cx).gslotsPtr + 8 * bindingId);
  row[0] = entry;
  row[1] = shape;
  if (entry) {
    MaybeArmBindingFuse(cx, bindingId, id);
  }
  return entry;
}

// `BindUnqualifiedGName atomId`: push the binding object for a global-name
// assignment. May GC/throw; writes the boxed object to the out-slot.
bool night_runtime_bind_unqualified_gname(JSContext* cx, uint32_t top,
                                          uint32_t atomId) {
  SetNightTop(cx, top);
  JS::HandleId id = AtomIdChecked(cx, atomId);
  JS::RootedValue res(cx);
  if (!js::night::NightBindUnqualifiedGName(cx, id, &res)) {
    return false;
  }
  WriteNightOut(top, res.get().asRawBits());
  return true;
}

// `SetGName`/`SetName` (and strict forms) `atomId`: assign `val` to the name on
// the binding object `env` (`strict` selects strict-mode error semantics). May
// GC/throw. The value stays on the stack (the translator re-pushes it).
bool night_runtime_set_name(JSContext* cx, uint32_t top, uint64_t env,
                            uint32_t atomId, uint64_t val, uint32_t strict) {
  SetNightTop(cx, top);
  JS::HandleId id = AtomIdChecked(cx, atomId);
  // Every compiled unqualified/global name write funnels through here;
  // blow the binding's fuses against the predicted literal before the store
  // (arming happens after the store succeeds, below). same for the
  // per-binding value fuse (a same-bits rewrite stays armed).
  MaybeGnameFuseBlow(atomId, val);
  MaybeBlowBindingFuseAtom(atomId, val);
  if (!js::night::NightSetName(cx, id, env, val, strict != 0)) {
    return false;
  }
  MaybeGnameFuseArmAfterStore(cx, atomId, val);
  MaybeRearmBindingFuseAtom(cx, atomId);
  return true;
}

// The pure element reads `night_runtime_get_element` and MIR's
// `getelem.data` serve first: an in-bounds dense element, a typed array's,
// the engine's megamorphic by-value lookup (filling the site's inline
// by-value probe), an arguments object's. No GC, no user code; true with
// the value in the out-slot.
static bool TryPureElementRead(JSContext* cx, uint32_t top, uint64_t recv,
                               uint64_t key) {
  // In-bounds, non-hole dense element of a native object: an own data
  // property, so the read is the element itself. Baseline inlines
  // this arm; the MIR tier's generic element read reaches it here.
  {
    JS::Value rv = JS::Value::fromRawBits(recv);
    JS::Value kv = JS::Value::fromRawBits(key);
    if (rv.isObject() && kv.isInt32() && kv.toInt32() >= 0 &&
        rv.toObject().is<js::NativeObject>()) {
      js::NativeObject* nobj = &rv.toObject().as<js::NativeObject>();
      uint32_t idx = uint32_t(kv.toInt32());
      if (idx < nobj->getDenseInitializedLength()) {
        JS::Value v = nobj->getDenseElement(idx);
        if (!v.isMagic(JS_ELEMENTS_HOLE)) {
          WriteNightOut(top, v.asRawBits());
          return true;
        }
      }
    }
  }
  // Typed-array fast path (pure: no GC, no user code): the inline dense arm
  // rejects typed arrays (their dense initializedLength is 0), so their
  // in-bounds int32-keyed reads land here.
  // getElementPure serves every non-BigInt scalar kind with a canonical
  // Value; OOB/detached/BigInt fall through to the generic path.
  {
    JS::Value rv = JS::Value::fromRawBits(recv);
    JS::Value kv = JS::Value::fromRawBits(key);
    if (rv.isObject() && kv.isInt32() && kv.toInt32() >= 0 &&
        rv.toObject().is<js::TypedArrayObject>()) {
      js::TypedArrayObject* ta = &rv.toObject().as<js::TypedArrayObject>();
      size_t idx = size_t(kv.toInt32());
      mozilla::Maybe<size_t> len = ta->length();
      if (len.isSome() && idx < *len) {
        JS::Value out;
        if (ta->getElementPure(idx, &out)) {
          WriteNightOut(top, out.asRawBits());
          return true;
        }
      }
    }
  }
  // Megamorphic by-value lookup through the ENGINE's cache (the same call
  // the JIT's megamorphic GetElem stubs make): atom-cache-aware key
  // conversion + (shape, key) cache over the proto walk. Pure (NoGC);
  // covers the string-keyed hashtable pattern (`table[key]` reads that
  // otherwise re-atomize + walk every time). Typed arrays are excluded: a
  // canonical numeric index string/number (e.g. "-1") never consults their
  // proto chain, but the generic walk would (mirrors CacheIR's refusal).
  {
    JS::Value rv = JS::Value::fromRawBits(recv);
    if (rv.isObject() && rv.toObject().is<js::NativeObject>() &&
        !rv.toObject().is<js::TypedArrayObject>()) {
      JS::Value vp[2] = {JS::Value::fromRawBits(key), JS::UndefinedValue()};
      if (js::jit::GetNativeDataPropertyByValuePure(cx, &rv.toObject(), nullptr,
                                                    vp)) {
        // Elem-mega fill: an atom-string key resolving through a plain
        // data-slot coordinate gets a mega-get row keyed (shape,
        // atomPtr|1) -- the elem key namespace, disjoint from the
        // property rows' small-integer atomIds (gated exactly on the
        // named-id bound) -- so the site's inline by-value probe serves
        // the next read helper-free. Everything here is pure.
        JS::Value kv2 = JS::Value::fromRawBits(key);
        uint32_t idxDummy;
        if (kv2.isString() && kv2.toString()->isAtom() &&
            !kv2.toString()->asAtom().isIndex(&idxDummy)) {
          JSAtom* atom = &kv2.toString()->asAtom();
          uint32_t akey = uint32_t(reinterpret_cast<uintptr_t>(atom)) | 1u;
          uint32_t recvShape, holderPtr, holderShape, slotEnc;
          if (akey > RtNames(cx).atoms.size() &&
              js::night::NightPopulateInlineGetIC(
                  cx, &rv.toObject(), JS::PropertyKey::NonIntAtom(atom),
                  &recvShape, &holderPtr, &holderShape, &slotEnc)) {
            MegaGetEntry& e = *MegaGet(cx, recvShape, akey);
            e.atomId = akey;
            e.holderPtr = holderPtr;
            e.holderShape = holderShape;
            e.slotEnc = slotEnc;
            e.pad = 0;
            e.shape = recvShape;
          }
        }
        WriteNightOut(top, vp[1].asRawBits());
        return true;
      }
    }
  }
  // Arguments-object element read fast path (`arguments[i]` reads served
  // once mapped-arguments support exists). The pure by-value/by-id mega paths
  // both decline: the Arguments class carries a resolve hook (lazy length /
  // callee / @@iterator), so GetNativeDataProperty*Pure bails. maybeGetElement
  // is the engine's own pure accessor -- element(i) forwards mapped args to the
  // CallObject slot; the guard mirrors it (OOB or any overridden/deleted
  // element -> generic path, which handles the proto walk / undefined result).
  {
    JS::Value rv = JS::Value::fromRawBits(recv);
    JS::Value kv = JS::Value::fromRawBits(key);
    if (rv.isObject() && kv.isInt32() && kv.toInt32() >= 0 &&
        rv.toObject().is<js::ArgumentsObject>()) {
      js::ArgumentsObject* ao = &rv.toObject().as<js::ArgumentsObject>();
      uint32_t i = uint32_t(kv.toInt32());
      if (i < ao->initialLength() && !ao->hasOverriddenElement()) {
        WriteNightOut(top, ao->element(i).asRawBits());
        return true;
      }
    }
  }
  return false;
}

bool night_runtime_get_element(JSContext* cx, uint32_t top, uint64_t recv,
                               uint64_t key) {
  SetNightTop(cx, top);
  if (TryPureElementRead(cx, top, recv, key)) {
    return true;
  }
  // String-receiver element read. The inline string arm requires a LINEAR
  // string, and the generic path below reads through a rope WITHOUT ever
  // flattening it (JSString::getChar linearizes only the rope child it
  // descends into), via a fresh StringObject wrapper per access -- so a
  // rope-built string indexed in a loop takes the generic path on every
  // character forever. Flatten the receiver once (in place: the JSString
  // cell itself becomes linear) and serve the read; subsequent reads at
  // the site hit the inline arm.
  {
    JS::Value rv = JS::Value::fromRawBits(recv);
    JS::Value kv = JS::Value::fromRawBits(key);
    if (rv.isString() && kv.isInt32() && kv.toInt32() >= 0) {
      uint32_t idx = uint32_t(kv.toInt32());
      JS::RootedString str(cx, rv.toString());
      if (idx < str->length()) {
        JSLinearString* lin = str->ensureLinear(cx);
        if (!lin) {
          return false;
        }
        char16_t c = lin->latin1OrTwoByteChar(idx);
        JSString* unit = cx->staticStrings().getUnitString(cx, c);
        if (!unit) {
          return false;
        }
        WriteNightOut(top, JS::StringValue(unit).asRawBits());
        return true;
      }
    }
  }
  JS::RootedObject obj(cx, ReceiverObject(cx, recv));
  if (!obj) {
    return false;
  }
  JS::RootedValue keyv(cx, JS::Value::fromRawBits(key));
  JS::RootedId id(cx);
  if (!JS_ValueToId(cx, keyv, &id)) {
    return false;
  }
  // Forward the ORIGINAL (possibly primitive) receiver (getter `this`).
  JS::RootedValue recvv(cx, JS::Value::fromRawBits(recv));
  JS::RootedValue res(cx);
  if (!JS_ForwardGetPropertyTo(cx, obj, id, recvv, &res)) {
    return false;
  }
  WriteNightOut(top, res.get().asRawBits());
  return true;
}

// The elem key namespace's word for an element store whose rows the set
// paths may cache: an atom (non-index) key on a native receiver that is not
// the active global (whose stores blow fuses); 0 otherwise.
static uint32_t ElemAtomKey(JSContext* cx, uint64_t recv, uint64_t key) {
  JS::Value rv = JS::Value::fromRawBits(recv);
  JS::Value kv = JS::Value::fromRawBits(key);
  uint32_t idx;
  if (!rv.isObject() || !rv.toObject().is<js::NativeObject>() ||
      IsActiveGlobal(&rv.toObject()) || !kv.isString() ||
      !kv.toString()->isAtom() || kv.toString()->asAtom().isIndex(&idx)) {
    return 0;
  }
  uint32_t k =
      uint32_t(reinterpret_cast<uintptr_t>(&kv.toString()->asAtom())) | 1u;
  return k > RtNames(cx).atoms.size() ? k : 0;
}

bool night_runtime_set_element(JSContext* cx, uint32_t top, uint64_t recv,
                               uint64_t key, uint64_t val, uint32_t strict) {
  SetNightTop(cx, top);
  // Typed-array store fast path: in-bounds int32 index, numeric value. The
  // inline dense-store arm rejects typed arrays (their dense initializedLength
  // is 0), so `ta[i] = number` lands here. `SetTypedArrayElement` does the
  // per-element-type coercion internally; a numeric value never GCs or throws
  // (a BigInt array would, which is correct -- we forward the error). OOB
  // integer-indexed writes have mode-dependent semantics, so leave those to
  // the generic path.
  {
    JS::Value rv = JS::Value::fromRawBits(recv);
    JS::Value kv = JS::Value::fromRawBits(key);
    JS::Value vv = JS::Value::fromRawBits(val);
    if (rv.isObject() && kv.isInt32() && kv.toInt32() >= 0 && vv.isNumber() &&
        rv.toObject().is<js::TypedArrayObject>()) {
      JS::Rooted<js::TypedArrayObject*> ta(
          cx, &rv.toObject().as<js::TypedArrayObject>());
      mozilla::Maybe<size_t> len = ta->length();
      if (len.isSome() && uint64_t(uint32_t(kv.toInt32())) < *len) {
        JS::RootedValue v(cx, vv);
        JS::ObjectOpResult result;
        if (!js::SetTypedArrayElement(cx, ta, uint64_t(uint32_t(kv.toInt32())),
                                      v, result)) {
          return false;
        }
        return true;
      }
    }
  }
  // In-bounds overwrite of a dense element: an own, writable data property
  // (not a hole, elements not frozen), so [[Set]] is the store itself, with
  // its barriers. MIR's inline arm does this without a call; the baseline
  // tier reaches it here. Same receiver gate as the append path below.
  {
    JS::Value rv = JS::Value::fromRawBits(recv);
    JS::Value kv = JS::Value::fromRawBits(key);
    if (rv.isObject() && kv.isInt32() && kv.toInt32() >= 0 &&
        rv.toObject().is<js::NativeObject>() &&
        (rv.toObject().is<js::ArrayObject>() ||
         rv.toObject().getClass()->cOps == nullptr)) {
      js::NativeObject* nobj = &rv.toObject().as<js::NativeObject>();
      uint32_t idx = uint32_t(kv.toInt32());
      if (idx < nobj->getDenseInitializedLength() &&
          !nobj->getDenseElement(idx).isMagic(JS_ELEMENTS_HOLE) &&
          !nobj->denseElementsAreFrozen()) {
        nobj->setDenseElement(idx, JS::Value::fromRawBits(val));
        return true;
      }
    }
  }
  // Dense append/overwrite fast path: a contiguous int32-keyed store to a
  // dense receiver with no shadowing hazards (no own sparse elements, no
  // indexed protos/class hooks). Receivers: Array, or ANY native class with
  // no class hooks at all (`cOps == null` -- dense element storage then
  // carries plain-object semantics; this also admits plain-object
  // BigIntegers and fresh decode buffers that an Array-only gate would
  // send through the full generic path). The inline wasm arm already
  // handles in-bounds non-frozen overwrites, so what lands here is append
  // (idx == initializedLength) and hole overwrite; setOrExtendDenseElements
  // does the extensibility / writable-length checks, capacity growth,
  // array-length update, and barriers, refusing (Incomplete) anything
  // irregular.
  {
    JS::Value rv = JS::Value::fromRawBits(recv);
    JS::Value kv = JS::Value::fromRawBits(key);
    if (rv.isObject() && kv.isInt32() && kv.toInt32() >= 0 &&
        rv.toObject().is<js::NativeObject>() &&
        (rv.toObject().is<js::ArrayObject>() ||
         rv.toObject().getClass()->cOps == nullptr)) {
      js::NativeObject* nobj = &rv.toObject().as<js::NativeObject>();
      uint32_t idx = uint32_t(kv.toInt32());
      if (idx <= nobj->getDenseInitializedLength() &&
          NoExtraIndexedFast(cx, nobj)) {
        JS::Rooted<js::NativeObject*> robj(cx, nobj);
        JS::RootedValue v(cx, JS::Value::fromRawBits(val));
        js::DenseElementResult r =
            robj->setOrExtendDenseElements(cx, idx, v.address(), 1);
        if (r == js::DenseElementResult::Failure) {
          return false;
        }
        if (r == js::DenseElementResult::Success) {
          if (RtEnv(cx).appendCachePtr) {
            // `robj`, not `nobj`: the extend path can GC-move the receiver.
            PrimeAppendRow(cx, robj);
          }
          return true;
        }
      }
    }
  }
  // An atom key's add (`props[name] = v` on an object being filled): the
  // global add table's row for (shape, atomPtr | 1) -- the elem key
  // namespace, as the elem-mega rows -- replays the transition with no
  // lookup. Filled below from the generic set.
  uint32_t addKey = ElemAtomKey(cx, recv, key);
  if (addKey) {
    js::NativeObject* nobj =
        &JS::Value::fromRawBits(recv).toObject().as<js::NativeObject>();
    uint32_t shapeW = js::night::NightObjectShape(nobj);
    SetAddRow& trow = SetAddAt(cx, shapeW, addKey);
    uint32_t nfixed = nobj->numFixedSlots();
    if (trow.gen == InlineGen(cx) && trow.oldShape == shapeW &&
        trow.atomId == addKey && !trow.skip &&
        js::night::NightTryAddPropTransition(
            cx, recv, trow.oldShape, trow.newShape, trow.slot, trow.protoPtrs,
            trow.protoShapes, trow.numProtos, val)) {
      SeedElemAddRow(cx, trow, nfixed);
      return true;
    }
  }
  JS::RootedObject obj(cx, ReceiverObject(cx, recv));
  if (!obj) {
    return false;
  }
  JS::RootedValue keyv(cx, JS::Value::fromRawBits(key));
  JS::RootedId id(cx);
  if (!JS_ValueToId(cx, keyv, &id)) {
    return false;
  }
  // Fused globals: a computed-key write to the global may hit a fused name;
  // blow exactly that one (the key is an id already).
  if (IsActiveGlobal(obj)) {
    BlowGnameFuseKey(id);
    BlowBindingFuseKey(id);
  }
  uint32_t shapeBefore = js::night::NightObjectShape(obj);
  uint32_t spanBefore = js::night::NightObjectSlotSpanIfShared(obj);
  if (!GenericSetWithStrict(cx, obj, id, val, recv, strict)) {
    return false;
  }
  if (addKey && js::night::NightObjectShape(obj) != shapeBefore) {
    // The set added the property: cache the transition (a GC during the
    // set may have moved the old shape; the row then never hits, and the
    // major-GC generation retires it).
    uint32_t newShape, slot, protoPtrs[4], protoShapes[4], numProtos;
    bool nurseryProto = false;
    bool skip = false;
    if (js::night::NightPopulateAddTransition(
            cx, obj, id, spanBefore, &newShape, &slot, protoPtrs, protoShapes,
            &numProtos, &nurseryProto, &skip) &&
        !nurseryProto && !skip) {
      SetAddRow& trow = SetAddAt(cx, shapeBefore, addKey);
      trow.gen = InlineGen(cx);
      trow.oldShape = shapeBefore;
      trow.atomId = addKey;
      trow.newShape = newShape;
      trow.slot = slot;
      trow.skip = skip;
      trow.numProtos = numProtos;
      for (uint32_t i = 0; i < 4; i++) {
        trow.protoPtrs[i] = i < numProtos ? protoPtrs[i] : 0;
        trow.protoShapes[i] = i < numProtos ? protoShapes[i] : 0;
      }
      if (obj->is<js::NativeObject>()) {
        SeedElemAddRow(cx, trow, obj->as<js::NativeObject>().numFixedSlots());
      }
    }
    return true;
  }
  // Elem-mega fill, the write-side twin of the get_element fill: an
  // atom-string key whose store landed on a writable plain data slot gets a
  // mega-set row keyed (shape, atomPtr|1), so the site's inline by-value
  // probe serves the next store helper-free (barriered slot overwrite off
  // the row). Pointers are re-derived from the rooted handles: the generic
  // set can GC. IsActiveGlobal receivers are excluded -- an inline slot
  // store would bypass the gname fuse blows above.
  if (id.isAtom() && obj->is<js::NativeObject>() && !IsActiveGlobal(obj)) {
    JSAtom* atom = id.toAtom();
    uint32_t akey = uint32_t(reinterpret_cast<uintptr_t>(atom)) | 1u;
    uint32_t recvShape, slotEnc, absSlot, reason;
    if (akey > RtNames(cx).atoms.size() &&
        js::night::NightPopulateInlineSetIC(cx, obj, id, &recvShape, &slotEnc,
                                            &absSlot, &reason)) {
      MegaSetEntry& e = *MegaSet(cx, recvShape, akey);
      e.atomId = akey;
      e.slotEnc = slotEnc;
      e.absSlot = absSlot;
      e.shape = recvShape;
    }
  }
  return true;
}

// Map an INIT_ATTR_* kind (translate.rs) to the property attributes the
// interpreter's GetInitDataPropAttrs assigns for the corresponding Init* op.
static unsigned InitAttrFlags(uint32_t kind) {
  switch (kind) {
    case 0:  // InitProp / InitElem
      return JSPROP_ENUMERATE;
    case 1:  // InitHiddenProp / InitHiddenElem (non-enumerable)
      return 0;
    case 2:  // InitLockedProp (non-enumerable, non-writable, non-configurable)
      return JSPROP_PERMANENT | JSPROP_READONLY;
    default:
      MOZ_CRASH("night-rt init: bad attr kind");
  }
}

// Object literal: a fresh empty `{}`. The translator's following init_prop/
// init_elem calls define its properties in source order. Fills the site's
// inline-alloc cell so subsequent allocations bump inline.
bool night_runtime_new_object(JSContext* cx, uint32_t top, uint32_t cell,
                              uint32_t nslots) {
  SetNightTop(cx, top);
  // NewObjectGCKind (the interpreter's NewInit kind): fixed slots available
  // for the literal's properties, so the init adds are raw fixed-slot stores
  // (JS_NewPlainObject would pick a 0-fixed-slot kind -> every add grows
  // dynamic slots and the inline init arm can never fire). A literal whose
  // layout row is longer (`nslots`, the compiler's) gets a kind with a
  // fixed slot for each field: a predicted field in a dynamic slot clears
  // SLOTS, on every allocation.
  js::gc::AllocKind kind = js::NewObjectGCKind();
  if (nslots > js::gc::GetGCKindSlots(kind)) {
    kind = js::gc::GetGCObjectKind(std::min<size_t>(nslots, js::NativeObject::MAX_FIXED_SLOTS));
  }
  JSObject* obj = js::NewPlainObjectWithAllocKind(cx, kind);
  if (!obj) {
    return false;
  }
  if (cell && RtState(cx).nurseryInlineOK) {
    js::night::NightFillAllocCellObject(LinMem<js::night::NightAllocCell>(cell),
                                        obj);
  }
  WriteNightOut(top, JS::ObjectValue(*obj).asRawBits());
  return true;
}

// Array literal: a fresh array of `length` (holes); init_elem fills it.
bool night_runtime_new_array(JSContext* cx, uint32_t top, uint32_t length,
                             uint32_t cell) {
  SetNightTop(cx, top);
  JS::RootedObject arr(cx, JS::NewArrayObject(cx, length));
  if (!arr) {
    return false;
  }
  if (cell && RtState(cx).nurseryInlineOK) {
    js::night::NightFillAllocCellArray(
        LinMem<js::night::NightArrayAllocCell>(cell), arr, length);
  }
  WriteNightOut(top, JS::ObjectValue(*arr).asRawBits());
  return true;
}

// Define an own named data property on a literal under construction
// (`InitProp`/`InitHiddenProp`/`InitLockedProp`; matches DefineDataProperty).
// `cacheIdx` (`UINT32_MAX` = none) is the site's prop-IC slot: plain inits
// replay inline off its add-transition row; this helper populates it.
bool night_runtime_init_prop(JSContext* cx, uint32_t top, uint64_t obj,
                             uint32_t atomId, uint64_t val, uint32_t attrs,
                             uint32_t cacheIdx) {
  SetNightTop(cx, top);
  JS::HandleId id = AtomIdChecked(cx, atomId);
  JS::RootedValue objv(cx, JS::Value::fromRawBits(obj));
  if (!objv.isObject()) {
    JS_ReportErrorASCII(cx,
                        "night_runtime_init_prop: receiver is not an object");
    return false;
  }
  // Plain-attr fast arm: replay a cached (oldShape, atom) -> newShape add
  // without the define machinery. Populated below from the generic path.
  if (attrs == 0) {
    uint32_t shapeW = js::night::NightObjectShape(&objv.toObject());
    InitAddRow& row = InitAddAt(cx, shapeW, atomId);
    if (row.oldShape == shapeW && row.atomId == atomId &&
        row.gen == InlineGen(cx) &&
        js::night::NightTryInitAddTransition(cx, obj, shapeW, row.newShape,
                                             row.slot, val)) {
      // Seed the SITE row too so subsequent inits replay inline (the early
      // return would otherwise starve it forever).
      if (cacheIdx != UINT32_MAX && !row.skip) {
        uint32_t* srow = InlineTransRow(cx, cacheIdx);
        uint32_t nfixed =
            objv.toObject().as<js::NativeObject>().numFixedSlots();
        FillTransRow(srow, shapeW, row.newShape, row.slot, nfixed, nullptr,
                     nullptr, 0);
      }
      return true;
    }
  }
  JS::RootedObject o(cx, &objv.toObject());
  JS::RootedValue v(cx, JS::Value::fromRawBits(val));
  uint32_t shapeBefore = js::night::NightObjectShape(o);
  uint32_t spanBefore = js::night::NightObjectSlotSpanIfShared(o);
  if (!JS_DefinePropertyById(cx, o, id, v, InitAttrFlags(attrs))) {
    return false;
  }
  if (attrs == 0 && js::night::NightObjectShape(o) != shapeBefore) {
    InitAddRow row;
    uint32_t protoPtrs[4], protoShapes[4], numProtos;
    bool nurseryProto = false;
    if (js::night::NightPopulateAddTransition(
            cx, o, id, spanBefore, &row.newShape, &row.slot, protoPtrs,
            protoShapes, &numProtos, &nurseryProto, &row.skip)) {
      row.gen = InlineGen(cx);
      row.oldShape = shapeBefore;
      row.atomId = atomId;
      InitAddAt(cx, shapeBefore, atomId) = row;
      // Site row for the inline replay arm (defines never consult the proto
      // chain, so the proto-guard pairs stay zero == always-pass); not for a
      // transition that skips slots, which the inline arm cannot replay.
      if (cacheIdx != UINT32_MAX && !row.skip) {
        uint32_t* srow = InlineTransRow(cx, cacheIdx);
        uint32_t nfixed = o->as<js::NativeObject>().numFixedSlots();
        FillTransRow(srow, shapeBefore, row.newShape, row.slot, nfixed, nullptr,
                     nullptr, 0);
      }
    }
  }
  return true;
}

// Define an own indexed data property on a literal under construction
// (`InitElem`/`InitElemArray`/`InitElemInc`; ToPropertyKey then DefineData).
bool night_runtime_init_elem(JSContext* cx, uint32_t top, uint64_t obj,
                             uint64_t key, uint64_t val, uint32_t attrs) {
  SetNightTop(cx, top);
  JS::RootedValue objv(cx, JS::Value::fromRawBits(obj));
  if (!objv.isObject()) {
    JS_ReportErrorASCII(cx,
                        "night_runtime_init_elem: receiver is not an object");
    return false;
  }
  // Dense fast arm (the InitElemArray/InitElemInc shape: int key appended to
  // a preallocated array literal): mirror InitElemArrayOperation. The
  // capacity/initlen/length guards route anything unusual (holes handled,
  // sparse/overflow/frozen not) to the generic define. An array with sparse
  // indexed properties may already own this index as a shape property (a
  // species-constructed array with a non-writable element, redefined by
  // `DefineDataProperty`): appending a dense element beside it would leave
  // two properties, so that shape takes the generic define too.
  {
    JS::Value keyRaw = JS::Value::fromRawBits(key);
    JS::Value valRaw = JS::Value::fromRawBits(val);
    JSObject* ro = &objv.toObject();
    if (attrs == 0 && keyRaw.isInt32() && ro->is<js::ArrayObject>()) {
      js::ArrayObject* arr = &ro->as<js::ArrayObject>();
      int32_t i = keyRaw.toInt32();
      if (i >= 0 && uint32_t(i) < arr->getDenseCapacity() &&
          uint32_t(i) == arr->getDenseInitializedLength() &&
          uint32_t(i) < arr->length() && arr->isExtensible() &&
          !arr->isIndexed() && !arr->denseElementsAreFrozen()) {
        arr->setDenseInitializedLength(uint32_t(i) + 1);
        if (valRaw.isMagic(JS_ELEMENTS_HOLE)) {
          arr->initDenseElementHole(uint32_t(i));
        } else {
          arr->initDenseElement(uint32_t(i), valRaw);
        }
        return true;
      }
    }
  }
  JS::RootedObject o(cx, &objv.toObject());
  JS::RootedValue keyv(cx, JS::Value::fromRawBits(key));
  JS::RootedValue v(cx, JS::Value::fromRawBits(val));
  JS::RootedId id(cx);
  if (!JS_ValueToId(cx, keyv, &id)) {
    return false;
  }
  return JS_DefinePropertyById(cx, o, id, v, InitAttrFlags(attrs));
}

// Generic binary arithmetic/bitop. `kind` matches the BINOP_* constants in
// js/src/night/compiler/src/wasm/translate.rs.
bool night_runtime_binop(JSContext* cx, uint32_t top, uint32_t kind, uint64_t a,
                         uint64_t b) {
  SetNightTop(cx, top);
  // Unary kinds (`b` is a dummy): BigInt-aware Inc/Dec.
  if (kind == 10 || kind == 11) {
    uint64_t r;
    if (!(kind == 10 ? js::night::NightInc(cx, a, &r)
                     : js::night::NightDec(cx, a, &r))) {
      return false;
    }
    WriteNightOut(top, r);
    return true;
  }
  JS::RootedValue lhs(cx, JS::Value::fromRawBits(a));
  JS::RootedValue rhs(cx, JS::Value::fromRawBits(b));
  JS::RootedValue res(cx);
  bool ok;
  switch (kind) {
    case 0:
      ok = js::SubValues(cx, &lhs, &rhs, &res);
      break;
    case 1:
      ok = js::MulValues(cx, &lhs, &rhs, &res);
      break;
    case 2:
      ok = js::DivValues(cx, &lhs, &rhs, &res);
      break;
    case 3:
      ok = js::ModValues(cx, &lhs, &rhs, &res);
      break;
    case 4:
      ok = js::BitOr(cx, &lhs, &rhs, &res);
      break;
    case 5:
      ok = js::BitAnd(cx, &lhs, &rhs, &res);
      break;
    case 6:
      ok = js::BitXor(cx, &lhs, &rhs, &res);
      break;
    case 7:
      ok = js::BitLsh(cx, &lhs, &rhs, &res);
      break;
    case 8:
      ok = js::BitRsh(cx, &lhs, &rhs, &res);
      break;
    case 9:
      ok = js::UrshValues(cx, &lhs, &rhs, &res);
      break;
    case 12:
      // Unary `~a` (`rhs` is a dummy): BigInt-aware BitNot.
      ok = js::BitNot(cx, &lhs, &res);
      break;
    default:
      MOZ_CRASH("night_runtime_binop: bad kind");
  }
  if (!ok) {
    return false;
  }
  WriteNightOut(top, res.get().asRawBits());
  return true;
}

// Generic comparison -> boolean. `kind` matches the CMP_* constants in
// translate.rs.
bool night_runtime_compare(JSContext* cx, uint32_t top, uint32_t kind,
                           uint64_t a, uint64_t b) {
  SetNightTop(cx, top);
  // String equality fast head (kinds 4-7; loose == on two strings is strict
  // ==): length mismatch rejects WITHOUT flattening (ropes carry length);
  // same pointer accepts; two distinct atoms reject (atoms are deduped);
  // both-linear compares chars in place. Only equal-length rope operands
  // fall through to the generic path's flatten.
  if (kind >= 4) {
    JS::Value av = JS::Value::fromRawBits(a);
    JS::Value bv = JS::Value::fromRawBits(b);
    if (av.isString() && bv.isString()) {
      JSString* sa = av.toString();
      JSString* sb = bv.toString();
      bool eq;
      bool known = true;
      if (sa == sb) {
        eq = true;
      } else if (sa->length() != sb->length()) {
        eq = false;
      } else if (sa->isAtom() && sb->isAtom()) {
        eq = false;
      } else if (sa->isLinear() && sb->isLinear()) {
        eq = js::EqualStrings(&sa->asLinear(), &sb->asLinear());
      } else {
        known = false;
      }
      if (known) {
        bool r = (kind == 4 || kind == 6) ? eq : !eq;
        WriteNightOut(top, JS::BooleanValue(r).asRawBits());
        return true;
      }
    }
  }
  JS::RootedValue lhs(cx, JS::Value::fromRawBits(a));
  JS::RootedValue rhs(cx, JS::Value::fromRawBits(b));
  bool result;
  bool ok;
  switch (kind) {
    case 0:
      ok = js::LessThan(cx, &lhs, &rhs, &result);
      break;
    case 1:
      ok = js::LessThanOrEqual(cx, &lhs, &rhs, &result);
      break;
    case 2:
      ok = js::GreaterThan(cx, &lhs, &rhs, &result);
      break;
    case 3:
      ok = js::GreaterThanOrEqual(cx, &lhs, &rhs, &result);
      break;
    case 4:
      ok = js::LooselyEqual(cx, lhs, rhs, &result);
      break;
    case 5:
      ok = js::LooselyEqual(cx, lhs, rhs, &result);
      result = !result;
      break;
    case 6:
      ok = js::StrictlyEqual(cx, lhs, rhs, &result);
      break;
    case 7:
      ok = js::StrictlyEqual(cx, lhs, rhs, &result);
      result = !result;
      break;
    default:
      MOZ_CRASH("night_runtime_compare: bad kind");
  }
  if (!ok) {
    return false;
  }
  WriteNightOut(top, JS::BooleanValue(result).asRawBits());
  return true;
}

// String constant: materialize the atom-table name as a JS string.
bool night_runtime_string(JSContext* cx, uint32_t top, uint32_t atomId) {
  SetNightTop(cx, top);
  if (atomId >= RtNames(cx).atoms.size()) {
    MOZ_CRASH("night_runtime_string: atomId out of range");
  }
  // NB: return a fresh copy rather than the pre-interned atom -- fresh short
  // literals are cheap nursery inline strings with better locality than a
  // tenured-atom pointer chase in a GC/latency-bound loop.
  JSString* str;
  if (RtNames(cx).latin1Ok[atomId]) {
    const std::string& l = RtNames(cx).latin1[atomId];
    str = js::NewStringCopyN<js::CanGC>(
        cx, reinterpret_cast<const JS::Latin1Char*>(l.data()), l.size());
  } else {
    const std::u16string& s = RtNames(cx).atoms[atomId];
    str = JS_NewUCStringCopyN(cx, s.data(), s.size());
  }
  if (!str) {
    return false;
  }
  WriteNightOut(top, JS::StringValue(str).asRawBits());
  return true;
}

// Leaf char-equality for the inline string-compare arm's residual: both
// operands proven LINEAR same-length strings by the wasm guards; EqualChars
// handles Latin1/two-byte mixes. Pure -- no GC, no throw, no rooting.
int32_t night_runtime_str_chars_eq(uint32_t a, uint32_t b) {
  JSLinearString* as = LinMem<JSLinearString>(a);
  JSLinearString* bs = LinMem<JSLinearString>(b);
  return js::EqualChars(as, bs) ? 1 : 0;
}

// --- track census ---------------------------------------------------------
//
// Per-site dynamic counters for the Opt-track work: which arm of a fork
// actually runs, and how many version entries execute on each track. Static
// censuses can say how much code is on a track; only this can say how much
// *execution* is. Deliberately unconditional and unsynchronised -- the
// compiler emits the calls only under `--census`, so a production module
// contains none of them, and the shell is single-threaded.
//
// A call per counted event is heavy. That is acceptable and even wanted: the
// output is a set of ratios at a single site, and a uniform per-event cost
// leaves those ratios intact.
namespace {


// Downstream attribution: a stack of departure-site cell pairs, bracketed
// by FRAME_PUSH/POP ticks (kinds 60/61) around may-run-user-code calls.
// Each frame carries two owners: `recent` (set by every departure tick,
// base kind 150-155 with any track bump) and `root` (set only by a bump-0
// tick, i.e. a departure taken FROM the Opt track -- the transition that
// started the current Dirty stretch; departures already on Dirty do not
// move it). A version-entry tick then bumps SYNTHESIZED records: kind 5/6 =
// Dirty/Side entries per most-recent departure (the marginal question:
// what does recovering this one departure flip), kind 7/8 = per ROOT
// departure (the causal question: which fall-off-the-happy-path event owns
// this stretch). The bracket keeps a callee's internal departures from
// leaking into the caller's attribution; an unpaired pop (e.g. a generator
// resume that skipped its push) is ignored, and the bottom cells start as
// the no-owner sentinel.
// Each frame also carries the stamp epoch (vm/JSObject.h) sampled at its
// bracket's PUSH: the POP compares, and the departure tick that follows is
// classified stamps-intact (kind 11) or stamps-broken (kind 12) -- "the
// callee wrote heap, but no stamp-guarded fact was invalidated" is exactly
// the population a keep-facts fork arm could recover. Root cells remember
// their owning departure's intactness so kind 13 = downstream Dirty entries
// under a stamps-intact root (kind 14 for Side). Kind 65 arrives from the
// compiled inline demote arms (census builds only) and advances the epoch.
struct NightDepartCells {
  uint32_t recent;
  uint32_t root;
  bool rootIntact;
  uint64_t epochAtPush;
};
}  // namespace

// The census's counts and attribution state (all null/off in a module
// compiled without census calls).
struct NightCensusState {
  std::map<uint64_t, uint64_t>* counts = nullptr;
  std::vector<NightDepartCells>* depart = nullptr;
  // Kind 70 (the per-block execution census, MIR's `block_census`) ticks
  // once per executed lowered block -- several per bytecode op -- so it
  // keeps a flat per-id counter instead of paying the map on every tick.
  std::vector<uint64_t>* block = nullptr;
  bool lastCallIntact = false;
  // `NIGHT_CENSUS_TRACE=N`: also print the first N MIR exits (kind 90),
  // guard failures (92) and epoch bumps (kind 66) in the order they happen,
  // with the epoch: the counts say what is hot, the order says what started
  // it.
  int64_t trace = -1;
};
static NightCensusState& RtCensus(JSContext* cx);

namespace {
constexpr uint32_t kNightNoDepart = 0xffffffffu;
constexpr size_t kNightDepartMaxDepth = 1u << 16;

void NightCensusDump() {
  JSContext* cx = CurrentNightContext();
  if (!RtCensus(cx).counts) {
    return;
  }
  fprintf(stderr, "night: census sites %zu\n", RtCensus(cx).counts->size());
  for (const auto& entry : *RtCensus(cx).counts) {
    fprintf(stderr, "night: census kind %u id %u n %llu\n",
            unsigned(entry.first >> 32), unsigned(entry.first & 0xffffffffu),
            static_cast<unsigned long long>(entry.second));
  }
  if (RtCensus(cx).block) {
    for (size_t i = 0; i < RtCensus(cx).block->size(); i++) {
      if ((*RtCensus(cx).block)[i]) {
        fprintf(stderr, "night: census kind 70 id %zu n %llu\n", i,
                static_cast<unsigned long long>((*RtCensus(cx).block)[i]));
      }
    }
  }
}

}  // namespace


static js::night::NightRuntimeData& RtRegex(JSContext* cx);

extern "C++" {
js::night::NightRuntimeData& js::night::NightData(JSContext* cx) {
  return RtRegex(cx);
}
}

// Re-read after wizer resume (`JS::NightActivate`): the program's top level
// runs while wizening, so a setting latched then would be the snapshot's.
#ifdef __wasi__
void __wasilibc_deinitialize_environ(void);
void __wasilibc_initialize_environ(void);
#endif
void NightCensusTraceRearm() {
  JSContext* cx = CurrentNightContext();
#ifdef __wasi__
  // The environment wasi-libc read while wizening is the snapshot's.
  __wasilibc_deinitialize_environ();
  __wasilibc_initialize_environ();
#endif
  const char* e = getenv("NIGHT_CENSUS_TRACE");
  RtCensus(cx).trace = e ? atoll(e) : 0;
}
static void NightCensusTrace(uint32_t kind, uint64_t id);
// The trace line of a set-helper store to a published object with TYPES:
// the property, the word, and whether the compiled caller vouched.
static void NightCensusTraceSet(uint32_t atomId, uint32_t word,
                                uint32_t flags) {
  JSContext* cx = CurrentNightContext();
  if (RtCensus(cx).trace > 0 && (word & js::night::kWordTypes) &&
      (!(word & js::night::kWordConstructing) || !(flags & 2))) {
    fprintf(stderr, "night: trace set %s word %x flags %u\n",
            std::string(RtNames(cx).atoms[atomId].begin(),
                        RtNames(cx).atoms[atomId].end())
                .c_str(),
            word, flags);
  }
}
// The trace line of a layout guard's failing object: its word, and each
// own property with its value's type.
static void NightCensusTraceObject(JSObject* obj) {
  fprintf(stderr, "night: trace object word %x", obj->externalWord());
  if (obj->is<js::NativeObject>()) {
    js::NativeObject& n = obj->as<js::NativeObject>();
    for (js::ShapePropertyIter<js::NoGC> it(n.shape()); !it.done(); it++) {
      JS::Value v = it->isDataProperty() ? n.getSlot(it->slot())
                                         : JS::UndefinedValue();
      const char* t = v.isInt32()      ? "int32"
                      : v.isDouble()   ? "double"
                      : v.isString()   ? "string"
                      : v.isObject()   ? "object"
                      : v.isUndefined() ? "undefined"
                      : v.isNull()     ? "null"
                      : v.isBoolean()  ? "bool"
                                       : "other";
      if (it->key().isAtom()) {
        JSAtom* a = it->key().toAtom();
        char buf[32] = {0};
        for (size_t i = 0; i < a->length() && i < 31; i++) {
          buf[i] = char(a->latin1OrTwoByteChar(i));
        }
        fprintf(stderr, " %s:%s@%u", buf, t, it->slot());
      }
    }
  }
  fprintf(stderr, "\n");
}
// The trace line of a stamp or restamp that leaves TYPES off although the
// layout claims it (`keepBits`): the object lost it before.
void NightCensusTraceStamp(const char* what, uint32_t layoutId,
                           uint32_t oldWord, uint32_t keepBits) {
  JSContext* cx = CurrentNightContext();
  if (RtCensus(cx).trace > 0 && (keepBits & js::night::kWordTypes) &&
      !(oldWord & js::night::kWordTypes)) {
    fprintf(stderr, "night: trace %s-notypes layout %u word %x\n", what,
            layoutId, oldWord);
  }
}
// The trace line of an engine demotion of an object under construction
// (no epoch bump, so the ordered trace would not show it otherwise).
void NightCensusTraceConstructing(uint32_t oldWord, uint32_t newWord,
                                  uint32_t site) {
  JSContext* cx = CurrentNightContext();
  if (RtCensus(cx).trace > 0 && (oldWord & js::night::kWordConstructing) &&
      (oldWord & js::night::kWordTypes) && !(newWord & js::night::kWordTypes)) {
    fprintf(stderr, "night: trace ctor-demote site %u word %x -> %x\n", site,
            oldWord, newWord);
  }
}
static void NightCensusTrace(uint32_t kind, uint64_t id) {
  JSContext* cx = CurrentNightContext();
  if (RtCensus(cx).trace < 0) {
    const char* e = getenv("NIGHT_CENSUS_TRACE");
    RtCensus(cx).trace = e ? atoll(e) : 0;
  }
  if (RtCensus(cx).trace > 0) {
    RtCensus(cx).trace--;
    fprintf(stderr, "night: trace kind %u id %llu epoch %llu\n", kind,
            (unsigned long long)id,
            (unsigned long long)RtState(cx).stampEpoch);
  }
}

int32_t night_runtime_census(uint32_t kind, uint32_t id) {
  JSContext* cx = CurrentNightContext();
  if (kind == 90 || kind == 92) {
    NightCensusTrace(kind, id);
  }
  if (kind == 96) {
    // A layout guard's failing object (`id` its address): printed while
    // tracing, never counted.
    if (RtCensus(cx).trace > 0) {
      NightCensusTraceObject(LinMem<JSObject>(id));
    }
    return 0;
  }
  if (!RtCensus(cx).counts) {
    RtCensus(cx).counts = new std::map<uint64_t, uint64_t>();
    RtCensus(cx).depart = new std::vector<NightDepartCells>{
        {kNightNoDepart, kNightNoDepart, false, RtState(cx).stampEpoch}};
    atexit(NightCensusDump);
  }
  if (kind == 70) {
    if (!RtCensus(cx).block) {
      RtCensus(cx).block = new std::vector<uint64_t>();
    }
    if (id >= RtCensus(cx).block->size()) {
      RtCensus(cx).block->resize(size_t(id) + 1024, 0);
    }
    (*RtCensus(cx).block)[id] += 1;
    return 0;
  }
  uint32_t base = kind < 200 ? kind : (kind < 400 ? kind - 200 : kind - 400);
  if (kind == 60) {
    if (RtCensus(cx).depart->size() < kNightDepartMaxDepth) {
      NightDepartCells c = RtCensus(cx).depart->back();
      c.epochAtPush = RtState(cx).stampEpoch;
      RtCensus(cx).depart->push_back(c);
    }
  } else if (kind == 61) {
    if (RtCensus(cx).depart->size() > 1) {
      RtCensus(cx).lastCallIntact =
          RtCensus(cx).depart->back().epochAtPush == RtState(cx).stampEpoch;
      RtCensus(cx).depart->pop_back();
    }
  } else if (kind == 65) {
    // Inline demote arm marker (counting only): the compiled arms bump the
    // epoch themselves in production now.
  } else if (base >= 150 && base <= 158) {
    RtCensus(cx).depart->back().recent = id;
    (*RtCensus(cx).counts)[((RtCensus(cx).lastCallIntact ? 11ull : 12ull) << 32) | id] += 1;
    if (kind < 200) {
      RtCensus(cx).depart->back().root = id;
      RtCensus(cx).depart->back().rootIntact = RtCensus(cx).lastCallIntact;
    }
  } else if (kind == 3) {
    (*RtCensus(cx).counts)[(5ull << 32) | RtCensus(cx).depart->back().recent] += 1;
    (*RtCensus(cx).counts)[(7ull << 32) | RtCensus(cx).depart->back().root] += 1;
    if (RtCensus(cx).depart->back().rootIntact) {
      (*RtCensus(cx).counts)[(13ull << 32) | RtCensus(cx).depart->back().root] += 1;
    }
  } else if (kind == 2) {
    (*RtCensus(cx).counts)[(6ull << 32) | RtCensus(cx).depart->back().recent] += 1;
    (*RtCensus(cx).counts)[(8ull << 32) | RtCensus(cx).depart->back().root] += 1;
    if (RtCensus(cx).depart->back().rootIntact) {
      (*RtCensus(cx).counts)[(14ull << 32) | RtCensus(cx).depart->back().root] += 1;
    }
  }
  (*RtCensus(cx).counts)[(static_cast<uint64_t>(kind) << 32) | id] += 1;
  return 0;
}

// The C++ half of the bump-site census (JSObject.h chokes call this on
// every ACTUAL epoch bump): kind 66, id = (engine site << 16) | the
// demoted word's class idx. Only records while a census module is running
// (RtCensus(cx).counts exists); the compiled inline demote arms are the other
// bump source and carry their own kind (65).
extern "C++" {
namespace js {
void NightBumpStampEpoch(uint32_t site, uint32_t oldWord) {
  JSContext* cx = CurrentNightContext();
  RtState(cx).stampEpoch++;
  NightNoteEpochBump(site, oldWord);
}

void NightNoteEpochBump(uint32_t site, uint32_t oldWord) {
  JSContext* cx = CurrentNightContext();
  if (!RtCensus(cx).counts) {
    return;
  }
  uint64_t id = (static_cast<uint64_t>(site) << 16) | (oldWord & 0xFFFFu);
  NightCensusTrace(66, id);
  (*RtCensus(cx).counts)[(66ull << 32) | id] += 1;
}
}  // namespace js
}  // extern "C++"

// Self-hosted intrinsic value by name (JSOp::GetIntrinsic). Mirrors the
// interpreter's GetIntrinsicOperation; the lookup may lazily clone the
// intrinsic from the self-hosting zone (GC/throw -> full handshake).
bool night_runtime_get_intrinsic(JSContext* cx, uint32_t top, uint32_t atomId) {
  SetNightTop(cx, top);
  if (!RtNames(cx).ids || atomId >= RtNames(cx).ids->size()) {
    MOZ_CRASH("night_runtime_get_intrinsic: atomId out of range");
  }
  JS::Rooted<js::PropertyName*> name(
      cx, (*RtNames(cx).ids)[atomId].get().toAtom()->asPropertyName());
  JS::RootedValue v(cx);
  if (!js::GlobalObject::getIntrinsicValue(cx, cx->global(), name, &v)) {
    return false;
  }
  WriteNightOut(top, v.get().asRawBits());
  return true;
}

// Miss arm of the inline intrinsic value-cell read: resolve by name, then arm
// the cell so subsequent reads are one i64 load. Intrinsics are set-once
// (the holder caches the lazily-cloned value), so an armed cell is valid
// until a major GC zeroes the region (compaction can move the cached
// object). Cache tenured values only: a nursery-fresh clone re-resolves
// until it tenures, so a minor GC can never leave a stale pointer. Raw bits
// 0 (double +0.0) stays uncached and simply re-resolves each read.
bool night_runtime_get_intrinsic_cell(JSContext* cx, uint32_t top,
                                      uint32_t atomId, uint32_t cellAddr) {
  SetNightTop(cx, top);
  if (!RtNames(cx).ids || atomId >= RtNames(cx).ids->size()) {
    MOZ_CRASH("night_runtime_get_intrinsic_cell: atomId out of range");
  }
  JS::Rooted<js::PropertyName*> name(
      cx, (*RtNames(cx).ids)[atomId].get().toAtom()->asPropertyName());
  JS::RootedValue v(cx);
  if (!js::GlobalObject::getIntrinsicValue(cx, cx->global(), name, &v)) {
    return false;
  }
  WriteNightOut(top, v.get().asRawBits());
  bool cacheable = v.isGCThing()
                       ? !js::gc::IsInsideNursery(
                             static_cast<js::gc::Cell*>(v.get().toGCThing()))
                       : v.get().asRawBits() != 0;
  if (cacheable) {
    *LinMem<uint64_t>(cellAddr) = v.get().asRawBits();
  }
  return true;
}

// `ToNumeric` coercion (number or BigInt; may call valueOf -> GC/throw).
bool night_runtime_tonumeric(JSContext* cx, uint32_t top, uint64_t a) {
  SetNightTop(cx, top);
  JS::RootedValue v(cx, JS::Value::fromRawBits(a));
  if (!js::ToNumeric(cx, &v)) {
    return false;
  }
  WriteNightOut(top, v.get().asRawBits());
  return true;
}

// `Pos` slow path: ToNumber (throws on BigInt, unlike ToNumeric).
bool night_runtime_pos(JSContext* cx, uint32_t top, uint64_t a) {
  SetNightTop(cx, top);
  JS::RootedValue v(cx, JS::Value::fromRawBits(a));
  double d;
  if (!JS::ToNumber(cx, v, &d)) {
    return false;
  }
  v.setNumber(d);
  WriteNightOut(top, v.get().asRawBits());
  return true;
}

// `Neg` slow path: NegOperation (ToNumeric + negate), via the engine wrapper.
bool night_runtime_neg(JSContext* cx, uint32_t top, uint64_t a) {
  SetNightTop(cx, top);
  return js::night::NightNeg(cx, a, LinMem<uint64_t>(top));
}

// `l instanceof r`: mirrors the interpreter's CASE(Instanceof).
bool night_runtime_instanceof(JSContext* cx, uint32_t top, uint64_t l,
                              uint64_t r, uint32_t cellAddr) {
  SetNightTop(cx, top);
  // Fast path (the dominant band): rhs is a plain function whose
  // @@hasInstance is the immutable default on Function.prototype. Then
  // `l instanceof r` is exactly OrdinaryHasInstance, so skip
  // InstanceofOperator's @@hasInstance GetProperty and the
  // Call(fun_symbolHasInstance) trampoline it drives. The default is proven by
  // LookupPropertyPure resolving @@hasInstance to a native property held by
  // Function.prototype: that property is an immutable (non-writable,
  // non-configurable) data property, so its value is guaranteed to be the
  // original hook -- no value guard needed. A shadowing own/proto @@hasInstance
  // makes the holder something other than Function.prototype -> slow path.
  {
    JS::Value rv = JS::Value::fromRawBits(r);
    if (rv.isObject() && rv.toObject().is<JSFunction>()) {
      JSFunction* fun = &rv.toObject().as<JSFunction>();
      uint32_t shapeBits = uint32_t(reinterpret_cast<uintptr_t>(fun->shape()));
      uint32_t gen = RtEnv(cx).propicGenPtr ? InlineGen(cx) : 0;
      uint32_t* e =
          &RtHasInst(cx)[2 * ((shapeBits >> 3) & (kHasInstCacheN - 1))];
      bool isDefault = (e[0] == shapeBits && e[1] == gen);
      if (!isDefault) {
        // Cache miss: verify the default. The cached fact is keyed on the
        // function shape, which encodes both the own properties (no own
        // @@hasInstance) and the direct proto -- so caching is sound only when
        // Function.prototype is the DIRECT proto (holder, immutable
        // @@hasInstance); an intermediate holder could gain a shadowing
        // @@hasInstance without changing fun's shape, so we don't cache those.
        JSObject* funProto = &cx->global()->getPrototype(JSProto_Function);
        JS::PropertyKey hid =
            JS::PropertyKey::Symbol(cx->wellKnownSymbols().hasInstance);
        js::NativeObject* holder = nullptr;
        js::PropertyResult prop;
        if (fun->staticPrototype() == funProto &&
            js::LookupPropertyPure(cx, fun, hid, &holder, &prop) &&
            prop.isNativeProperty() && holder == funProto) {
          e[0] = shapeBits;
          e[1] = gen;
          isDefault = true;
        }
      }
      if (isDefault) {
        JS::RootedObject obj(cx, fun);
        JS::RootedValue lval(cx, JS::Value::fromRawBits(l));
        bool cond = false;
        if (!JS::OrdinaryHasInstance(cx, obj, lval, &cond)) {
          return false;
        }
        // OrdinaryHasInstance can allocate (it materializes the lazy
        // `.prototype` as an own data slot, which also changes the
        // function's shape) and so can move `fun`; every use below must go
        // through the rooted handle, and the cell must be armed with the
        // live post-materialization shape, not the entry-time one.
        fun = &obj->as<JSFunction>();
        // Populate the per-site inline cell [funShape, gen, protoSlotEnc] so
        // subsequent instanceofs at this site skip the reactor entirely.
        // holderPtr==0 (own) is required -- the inline hit reads the slot
        // off the LIVE receiver, and same-shape guarantees the same own slot.
        if (cellAddr) {
          uint32_t recvShape, holderPtr, holderShape, slotEnc;
          JS::PropertyKey protoKey = js::NameToId(cx->names().prototype);
          if (js::night::NightPopulateInlineGetIC(cx, fun, protoKey, &recvShape,
                                                  &holderPtr, &holderShape,
                                                  &slotEnc) &&
              holderPtr == 0) {
            uint32_t* cell = LinMem<uint32_t>(cellAddr);
            cell[2] = slotEnc;
            cell[1] = gen;
            cell[0] = recvShape;  // validity marker written last
          }
        }
        WriteNightOut(top, JS::BooleanValue(cond).asRawBits());
        return true;
      }
    }
  }
  return js::night::NightInstanceof(cx, l, r, LinMem<uint64_t>(top));
}

// `delete val.name`: DelPropOperation<strict> via the engine wrapper.
bool night_runtime_del_prop(JSContext* cx, uint32_t top, uint64_t val,
                            uint32_t atomId, uint32_t strict) {
  SetNightTop(cx, top);
  JS::HandleId id = AtomIdChecked(cx, atomId);
  // Fused globals: deleting a fused global unbinds it; blow its fuses.
  if (JS::Value::fromRawBits(val).isObject() &&
      IsActiveGlobal(&JS::Value::fromRawBits(val).toObject())) {
    BlowGnameFuse(atomId);
    BlowBindingFuseAtom(atomId);
  }
  return js::night::NightDelProp(cx, val, id, strict != 0,
                                 LinMem<uint64_t>(top));
}

// `JSOp::MutateProto`: object-literal `{ __proto__: expr }`. Stack was
// [obj, proto]; the caller keeps obj. Set obj's prototype when `proto` is
// object-or-null (matching the interpreter), else leave it untouched.
bool night_runtime_mutate_proto(JSContext* cx, uint32_t top, uint64_t obj,
                                uint64_t proto) {
  SetNightTop(cx, top);
  JS::RootedValue protov(cx, JS::Value::fromRawBits(proto));
  if (!protov.isObjectOrNull()) {
    return true;
  }
  JS::RootedValue objv(cx, JS::Value::fromRawBits(obj));
  JS::RootedObject o(cx, &objv.toObject());
  JS::RootedObject newProto(cx, protov.toObjectOrNull());
  return JS_SetPrototype(cx, o, newProto);
}

// JSOp::InitHomeObject: `[fn, homeObj] -> [fn]`. Store `homeObj` as the
// method's
// [[HomeObject]] (a function extended slot). Leaves `fn` on the stack (the
// driver keeps it). A raw extended-slot store (write barrier only, no GC).
bool night_runtime_init_home_object(JSContext* cx, uint32_t top,
                                    uint64_t fnBits, uint64_t homeBits) {
  SetNightTop(cx, top);
  JSFunction* fn = &JS::Value::fromRawBits(fnBits).toObject().as<JSFunction>();
  JSObject* homeObj = &JS::Value::fromRawBits(homeBits).toObject();
  js::night::NightSetHomeObject(fn, homeObj);
  return true;
}

// JSOp::SuperBase: `[callee] -> [superBase]`. superBase = the callee method's
// [[HomeObject]]'s [[Prototype]] (the object `super.*` reads from). The proto
// may be null; written as an ObjectOrNull just like the interpreter.
bool night_runtime_super_base(JSContext* cx, uint32_t top,
                              uint64_t calleeBits) {
  SetNightTop(cx, top);
  JSFunction* fn =
      &JS::Value::fromRawBits(calleeBits).toObject().as<JSFunction>();
  JSObject* homeObj = js::night::NightGetHomeObject(fn);
  JSObject* superBase = js::HomeObjectSuperBase(homeObj);
  WriteNightOut(top, JS::ObjectOrNullValue(superBase).asRawBits());
  return true;
}

// JSOp::SuperFun: `[callee] -> [superFun]`. The parent constructor = the
// derived class constructor's [[Prototype]] (used by `super()`), reached
// inside a derived constructor. Returns the callee's static prototype.
bool night_runtime_super_fun(JSContext* cx, uint32_t top, uint64_t calleeBits) {
  SetNightTop(cx, top);
  JSObject* callee = &JS::Value::fromRawBits(calleeBits).toObject();
  JSObject* superFun = callee->staticPrototype();
  WriteNightOut(top, JS::ObjectOrNullValue(superFun).asRawBits());
  return true;
}

// JSOp::GetPropSuper: `[receiver, superBase] -> [value]`. GetProperty on
// `superBase` (an object or null) with `receiver` as the this/receiver. May
// GC/throw (getters, ToObject on a null superBase).
bool night_runtime_get_prop_super(JSContext* cx, uint32_t top,
                                  uint64_t recvBits, uint64_t lvalBits,
                                  uint32_t atomId) {
  SetNightTop(cx, top);
  JS::HandleId id = AtomIdChecked(cx, atomId);
  JS::RootedValue lval(cx, JS::Value::fromRawBits(lvalBits));
  JS::RootedValue receiver(cx, JS::Value::fromRawBits(recvBits));
  JS::RootedObject obj(cx, js::ToObjectFromStackForPropertyAccess(
                               cx, lval, JSDVG_SEARCH_STACK, id));
  if (!obj) {
    return false;
  }
  JS::RootedValue res(cx);
  if (!js::GetProperty(cx, obj, receiver, id, &res)) {
    return false;
  }
  WriteNightOut(top, res.get().asRawBits());
  return true;
}

// JSOp::GetElemSuper: `[receiver, key, superBase] -> [value]`. Computed-key
// GetProperty on `superBase` with `receiver` as the receiver. Mirrors the
// interpreter's order: ToObject(superBase) first, then ToPropertyKey(key).
bool night_runtime_get_elem_super(JSContext* cx, uint32_t top,
                                  uint64_t recvBits, uint64_t keyBits,
                                  uint64_t lvalBits) {
  SetNightTop(cx, top);
  JS::RootedValue lval(cx, JS::Value::fromRawBits(lvalBits));
  JS::RootedValue receiver(cx, JS::Value::fromRawBits(recvBits));
  JS::RootedValue keyv(cx, JS::Value::fromRawBits(keyBits));
  JS::RootedObject obj(cx, js::ToObjectFromStackForPropertyAccess(
                               cx, lval, JSDVG_SEARCH_STACK, keyv));
  if (!obj) {
    return false;
  }
  JS::RootedId id(cx);
  if (!JS_ValueToId(cx, keyv, &id)) {
    return false;
  }
  JS::RootedValue res(cx);
  if (!js::GetProperty(cx, obj, receiver, id, &res)) {
    return false;
  }
  WriteNightOut(top, res.get().asRawBits());
  return true;
}

// JSOp::SetPropSuper / StrictSetPropSuper: `[receiver, superBase, value] ->
// [value]`. Sets the named property on `superBase` with `receiver` as the
// receiver -- a super write defines the own property on `receiver`, not on the
// base. The result left on the stack is `value`.
bool night_runtime_set_prop_super(JSContext* cx, uint32_t top,
                                  uint64_t recvBits, uint64_t lvalBits,
                                  uint32_t atomId, uint64_t valBits,
                                  uint32_t strict) {
  SetNightTop(cx, top);
  JS::Rooted<JS::PropertyKey> id(cx, AtomIdChecked(cx, atomId));
  JS::RootedValue lval(cx, JS::Value::fromRawBits(lvalBits));
  JS::RootedValue receiver(cx, JS::Value::fromRawBits(recvBits));
  JS::RootedValue rval(cx, JS::Value::fromRawBits(valBits));
  JS::Rooted<js::PropertyName*> name(cx, id.get().toAtom()->asPropertyName());
  if (!js::SetPropertySuper(cx, lval, receiver, name, rval, strict != 0)) {
    return false;
  }
  WriteNightOut(top, rval.get().asRawBits());
  return true;
}

// JSOp::SetElemSuper / StrictSetElemSuper: `[receiver, key, superBase, value]
// -> [value]`. Computed-key variant of the above.
bool night_runtime_set_elem_super(JSContext* cx, uint32_t top,
                                  uint64_t recvBits, uint64_t keyBits,
                                  uint64_t lvalBits, uint64_t valBits,
                                  uint32_t strict) {
  SetNightTop(cx, top);
  JS::RootedValue lval(cx, JS::Value::fromRawBits(lvalBits));
  JS::RootedValue receiver(cx, JS::Value::fromRawBits(recvBits));
  JS::RootedValue index(cx, JS::Value::fromRawBits(keyBits));
  JS::RootedValue rval(cx, JS::Value::fromRawBits(valBits));
  if (!js::SetElementSuper(cx, lval, receiver, index, rval, strict != 0)) {
    return false;
  }
  WriteNightOut(top, rval.get().asRawBits());
  return true;
}

bool night_runtime_tostring(JSContext* cx, uint32_t top, uint64_t v) {
  SetNightTop(cx, top);
  JS::RootedValue val(cx, JS::Value::fromRawBits(v));
  JSString* str = JS::ToString(cx, val);
  if (!str) {
    return false;
  }
  WriteNightOut(top, JS::StringValue(str).asRawBits());
  return true;
}

// `Pow` (`**`): generic numeric/bigint exponentiation. ToNumeric-coerces both
// operands (may GC/throw) then computes the result. Writes it to the out-slot.
bool night_runtime_pow(JSContext* cx, uint32_t top, uint64_t a, uint64_t b) {
  SetNightTop(cx, top);
  JS::RootedValue lhs(cx, JS::Value::fromRawBits(a));
  JS::RootedValue rhs(cx, JS::Value::fromRawBits(b));
  JS::RootedValue res(cx);
  if (!js::PowValues(cx, &lhs, &rhs, &res)) {
    return false;
  }
  WriteNightOut(top, res.get().asRawBits());
  return true;
}

// `CheckObjCoercible`: throw a TypeError if `v` is null/undefined; otherwise a
// no-op (the value stays on the stack). Returns false on the throwing path.
bool night_runtime_check_obj_coercible(JSContext* cx, uint32_t top,
                                       uint64_t v) {
  JS::Value val = JS::Value::fromRawBits(v);
  if (val.isNullOrUndefined()) {
    SetNightTop(cx, top);
    JS::RootedValue rv(cx, val);
    return js::ThrowObjectCoercible(cx, rv);
  }
  return true;
}

// `CheckClassHeritage`: throw if the `extends` operand is neither a constructor
// nor null; otherwise a no-op. Returns false on the throwing path.
bool night_runtime_check_class_heritage(JSContext* cx, uint32_t top,
                                        uint64_t v) {
  SetNightTop(cx, top);
  JS::RootedValue heritage(cx, JS::Value::fromRawBits(v));
  return js::CheckClassHeritageOperation(cx, heritage);
}

// `Generator`: create this frame's generator object (callee/env captured;
// subtype from the callee script). May GC; result to the out-slot.
bool night_runtime_create_generator(JSContext* cx, uint32_t top,
                                    uint64_t callee, uint64_t env) {
  SetNightTop(cx, top);
  uint64_t out = 0;
  if (!js::night::NightCreateGenerator(cx, callee, env, &out)) {
    return false;
  }
  WriteNightOut(top, out);
  return true;
}

// `InitialYield`/`Yield` suspend: save locals + live operands (already
// spilled to the frame by the caller) into the generator's storage. Leaf.
int32_t night_runtime_gen_suspend(JSContext* cx, uint64_t gen, uint32_t k,
                                  uint32_t localsPtr, uint32_t nlocals,
                                  uint32_t opsPtr, uint32_t nops,
                                  uint64_t env) {
  js::night::NightGenSuspend(cx, gen, k, LinMem<JS::Value>(localsPtr), nlocals,
                             LinMem<JS::Value>(opsPtr), nops, env);
  return 1;
}

// Resume restore: copy the generator's saved state back into the frame
// (locals, operands, env head), mark it running. Leaf.
int32_t night_runtime_gen_restore(JSContext* cx, uint64_t gen,
                                  uint32_t localsPtr, uint32_t nlocals,
                                  uint32_t envPtr, uint32_t opsPtr) {
  return int32_t(js::night::NightGenRestore(
      cx, gen, LinMem<JS::Value>(localsPtr), nlocals, LinMem<JS::Value>(envPtr),
      LinMem<JS::Value>(opsPtr)));
}

// `CheckResumeKind`, non-Next kinds: always raises (Throw: val; Return:
// stages val in the frame's rval slot and raises the closing magic).
bool night_runtime_gen_check_resume(JSContext* cx, uint32_t top, uint64_t gen,
                                    uint64_t val, uint32_t kind,
                                    uint32_t rvalAddr) {
  SetNightTop(cx, top);
  return js::night::NightGenCheckResume(cx, gen, val, kind,
                                        LinMem<JS::Value>(rvalAddr));
}

// Generator error-epilogue closing check: clear + report a pending
// JS_GENERATOR_CLOSING magic. Leaf.
int32_t night_runtime_gen_closing(JSContext* cx) {
  return js::night::NightGenClosing(cx);
}

// Peek-only closing check for the catch-pad split: the magic stays pending
// (the rerouted unwind's finallys / epilogue still observe it). Leaf.
int32_t night_runtime_gen_is_closing(JSContext* cx) {
  return js::night::NightGenIsClosing(cx);
}

// The MIR guard-failure stress mode (`--mir-stress N`): every guard also
// calls this, and fails when it returns 1, which it does on every
// `period`-th call. Leaf.
int32_t night_runtime_mir_stress(uint32_t period) {
  JSContext* cx = CurrentNightContext();
  uint32_t& count = RtState(cx).stressCount;
  return period != 0 && ++count % period == 0 ? 1 : 0;
}

// The stamp of `obj`, whose slots below `n` all hold properties, with
// layout `layoutId`, keeping `keepBits` of its word `w0`; and CLOSED where
// `keepBits` says the layout may be (as a bit of `w0` it is an early-key
// bit, never kept) and those are its row's fields (SLOTS) and its only ones
// (a span of `n`), as MIR's `or_closed_if_span`.
static uint32_t NightClosedIfExact(js::NativeObject* obj, uint32_t layoutId,
                                   uint32_t w0, uint32_t keepBits, uint32_t n) {
  uint32_t w = (layoutId + 1) | (w0 & keepBits & ~js::night::kWordClosed);
  if ((keepBits & js::night::kWordClosed) && (w & js::night::kWordSlots) &&
      obj->is<js::PlainObject>() && obj->slotSpan() == n) {
    w |= js::night::kWordClosed;
  }
  return w;
}

// The ctor-exit stamp's first-stamp form (MIR's `ctor_stamp_inline`),
// as a helper: the same ownership and span gates, the same new word, no
// epoch bump (a sentinel word carries no facts).
void night_runtime_ctor_stamp(uint64_t thisBits, uint32_t layoutId,
                              uint32_t nFields, uint32_t keepBits) {
  JS::Value v = JS::Value::fromRawBits(thisBits);
  if (!v.isObject() || !v.toObject().is<js::NativeObject>()) {
    return;
  }
  js::NativeObject* obj = &v.toObject().as<js::NativeObject>();
  uint32_t w0 = obj->externalWord();
  if (!(w0 & js::night::kWordConstructing)) {
    return;
  }
  uint32_t key = (w0 >> 18) & 0x0FFF;
  if (key != 0 && key != layoutId + 1) {
    return;
  }
  if (!js::night::NightSlotsCovered(obj, nFields)) {
    return;
  }
  NightCensusTraceStamp("ctor", layoutId, w0, keepBits);
  obj->setExternalWord(NightClosedIfExact(obj, layoutId, w0, keepBits, nFields));
}

// The restamp form (MIR's inline `restamp`), as a helper. No epoch
// bump: the only stamped words the gates admit are prefix-stamped ones,
// and advancing those falsifies nothing a caller carries.
void night_runtime_ctor_restamp(uint64_t thisBits, uint32_t layoutId,
                                uint32_t nFields, uint32_t keepBits,
                                uint32_t prefix0, uint32_t prefix1,
                                uint32_t prefix2, uint32_t prefix3) {
  JS::Value v = JS::Value::fromRawBits(thisBits);
  if (!v.isObject() || !v.toObject().is<js::NativeObject>()) {
    return;
  }
  js::NativeObject* obj = &v.toObject().as<js::NativeObject>();
  uint32_t w0 = obj->externalWord();
  // Under the sentinel the low half is a set of fields, not an identity.
  uint32_t idx = w0 & js::night::kWordConstructing ? 0 : w0 & 0xFFFF;
  if (idx == layoutId + 1) {
    return;
  }
  const uint32_t prefixes[4] = {prefix0, prefix1, prefix2, prefix3};
  auto isPrefix = [&](uint32_t k) {
    for (uint32_t p : prefixes) {
      if (p != 0 && k == p) {
        return true;
      }
    }
    return false;
  };
  bool ok = false;
  if (w0 & js::night::kWordConstructing) {
    uint32_t key = (w0 >> 18) & 0x0FFF;
    ok = key == 0 || key == layoutId + 1 || isPrefix(key);
  } else {
    ok = isPrefix(idx) && !(w0 & js::night::kWordAdvIneligible);
  }
  if (!ok || !js::night::NightSlotsCovered(obj, nFields)) {
    return;
  }
  NightCensusTraceStamp("restamp", layoutId, w0, keepBits);
  obj->setExternalWord(NightClosedIfExact(obj, layoutId, w0, keepBits, nFields));
}

// `FinalYieldRval`: close the completed generator.
bool night_runtime_gen_final(JSContext* cx, uint32_t top, uint64_t gen) {
  SetNightTop(cx, top);
  js::night::NightGenFinal(cx, gen);
  return true;
}

// `AsyncAwait`: register the await continuation; promise to the out-slot.
bool night_runtime_async_await(JSContext* cx, uint32_t top, uint64_t gen,
                               uint64_t val) {
  SetNightTop(cx, top);
  uint64_t out = 0;
  if (!js::night::NightAsyncAwait(cx, gen, val, &out)) {
    return false;
  }
  WriteNightOut(top, out);
  return true;
}

// `AsyncResolve`: fulfill the result promise; promise to the out-slot.
bool night_runtime_async_resolve(JSContext* cx, uint32_t top, uint64_t gen,
                                 uint64_t val) {
  SetNightTop(cx, top);
  uint64_t out = 0;
  if (!js::night::NightAsyncResolve(cx, gen, val, &out)) {
    return false;
  }
  WriteNightOut(top, out);
  return true;
}

// `AsyncReject`: reject the result promise; promise to the out-slot.
bool night_runtime_async_reject(JSContext* cx, uint32_t top, uint64_t gen,
                                uint64_t reason, uint64_t stack) {
  SetNightTop(cx, top);
  uint64_t out = 0;
  if (!js::night::NightAsyncReject(cx, gen, reason, stack, &out)) {
    return false;
  }
  WriteNightOut(top, out);
  return true;
}

// `CanSkipAwait`: boolean to the out-slot.
bool night_runtime_can_skip_await(JSContext* cx, uint32_t top, uint64_t val) {
  SetNightTop(cx, top);
  uint64_t out = 0;
  if (!js::night::NightCanSkipAwait(cx, val, &out)) {
    return false;
  }
  WriteNightOut(top, out);
  return true;
}

// `MaybeExtractAwaitValue`: (maybe-)extracted value to the out-slot.
bool night_runtime_maybe_extract_await(JSContext* cx, uint32_t top,
                                       uint64_t val, uint32_t canSkip) {
  SetNightTop(cx, top);
  uint64_t out = 0;
  if (!js::night::NightMaybeExtractAwait(cx, val, canSkip, &out)) {
    return false;
  }
  WriteNightOut(top, out);
  return true;
}

// `CheckIsObj`: throw a TypeError (per the CheckIsObjectKind byte) if `v` is
// not an object; otherwise a no-op. Returns false on the throwing path.
bool night_runtime_check_is_obj(JSContext* cx, uint32_t top, uint64_t v,
                                uint32_t kind) {
  if (!JS::Value::fromRawBits(v).isObject()) {
    SetNightTop(cx, top);
    return js::ThrowCheckIsObject(cx, js::CheckIsObjectKind(uint8_t(kind)));
  }
  return true;
}

// `CheckThis`: throw a ReferenceError if `this` is the uninitialized-lexical
// magic value (derived-class `this` used before `super()`); else a no-op.
bool night_runtime_check_this(JSContext* cx, uint32_t top, uint64_t v) {
  if (JS::Value::fromRawBits(v).isMagic(JS_UNINITIALIZED_LEXICAL)) {
    SetNightTop(cx, top);
    return js::ThrowUninitializedThis(cx);
  }
  return true;
}

// `CheckLexical`/`CheckAliasedLexical`: throw a ReferenceError (TDZ) if `v` is
// the uninitialized-lexical magic value; else a no-op. `pcOffset` locates the
// op in the still-intact script bytecode so the engine can name the binding in
// the error message. Returns false on the throwing path.
bool night_runtime_check_lexical(JSContext* cx, uint32_t top, uint64_t v,
                                 uint32_t script, uint32_t pcOffset) {
  if (JS::Value::fromRawBits(v).isMagic(JS_UNINITIALIZED_LEXICAL)) {
    SetNightTop(cx, top);
    JS::RootedScript s(cx, reinterpret_cast<JSScript*>(uintptr_t(script)));
    js::ReportRuntimeLexicalError(cx, JSMSG_UNINITIALIZED_LEXICAL, s,
                                  s->code() + pcOffset);
    return false;
  }
  return true;
}

// `ThrowSetConst`: unconditionally throw the "assignment to const" TypeError.
// `pcOffset` locates the op so the engine can name the const binding.
void night_runtime_throw_set_const(JSContext* cx, uint32_t top, uint32_t script,
                                   uint32_t pcOffset) {
  SetNightTop(cx, top);
  JS::RootedScript s(cx, reinterpret_cast<JSScript*>(uintptr_t(script)));
  js::ReportRuntimeLexicalError(cx, JSMSG_BAD_CONST_ASSIGN, s,
                                s->code() + pcOffset);
}

// `PushLexicalEnv`: create a BlockLexicalEnvironmentObject for the scope named
// by the JOF_SCOPE gcthing at `pcOffset` over the current env head `env`, and
// write the new env to the out-slot. May GC. `env` is the enclosing chain head.
bool night_runtime_push_lexical_env(JSContext* cx, uint32_t top, uint64_t env,
                                    uint32_t script, uint32_t pcOffset) {
  SetNightTop(cx, top);
  JSScript* s = reinterpret_cast<JSScript*>(uintptr_t(script));
  JS::Rooted<js::LexicalScope*> scope(
      cx, &s->getScope(s->code() + pcOffset)->as<js::LexicalScope>());
  JS::RootedObject enclosing(cx, &JS::Value::fromRawBits(env).toObject());
  js::BlockLexicalEnvironmentObject* newEnv =
      js::BlockLexicalEnvironmentObject::createWithoutEnclosing(cx, scope);
  if (!newEnv) {
    return false;
  }
  newEnv->initEnclosingEnvironment(enclosing);
  WriteNightOut(top, JS::ObjectValue(*newEnv).asRawBits());
  return true;
}

// `PushClassBodyEnv`: like PushLexicalEnv but a
// ClassBodyLexicalEnvironmentObject for the ClassBodyScope named by the gcthing
// at `pcOffset`. May GC.
bool night_runtime_push_class_body_env(JSContext* cx, uint32_t top,
                                       uint64_t env, uint32_t script,
                                       uint32_t pcOffset) {
  SetNightTop(cx, top);
  JSScript* s = reinterpret_cast<JSScript*>(uintptr_t(script));
  JS::Rooted<js::ClassBodyScope*> scope(
      cx, &s->getScope(s->code() + pcOffset)->as<js::ClassBodyScope>());
  JS::RootedObject enclosing(cx, &JS::Value::fromRawBits(env).toObject());
  js::ClassBodyLexicalEnvironmentObject* newEnv =
      js::ClassBodyLexicalEnvironmentObject::createWithoutEnclosing(cx, scope);
  if (!newEnv) {
    return false;
  }
  newEnv->initEnclosingEnvironment(enclosing);
  WriteNightOut(top, JS::ObjectValue(*newEnv).asRawBits());
  return true;
}

// `FreshenLexicalEnv`: clone the current innermost block lexical env (fresh
// per-iteration bindings; copies all binding values) and write it to the
// out-slot. `env` is the current env head. May GC.
bool night_runtime_freshen_lexical_env(JSContext* cx, uint32_t top,
                                       uint64_t env) {
  SetNightTop(cx, top);
  JS::Rooted<js::BlockLexicalEnvironmentObject*> cur(
      cx, &JS::Value::fromRawBits(env)
               .toObject()
               .as<js::BlockLexicalEnvironmentObject>());
  js::BlockLexicalEnvironmentObject* fresh =
      js::BlockLexicalEnvironmentObject::clone(cx, cur);
  if (!fresh) {
    return false;
  }
  WriteNightOut(top, JS::ObjectValue(*fresh).asRawBits());
  return true;
}

// `RecreateLexicalEnv`: recreate the current innermost block lexical env (all
// bindings reset to the TDZ magic) and write it to the out-slot. May GC.
bool night_runtime_recreate_lexical_env(JSContext* cx, uint32_t top,
                                        uint64_t env) {
  SetNightTop(cx, top);
  JS::Rooted<js::BlockLexicalEnvironmentObject*> cur(
      cx, &JS::Value::fromRawBits(env)
               .toObject()
               .as<js::BlockLexicalEnvironmentObject>());
  js::BlockLexicalEnvironmentObject* fresh =
      js::BlockLexicalEnvironmentObject::recreate(cx, cur);
  if (!fresh) {
    return false;
  }
  WriteNightOut(top, JS::ObjectValue(*fresh).asRawBits());
  return true;
}

// `InitGLexical`: initialize the global lexical binding named at `pcOffset`
// with `val` (clears the TDZ). Reuses the engine's inline op over the syntactic
// global lexical environment. Leaves `val` on the stack (out-slot untouched).
bool night_runtime_init_glexical(JSContext* cx, uint32_t top, uint64_t val,
                                 uint32_t script, uint32_t pcOffset) {
  SetNightTop(cx, top);
  JSScript* s = reinterpret_cast<JSScript*>(uintptr_t(script));
  MOZ_RELEASE_ASSERT(!s->hasNonSyntacticScope());
  js::ExtensibleLexicalEnvironmentObject* lexicalEnv =
      &cx->global()->lexicalEnvironment();
  JS::RootedValue value(cx, JS::Value::fromRawBits(val));
  js::InitGlobalLexicalOperation(cx, lexicalEnv, s, s->code() + pcOffset,
                                 value);
  return true;
}

// `GetName`: scope-chain read of `atomId` over env head `env`. `forTypeof`
// selects the non-throwing `GetNameMode::TypeOf` lookup (the `typeof foo`
// kludge). Result to the out-slot. May GC/throw.
bool night_runtime_get_name(JSContext* cx, uint32_t top, uint64_t env,
                            uint32_t atomId, uint32_t forTypeof) {
  SetNightTop(cx, top);
  JS::HandleId id = AtomIdChecked(cx, atomId);
  JS::Rooted<js::PropertyName*> name(cx, id.toAtom()->asPropertyName());
  JS::RootedObject envChain(cx, &JS::Value::fromRawBits(env).toObject());
  JS::RootedValue rval(cx);
  bool ok = forTypeof != 0 ? js::GetEnvironmentName<js::GetNameMode::TypeOf>(
                                 cx, envChain, name, &rval)
                           : js::GetEnvironmentName<js::GetNameMode::Normal>(
                                 cx, envChain, name, &rval);
  if (!ok) {
    return false;
  }
  WriteNightOut(top, rval.get().asRawBits());
  return true;
}

// `BindName`: push the environment object a following `SetName` assigns into
// (scope-chain binding resolution with a global default). To the out-slot.
bool night_runtime_bind_name(JSContext* cx, uint32_t top, uint64_t env,
                             uint32_t atomId) {
  SetNightTop(cx, top);
  JS::HandleId id = AtomIdChecked(cx, atomId);
  JS::Rooted<js::PropertyName*> name(cx, id.toAtom()->asPropertyName());
  JS::RootedObject envChain(cx, &JS::Value::fromRawBits(env).toObject());
  JSObject* bound = js::LookupNameWithGlobalDefault(cx, name, envChain);
  if (!bound) {
    return false;
  }
  WriteNightOut(top, JS::ObjectValue(*bound).asRawBits());
  return true;
}

// `GetBoundName`: read `atomId` from the already-bound environment `env`
// (pairs with `BindName` for compound assignments). To the out-slot. May GC.
bool night_runtime_get_bound_name(JSContext* cx, uint32_t top, uint64_t env,
                                  uint32_t atomId) {
  SetNightTop(cx, top);
  JS::HandleId id = AtomIdChecked(cx, atomId);
  JS::RootedObject envObj(cx, &JS::Value::fromRawBits(env).toObject());
  JS::RootedValue rval(cx);
  if (!js::GetNameBoundInEnvironment(cx, envObj, id, &rval)) {
    return false;
  }
  WriteNightOut(top, rval.get().asRawBits());
  return true;
}

// `BindUnqualifiedName`: binding resolution for a `name =` store over env head
// `env` (adds a property to the global object when undeclared). To the
// out-slot.
bool night_runtime_bind_unqualified_name(JSContext* cx, uint32_t top,
                                         uint64_t env, uint32_t atomId) {
  SetNightTop(cx, top);
  JS::HandleId id = AtomIdChecked(cx, atomId);
  JS::Rooted<js::PropertyName*> name(cx, id.toAtom()->asPropertyName());
  JS::RootedObject envChain(cx, &JS::Value::fromRawBits(env).toObject());
  JSObject* bound = js::LookupNameUnqualified(cx, name, envChain);
  if (!bound) {
    return false;
  }
  WriteNightOut(top, JS::ObjectValue(*bound).asRawBits());
  return true;
}

// `BindVar`: the var environment object for the env head `env`. To the
// out-slot. Never GCs / fails.
bool night_runtime_bind_var(JSContext* cx, uint32_t top, uint64_t env) {
  SetNightTop(cx, top);
  JS::RootedObject envChain(cx, &JS::Value::fromRawBits(env).toObject());
  JSObject* varObj = js::BindVarOperation(cx, envChain);
  WriteNightOut(top, JS::ObjectValue(*varObj).asRawBits());
  return true;
}

// `DelName`: `delete name` (unqualified) over env head `env` -> boolean to the
// out-slot. May GC/throw.
bool night_runtime_del_name(JSContext* cx, uint32_t top, uint64_t env,
                            uint32_t atomId) {
  SetNightTop(cx, top);
  JS::HandleId id = AtomIdChecked(cx, atomId);
  JS::Rooted<js::PropertyName*> name(cx, id.toAtom()->asPropertyName());
  JS::RootedObject envChain(cx, &JS::Value::fromRawBits(env).toObject());
  JS::RootedValue res(cx, JS::BooleanValue(true));
  if (!js::DeleteNameOperation(cx, name, envChain, &res)) {
    return false;
  }
  // A delete may have removed a global binding; any inline literal/value fuse
  // cached for this name is now stale, so blow both so later reads re-resolve.
  BlowGnameFuse(atomId);
  BlowBindingFuseAtom(atomId);
  WriteNightOut(top, res.get().asRawBits());
  return true;
}

// `PushVarEnv`: create a VarEnvironmentObject for the (eval/var) scope at
// `pcOffset` over env head `env`; writes the new env to the out-slot. May GC.
bool night_runtime_push_var_env(JSContext* cx, uint32_t top, uint64_t env,
                                uint32_t script, uint32_t pcOffset) {
  SetNightTop(cx, top);
  JSScript* s = reinterpret_cast<JSScript*>(uintptr_t(script));
  JS::Rooted<js::VarScope*> scope(
      cx, &s->getScope(s->code() + pcOffset)->as<js::VarScope>());
  JS::RootedObject enclosing(cx, &JS::Value::fromRawBits(env).toObject());
  js::VarEnvironmentObject* newEnv =
      js::VarEnvironmentObject::createWithoutEnclosing(cx, scope);
  if (!newEnv) {
    return false;
  }
  newEnv->initEnclosingEnvironment(enclosing);
  WriteNightOut(top, JS::ObjectValue(*newEnv).asRawBits());
  return true;
}

// `EnterWith`: create a WithEnvironmentObject wrapping `val` (coerced to an
// object) for the WithScope at `pcOffset` over env head `env`; writes the new
// env to the out-slot. May GC/throw (ToObject on a primitive).
bool night_runtime_enter_with(JSContext* cx, uint32_t top, uint64_t env,
                              uint64_t val, uint32_t script,
                              uint32_t pcOffset) {
  SetNightTop(cx, top);
  JSScript* s = reinterpret_cast<JSScript*>(uintptr_t(script));
  JS::Rooted<js::WithScope*> scope(
      cx, &s->getScope(s->code() + pcOffset)->as<js::WithScope>());
  JS::RootedValue v(cx, JS::Value::fromRawBits(val));
  JS::RootedObject obj(cx);
  if (v.isObject()) {
    obj = &v.toObject();
  } else {
    obj = JS::ToObject(cx, v);
    if (!obj) {
      return false;
    }
  }
  JS::RootedObject enclosing(cx, &JS::Value::fromRawBits(env).toObject());
  js::WithEnvironmentObject* withobj = js::WithEnvironmentObject::create(
      cx, obj, enclosing, scope, JS::SupportUnscopables::Yes);
  if (!withobj) {
    return false;
  }
  WriteNightOut(top, JS::ObjectValue(*withobj).asRawBits());
  return true;
}

// `ThrowMsg`: unconditionally throw the error named by the ThrowMsgKind byte.
void night_runtime_throw_msg(JSContext* cx, uint32_t top, uint32_t kind) {
  SetNightTop(cx, top);
  js::ThrowMsgOperation(cx, unsigned(kind));
}

// `BuiltinObject`: the builtin constructor/prototype named by the
// BuiltinObjectKind byte. Writes the object to the out-slot; may GC.
bool night_runtime_builtin_object(JSContext* cx, uint32_t top, uint32_t kind) {
  SetNightTop(cx, top);
  JSObject* builtin =
      js::BuiltinObjectOperation(cx, js::BuiltinObjectKind(uint8_t(kind)));
  if (!builtin) {
    return false;
  }
  WriteNightOut(top, JS::ObjectValue(*builtin).asRawBits());
  return true;
}

// `BuiltinObject` through a per-kind value cell (the GetIntrinsic cell
// pattern; the cell lives in the intrinsic-cell region and is zeroed with
// it on compacting GC): the builtin is a realm constant, so an armed cell
// serves every later read as a pure load.
bool night_runtime_builtin_object_cell(JSContext* cx, uint32_t top,
                                       uint32_t kind, uint32_t cellAddr) {
  SetNightTop(cx, top);
  JSObject* builtin =
      js::BuiltinObjectOperation(cx, js::BuiltinObjectKind(uint8_t(kind)));
  if (!builtin) {
    return false;
  }
  JS::Value v = JS::ObjectValue(*builtin);
  WriteNightOut(top, v.asRawBits());
  if (!js::gc::IsInsideNursery(static_cast<js::gc::Cell*>(builtin))) {
    *LinMem<uint64_t>(cellAddr) = v.asRawBits();
  }
  return true;
}

// For-in support. `Iter` is the only fallible step (ValueToIterator may
// GC/throw building the PropertyIteratorObject); the per-step
// `IteratorMore` and the `CloseIterator` are leaf operations
// (vm/Iteration.h), so their helpers skip the rooting handshake.
bool night_runtime_iter(JSContext* cx, uint32_t top, uint64_t val) {
  SetNightTop(cx, top);
  JS::Rooted<JS::Value> v(cx, JS::Value::fromRawBits(val));
  JSObject* iter = js::ValueToIterator(cx, v);
  if (!iter) {
    return false;
  }
  WriteNightOut(top, JS::ObjectValue(*iter).asRawBits());
  return true;
}

uint64_t night_runtime_more_iter(JSContext* cx, uint64_t iter) {
  (void)cx;
  return js::IteratorMore(&JS::Value::fromRawBits(iter).toObject()).asRawBits();
}

void night_runtime_end_iter(JSContext* cx, uint64_t iter) {
  (void)cx;
  js::CloseIterator(&JS::Value::fromRawBits(iter).toObject());
}

// A for-in started in compiled code from a shape's cached iterator stored
// a nursery object in it: the whole-cell post barrier (leaf).
void night_runtime_post_whole_cell(JSContext* cx, uint32_t cell) {
  js::night::NightPostWholeCell(cx, cell);
}

void night_runtime_close_iter_for_exception(JSContext* cx, uint32_t top,
                                            uint64_t done, uint64_t iter) {
  JS::RootedValue doneValue(cx, JS::Value::fromRawBits(done));
  MOZ_RELEASE_ASSERT(!doneValue.isMagic());
  if (JS::ToBoolean(doneValue)) {
    return;
  }
  SetNightTop(cx, top);
  JS::RootedObject iterObject(cx, &JS::Value::fromRawBits(iter).toObject());
  // Runs the iterator's `return()`; preserves the pending exception via
  // AutoSaveExceptionState (or leaves the return()'s own throw pending).
  (void)js::IteratorCloseForException(cx, iterObject);
}

// `Symbol code`: push the well-known symbol named by the `SymbolCode` byte
// (e.g. `@@iterator`). Well-known symbols are runtime-pinned tenured values,
// so this is a leaf (no GC, no throw).
uint64_t night_runtime_symbol(JSContext* cx, uint32_t code) {
  JS::Symbol* sym = cx->wellKnownSymbols().get(size_t(code));
  return JS::SymbolValue(sym).asRawBits();
}

// `OptimizeGetIterator`: a pure predicate -- true when `v` is an array with the
// default (unmodified) iteration protocol, so a for-of/destructuring can skip
// the iterator-object dance. Reads realm fuses/shapes only (no GC, no throw),
// hence a leaf returning the boolean directly.
uint32_t night_runtime_optimize_get_iterator(JSContext* cx, uint64_t v) {
  return js::OptimizeGetIterator(JS::Value::fromRawBits(v), cx) ? 1 : 0;
}

// `CloseIter kind`: run IteratorClose on `iter` with the given `CompletionKind`
// (Normal/Throw/Return). May run a user `return` method -> may GC/throw.
bool night_runtime_close_iter(JSContext* cx, uint32_t top, uint64_t iter,
                              uint32_t kind) {
  SetNightTop(cx, top);
  JS::RootedObject it(cx, &JS::Value::fromRawBits(iter).toObject());
  return js::CloseIterOperation(cx, it, js::CompletionKind(uint8_t(kind)));
}

// `ToAsyncIter`: wrap the sync iterator `iter` (with its `next` method) in an
// async-from-sync iterator. `iter` is `sp[-2]`, `nextMethod` is `sp[-1]`; the
// wrapper object goes to the out-slot. May GC (allocates).
bool night_runtime_to_async_iter(JSContext* cx, uint32_t top, uint64_t iter,
                                 uint64_t nextMethod) {
  SetNightTop(cx, top);
  JS::RootedObject iterObj(cx, &JS::Value::fromRawBits(iter).toObject());
  JS::RootedValue next(cx, JS::Value::fromRawBits(nextMethod));
  JSObject* asyncIter = js::CreateAsyncFromSyncIterator(cx, iterObj, next);
  if (!asyncIter) {
    return false;
  }
  WriteNightOut(top, JS::ObjectValue(*asyncIter).asRawBits());
  return true;
}

// `SpreadCall`/`SpreadNew`: call/construct `callee` with the elements of the
// packed array `arr` spread as actual arguments. `constructing` selects between
// the two forms (and picks `newTarget` for the construct case). Wraps the
// engine's `SpreadCallOperation`; the eval family is out of scope. May
// GC/throw. The engine op reads only the opcode byte from `pc` and never
// dereferences `script`, so a stack-local op byte and a null script suffice
// here.
bool night_runtime_spread_call(JSContext* cx, uint32_t top, uint64_t calleeBits,
                               uint64_t thisvBits, uint64_t arrBits,
                               uint64_t newTargetBits, uint32_t constructing) {
  SetNightTop(cx, top);
  JS::RootedValue callee(cx, JS::Value::fromRawBits(calleeBits));
  JS::RootedValue thisv(cx, JS::Value::fromRawBits(thisvBits));
  JS::RootedValue arr(cx, JS::Value::fromRawBits(arrBits));
  JS::RootedValue newTarget(cx, JS::Value::fromRawBits(newTargetBits));
  JS::RootedValue res(cx);
  JS::RootedScript script(cx, nullptr);
  jsbytecode op = jsbytecode(constructing ? JSOp::SpreadNew : JSOp::SpreadCall);
  if (!js::SpreadCallOperation(cx, script, &op, thisv, callee, arr, newTarget,
                               &res)) {
    return false;
  }
  WriteNightOut(top, res.asRawBits());
  return true;
}

// `OptimizeSpreadCall`: if the spread argument `v` can be forwarded directly (a
// packed array / arguments object with the default iterator), write that array
// to the out-slot; otherwise write `undefined` (caller falls back to the full
// iterator spread). May GC (materializes an arguments-object copy).
bool night_runtime_optimize_spread_call(JSContext* cx, uint32_t top,
                                        uint64_t v) {
  SetNightTop(cx, top);
  JS::RootedValue arg(cx, JS::Value::fromRawBits(v));
  JS::RootedValue result(cx);
  if (!js::OptimizeSpreadCall(cx, arg, &result)) {
    return false;
  }
  WriteNightOut(top, result.asRawBits());
  return true;
}

// `Arguments`: the frame at `sp` is `[callee, this, args...]` with `argc`
// actuals; the arg slots live in the rooted AOT-stack scan region, so the
// engine may treat them as marked locations.
bool night_runtime_arguments(JSContext* cx, uint32_t top, uint32_t sp,
                             uint32_t argc) {
  SetNightTop(cx, top);
  const uint64_t* frame = LinMem<const uint64_t>(sp);
  return js::night::NightArguments(
      cx, frame[0], reinterpret_cast<const JS::Value*>(frame + 2), argc,
      LinMem<uint64_t>(top));
}

// `Arguments` for a script that also closes over bindings: `env` is the
// activation's environment head (its CallObject), passed as the scope chain so
// call-object-aliased formals forward `arguments[i]` to the CallObject slot.
bool night_runtime_arguments_env(JSContext* cx, uint32_t top, uint32_t sp,
                                 uint32_t argc, uint64_t env) {
  SetNightTop(cx, top);
  const uint64_t* frame = LinMem<const uint64_t>(sp);
  return js::night::NightArgumentsEnv(
      cx, frame[0], reinterpret_cast<const JS::Value*>(frame + 2), argc, env,
      LinMem<uint64_t>(top));
}

// `Rest`: build the rest array from the actuals beyond the formal count.
// nformal = callee.nargs() - 1 (the rest binding counts in nargs); the actuals
// live at frame+2 (after callee, this) and stay rooted below `top`.
bool night_runtime_rest(JSContext* cx, uint32_t top, uint32_t sp, uint32_t argc,
                        uint32_t nformal) {
  SetNightTop(cx, top);
  const JS::Value* argv = reinterpret_cast<const JS::Value*>(
      static_cast<uintptr_t>(sp) + 2 * sizeof(uint64_t));
  uint32_t nrest = (argc > nformal) ? argc - nformal : 0;
  js::ArrayObject* arr = js::NewDenseCopiedArray(cx, nrest, argv + nformal);
  if (!arr) {
    return false;
  }
  WriteNightOut(top, JS::ObjectValue(*arr).asRawBits());
  return true;
}

// `ImplicitThis`: the implicit `this` for an unqualified name call, computed
// from the environment object `env`. Undefined in ordinary scopes; the
// with-object for a with-scope. Infallible.
bool night_runtime_implicit_this(JSContext* cx, uint32_t top, uint64_t env) {
  SetNightTop(cx, top);
  JS::RootedObject envObj(cx, &JS::Value::fromRawBits(env).toObject());
  JS::RootedValue res(cx);
  js::ImplicitThisOperation(cx, envObj, &res);
  WriteNightOut(top, res.get().asRawBits());
  return true;
}

// `CheckThisReinit`: throw if `v` is NOT the uninitialized-lexical magic (i.e.
// `super()` already ran), else a no-op.
bool night_runtime_check_this_reinit(JSContext* cx, uint32_t top, uint64_t v) {
  if (!JS::Value::fromRawBits(v).isMagic(JS_UNINITIALIZED_LEXICAL)) {
    SetNightTop(cx, top);
    return js::ThrowInitializedThis(cx);
  }
  return true;
}

// `CheckReturn` (derived ctor): reconcile the frame's return value `rval` with
// `thisv`. An object `rval` is returned as-is; undefined `rval` returns
// `thisv` (throwing if `thisv` is the uninitialized-lexical magic); any other
// `rval` is the bad-derived-return TypeError.
bool night_runtime_check_return(JSContext* cx, uint32_t top, uint64_t thisv,
                                uint64_t rval) {
  JS::Value r = JS::Value::fromRawBits(rval);
  if (r.isObject()) {
    WriteNightOut(top, rval);
    return true;
  }
  SetNightTop(cx, top);
  if (!r.isUndefined()) {
    JS::RootedValue rv(cx, r);
    js::ReportValueError(cx, JSMSG_BAD_DERIVED_RETURN, JSDVG_IGNORE_STACK, rv,
                         nullptr);
    return false;
  }
  if (JS::Value::fromRawBits(thisv).isMagic(JS_UNINITIALIZED_LEXICAL)) {
    return js::ThrowUninitializedThis(cx);
  }
  WriteNightOut(top, thisv);
  return true;
}

// `ObjWithProto`: `Object.create(proto)` for an object literal with an explicit
// `__proto__`. `proto` must be object-or-null (else a TypeError). May GC.
bool night_runtime_obj_with_proto(JSContext* cx, uint32_t top, uint64_t proto) {
  SetNightTop(cx, top);
  JS::RootedValue protoVal(cx, JS::Value::fromRawBits(proto));
  JSObject* obj = js::ObjectWithProtoOperation(cx, protoVal);
  if (!obj) {
    return false;
  }
  WriteNightOut(top, JS::ObjectValue(*obj).asRawBits());
  return true;
}

// `FunWithProto`: clone the function template `script->getFunction(funcIndex)`
// with the explicit prototype `proto` over the enclosing environment `env`
// (class heritage). May GC.
bool night_runtime_fun_with_proto(JSContext* cx, uint32_t top, uint64_t env,
                                  uint64_t proto, uint32_t script,
                                  uint32_t funcIndex) {
  SetNightTop(cx, top);
  JS::RootedScript s(cx, reinterpret_cast<JSScript*>(uintptr_t(script)));
  JS::RootedFunction fun(cx, s->getFunction(js::GCThingIndex(funcIndex)));
  JS::RootedObject parent(cx, &JS::Value::fromRawBits(env).toObject());
  JS::RootedObject protoObj(cx, &JS::Value::fromRawBits(proto).toObject());
  JSObject* obj = js::FunWithProtoOperation(cx, fun, parent, protoObj);
  if (!obj) {
    return false;
  }
  WriteNightOut(top, JS::ObjectValue(*obj).asRawBits());
  return true;
}

// `SetFunName`: set the inferred `name` on the anonymous function `fun` under
// the FunctionPrefixKind byte. May GC/throw. Leaves `fun` on the stack.
bool night_runtime_set_fun_name(JSContext* cx, uint32_t top, uint64_t fun,
                                uint64_t name, uint32_t prefixKind) {
  SetNightTop(cx, top);
  JS::RootedFunction f(
      cx, &JS::Value::fromRawBits(fun).toObject().as<JSFunction>());
  JS::RootedValue nameVal(cx, JS::Value::fromRawBits(name));
  return js::SetFunctionName(cx, f, nameVal,
                             static_cast<js::FunctionPrefixKind>(prefixKind));
}

int32_t night_runtime_slots_covered(uint32_t obj, uint32_t n) {
  JSObject* o = reinterpret_cast<JSObject*>(uintptr_t(obj));
  return js::night::NightSlotsCovered(&o->as<js::NativeObject>(), n) ? 1 : 0;
}

// Mapped-arguments formal access: once a mapped args object exists it is the
// canonical location for the formals (the interpreter's GetArg/SetArg go
// through it when argsObjAliasesFormals()); the AOT body mirrors that via
// these leaves. arg() is a raw data read; setArg runs the GCPtr barriers.
uint64_t night_runtime_get_mapped_arg(uint64_t objBits, uint32_t i) {
  js::ArgumentsObject& obj =
      JS::Value::fromRawBits(objBits).toObject().as<js::ArgumentsObject>();
  return obj.arg(i).asRawBits();
}

void night_runtime_set_mapped_arg(uint64_t objBits, uint32_t i, uint64_t val) {
  js::ArgumentsObject& obj =
      JS::Value::fromRawBits(objBits).toObject().as<js::ArgumentsObject>();
  obj.setArg(i, JS::Value::fromRawBits(val));
}

bool night_runtime_in(JSContext* cx, uint32_t top, uint64_t id,
                      uint64_t objBits) {
  SetNightTop(cx, top);
  JS::RootedValue rref(cx, JS::Value::fromRawBits(objBits));
  JS::RootedValue lref(cx, JS::Value::fromRawBits(id));
  if (!rref.isObject()) {
    js::ReportInNotObjectError(cx, lref, rref);
    return false;
  }
  JS::RootedObject obj(cx, &rref.toObject());
  JS::RootedId key(cx);
  if (!JS_ValueToId(cx, lref, &key)) {
    return false;
  }
  bool found;
  if (!js::HasProperty(cx, obj, key, &found)) {
    return false;
  }
  WriteNightOut(top, JS::BooleanValue(found).asRawBits());
  return true;
}

// The has-own rows: the mega get table's third key namespace, `atomPtr | 2`
// (the property rows hold small atom ids, the element rows `atomPtr | 1`),
// whose slotEnc is 1 when the receiver has the property as its own and 0
// when it does not. The receiver's shape pins that for a native object
// without a resolve hook that could define the key and a key that is a
// non-index atom (the shape does not pin dense elements, nor a typed
// array's canonical numeric strings). The compiled `hasOwn` probes them.
static bool HasOwnRow(JSContext* cx, const JS::Value& v, const JS::Value& k,
                      bool* found) {
  JS::AutoCheckCannotGC nogc;
  uint32_t idx;
  if (!v.isObject() || !k.isString() || !k.toString()->isAtom() ||
      k.toString()->asAtom().isIndex(&idx)) {
    return false;
  }
  JSObject* obj = &v.toObject();
  if (!obj->is<js::NativeObject>() || obj->is<js::TypedArrayObject>() ||
      obj->getOpsLookupProperty()) {
    return false;
  }
  js::NativeObject* nobj = &obj->as<js::NativeObject>();
  JSAtom* atom = &k.toString()->asAtom();
  jsid id = JS::PropertyKey::NonIntAtom(atom);
  if (js::ClassMayResolveId(cx->names(), nobj->getClass(), id, nobj)) {
    return false;
  }
  *found = nobj->lookupPure(id).isSome();
  uint32_t key = uint32_t(reinterpret_cast<uintptr_t>(atom)) | 2u;
  if (key > RtNames(cx).atoms.size()) {
    uint32_t shape = js::night::NightObjectShape(nobj);
    MegaGetEntry& e = *MegaGet(cx, shape, key);
    e.shape = 0;
    e.atomId = key;
    e.holderPtr = 0;
    e.holderShape = shape;
    e.slotEnc = *found ? 1 : 0;
    e.pad = 0;
    e.shape = shape;
  }
  return true;
}

bool night_runtime_has_own(JSContext* cx, uint32_t top, uint64_t id,
                           uint64_t val) {
  SetNightTop(cx, top);
  {
    bool found;
    if (HasOwnRow(cx, JS::Value::fromRawBits(val), JS::Value::fromRawBits(id),
                  &found)) {
      WriteNightOut(top, JS::BooleanValue(found).asRawBits());
      return true;
    }
  }
  JS::RootedValue v(cx, JS::Value::fromRawBits(val));
  JS::RootedValue idv(cx, JS::Value::fromRawBits(id));
  bool found;
  if (!js::HasOwnProperty(cx, v, idv, &found)) {
    return false;
  }
  WriteNightOut(top, JS::BooleanValue(found).asRawBits());
  return true;
}

bool night_runtime_to_property_key(JSContext* cx, uint32_t top, uint64_t val) {
  SetNightTop(cx, top);
  JS::RootedValue v(cx, JS::Value::fromRawBits(val));
  JS::RootedValue out(cx);
  if (!js::ToPropertyKeyOperation(cx, v, &out)) {
    return false;
  }
  WriteNightOut(top, out.get().asRawBits());
  return true;
}

bool night_runtime_del_elem(JSContext* cx, uint32_t top, uint64_t val,
                            uint64_t key, uint32_t strict) {
  SetNightTop(cx, top);
  JS::RootedValue v(cx, JS::Value::fromRawBits(val));
  JS::RootedValue k(cx, JS::Value::fromRawBits(key));
  bool res = false;
  // Fused globals: computed-key delete on the global blows the key's fuse
  // (see BlowGnameFuseKey).
  if (v.isObject() && IsActiveGlobal(&v.toObject())) {
    JS::RootedId did(cx);
    if (JS_ValueToId(cx, k, &did)) {
      BlowGnameFuseKey(did);
      BlowBindingFuseKey(did);
    } else {
      JS_ClearPendingException(cx);
      BlowAllGnameFuses();
      BlowAllBindingFuses();
    }
  }
  bool ok = strict ? js::DelElemOperation<true>(cx, v, k, &res)
                   : js::DelElemOperation<false>(cx, v, k, &res);
  if (!ok) {
    return false;
  }
  WriteNightOut(top, JS::BooleanValue(res).asRawBits());
  return true;
}

bool night_runtime_global_this(JSContext* cx, uint32_t top) {
  SetNightTop(cx, top);
  JSObject* thisObj = cx->global()->lexicalEnvironment().thisObject();
  WriteNightOut(top, JS::ObjectValue(*thisObj).asRawBits());
  return true;
}

// Sloppy `FunctionThis` slow arm: null/undefined -> the global `this`,
// primitive -> its wrapper object. The inline fast arm already handled
// object-tagged `this`.
bool night_runtime_box_nonstrict_this(JSContext* cx, uint32_t top,
                                      uint64_t thisv) {
  SetNightTop(cx, top);
  JS::RootedValue v(cx, JS::Value::fromRawBits(thisv));
  JSObject* obj = js::BoxNonStrictThis(cx, v);
  if (!obj) {
    return false;
  }
  WriteNightOut(top, JS::ObjectValue(*obj).asRawBits());
  return true;
}

bool night_runtime_regexp(JSContext* cx, uint32_t top, void* script,
                          uint32_t index) {
  SetNightTop(cx, top);
  JSScript* s = reinterpret_cast<JSScript*>(script);
  JS::Rooted<js::RegExpObject*> re(
      cx, &s->getRegExp(js::GCThingIndex(index))->as<js::RegExpObject>());
  JSObject* obj = js::CloneRegExpObject(cx, re);
  if (!obj) {
    return false;
  }
  WriteNightOut(top, JS::ObjectValue(*obj).asRawBits());
  return true;
}

// Define an accessor property (getter or setter, per `kind` bit0) named `id` on
// `o` from the function `f`; `kind` bit1 selects a hidden (non-enumerable)
// property. Shared tail of the InitProp/InitElem getter-setter helpers.
static bool DefineAccessorFromKind(JSContext* cx, JS::HandleObject o,
                                   JS::HandleId id, JS::HandleObject f,
                                   uint32_t kind) {
  unsigned attrs = (kind & 2) ? 0 : JSPROP_ENUMERATE;
  JS::RootedObject getter(cx);
  JS::RootedObject setter(cx);
  if (kind & 1) {
    setter = f;
  } else {
    getter = f;
  }
  return js::DefineAccessorProperty(cx, o, id, getter, setter, attrs);
}

bool night_runtime_init_prop_getset(JSContext* cx, uint32_t top, uint64_t obj,
                                    uint32_t atomId, uint64_t fn,
                                    uint32_t kind) {
  SetNightTop(cx, top);
  JS::RootedId id(cx, AtomIdChecked(cx, atomId));
  JS::RootedObject o(cx, &JS::Value::fromRawBits(obj).toObject());
  JS::RootedObject f(cx, &JS::Value::fromRawBits(fn).toObject());
  return DefineAccessorFromKind(cx, o, id, f, kind);
}

// `InitElemGetter`/`InitElemSetter` (+Hidden forms): define an accessor with a
// computed key (mirrors js::InitElemGetterSetterOperation). `kind` bit0 =
// setter, bit1 = hidden (non-enumerable). May GC/throw (ToPropertyKey).
bool night_runtime_init_elem_getset(JSContext* cx, uint32_t top, uint64_t obj,
                                    uint64_t key, uint64_t fn, uint32_t kind) {
  SetNightTop(cx, top);
  JS::RootedObject o(cx, &JS::Value::fromRawBits(obj).toObject());
  JS::RootedValue keyv(cx, JS::Value::fromRawBits(key));
  JS::RootedObject f(cx, &JS::Value::fromRawBits(fn).toObject());
  JS::RootedId id(cx);
  if (!js::ToPropertyKey(cx, keyv, &id)) {
    return false;
  }
  return DefineAccessorFromKind(cx, o, id, f, kind);
}

// `CheckPrivateField`: private brand/presence check (mirrors the interpreter's
// CheckPrivateFieldOperation). `cond`/`kind` are the ThrowCondition and
// ThrowMsgKind immediate bytes. Writes the presence bool to the out-slot;
// throws per the ThrowCondition. May GC.
bool night_runtime_check_private_field(JSContext* cx, uint32_t top,
                                       uint64_t obj, uint64_t key,
                                       uint32_t cond, uint32_t kind) {
  SetNightTop(cx, top);
  JS::RootedValue val(cx, JS::Value::fromRawBits(obj));
  JS::RootedValue idval(cx, JS::Value::fromRawBits(key));
  js::ThrowCondition condition = static_cast<js::ThrowCondition>(cond);
  js::ThrowMsgKind msgKind = static_cast<js::ThrowMsgKind>(kind);

  if (condition == js::ThrowCondition::OnlyCheckRhs) {
    if (!val.isObject()) {
      js::ReportInNotObjectError(cx, idval, val);
      return false;
    }
  }

  if (condition == js::ThrowCondition::ThrowHas) {
    if (JS::EnsureCanAddPrivateElementOp op =
            cx->runtime()->canAddPrivateElement) {
      if (!op(cx, val)) {
        return false;
      }
    }
  }

  bool result = false;
  if (!js::HasOwnProperty(cx, val, idval, &result)) {
    return false;
  }

  bool willThrow = (condition == js::ThrowCondition::ThrowHasNot && !result) ||
                   (condition == js::ThrowCondition::ThrowHas && result);
  if (willThrow) {
    JS_ReportErrorNumberASCII(cx, js::GetErrorMessage, nullptr,
                              js::ThrowMsgKindToErrNum(msgKind));
    return false;
  }

  WriteNightOut(top, JS::BooleanValue(result).asRawBits());
  return true;
}

// `NewPrivateName atomId`: create a fresh private-name symbol whose description
// is the atom `atomId` (mirrors the interpreter's NewPrivateName). May GC.
bool night_runtime_new_private_name(JSContext* cx, uint32_t top,
                                    uint32_t atomId) {
  SetNightTop(cx, top);
  // Atomize the chars directly: the description can be an index-like atom
  // (a private BRAND symbol is described by the inferred class name, e.g.
  // "0" for `{0: class { #m() {} }}`), which AtomIdChecked would have
  // interned as an INT PropertyKey with no atom to recover.
  if (atomId >= RtNames(cx).atoms.size()) {
    MOZ_CRASH("night_runtime_new_private_name: atomId out of range");
  }
  const std::u16string& s = RtNames(cx).atoms[atomId];
  JS::Rooted<JSString*> desc(cx, JS_AtomizeUCStringN(cx, s.data(), s.size()));
  if (!desc) {
    return false;
  }
  JS::Symbol* sym =
      JS::Symbol::new_(cx, JS::SymbolCode::PrivateNameSymbol, desc);
  if (!sym) {
    return false;
  }
  WriteNightOut(top, JS::SymbolValue(sym).asRawBits());
  return true;
}

// JS ToBoolean: a pure structural test on the value, so this is a leaf (no
// rooting/err handshake on the caller side).
int32_t night_runtime_to_boolean(JSContext* cx, uint64_t a) {
  JS::RootedValue v(cx, JS::Value::fromRawBits(a));
  return JS::ToBoolean(v) ? 1 : 0;
}

// `typeof a`: the type string (a pinned common atom). Leaf (no GC/throw).
uint64_t night_runtime_typeof(JSContext* cx, uint64_t a) {
  return js::night::NightTypeof(cx, a);
}

// Fused `typeof a CMP "type"` (`TypeofEq`). The operand byte mirrors
// js::TypeofEqOperand: low bits = JSType, bit 0x80 = `!==`. Infallible leaf.
int32_t night_runtime_typeof_eq(JSContext* cx, uint64_t a, uint32_t operand) {
  JSType type = JSType(operand & 0x7f);
  bool eq = js::TypeOfValue(JS::Value::fromRawBits(a)) == type;
  bool neq = (operand & 0x80) != 0;
  return (eq != neq) ? 1 : 0;
}

// Arm MIR's regexp arm for `re` (see Night_strlitRegExpShapeOff): the
// optimizable shape and the row of re's shared, so a later exec/test of it
// that does not match runs its matcher with no call here.
static void ArmRegExpLeaf(JSContext* cx, uint64_t re) {
  uint32_t base = RtState(cx).strLitBase;
  uint32_t shape, shared, l1, tb;
  if (!base || !js::NightRegExpLeafRow(cx, JS::Value::fromRawBits(re), &shape,
                                       &shared, &l1, &tb)) {
    return;
  }
  *LinMem<uint32_t>(base + js::night::Night_strlitRegExpShapeOff) = shape;
  js::night::NightRegexLeafBlock& blk = js::night::NightData(cx).regexLeaf;
  js::night::NightRegexLeafRow& row =
      blk.rows[(shared >> 4) & (js::night::Night_regexLeafRows - 1)];
  row.shared = shared;
  row.latin1Idx = l1;
  row.twobyteIdx = tb;
}

uint64_t night_runtime_regexp_leaf(JSContext* cx, uint64_t re, uint64_t str,
                                   uint32_t forTest) {
  JS::Value out;
  int r = js::NightRegExpLeaf(cx, JS::Value::fromRawBits(re),
                              JS::Value::fromRawBits(str), forTest != 0, &out);
  ArmRegExpLeaf(cx, re);
  if (r == 1) {
    return out.asRawBits();
  }
  return JS::MagicValue(JS_GENERIC_MAGIC).asRawBits();
}

// Strict-equality of `a` against an immediate constant (`StrictConstantEq`).
// Infallible leaf; the translator negates for the `Ne` form.
int32_t night_runtime_constant_strict_eq(JSContext* cx, uint64_t a,
                                         uint32_t operand) {
  return js::ConstantStrictEqual(JS::Value::fromRawBits(a), uint16_t(operand))
             ? 1
             : 0;
}

// Both operands are strings (the compiled arm proved the tags). ConcatStrings
// builds a rope (or copies into an inline string when both sides are already
// linear and short): it allocates but runs no user code and writes no
// pre-existing heap, which is what admits the quiet-alloc classification --
// the compiled continuation keeps its facts and its track across this call.
bool night_runtime_concat(JSContext* cx, uint32_t top, uint64_t a, uint64_t b) {
  SetNightTop(cx, top);
  JS::Value av = JS::Value::fromRawBits(a);
  JS::Value bv = JS::Value::fromRawBits(b);
  MOZ_ASSERT(av.isString() && bv.isString());
  JS::RootedString lstr(cx, av.toString());
  JS::RootedString rstr(cx, bv.toString());
  JSString* res = js::ConcatStrings<js::CanGC>(cx, lstr, rstr);
  if (!res) {
    return false;
  }
  WriteNightOut(top, JS::StringValue(res).asRawBits());
  return true;
}

bool night_runtime_add(JSContext* cx, uint32_t top, uint64_t a, uint64_t b) {
  SetNightTop(cx, top);
  // String + string is the dominant non-numeric `+` population (the inline
  // arms cover numeric operands): concat directly, skipping AddValues'
  // ToPrimitive/ToNumeric dispatch on both operands.
  {
    JS::Value av = JS::Value::fromRawBits(a);
    JS::Value bv = JS::Value::fromRawBits(b);
    if (av.isString() && bv.isString()) {
      JS::RootedString lstr(cx, av.toString());
      JS::RootedString rstr(cx, bv.toString());
      JSString* res = js::ConcatStrings<js::CanGC>(cx, lstr, rstr);
      if (!res) {
        return false;
      }
      WriteNightOut(top, JS::StringValue(res).asRawBits());
      return true;
    }
  }
  // Generic JS `+` (numeric add or string concat; may GC, may throw).
  JS::RootedValue lhs(cx, JS::Value::fromRawBits(a));
  JS::RootedValue rhs(cx, JS::Value::fromRawBits(b));
  JS::RootedValue res(cx);
  if (!js::AddValues(cx, &lhs, &rhs, &res)) {
    return false;
  }
  WriteNightOut(top, res.get().asRawBits());
  return true;
}

bool night_runtime_call_iter(JSContext* cx, uint32_t top, uint32_t sp,
                             uint32_t argc) {
  JS::Value* frame = LinMem<JS::Value>(sp);
  if (frame[0].isPrimitive()) {
    SetNightTop(cx, top);
    JS::RootedValue iterable(cx, frame[1]);
    // No bytecode frame to decompile the expression from; without a
    // fallback the reporter would source the object itself, which calls a
    // user-defined `toSource`. Name the class instead.
    JS::RootedString fallback(cx);
    if (iterable.isObject()) {
      fallback = JS_NewStringCopyZ(cx, iterable.toObject().getClass()->name);
      if (!fallback) {
        return false;
      }
    }
    js::ReportValueError(cx, JSMSG_NOT_ITERABLE, JSDVG_IGNORE_STACK, iterable,
                         fallback);
    return false;
  }
  return night_runtime_call(cx, top, sp, argc);
}

bool night_runtime_call(JSContext* cx, uint32_t top, uint32_t sp,
                        uint32_t argc) {
  SetNightTop(cx, top);
  // The frame at `sp` is [callee, this, arg0..arg_{argc-1}] as boxed Values
  // (rooted: `top` covers it). Invoke via the engine call path (which itself
  // dispatches to AOT/interpreter/native).
  JS::Value* frame = LinMem<JS::Value>(sp);
  // Native fast path: the frame is already a valid `vp` array rooted in the
  // AOT scan region, so a C++ native can run on it in place -- no arg copy,
  // no InternalCall dispatch on the hot JS::Call round trips.
  // Mirrors CallJSNative minus debugger hooks (none in the reactor).
  if (frame[0].isObject() && frame[0].toObject().is<JSFunction>()) {
    JSFunction* fun = &frame[0].toObject().as<JSFunction>();
    // defineProperty-family redefinition of a global binding bypasses
    // every compiled write hook -- blow the targeted fuse first. Checked by
    // FUNCTION IDENTITY before the native dispatch below: these definers can
    // be SELF-HOSTED JS (isNativeFun() false), in which case the call
    // proceeds via JS::Call -- the fuse blow must not depend on native-ness.
    if (MOZ_UNLIKELY(
            (RtFns(cx).defineProperty &&
             frame[0].asRawBits() == RtFns(cx).defineProperty->get().asRawBits()) ||
            (RtFns(cx).reflectDefineProperty &&
             frame[0].asRawBits() ==
                 RtFns(cx).reflectDefineProperty->get().asRawBits()))) {
      if (argc >= 2 && frame[2].isObject() &&
          IsActiveGlobal(&frame[2].toObject())) {
        JS::RootedId defId(cx);
        JS::RootedValue defKey(cx, frame[3]);
        if (JS_ValueToId(cx, defKey, &defId)) {
          BlowBindingFuseKey(defId);
          BlowGnameFuseKey(defId);
        } else {
          JS_ClearPendingException(cx);
          BlowAllBindingFuses();
          BlowAllGnameFuses();
        }
      } else if (argc >= 3 && frame[2].isObject() && frame[3].isString() &&
                 frame[3].toString()->isAtom() &&
                 frame[0].asRawBits() ==
                     RtFns(cx).defineProperty->get().asRawBits()) {
        // A define on a stamped object that leaves its TYPES true keeps
        // the bit (`DefineKeepsTypes`), as a vouched set does.
        JSObject* target = &frame[2].toObject();
        JS::PropertyKey key =
            js::AtomToId(&frame[3].toString()->asAtom());
        if (DefineKeepsTypes(cx, target, key, frame[4])) {
          AutoVouchedStore v(true);
          JS::RootedValue rval(cx);
          JS::HandleValueArray args =
              JS::HandleValueArray::fromMarkedLocation(argc, frame + 2);
          JS::RootedValue fval(cx, frame[0]);
          JS::RootedValue thisv(cx, frame[1]);
          if (!JS::Call(cx, thisv, fval, args, &rval)) {
            return false;
          }
          WriteNightOut(top, rval.get().asRawBits());
          return true;
        }
      }
    } else if (MOZ_UNLIKELY(RtFns(cx).defineProperties &&
                            frame[0].asRawBits() ==
                                RtFns(cx).defineProperties->get().asRawBits())) {
      if (argc >= 1 && frame[2].isObject() &&
          IsActiveGlobal(&frame[2].toObject())) {
        BlowAllBindingFuses();
        BlowAllGnameFuses();
      }
    }
    // RegExp.prototype.exec/.test fast path (self-hosted, so it does NOT take
    // the native branch below). Guard by callee identity + an optimizable
    // RegExpObject `this` + a string arg; dispatch the engine's JIT exec/test
    // directly, bypassing the interpreted self-hosted frame. The identity
    // guard means an instance-level `.exec` override still takes the generic
    // path (its callee would not match this cell).
    if (MOZ_UNLIKELY(RtFns(cx).regExpExec || RtFns(cx).regExpTest)) {
      bool isExec = RtFns(cx).regExpExec &&
                    frame[0].asRawBits() == RtFns(cx).regExpExec->get().asRawBits();
      bool isTest = RtFns(cx).regExpTest &&
                    frame[0].asRawBits() == RtFns(cx).regExpTest->get().asRawBits();
      // The FromJit entries assume a non-negative int32 lastIndex (the JIT
      // guards it before taking them). Anything else must run the
      // self-hosted path, which applies ToLength (side effects + clamping).
      // RegExpBuiltinExec reads lastIndex for every regexp, so a non-number
      // value is observable even when the regexp is neither global nor
      // sticky and the value itself is ignored.
      auto lastIndexOk = [](JSObject* obj) {
        js::RegExpObject* re = &obj->as<js::RegExpObject>();
        JS::Value li = re->getLastIndex();
        if (!re->isGlobalOrSticky()) {
          return li.isNumber();
        }
        return li.isInt32() && li.toInt32() >= 0;
      };
      if ((isExec || isTest) && argc >= 1 && frame[2].isString() &&
          frame[1].isObject() && frame[1].toObject().is<js::RegExpObject>() &&
          js::IsOptimizableRegExpObject(&frame[1].toObject(), cx) &&
          lastIndexOk(&frame[1].toObject())) {
        js::AutoCheckRecursionLimit recursion(cx);
        if (!recursion.check(cx)) {
          return false;
        }
        // Collapsed one-frame path when the regex has an AOT wasm matcher:
        // matcher + lazy statics + lastIndex, no result object for test().
        if (js::night::NightData(cx).regexTableCount != 0) {
          bool handled = false;
          if (!js::NightRegExpExecTestFast(cx, frame, isTest, &handled)) {
            return false;
          }
          if (handled) {
            WriteNightOut(top, frame[0].asRawBits());
            return true;
          }
        }
        JS::Rooted<js::RegExpObject*> re(
            cx, &frame[1].toObject().as<js::RegExpObject>());
        JS::RootedString input(cx, frame[2].toString());
        if (isTest) {
          bool result = false;
          if (!js::RegExpBuiltinExecTestFromJit(cx, re, input, &result)) {
            return false;
          }
          WriteNightOut(top, JS::BooleanValue(result).asRawBits());
          return true;
        }
        JS::RootedValue out(cx);
        if (!js::RegExpBuiltinExecMatchFromJit(cx, re, input, nullptr, &out)) {
          return false;
        }
        WriteNightOut(top, out.asRawBits());
        return true;
      }
    }
    if (fun->isNativeFun()) {
      js::AutoCheckRecursionLimit recursion(cx);
      if (!recursion.check(cx)) {
        return false;
      }
      // apply/call forwarding: dispatch a compiled AOT target directly.
      JSNative native = fun->native();
      if (native == js::fun_apply || native == js::fun_call) {
        JS::Value thisArg = argc >= 1 ? frame[2] : JS::UndefinedValue();
        uint64_t rv = 0;
        js::night::EnterNightStatus st;
        if (native == js::fun_apply) {
          JS::Value arrv = argc >= 2 ? frame[3] : JS::UndefinedValue();
          st = js::night::NightApplyOrCall(cx, frame[1], thisArg, nullptr, 0,
                                           &arrv, &rv);
        } else {
          uint32_t fwd = argc >= 1 ? argc - 1 : 0;
          st = js::night::NightApplyOrCall(cx, frame[1], thisArg, frame + 3,
                                           fwd, nullptr, &rv);
        }
        if (st == js::night::EnterNightStatus::Ok) {
          WriteNightOut(top, rv);
          return true;
        }
        if (st == js::night::EnterNightStatus::Error) {
          return false;
        }
        // NotEntered: fall through to the generic native call.
      }
      // A char-access method on a rope receiver: flatten once so every later
      // call takes the compiled inline arm (the native reads ropes without
      // flattening, so the arm's linear guard would miss forever). Mirrors
      // CacheIR's LinearizeForCharAccess.
      if (IsRopeCharAccess(cx, frame[0], frame[1])) {
        if (!frame[1].toString()->ensureLinear(cx)) {
          return false;
        }
      }
      // Re-derive from the rooted frame slot: the flatten above (and the
      // defineProperty intercept's JS_ValueToId) can GC-move the function.
      fun = &frame[0].toObject().as<JSFunction>();
      js::AutoRealm ar(cx, fun);
      if (!fun->native()(cx, argc, frame)) {
        return false;
      }
      WriteNightOut(top, frame[0].asRawBits());
      return true;
    }
  }
  JS::RootedValue callee(cx, frame[0]);
  JS::RootedValue thisv(cx, frame[1]);
  JS::RootedValueVector args(cx);
  if (!args.reserve(argc)) {
    return false;
  }
  for (uint32_t i = 0; i < argc; i++) {
    args.infallibleAppend(frame[2 + i]);
  }
  JS::RootedValue rval(cx);
  if (!JS::Call(cx, thisv, callee, JS::HandleValueArray(args), &rval)) {
    return false;
  }
  WriteNightOut(top, rval.get().asRawBits());
  return true;
}

// Lean native dispatch for the String.prototype direct-dispatch arms: the
// callee at frame[0] was proved a pristine builtin native by a callee-identity
// cell, so run it directly on the in-place `vp` frame (rooted by `top`) --
// mirrors night_runtime_call's native tail without the classify / apply-call /
// RegExp / rope-flatten / tracing branches.
bool night_runtime_native_dispatch(JSContext* cx, uint32_t top, uint32_t sp,
                                   uint32_t argc) {
  SetNightTop(cx, top);
  JS::Value* frame = LinMem<JS::Value>(sp);
  JSFunction* fun = &frame[0].toObject().as<JSFunction>();
  // Defensive: cells are only armed for natives, but never call a non-native
  // native() -- fall back to the generic path (also handles apply/call/etc).
  if (MOZ_UNLIKELY(!fun->isNativeFun())) {
    return night_runtime_call(cx, top, sp, argc);
  }
  // fun_apply/fun_call want night_runtime_call's AOT-forwarding fast arms.
  JSNative native = fun->native();
  if (MOZ_UNLIKELY(native == js::fun_apply || native == js::fun_call)) {
    return night_runtime_call(cx, top, sp, argc);
  }
  // The defineProperty family must run night_runtime_call's binding-fuse blow
  // intercept (a global-binding redefinition bypasses every compiled write
  // hook otherwise).
  if (MOZ_UNLIKELY(
          (RtFns(cx).defineProperty &&
           frame[0].asRawBits() == RtFns(cx).defineProperty->get().asRawBits()) ||
          (RtFns(cx).reflectDefineProperty &&
           frame[0].asRawBits() ==
               RtFns(cx).reflectDefineProperty->get().asRawBits()) ||
          (RtFns(cx).defineProperties &&
           frame[0].asRawBits() == RtFns(cx).defineProperties->get().asRawBits()))) {
    return night_runtime_call(cx, top, sp, argc);
  }
  // RegExpMatcher/RegExpSearcher with an AOT wasm matcher: run the collapsed
  // fast path (matcher call + statics + result in one frame), skipping the
  // Matcher/Impl/ExecuteRegExp/execute stack. Unhandled falls through to the
  // ordinary native invoke below.
  if ((native == js::RegExpMatcher || native == js::RegExpSearcher) &&
      js::night::NightData(cx).regexTableCount != 0) {
    bool handled = false;
    if (!js::NightRegExpBuiltinFast(cx, frame, argc,
                                    native == js::RegExpSearcher, &handled)) {
      return false;
    }
    if (handled) {
      WriteNightOut(top, frame[0].asRawBits());
      return true;
    }
  }
  // Char-access method on a rope receiver: flatten once so later calls take
  // the compiled inline arm (mirrors the night_runtime_call arm; see there).
  if (MOZ_UNLIKELY(IsRopeCharAccess(cx, frame[0], frame[1]))) {
    if (!frame[1].toString()->ensureLinear(cx)) {
      return false;
    }
    fun = &frame[0].toObject().as<JSFunction>();
  }
  // Array.prototype.push dense arm for the shapes the compiled inline arm
  // does not cover (argc >= 2; multi-element pushes). Same guard set as
  // the wasm arm (identity, Array clasp, append-safe flags, len ==
  // initializedLength, and no possibly-indexed proto chain: push is
  // `Set(O, len, v)`, which a proto indexed accessor/non-writable element
  // intercepts); setOrExtendDenseElements handles growth, barriers, and
  // the length update, and reports Incomplete for anything odd -> generic.
  if (MOZ_UNLIKELY(frame[0].asRawBits() == RtState(cx).pushFnBits) &&
      RtState(cx).pushFnBits && argc >= 1 && frame[1].isObject() &&
      frame[1].toObject().is<js::ArrayObject>()) {
    auto* arr = &frame[1].toObject().as<js::ArrayObject>();
    uint32_t initlen = arr->getDenseInitializedLength();
    uint32_t len = arr->length();
    if (len == initlen && arr->lengthIsWritable() && arr->isExtensible() &&
        !arr->getElementsHeader()->isSealed() && NoExtraIndexedFast(cx, arr) &&
        uint64_t(len) + argc <= uint64_t(INT32_MAX)) {
      // Rooted: the extend path can GC-move the receiver, and the append
      // row must be primed with the LIVE object.
      JS::Rooted<js::ArrayObject*> rarr(cx, arr);
      js::DenseElementResult r =
          rarr->setOrExtendDenseElements(cx, len, &frame[2], argc);
      if (r == js::DenseElementResult::Failure) {
        return false;
      }
      if (r == js::DenseElementResult::Success) {
        if (RtEnv(cx).appendCachePtr) {
          PrimeAppendRow(cx, rarr);
        }
        WriteNightOut(top, JS::Int32Value(int32_t(len + argc)).asRawBits());
        return true;
      }
    }
  }
  js::AutoCheckRecursionLimit recursion(cx);
  if (!recursion.check(cx)) {
    return false;
  }
  // A native of this realm (the common case) runs with no realm switch.
  if (MOZ_LIKELY(fun->realm() == cx->realm())) {
    if (!native(cx, argc, frame)) {
      return false;
    }
  } else {
    js::AutoRealm ar(cx, fun);
    if (!fun->native()(cx, argc, frame)) {
      return false;
    }
  }
  WriteNightOut(top, frame[0].asRawBits());
  return true;
}

// Compile-time-recognized `T.apply(thisArg, arguments)` super-call forward.
// The site proved (per-script) that `arguments` is ONLY
// forwarded -- never modified/aliased -- and the function is non-strict, so the
// caller's live actuals at `callerSp[2..]` ARE the arguments elements: no
// arguments object is built. Fast path: enter T's compiled AOT body directly
// with the forwarded actuals (NightApplyOrCall's argv path). Fallback (T not
// compiled, or `.apply` overridden): faithfully reconstruct
// `applyFn.call(T, thisArg, argsObj)` with a rebuilt arguments object so the
// pathological cases keep exact semantics.
bool night_runtime_apply_fwd(JSContext* cx, uint32_t top, uint64_t applyFnBits,
                             uint64_t targetBits, uint64_t thisBits,
                             uint32_t callerSp, uint32_t callerArgc) {
  SetNightTop(cx, top);
  JS::Value* callerFrame = LinMem<JS::Value>(callerSp);
  JS::Value* actuals = callerFrame + 2;
  JS::Value applyFn = JS::Value::fromRawBits(applyFnBits);
  bool isApply = false;
  if (applyFn.isObject() && applyFn.toObject().is<JSFunction>()) {
    JSFunction* f = &applyFn.toObject().as<JSFunction>();
    if (f->isNativeFun() && f->native() == js::fun_apply) {
      isApply = true;
    }
  }
  if (isApply) {
    JS::Value targetv = JS::Value::fromRawBits(targetBits);
    JS::Value thisv = JS::Value::fromRawBits(thisBits);
    uint64_t rv = 0;
    js::night::EnterNightStatus st = js::night::NightApplyOrCall(
        cx, targetv, thisv, actuals, callerArgc, nullptr, &rv);
    if (st == js::night::EnterNightStatus::Ok) {
      WriteNightOut(top, rv);
      return true;
    }
    if (st == js::night::EnterNightStatus::Error) {
      return false;
    }
    // NotEntered: fall through to the faithful generic reconstruction.
  }
  // Root the three raw-bit values BEFORE the arguments-object allocation
  // below (it can GC and move them).
  JS::RootedValue applyv(cx, applyFn);
  JS::RootedValue targetv(cx, JS::Value::fromRawBits(targetBits));
  JS::RootedValue thisv(cx, JS::Value::fromRawBits(thisBits));
  uint64_t argsObjBits = 0;
  if (!js::night::NightArguments(cx, callerFrame[0].asRawBits(), actuals,
                                 callerArgc, &argsObjBits)) {
    return false;
  }
  JS::RootedValue argsObj(cx, JS::Value::fromRawBits(argsObjBits));
  JS::RootedValueVector callArgs(cx);
  if (!callArgs.reserve(2)) {
    return false;
  }
  callArgs.infallibleAppend(thisv);
  callArgs.infallibleAppend(argsObj);
  JS::RootedValue rval(cx);
  // `T.apply(thisArg, argsObj)` == invoke `applyFn` with this = T.
  if (!JS::Call(cx, targetv, applyv, JS::HandleValueArray(callArgs), &rval)) {
    return false;
  }
  WriteNightOut(top, rval.get().asRawBits());
  return true;
}

// Generic `new`. The frame at `sp` is `[callee, this_placeholder,
// arg0.., newTarget]`. For a sized site (`nSlots` is the predicted fixed-slot
// count) the engine half creates an empty `this` with enough fixed slots and
// constructs on it directly (no CreateThis hook, no global state -- `N` flows
// straight in); otherwise it is an ordinary construct. The result is written
// to the out-slot at `top`.
bool night_runtime_construct(JSContext* cx, uint32_t top, uint32_t sp,
                             uint32_t argc, uint32_t nSlots,
                             uint32_t stampWord) {
  SetNightTop(cx, top);
#ifdef ENABLE_JS_NIGHTMONKEY
  return js::night::NightConstruct(cx, LinMem<void>(sp), argc, nSlots,
                                   stampWord, LinMem<uint64_t>(top));
#else
  (void)sp;
  (void)argc;
  (void)nSlots;
  (void)stampWord;
  return false;
#endif
}

// Fill construct cell `cellAddr` from a fresh `this` made for `callee`
// (see `night_runtime_create_this`).
static void FillConstructCell(JSContext* cx, uint32_t cellAddr, uint64_t out,
                              uint64_t calleeBits) {
  if (!cellAddr) {
    return;
  }
  JS::Value ov = JS::Value::fromRawBits(out);
  JS::Value cv = JS::Value::fromRawBits(calleeBits);
  auto* cell = LinMem<js::night::NightConstructCell>(cellAddr);
  if (ov.isObject() && cv.isObject() && cv.toObject().is<JSFunction>() &&
      js::night::NightFillAllocCellObject(&cell->alloc, &ov.toObject())) {
    JSObject* thisObj = &ov.toObject();
    JS::RootedObject callee(cx, &cv.toObject());
    uint32_t recvShape, holderPtr, holderShape, slotEnc;
    JS::PropertyKey protoKey = js::NameToId(cx->names().prototype);
    if (js::night::NightPopulateInlineGetIC(cx, callee, protoKey, &recvShape,
                                            &holderPtr, &holderShape,
                                            &slotEnc) &&
        holderPtr == 0) {
      cell->protoPtr =
          uint32_t(reinterpret_cast<uintptr_t>(thisObj->staticPrototype()));
      cell->protoSlotEnc = slotEnc;
      cell->gen = RtEnv(cx).propicGenPtr ? InlineGen(cx) : 0;
      // The ctor shape arms the guard, so it is written last.
      cell->ctorShape =
          uint32_t(reinterpret_cast<uintptr_t>(callee->shape()));
    }
  }
}

// Direct construct: create `this` for a specialized `new`; writes the boxed
// object to the out-slot at `top`. May GC (allocates) -> the caller uses the
// rooting handshake.
bool night_runtime_create_this(JSContext* cx, uint32_t top, uint64_t calleeBits,
                               uint64_t newTargetBits, uint32_t nSlots,
                               uint32_t cellAddr, uint32_t stampWord) {
  SetNightTop(cx, top);
#ifdef ENABLE_JS_NIGHTMONKEY
  uint64_t out = 0;
  if (!js::night::NightCreateThis(cx, calleeBits, newTargetBits, nSlots, &out,
                                  stampWord)) {
    return false;
  }
  // Populate the per-site construct cell so subsequent `new C()` at this site
  // nursery-bumps `this` inline. Only when `this` is an empty PlainObject
  // (NightFillAllocCellObject fills the alloc fields [shape,total,slots,
  // elements,header] @0..16 from it) AND C's `.prototype` is an own data slot;
  // then stamp the guard fields [ctorShape@20, gen@24, protoPtr@28,
  // protoSlotEnc@32]. The inline hit guards C's shape + generation + a LIVE
  // re-read of `.prototype == protoPtr` (a reassignment leaves the shape but
  // must not reuse the stale this-shape).
  FillConstructCell(cx, cellAddr, out, calleeBits);
  WriteNightOut(top, out);
  return true;
#else
  (void)calleeBits;
  (void)newTargetBits;
  (void)nSlots;
  (void)cellAddr;
  return false;
#endif
}

// MIR's `new_this`: `night_runtime_create_this` for a proven scripted
// constructor that is its own new.target, its `prototype` already read
// (`protoBits`). Fills the site's construct cell, whose inline arm then
// compares the prototype with the cell's. Runs no code. May GC.
bool night_runtime_new_this(JSContext* cx, uint32_t top, uint64_t calleeBits,
                            uint64_t protoBits, uint32_t nSlots,
                            uint32_t cellAddr, uint32_t stampWord) {
  SetNightTop(cx, top);
#ifdef ENABLE_JS_NIGHTMONKEY
  uint64_t out = 0;
  if (!js::night::NightNewThis(cx, calleeBits, protoBits, nSlots, &out,
                               stampWord)) {
    return false;
  }
  FillConstructCell(cx, cellAddr, out, calleeBits);
  WriteNightOut(top, out);
  return true;
#else
  (void)calleeBits;
  (void)protoBits;
  (void)nSlots;
  (void)cellAddr;
  (void)stampWord;
  return false;
#endif
}

// The final part of construct cell `cellAddr` (MIR's `new_this.init`), from
// `obj` just given its layout's first `n` row fields: its shape, armed only
// where those fields are its only properties, each in its row's fixed slot
// (what the inline path's stores write), the alloc part is current (this
// generation's), and the prototype chain is at most two tenured objects,
// whose shapes the inline path re-checks.
static void FillConstructCellFinal(JSContext* cx, uint32_t cellAddr, JSObject* obj,
                                   const std::vector<uint32_t>& row,
                                   uint32_t n) {
  if (!cellAddr || !RtNames(cx).ids || !obj->is<js::NativeObject>()) {
    return;
  }
  auto* cell = LinMem<js::night::NightConstructCell>(cellAddr);
  if (!cell->ctorShape || cell->gen != (RtEnv(cx).propicGenPtr ? InlineGen(cx) : 0)) {
    return;
  }
  auto& nobj = obj->as<js::NativeObject>();
  if (nobj.slotSpan() != n || n > nobj.numFixedSlots()) {
    return;
  }
  for (uint32_t i = 0; i < n; i++) {
    mozilla::Maybe<js::PropertyInfo> prop =
        nobj.lookupPure((*RtNames(cx).ids)[row[i]].get());
    if (prop.isNothing() || !prop->isDataProperty() || prop->slot() != i) {
      return;
    }
  }
  JSObject* p = obj->staticPrototype();
  if (!p || uint32_t(reinterpret_cast<uintptr_t>(p)) != cell->protoPtr ||
      js::gc::IsInsideNursery(p)) {
    return;
  }
  JSObject* p2 = p->staticPrototype();
  if (p2 && (p2->staticPrototype() || js::gc::IsInsideNursery(p2))) {
    return;
  }
  cell->protoShape = js::night::NightObjectShape(p);
  cell->proto2Ptr = uint32_t(reinterpret_cast<uintptr_t>(p2));
  cell->proto2Shape = p2 ? js::night::NightObjectShape(p2) : 0;
  // Written last: it arms the row.
  cell->finalShape = js::night::NightObjectShape(obj);
}

uint32_t night_runtime_new_this_init(JSContext* cx, uint32_t top,
                                     uint64_t calleeBits, uint64_t protoBits,
                                     uint32_t nSlots, uint32_t cellAddr,
                                     uint32_t stampWord, uint32_t valsAddr,
                                     uint32_t n, uint32_t cache0,
                                     uint32_t wantBits) {
  SetNightTop(cx, top);
#ifdef ENABLE_JS_NIGHTMONKEY
  // The layout under construction: the stamp word's early key.
  uint32_t half = stampWord >> 16;
  uint32_t k = (half & 0x8000) ? (half >> 2) & 0xfff : 0;
  if (k == 0 || k - 1 >= RtLayouts(cx).rows.size() ||
      RtLayouts(cx).rows[k - 1].size() < n) {
    return 2;
  }
  const std::vector<uint32_t>& row = RtLayouts(cx).rows[k - 1];
  uint64_t out = 0;
  if (!js::night::NightNewThis(cx, calleeBits, protoBits, nSlots, &out,
                               stampWord)) {
    return 0;
  }
  FillConstructCell(cx, cellAddr, out, calleeBits);
  JS::RootedObject obj(cx, &JS::Value::fromRawBits(out).toObject());
  for (uint32_t i = 0; i < n; i++) {
    // Reread each time: the values are rooted where they are (below
    // `top`), and a GC may have moved them.
    uint64_t val = *LinMem<uint64_t>(valsAddr + 8 * i);
    uint32_t r = night_runtime_init_field(
        cx, top, JS::ObjectValue(*obj).asRawBits(), row[i], val, cache0 + i,
        (2u << i) - 1, wantBits);
    if (!r) {
      return cx->isExceptionPending() ? 0 : 2;
    }
  }
  FillConstructCellFinal(cx, cellAddr, obj, row, n);
  WriteNightOut(top, JS::ObjectValue(*obj).asRawBits());
  return 1;
#else
  (void)calleeBits;
  (void)protoBits;
  (void)nSlots;
  (void)cellAddr;
  (void)stampWord;
  (void)valsAddr;
  (void)n;
  (void)cache0;
  (void)wantBits;
  return 0;
#endif
}

// --- closure support: thin POD wrappers over the js::night:: helpers. The
// may-GC ones take `top`, install it, and pass the out-slot (= top) through.
// ---

bool night_runtime_env_setup(JSContext* cx, uint32_t top, uint32_t sp,
                             uint32_t script, uint32_t cellAddr) {
  SetNightTop(cx, top);
  if (!js::night::NightEnvSetup(cx, LinMem<void>(sp), LinMem<void>(script),
                                LinMem<uint64_t>(top))) {
    return false;
  }
#ifdef ENABLE_JS_NIGHTMONKEY
  // Fill the row the inline prologue replays: only for a prologue that makes
  // a CallObject and nothing else (no named-lambda environment).
  auto* cell = LinMem<js::night::NightEnvCell>(cellAddr);
  JS::Value out = JS::Value::fromRawBits(*LinMem<uint64_t>(top));
  JSScript* s = LinMem<JSScript>(script);
  if (cellAddr && RtEnv(cx).propicGenPtr && !s->isGlobalCode() &&
      out.isObject()) {
    JS::Value calleeV = LinMem<JS::Value>(sp)[0];
    JSFunction* callee = &calleeV.toObject().as<JSFunction>();
    if (callee->needsCallObject() && !callee->needsNamedLambdaEnvironment() &&
        js::night::NightFillEnvCell(cell, &out.toObject())) {
      cell->gen = InlineGen(cx);
      // The slot span (enclosing, callee, bindings) arms the row.
      cell->armed = out.toObject().as<js::NativeObject>().slotSpan();
    }
  }
#else
  (void)cellAddr;
#endif
  return true;
}

bool night_runtime_global_decl_instantiation(JSContext* cx, uint32_t top,
                                             uint32_t script,
                                             uint32_t gcthingIndex) {
  SetNightTop(cx, top);
  return js::night::NightGlobalDeclInstantiation(cx, LinMem<void>(script),
                                                 gcthingIndex);
}

uint64_t night_runtime_object(JSContext* cx, uint32_t script,
                              uint32_t gcthingIndex) {
  return js::night::NightObject(cx, LinMem<void>(script), gcthingIndex);
}

uint64_t night_runtime_get_aliased(JSContext* cx, uint64_t env, uint32_t hops,
                                   uint32_t slot) {
  return js::night::NightGetAliased(cx, env, hops, slot);
}

void night_runtime_set_aliased(JSContext* cx, uint64_t env, uint32_t hops,
                               uint32_t slot, uint64_t val) {
  js::night::NightSetAliased(cx, env, hops, slot, val);
}

bool night_runtime_lambda(JSContext* cx, uint32_t top, uint64_t env,
                          uint32_t script, uint32_t funcIndex,
                          uint32_t cellAddr) {
  SetNightTop(cx, top);
  if (!js::night::NightLambda(cx, env, LinMem<void>(script), funcIndex,
                              LinMem<uint64_t>(top))) {
    return false;
  }
#ifdef ENABLE_JS_NIGHTMONKEY
  // Fill the row the inline Lambda replays: the clone must be the canonical
  // function's object word for word but for its environment slot, which is
  // what the replay copies.
  auto* cell = LinMem<js::night::NightLambdaCell>(cellAddr);
  JS::Value out = JS::Value::fromRawBits(*LinMem<uint64_t>(top));
  if (cellAddr && RtEnv(cx).propicGenPtr && out.isObject()) {
    JSObject* clone = &out.toObject();
    JSFunction* canonical =
        LinMem<JSScript>(script)->getFunction(js::GCThingIndex(funcIndex));
    if (!js::gc::IsInsideNursery(canonical) && canonical->isInterpreted() &&
        !canonical->hasDynamicSlots() &&
        js::night::NightFillLambdaCell(cell, clone)) {
      size_t size = js::gc::Arena::thingSize(canonical->getAllocKind());
      size_t env = js::NativeObject::getFixedSlotOffset(
          JSFunction::NativeFuncOrInterpretedEnvSlot);
      const uint8_t* a = reinterpret_cast<const uint8_t*>(clone);
      const uint8_t* b = reinterpret_cast<const uint8_t*>(canonical);
      if (clone->as<JSFunction>().getAllocKind() ==
              canonical->getAllocKind() &&
          memcmp(a, b, env) == 0 &&
          memcmp(a + env + 8, b + env + 8, size - env - 8) == 0) {
        cell->gen = InlineGen(cx);
        // The canonical function arms the row.
        cell->templateFun = uint32_t(reinterpret_cast<uintptr_t>(canonical));
      }
    }
  }
#else
  (void)cellAddr;
#endif
  return true;
}

bool night_runtime_exception(JSContext* cx, uint32_t top) {
  SetNightTop(cx, top);
  return js::night::NightException(cx, LinMem<uint64_t>(top));
}

void night_runtime_throw(JSContext* cx, uint32_t top, uint64_t val) {
  SetNightTop(cx, top);
  js::night::NightThrow(cx, val);
}

void night_runtime_throw_with_stack(JSContext* cx, uint32_t top, uint64_t val,
                                    uint64_t stack) {
  SetNightTop(cx, top);
  js::night::NightThrowWithStack(cx, val, stack);
}

bool night_runtime_get_exception_for_finally(JSContext* cx, uint64_t* excOut,
                                             uint64_t* stackOut) {
  return js::night::NightGetExceptionForFinally(cx, excOut, stackOut);
}

}  // extern "C"

// Dynamic-code fuse maintenance (Night.h). The blow point is
// ScriptSource::assignSource -- the sole caller-of-record for every
// frontend compile from source text -- so this fires for eval, the
// Function-family constructors, ShadowRealm, module compiles and every
// embedder/shell compile entry alike, whether or not the source mentions
// BigInt. Conservative by construction: the fuse says "unscanned code
// exists", not "a BigInt exists".
void js::night::NightGlobalDataStore(JS::PropertyKey id, uint64_t valueBits) {
  JSContext* cx = CurrentNightContext();
  if (RtNames(cx).ids) {
    for (const GnameFuse& f : RtNames(cx).fuses) {
      if ((*RtNames(cx).ids)[f.atom] == id) {
        if (valueBits != f.literal) {
          *GnameFuseCell(cx, f.cell) = 2;
        }
        break;
      }
    }
  }
  if (RtState(cx).globalValsBase && RtNames(cx).bindingKeys) {
    for (size_t i = 0; i < RtNames(cx).bindingKeys->size(); i++) {
      if ((*RtNames(cx).bindingKeys)[i].get() == id) {
        MaybeBlowBindingFuseId(uint32_t(i), valueBits);
        break;
      }
    }
  }
}

void js::night::NightGlobalKeyBlow(JS::PropertyKey id) {
  BlowGnameFuseKey(id);
  BlowBindingFuseKey(id);
}

void js::night::NightBlowDynamicCodeFuse() {
  JSContext* cx = CurrentNightContext();
  RtState(cx).dynCodeSeen = true;
  if (RtState(cx).dynCodeFuseAddr) {
    *LinMem<uint32_t>(RtState(cx).dynCodeFuseAddr) = 1;
  }
}

void js::night::NightRearmDynamicCodeFuse() {
  JSContext* cx = CurrentNightContext();
  RtState(cx).dynCodeSeen = false;
  if (RtState(cx).dynCodeFuseAddr) {
    *LinMem<uint32_t>(RtState(cx).dynCodeFuseAddr) = 0;
  }
}

// Analysis-chosen slot layouts (docs/MIR-KICKOFF-6.md). A layout row names a
// class's fields in slot order: the union of the constructor's fields over
// its paths, so an object whose path writes them in another order, or skips
// some, would put later fields in lower slots than the row says and lose
// SLOTS. Instead each row field goes in its row slot whatever the insertion
// order (the engine's custom-slot shapes: skipped slots become holes, a
// later add fills one). The property order the program sees is unchanged.
//
// The slot of a name for a layout: its row position, or, for a name the row
// lacks, its position in the rows extending the row (a two-phase
// constructor's delegate fills the suffix), when they agree.
struct NightSlotTable {
  bool built = false;
  std::vector<std::pair<uint64_t, uint32_t>> slots;  // (jsid bits, slot)
};
static std::vector<NightSlotTable>& RtSlotTables(JSContext* cx);

static const NightSlotTable& NightSlotTableFor(JSContext* cx, uint32_t layout) {
  if (RtSlotTables(cx).size() < RtLayouts(cx).rows.size()) {
    RtSlotTables(cx).resize(RtLayouts(cx).rows.size());
  }
  NightSlotTable& t = RtSlotTables(cx)[layout];
  if (t.built) {
    return t;
  }
  t.built = true;
  const std::vector<uint32_t>& atoms = RtLayouts(cx).rows[layout];
  auto key = [cx](uint32_t atom) {
    return (*RtNames(cx).ids)[atom].get().asRawBits();
  };
  for (uint32_t i = 0; i < atoms.size(); i++) {
    t.slots.emplace_back(key(atoms[i]), i);
  }
  // Extensions: (jsid, slot), with UINT32_MAX where two rows disagree.
  std::vector<std::pair<uint64_t, uint32_t>> ext;
  for (const auto& cand : RtLayouts(cx).rows) {
    if (cand.size() <= atoms.size() ||
        !std::equal(atoms.begin(), atoms.end(), cand.begin())) {
      continue;
    }
    for (uint32_t i = uint32_t(atoms.size()); i < uint32_t(cand.size()); i++) {
      uint64_t k = key(cand[i]);
      auto it = std::find_if(ext.begin(), ext.end(),
                             [k](const auto& e) { return e.first == k; });
      if (it == ext.end()) {
        ext.emplace_back(k, i);
      } else if (it->second != i) {
        it->second = UINT32_MAX;
      }
    }
  }
  for (const auto& e : ext) {
    if (e.second != UINT32_MAX) {
      t.slots.push_back(e);
    }
  }
  return t;
}

// The layout a class word names: the early key while constructing, else the
// stamped idx; UINT32_MAX for none.
static uint32_t NightWordLayout(JSContext* cx, uint32_t w) {
  uint32_t half = w >> 16;
  uint32_t k = (half & 0x8000) ? (half >> 2) & 0xfff : w & 0xffff;
  if (k == 0 || k - 1 >= RtLayouts(cx).rows.size()) {
    return UINT32_MAX;
  }
  return k - 1;
}

// (parent shape, key, slot) -> the custom-slot shape, or null where the
// engine refused the placement. Holds raw shape pointers: purged with the
// other movable caches at every major GC.
struct NightAddMemoKey {
  uintptr_t shape;
  uint64_t id;
  uint32_t slot;
  bool operator==(const NightAddMemoKey& o) const {
    return shape == o.shape && id == o.id && slot == o.slot;
  }
};
struct NightAddMemoHash {
  size_t operator()(const NightAddMemoKey& k) const {
    uint64_t h = uint64_t(k.shape) * 0x9E3779B97F4A7C15ull;
    h ^= k.id + 0x7F4A7C15ull + (h << 6) + (h >> 2);
    h ^= uint64_t(k.slot) * 0xC2B2AE3D27D4EB4Full;
    return size_t(h ^ (h >> 29));
  }
};
using NightAddMemo =
    std::unordered_map<NightAddMemoKey, js::SharedShape*, NightAddMemoHash>;
static NightAddMemo& RtAddMemo(JSContext* cx);

void js::night::NightPurgeAddMemo() {
  JSContext* cx = CurrentNightContext();
  RtAddMemo(cx).clear();
}

// The engine's slot-placement hook (JS::ExternalCompilerHooks::shapeForAdd):
// a plain data property named by the object's layout goes in its row slot,
// if that is a fixed slot (predictions are fixed slots) and not already the
// span (where the engine's own add puts it). Only while SLOTS holds: once it
// is clear no consumer reads the placement.
bool js::night::NightShapeForAdd(JSContext* cx,
                                 JS::Handle<js::NativeObject*> obj,
                                 JS::HandleId id, uint8_t flags,
                                 js::SharedShape** result) {
  *result = nullptr;
  uint32_t w = obj->externalWord();
  if (!(w & kWordSlots) || !RtNames(cx).ids ||
      flags != js::PropertyFlags::defaultDataPropFlags.toRaw()) {
    return true;
  }
  uint32_t layout = NightWordLayout(cx, w);
  if (layout == UINT32_MAX) {
    return true;
  }
  uint64_t idBits = id.get().asRawBits();
  uint32_t slot = UINT32_MAX;
  for (const auto& e : NightSlotTableFor(cx, layout).slots) {
    if (e.first == idBits) {
      slot = e.second;
      break;
    }
  }
  js::SharedShape* shape = obj->sharedShape();
  if (slot == UINT32_MAX || slot >= obj->numFixedSlots() ||
      slot == shape->slotSpan()) {
    return true;
  }
  NightAddMemoKey key{uintptr_t(shape), idBits, slot};
  auto it = RtAddMemo(cx).find(key);
  if (it != RtAddMemo(cx).end()) {
    *result = it->second;
    return true;
  }
  JS::Rooted<js::SharedShape*> parent(cx, shape);
  js::SharedShape* chosen = nullptr;
  if (!js::ExternalShapeWithPropertyAtSlot(cx, parent, id, flags, slot,
                                           &chosen)) {
    return false;
  }
  // The allocation may have run a GC (which purges the memo and may move
  // the parent): key by where the parent is now.
  key.shape = uintptr_t(parent.get());
  RtAddMemo(cx).emplace(key, chosen);
  *result = chosen;
  return true;
}

// Whether every slot below `n` holds a property (none is a hole). With
// sequential slots that is span >= n; with permuted slots the properties
// below n are counted.
bool js::night::NightSlotsCovered(js::NativeObject* obj, uint32_t n) {
  if (obj->inDictionaryMode() || obj->slotSpan() < n) {
    return false;
  }
  js::Shape* shape = obj->shape();
  if (!shape->hasPermutedSlots()) {
    return true;
  }
  uint32_t count = 0;
  for (js::ShapePropertyIter<js::NoGC> iter(&shape->asNative()); !iter.done();
       iter++) {
    if (iter->hasSlot() && iter->slot() < n) {
      count++;
    }
  }
  return count == n;
}

// Two-bit-stamp per-add SLOTS maintenance (Night.h; called from the
// engine's property add chokepoints, always on). The receiver's layout is
// identified from the class word (early key while constructing, else the
// stamped idx); the atom resolves through the receiver's own prefix and
// its clump extensions (the prefix-stamp -> init-delegate flow); an add
// that deviates -- predicted at another position, landing in a dynamic
// slot, or unpredicted INSIDE the clump's extension bound -- clears the
// SLOTS bit.
void js::night::NightAddPropCheck(JSObject* obj, JS::PropertyKey id,
                                  uint32_t slot, uint32_t nfixed) {
  JSContext* cx = CurrentNightContext();
  js::night::NightClearClosedBit(obj);
  uint32_t w = obj->externalWord();
  if (MOZ_LIKELY((w & 0x00020000u) == 0)) {
    return;
  }
  uint32_t half = w >> 16;
  uint32_t layout;
  if (half & 0x8000) {
    // The key is half bits 2..13; bit 14 is RANGES, which is seeded during
    // construction and so must not be read as part of the key.
    uint32_t k = (half >> 2) & 0xfff;
    if (k == 0) {
      // A keyless sentinel never seeds SLOTS; stay conservative if one
      // carries it anyway.
      js::night::NightClearSlotsBit(obj, js::night::NightBumpSite::SlotsAddMismatch);
      return;
    }
    layout = k - 1;
  } else {
    uint32_t idx = w & 0xffff;
    if (idx == 0) {
      js::night::NightClearSlotsBit(obj, js::night::NightBumpSite::SlotsAddMismatch2);
      return;
    }
    layout = idx - 1;
  }
  if (layout >= RtLayouts(cx).rows.size() || !RtNames(cx).ids) {
    js::night::NightClearSlotsBit(obj, js::night::NightBumpSite::SlotsAddMismatch3);
    return;
  }
  const std::vector<uint32_t>& atoms = RtLayouts(cx).rows[layout];
  uint32_t extLen = layout < RtLayouts(cx).extLen.size() ? RtLayouts(cx).extLen[layout]
                                                    : uint32_t(atoms.size());
  // Fast path: an append past the clump's longest prefix can neither sit
  // inside a guarded prefix nor be one of its predictions.
  if (slot >= extLen) {
    return;
  }
  uint32_t pos = UINT32_MAX;
  for (uint32_t i = 0; i < atoms.size(); i++) {
    if ((*RtNames(cx).ids)[atoms[i]].get() == id) {
      pos = i;
      break;
    }
  }
  bool clear;
  if (pos == UINT32_MAX) {
    // Clump-aware resolution: an extending layout predicting this atom at
    // exactly the assigned slot keeps the bit (the delegate flow).
    bool ext = false;
    for (const auto& cand : RtLayouts(cx).rows) {
      if (cand.size() <= atoms.size() ||
          !std::equal(atoms.begin(), atoms.end(), cand.begin())) {
        continue;
      }
      for (uint32_t i = uint32_t(atoms.size()); i < uint32_t(cand.size());
           i++) {
        if ((*RtNames(cx).ids)[cand[i]].get() == id) {
          ext = i == slot;
          break;
        }
      }
      if (ext) {
        break;
      }
    }
    // Unpredicted inside the extension bound: a guarded prefix slot now
    // holds an unexpected name.
    clear = !ext || slot >= nfixed;
    // The clear-vs-ineligible split: an unpredicted name landing BEYOND
    // the receiver's OWN layout leaves the own prefix bijection true
    // (slots assign sequentially) -- only the prefix-advance certificate
    // dies. Keep SLOTS, mark advance-ineligible, bump nothing. Stamped
    // (non-sentinel) words only: while the sentinel is up, bit 18 is
    // part of the early key.
    if (clear && !(half & 0x8000) && slot >= atoms.size()) {
      js::night::NightSetAdvIneligible(obj);
      return;
    }
  } else {
    clear = slot >= nfixed || slot != pos;
    // A field of the layout under construction, at its slot: into the
    // word's set of the fields added (MIR.md §2.3).
    if (!clear && (half & 0x8000) && pos < js::night::kCtorSetBits) {
      obj->setExternalWord(obj->externalWord() | (1u << pos));
    }
  }
  if (clear) {
    js::night::NightClearSlotsBit(obj, js::night::NightBumpSite::SlotsAddMismatch4);
  }
}

// --- baseline-tier helpers -------------------------------------------------
//
// The ops no other lowering needed a helper for (docs/BASELINE.md §6). Each
// is the interpreter's case for the op, with the frame state it reads from
// `REGS` passed in: the env chain, the script, and the pc offset.

static jsbytecode* NightPcOf(JSScript* script, uint32_t pcOffset) {
  return script->offsetToPC(pcOffset);
}

// `BigInt`: the script's BigInt literal at `gcthingIndex`.
bool night_runtime_bigint(JSContext* cx, uint32_t top, uint32_t script,
                          uint32_t gcthingIndex) {
  SetNightTop(cx, top);
  JSScript* s = LinMem<JSScript>(script);
  WriteNightOut(
      top,
      JS::BigIntValue(s->getBigInt(js::GCThingIndex(gcthingIndex))).asRawBits());
  return true;
}

// `NonSyntacticGlobalThis`.
bool night_runtime_non_syntactic_global_this(JSContext* cx, uint32_t top,
                                             uint64_t env) {
  SetNightTop(cx, top);
  JS::RootedObject envChain(cx, &JS::Value::fromRawBits(env).toObject());
  JS::RootedValue res(cx);
  js::GetNonSyntacticGlobalThis(cx, envChain, &res);
  WriteNightOut(top, res.get().asRawBits());
  return true;
}

// `SetIntrinsic` (self-hosted code only).
bool night_runtime_set_intrinsic(JSContext* cx, uint32_t top, uint32_t script,
                                 uint32_t pcOffset, uint64_t val) {
  SetNightTop(cx, top);
  JSScript* s = LinMem<JSScript>(script);
  JS::RootedValue v(cx, JS::Value::fromRawBits(val));
  return js::SetIntrinsicOperation(cx, s, NightPcOf(s, pcOffset), v);
}

// `EnvCallee`: the callee of the CallObject `hops` up the env chain. Leaf.
uint64_t night_runtime_env_callee(JSContext* cx, uint64_t env, uint32_t hops) {
  (void)cx;
  JSObject* e = &JS::Value::fromRawBits(env).toObject();
  for (uint32_t i = 0; i < hops; i++) {
    e = &e->as<js::EnvironmentObject>().enclosingEnvironment();
  }
  return JS::ObjectValue(e->as<js::CallObject>().callee()).asRawBits();
}

// `Eval`/`StrictEval`: `[callee, this, args...]` at `sp`. A direct eval when
// the callee is this realm's `eval`, run against the frame's env chain; any
// other callee is an ordinary call.
bool night_runtime_eval(JSContext* cx, uint32_t top, uint32_t sp,
                        uint32_t argc, uint64_t env, uint32_t script,
                        uint32_t pcOffset) {
  SetNightTop(cx, top);
  JS::Value* frame = LinMem<JS::Value>(sp);
  if (!cx->global()->valueIsEval(frame[0])) {
    return night_runtime_call(cx, top, sp, argc);
  }
  JS::RootedValue arg(cx, argc > 0 ? frame[2] : JS::UndefinedValue());
  JS::RootedObject envChain(cx, &JS::Value::fromRawBits(env).toObject());
  JS::RootedScript s(cx, LinMem<JSScript>(script));
  JS::RootedValue res(cx);
  if (!js::night::NightDirectEval(cx, arg, envChain, s,
                                  NightPcOf(s, pcOffset), &res)) {
    return false;
  }
  WriteNightOut(top, res.get().asRawBits());
  return true;
}

// `SpreadEval`/`StrictSpreadEval`: `[callee, this, args array]`. A direct
// eval of the array's first element when the callee is `eval`, else an
// ordinary spread call.
bool night_runtime_spread_eval(JSContext* cx, uint32_t top, uint64_t callee,
                               uint64_t thisv, uint64_t arr, uint64_t env,
                               uint32_t script, uint32_t pcOffset) {
  SetNightTop(cx, top);
  if (!cx->global()->valueIsEval(JS::Value::fromRawBits(callee))) {
    return night_runtime_spread_call(cx, top, callee, thisv, arr,
                                     JS::NullValue().asRawBits(), 0);
  }
  JS::RootedObject arrObj(cx, &JS::Value::fromRawBits(arr).toObject());
  JS::RootedValue arg(cx);
  if (!JS_GetElement(cx, arrObj, 0, &arg)) {
    return false;
  }
  JS::RootedObject envChain(cx, &JS::Value::fromRawBits(env).toObject());
  JS::RootedScript s(cx, LinMem<JSScript>(script));
  JS::RootedValue res(cx);
  if (!js::night::NightDirectEval(cx, arg, envChain, s,
                                  NightPcOf(s, pcOffset), &res)) {
    return false;
  }
  WriteNightOut(top, res.get().asRawBits());
  return true;
}

// `DynamicImport`: `[specifier, options] -> [promise]`.
bool night_runtime_dynamic_import(JSContext* cx, uint32_t top, uint32_t script,
                                  uint64_t specifier, uint64_t options) {
  SetNightTop(cx, top);
  JS::RootedScript s(cx, LinMem<JSScript>(script));
  JS::RootedValue spec(cx, JS::Value::fromRawBits(specifier));
  JS::RootedValue opts(cx, JS::Value::fromRawBits(options));
  JSObject* promise = js::StartDynamicModuleImport(cx, s, spec, opts);
  if (!promise) {
    return false;
  }
  WriteNightOut(top, JS::ObjectValue(*promise).asRawBits());
  return true;
}

// `ImportMeta`.
bool night_runtime_import_meta(JSContext* cx, uint32_t top, uint32_t script) {
  SetNightTop(cx, top);
  JS::RootedScript s(cx, LinMem<JSScript>(script));
  JSObject* meta = js::ImportMetaOperation(cx, s);
  if (!meta) {
    return false;
  }
  WriteNightOut(top, JS::ObjectValue(*meta).asRawBits());
  return true;
}

// `GetImport`.
bool night_runtime_get_import(JSContext* cx, uint32_t top, uint64_t env,
                              uint32_t script, uint32_t pcOffset) {
  SetNightTop(cx, top);
  JS::RootedObject envChain(cx, &JS::Value::fromRawBits(env).toObject());
  JS::RootedScript s(cx, LinMem<JSScript>(script));
  JS::RootedValue res(cx);
  if (!js::GetImportOperation(cx, envChain, s, NightPcOf(s, pcOffset), &res)) {
    return false;
  }
  WriteNightOut(top, res.get().asRawBits());
  return true;
}

// The explicit-resource-management ops exist only when the engine enables
// the proposal; without it the helpers are unreachable but still exported,
// so the helper table is the same either way.

// `AddDisposable`: `[val, method, needsClosure] ->`.
bool night_runtime_add_disposable(JSContext* cx, uint32_t top, uint64_t env,
                                  uint64_t val, uint64_t method,
                                  uint64_t needsClosure, uint32_t hint) {
  SetNightTop(cx, top);
#ifndef ENABLE_EXPLICIT_RESOURCE_MANAGEMENT
  MOZ_CRASH("AddDisposable without explicit resource management");
#else
  JS::RootedObject envObj(cx, &JS::Value::fromRawBits(env).toObject());
  JS::RootedValue v(cx, JS::Value::fromRawBits(val));
  JS::RootedValue m(cx, JS::Value::fromRawBits(method));
  return js::AddDisposableResourceToCapability(
      cx, envObj, v, m, JS::Value::fromRawBits(needsClosure).toBoolean(),
      js::UsingHint(uint8_t(hint)));
#endif
}

// `TakeDisposeCapability`: `-> [disposables or undefined]`.
bool night_runtime_take_dispose_capability(JSContext* cx, uint32_t top,
                                           uint64_t env) {
  SetNightTop(cx, top);
#ifndef ENABLE_EXPLICIT_RESOURCE_MANAGEMENT
  MOZ_CRASH("TakeDisposeCapability without explicit resource management");
#else
  JSObject* envObj = &JS::Value::fromRawBits(env).toObject();
  auto& denv = envObj->as<js::DisposableEnvironmentObject>();
  JS::Value maybe = denv.getDisposables();
  if (maybe.isUndefined()) {
    WriteNightOut(top, JS::UndefinedValue().asRawBits());
  } else {
    WriteNightOut(top, JS::ObjectValue(maybe.toObject()).asRawBits());
    denv.clearDisposables();
  }
  return true;
#endif
}

// `CreateSuppressedError`: `[error, suppressed] -> [SuppressedError]`.
bool night_runtime_create_suppressed_error(JSContext* cx, uint32_t top,
                                           uint64_t error,
                                           uint64_t suppressed) {
  SetNightTop(cx, top);
#ifndef ENABLE_EXPLICIT_RESOURCE_MANAGEMENT
  MOZ_CRASH("CreateSuppressedError without explicit resource management");
#else
  JS::RootedValue e(cx, JS::Value::fromRawBits(error));
  JS::RootedValue sup(cx, JS::Value::fromRawBits(suppressed));
  js::ErrorObject* obj = js::CreateSuppressedError(cx, e, sup);
  if (!obj) {
    return false;
  }
  WriteNightOut(top, JS::ObjectValue(*obj).asRawBits());
  return true;
#endif
}

// `Resume`: `[gen, val, kind] -> [result]`, the way the JITs do it
// (jit::InterpretResume): through the self-hosted InterpretGeneratorResume,
// which runs in the interpreter (it is ForceInterpreter) and whose own
// `Resume` re-enters a NightMonkey generator through the resume hook.
bool night_runtime_resume(JSContext* cx, uint32_t top, uint64_t gen,
                          uint64_t val, uint64_t kind) {
  SetNightTop(cx, top);
  js::GeneratorResumeKind rk =
      js::IntToResumeKind(JS::Value::fromRawBits(kind).toInt32());
  JSAtom* kindAtom = js::ResumeKindToAtom(cx, rk);
  js::FixedInvokeArgs<3> args(cx);
  args[0].set(JS::Value::fromRawBits(gen));
  args[1].set(JS::Value::fromRawBits(val));
  args[2].setString(kindAtom);
  JS::RootedValue res(cx);
  if (!js::CallSelfHostedFunction(cx, cx->names().InterpretGeneratorResume,
                                  JS::UndefinedHandleValue, args, &res)) {
    return false;
  }
  WriteNightOut(top, res.get().asRawBits());
  return true;
}

// ===========================================================================
// The runtime state (see "Runtime state" at the top)
// ===========================================================================

struct js::night::NightRuntimeState {
  js::night::NightEnvDesc env;
  NightNameTables names;
  NightPristineFns fns;
  NightLayoutTable layouts;
  NightState state;
  SetAddRow setAdd[kSetAddSize];
  InitAddRow initAdd[kInitAddSize];
  uint32_t hasInst[kHasInstCacheN * 2] = {};
  // The compiled get probe reads it too (its address is published in the
  // strlit block at install).
  alignas(16) GChainEntry gchain[kGChainSize] = {};
  uintptr_t noExtra[kNoExtraCacheN * 5] = {};
  std::vector<MethodDep> methodDeps;
  std::vector<NightSlotTable> slotTables;
  NightAddMemo addMemo;
  NightCensusState census;
  js::night::NightRuntimeData regex;
};

js::night::NightRuntimeState* js::night::NewNightRuntimeState() {
  return js_new<NightRuntimeState>();
}

void js::night::DeleteNightRuntimeState(NightRuntimeState* state) {
  js_delete(state);
}

static inline js::night::NightRuntimeState& Rt(JSContext* cx) {
  return *js::nightrt::NightStateOf(cx)->runtime;
}
static js::night::NightEnvDesc& RtEnv(JSContext* cx) { return Rt(cx).env; }
static NightNameTables& RtNames(JSContext* cx) { return Rt(cx).names; }
static NightPristineFns& RtFns(JSContext* cx) { return Rt(cx).fns; }
static NightLayoutTable& RtLayouts(JSContext* cx) { return Rt(cx).layouts; }
static NightState& RtState(JSContext* cx) { return Rt(cx).state; }
static SetAddRow* RtSetAdd(JSContext* cx) { return Rt(cx).setAdd; }
static InitAddRow* RtInitAdd(JSContext* cx) { return Rt(cx).initAdd; }
static uint32_t* RtHasInst(JSContext* cx) { return Rt(cx).hasInst; }
static GChainEntry* RtGChain(JSContext* cx) { return Rt(cx).gchain; }
static uintptr_t* RtNoExtra(JSContext* cx) { return Rt(cx).noExtra; }
static std::vector<MethodDep>& RtMethodDeps(JSContext* cx) {
  return Rt(cx).methodDeps;
}
static std::vector<NightSlotTable>& RtSlotTables(JSContext* cx) {
  return Rt(cx).slotTables;
}
static NightAddMemo& RtAddMemo(JSContext* cx) { return Rt(cx).addMemo; }
static NightCensusState& RtCensus(JSContext* cx) { return Rt(cx).census; }
static js::night::NightRuntimeData& RtRegex(JSContext* cx) {
  return Rt(cx).regex;
}
