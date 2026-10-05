/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80: */

/*
 * The AOT regexp fast paths: the collapsed RegExpMatcher / RegExpSearcher /
 * RegExp.prototype.exec+test frames the AOT runtime calls instead of the
 * ordinary natives, and the AOT-compiled Wasm matcher divert that
 * RegExpShared::execute takes ahead of the irregexp jit/interpreter.
 */

#include "mozilla/ArrayUtils.h"     // mozilla::ArrayEqual
#include "mozilla/PodOperations.h"  // mozilla::PodCopy

#include "builtin/RegExp.h"
#include "irregexp/RegExpAPI.h"  // js::irregexp::kExternalMatcher*
#include "js/GCAPI.h"            // JS::AutoCheckCannotGC
#include "runtime/NightContext.h"
#include "runtime/NightRegExp.h"
#include "runtime/NightRuntimeData.h"
#include "vm/GlobalObject.h"
#include "vm/JSContext.h"
#include "vm/MatchPairs.h"
#include "vm/RegExpObject.h"
#include "vm/RegExpShared.h"
#include "vm/RegExpStatics.h"
#include "vm/Runtime.h"
#include "vm/StringType.h"

#include "vm/JSObject-inl.h"

using namespace js;

#ifdef ENABLE_JS_NIGHTMONKEY
/*
 * Run a compiled shared's match: an atom by the engine's own atom matcher (a
 * plain string search, no GC), a regexp by its AOT matcher. False to fall
 * back (no matcher, or the matcher gave up).
 */
static bool NightMatch(JSContext* cx, MutableHandleRegExpShared shared,
                       Handle<JSLinearString*> input, size_t start,
                       VectorMatchPairs* matches, RegExpRunStatus* status) {
  if (shared->kind() == RegExpShared::Kind::Atom) {
    *status = RegExpShared::executeAtom(shared, input, start, matches);
    return true;
  }
  MOZ_ASSERT(shared->kind() == RegExpShared::Kind::RegExp);
  return irregexp::TryNightRegexMatch(cx, shared, input, start, matches,
                                      input->hasLatin1Chars(), status);
}

/*
 * Collapsed AOT fast path for the RegExpMatcher/RegExpSearcher intrinsics,
 * called from the AOT runtime's native dispatch with the rooted call frame
 * `[callee, this, regexp, string, lastIndex]`. When the shared has an
 * AOT-compiled wasm matcher, this performs the whole
 * Matcher/Impl/ExecuteRegExp/Impl/execute stack in one frame: matcher call,
 * statics update, result creation. Sets *handled=false (returning true) to
 * fall back to the ordinary native for anything unusual: unparsed/atom
 * shared (the first call per regex compiles via the generic path), no
 * matcher for the encoding, matcher RETRY, or unexpected argument shapes.
 */
bool js::NightRegExpBuiltinFast(JSContext* cx, Value* frame, unsigned argc,
                                bool searcher, bool* handled) {
  *handled = false;
  if (argc != 3 || !frame[2].isObject() ||
      !frame[2].toObject().is<RegExpObject>() || !frame[3].isString() ||
      !frame[4].isInt32()) {
    return true;
  }
  Rooted<RegExpObject*> reobj(cx, &frame[2].toObject().as<RegExpObject>());
  RootedRegExpShared shared(cx, RegExpObject::getShared(cx, reobj));
  if (!shared) {
    return false;
  }
  // Fully-compiled regexps and atoms only: pairCount / named captures /
  // the groups template are set during compilation, and
  // CreateRegExpMatchResult needs them. The first execution per regex runs
  // the generic path and compiles.
  if (shared->kind() == RegExpShared::Kind::Unparsed) {
    return true;
  }
  int32_t lastIndex = frame[4].toInt32();
  RootedString string(cx, frame[3].toString());
  Rooted<JSLinearString*> input(cx, string->ensureLinear(cx));
  if (!input) {
    return false;
  }
  if (lastIndex < 0 || size_t(lastIndex) > input->length()) {
    return true;
  }
  VectorMatchPairs matches;
  if (!matches.externalAllocOrExpandArray(shared->pairCount())) {
    ReportOutOfMemory(cx);
    return false;
  }
#  ifdef DEBUG
  if (searcher) {
    cx->regExpSearcherLastLimit = RegExpSearcherLastLimitSentinel;
  }
#  endif
  RegExpRunStatus status;
  if (!NightMatch(cx, &shared, input, size_t(lastIndex), &matches, &status)) {
    return true;
  }
  if (status == RegExpRunStatus::Success) {
    RegExpStatics* res = GlobalObject::getRegExpStatics(cx, cx->global());
    if (!res) {
      return false;
    }
    res->updateLazily(cx, input, shared, size_t(lastIndex));
  }
  if (searcher) {
    int32_t result = status == RegExpRunStatus::Success
                         ? CreateRegExpSearchResult(cx, matches)
                         : -1;
    frame[0] = Int32Value(result);
  } else if (status == RegExpRunStatus::Success_NotFound) {
    frame[0] = NullValue();
  } else {
    RootedValue rv(cx);
    if (!CreateRegExpMatchResult(cx, shared, string, matches, &rv)) {
      return false;
    }
    frame[0] = rv;
  }
  *handled = true;
  return true;
}

/*
 * Collapsed AOT fast path for the pristine RegExp.prototype.exec/.test
 * callee-identity arm in the AOT runtime's generic call helper. The frame is
 * the rooted AOT call frame `[callee, this(=regexp), string]`; the caller has
 * already proved `this` an optimizable RegExpObject with (for global/sticky)
 * a non-negative int32 lastIndex, and the string argument. Mirrors
 * RegExpBuiltinExec{Match,Test}FromJit exactly: lastIndex read/reset/update
 * for global/sticky, statics update (lazily) on success, null/false vs match
 * result. test() allocates NOTHING on this path (no result object, no
 * dependent strings, lazy statics). *handled=false falls back to the
 * FromJit path (first call per regex compiles there; RETRY likewise).
 */
bool js::NightRegExpExecTestFast(JSContext* cx, Value* frame, bool forTest,
                                 bool* handled) {
  *handled = false;
  Rooted<RegExpObject*> reobj(cx, &frame[1].toObject().as<RegExpObject>());
  RootedRegExpShared shared(cx, RegExpObject::getShared(cx, reobj));
  if (!shared) {
    return false;
  }
  if (shared->kind() == RegExpShared::Kind::Unparsed) {
    return true;
  }
  RootedString string(cx, frame[2].toString());
  bool globalOrSticky = reobj->isGlobalOrSticky();
  int32_t lastIndex = 0;
  if (globalOrSticky) {
    Value li = reobj->getLastIndex();
    if (!li.isInt32() || li.toInt32() < 0) {
      return true;
    }
    lastIndex = li.toInt32();
    if (size_t(lastIndex) > string->length()) {
      if (!SetLastIndex<false>(cx, reobj, 0)) {
        return false;
      }
      frame[0] = forTest ? BooleanValue(false) : NullValue();
      *handled = true;
      return true;
    }
  }
  Rooted<JSLinearString*> input(cx, string->ensureLinear(cx));
  if (!input) {
    return false;
  }
  // Mirror ExecuteRegExp: the statics object is (lazily) created before
  // execution, so an OOM there errors identically.
  RegExpStatics* res = GlobalObject::getRegExpStatics(cx, cx->global());
  if (!res) {
    return false;
  }
  VectorMatchPairs matches;
  if (!matches.externalAllocOrExpandArray(shared->pairCount())) {
    ReportOutOfMemory(cx);
    return false;
  }
  RegExpRunStatus status;
  // The match the compiled call's leaf just ran for this exec(), if it is
  // this one's: its pairs, not a second run of the matcher.
  nightrt::NightLeafMatch& leaf = nightrt::NightStateOf(cx)->leafMatch;
  if (leaf.pairCount != 0 && !globalOrSticky && leaf.shared == shared &&
      leaf.input == input && leaf.pairCount == matches.pairCount() &&
      leaf.gcNumber == cx->runtime()->gc.gcNumber()) {
    mozilla::PodCopy(matches.pairsRaw(), leaf.pairs, 2 * leaf.pairCount);
    leaf.pairCount = 0;
    status = RegExpRunStatus::Success;
  } else if (!NightMatch(cx, &shared, input, size_t(lastIndex), &matches,
                         &status)) {
    return true;
  }
  if (status == RegExpRunStatus::Success) {
    res->updateLazily(cx, input, shared, size_t(lastIndex));
    if (globalOrSticky && !SetLastIndex<false>(cx, reobj, matches[0].limit)) {
      return false;
    }
    if (forTest) {
      frame[0] = BooleanValue(true);
    } else {
      RootedValue rv(cx);
      if (!CreateRegExpMatchResult(cx, shared, string, matches, &rv)) {
        return false;
      }
      frame[0] = rv;
    }
  } else {
    if (globalOrSticky && !SetLastIndex<false>(cx, reobj, 0)) {
      return false;
    }
    frame[0] = forTest ? BooleanValue(false) : NullValue();
  }
  *handled = true;
  return true;
}

/*
 * The compiled call's RegExp.prototype.exec/.test arm: a leaf (no GC, no
 * rooting) that decides the call without a frame when it can. `thisv` must be
 * an optimizable RegExpObject that is neither global nor sticky (so lastIndex
 * is read but never written: the call leaves the heap as it found it), with a
 * compiled shared (an atom, or a regexp with an AOT matcher); `strv` a linear
 * string. Returns 1 with *out the result for a failed match (null / false)
 * and a successful test() (true), updating the statics as the engine does; 2
 * for a successful exec(), whose result object the caller's generic path
 * builds from the pairs kept in the context's NightLeafMatch; 0 where any of
 * that does not hold.
 */
int js::NightRegExpLeaf(JSContext* cx, const Value& thisv, const Value& strv,
                        bool forTest, Value* out) {
  JS::AutoCheckCannotGC nogc;
  if (!thisv.isObject() || !strv.isString() ||
      !IsOptimizableRegExpObject(&thisv.toObject(), cx)) {
    return 0;
  }
  RegExpObject* reobj = &thisv.toObject().as<RegExpObject>();
  if (reobj->isGlobalOrSticky() || !reobj->getLastIndex().isNumber() ||
      !reobj->hasShared()) {
    return 0;
  }
  RegExpShared* shared = reobj->getShared();
  if (shared->kind() == RegExpShared::Kind::Unparsed ||
      !strv.toString()->isLinear()) {
    return 0;
  }
  RegExpStatics* res = cx->global()->regExpRealm().regExpStatics.get();
  if (!res) {
    return 0;
  }
  JSLinearString* input = &strv.toString()->asLinear();
  VectorMatchPairs matches;
  if (!matches.externalAllocOrExpandArray(shared->pairCount())) {
    return 0;
  }
  RegExpRunStatus status;
  if (!NightMatch(cx,
                  JS::MutableHandle<RegExpShared*>::fromMarkedLocation(&shared),
                  JS::Handle<JSLinearString*>::fromMarkedLocation(&input), 0,
                  &matches, &status)) {
    return 0;
  }
  if (status == RegExpRunStatus::Success_NotFound) {
    *out = forTest ? BooleanValue(false) : NullValue();
    return 1;
  }
  if (!forTest) {
    // The generic path builds the result (it allocates); keep the pairs
    // for it (NightRegExpExecTestFast).
    nightrt::NightLeafMatch& leaf = nightrt::NightStateOf(cx)->leafMatch;
    if (matches.pairCount() <= nightrt::NightLeafMatch::kMaxPairs) {
      leaf.shared = shared;
      leaf.input = input;
      leaf.gcNumber = cx->runtime()->gc.gcNumber();
      leaf.pairCount = uint32_t(matches.pairCount());
      mozilla::PodCopy(leaf.pairs, matches.pairsRaw(), 2 * leaf.pairCount);
    }
    return 2;
  }
  res->updateLazily(cx, input, shared, 0);
  *out = BooleanValue(true);
  return 1;
}

bool js::NightRegExpLeafRow(JSContext* cx, const Value& thisv,
                            uint32_t* shape, uint32_t* shared,
                            uint32_t* latin1Idx, uint32_t* twobyteIdx) {
  JS::AutoCheckCannotGC nogc;
  if (!thisv.isObject() || !IsOptimizableRegExpObject(&thisv.toObject(), cx)) {
    return false;
  }
  RegExpObject* reobj = &thisv.toObject().as<RegExpObject>();
  if (reobj->isGlobalOrSticky() || !reobj->hasShared()) {
    return false;
  }
  RegExpShared* re = reobj->getShared();
  if (re->kind() != RegExpShared::Kind::RegExp) {
    return false;
  }
  const js::night::NightRegexEntry* e = irregexp::NightRegexEntryFor(cx, re);
  if (!e || e->pairCount > js::night::Night_regexLeafMaxPairs ||
      (e->latin1Idx == 0 && e->twobyteIdx == 0)) {
    return false;
  }
  *shape = uint32_t(reinterpret_cast<uintptr_t>(reobj->shape()));
  *shared = uint32_t(reinterpret_cast<uintptr_t>(re));
  *latin1Idx = e->latin1Idx;
  *twobyteIdx = e->twobyteIdx;
  return true;
}

namespace js {
namespace irregexp {

// Try the AOT-compiled Wasm matcher for this RegExpShared. Returns true and
// sets *out when the matcher decided the match (found / not found); returns
// false to fall back to the ordinary irregexp path (no matcher for this
// pattern/encoding, or the matcher gave up: backtrack budget or stack limit).
// Called from RegExpShared::execute -- the funnel every regexp-builtin path
// goes through -- so a hit skips the jit-choice + interpreter layering
// entirely. The resolved matcher is cached on the shared: after the first
// call, dispatch is one load + call_indirect.
static_assert(js::night::kRegexMatcherSuccess == kExternalMatcherSuccess);
static_assert(js::night::kRegexMatcherFailure == kExternalMatcherFailure);

// The AOT matcher entry for `re`, resolving the shared's external word on
// first use; null where there is none.
const js::night::NightRegexEntry* NightRegexEntryFor(JSContext* cx,
                                                     RegExpShared* re) {
  js::night::NightRuntimeData& aot = js::night::NightData(cx);
  if (aot.regexTableCount == 0) {
    return nullptr;
  }
  // The shared's external word caches the lookup: 0 unresolved, 1 no
  // matcher, else table index + 2.
  uint32_t word = re->externalWord();
  if (word == 0) {
    // Resolve once per shared: match (pattern chars, flags) against the
    // published table.
    word = 1;
    JSAtom* src = re->getSource();
    uint32_t flags = re->getFlags().value();
    JS::AutoCheckCannotGC nogc;
    for (uint32_t i = 0; i < aot.regexTableCount; i++) {
      const js::night::NightRegexEntry& e = aot.regexTable[i];
      if (e.flags != flags || e.patternLen != src->length()) {
        continue;
      }
      bool equal = true;
      if (src->hasLatin1Chars()) {
        const JS::Latin1Char* c = src->latin1Chars(nogc);
        for (uint32_t j = 0; j < e.patternLen; j++) {
          if (char16_t(c[j]) != e.pattern[j]) {
            equal = false;
            break;
          }
        }
      } else {
        equal = mozilla::ArrayEqual(src->twoByteChars(nogc), e.pattern,
                                    size_t(e.patternLen));
      }
      if (equal) {
        word = i + 2;
        break;
      }
    }
    re->setExternalWord(word);
  }
  if (word == 1) {
    return nullptr;
  }
  return &aot.regexTable[word - 2];
}

bool TryNightRegexMatch(JSContext* cx, MutableHandleRegExpShared re,
                        Handle<JSLinearString*> input, size_t startIndex,
                        VectorMatchPairs* matches, bool latin1,
                        RegExpRunStatus* out) {
  js::night::NightRuntimeData& aot = js::night::NightData(cx);
  const js::night::NightRegexEntry* ep = NightRegexEntryFor(cx, re);
  if (!ep) {
    return false;
  }
  const js::night::NightRegexEntry& e = *ep;
  uint32_t funcIdx = latin1 ? e.latin1Idx : e.twobyteIdx;
  if (funcIdx == 0 || matches->pairCount() != e.pairCount) {
    return false;
  }
  // A Wasm C function pointer IS an indirect-table index; the matcher was
  // emitted with exactly this all-i32 signature.
  using RegexFn =
      int32_t (*)(const void* input, int32_t lengthChars, int32_t start,
                  int32_t* outputRegs, int32_t* btStack, int32_t btStackElems);
  auto fn = reinterpret_cast<RegexFn>(uintptr_t(funcIdx));
  int32_t status;
  {
    JS::AutoCheckCannotGC nogc;
    const void* chars =
        latin1 ? static_cast<const void*>(input->latin1Chars(nogc))
               : static_cast<const void*>(input->twoByteChars(nogc));
    status = fn(chars, int32_t(input->length()), int32_t(startIndex),
                matches->pairsRaw(), aot.regexBtStack,
                int32_t(aot.regexBtStackElems));
  }
  if (status == js::night::kRegexMatcherSuccess) {
    aot.regexNightMatches++;
    *out = RegExpRunStatus::Success;
    return true;
  }
  if (status == js::night::kRegexMatcherFailure) {
    aot.regexNightMatches++;
    *out = RegExpRunStatus::Success_NotFound;
    return true;
  }
  // RETRY (budget/stack): rerun this match in the interpreter.
  aot.regexNightFallbacks++;
  return false;
}

}  // namespace irregexp
}  // namespace js
#endif  // ENABLE_JS_NIGHTMONKEY
