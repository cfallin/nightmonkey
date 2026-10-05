/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80: */

#ifndef night_runtime_NightRegExp_h
#define night_runtime_NightRegExp_h

#include "js/RootingAPI.h"
#include "js/TypeDecls.h"
#include "js/Value.h"
#include "vm/RegExpShared.h"

namespace js {

class VectorMatchPairs;

// Collapsed AOT-matcher fast path for the RegExpMatcher (searcher=false) /
// RegExpSearcher (searcher=true) intrinsics; frame is the rooted AOT call
// frame [callee, this, regexp, string, lastIndex]. On *handled, the result
// has been written to frame[0]. *handled=false falls back to the native.
[[nodiscard]] bool NightRegExpBuiltinFast(JSContext* cx, JS::Value* frame,
                                          unsigned argc, bool searcher,
                                          bool* handled);

// Collapsed AOT fast path for the pristine RegExp.prototype.exec
// (forTest=false) / .test (forTest=true) callee-identity arm; frame is the
// rooted AOT call frame [callee, this(=regexp), string]. On *handled, the
// result (match array / null / boolean) is in frame[0]. test() allocates
// nothing on this path.
[[nodiscard]] bool NightRegExpExecTestFast(JSContext* cx, JS::Value* frame,
                                           bool forTest, bool* handled);

// The compiled exec/test arm's leaf (no GC): 1 with *out the result, 2 for a
// matching exec() (the caller builds the result), 0 to take the call. See
// the definition for what it decides.
int NightRegExpLeaf(JSContext* cx, const JS::Value& thisv,
                    const JS::Value& strv, bool forTest, JS::Value* out);

// What MIR's regexp arm needs to decide a non-matching exec/test of `thisv`
// itself (no GC): where it is an optimizable RegExpObject, neither global
// nor sticky, whose compiled shared has AOT matchers: its shape, its shared
// and the matchers' table indices (0 for an encoding without one). False
// otherwise.
bool NightRegExpLeafRow(JSContext* cx, const JS::Value& thisv,
                        uint32_t* shape, uint32_t* shared, uint32_t* latin1Idx,
                        uint32_t* twobyteIdx);

namespace night {
struct NightRegexEntry;
}

namespace irregexp {

// Try the AOT-compiled Wasm matcher for this RegExpShared (single match).
// Returns true and sets *out when the matcher decided the match; false to
// fall back to the ordinary irregexp path. Registered as the engine's
// regexpMatch hook, consulted from RegExpShared::execute (the funnel for
// Matcher/Searcher/Tester/BuiltinExec), so the whole jit-choice/interpreter
// layering is skipped on a hit.
bool TryNightRegexMatch(JSContext* cx, MutableHandleRegExpShared re,
                        Handle<JSLinearString*> input, size_t startIndex,
                        VectorMatchPairs* matches, bool latin1,
                        RegExpRunStatus* out);

// The AOT matcher entry for `re`, if it has one.
const js::night::NightRegexEntry* NightRegexEntryFor(JSContext* cx,
                                                     RegExpShared* re);

}  // namespace irregexp
}  // namespace js

#endif  // night_runtime_NightRegExp_h
