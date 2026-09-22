/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

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

}  // namespace irregexp
}  // namespace js

#endif  // night_runtime_NightRegExp_h
