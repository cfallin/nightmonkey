/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80: */

#ifndef night_runtime_NightSnapshotExtras_h
#define night_runtime_NightSnapshotExtras_h

#include <set>
#include <stdint.h>
#include <string>
#include <utility>
#include <vector>

#include "js/GCVector.h"
#include "js/TypeDecls.h"

namespace js {
namespace night {

// One collected regex literal program (both subject encodings), shared
// between the snapshot-extras capture and the in-process batch.
struct NightRegexProgram {
  std::u16string pattern;
  uint32_t flags = 0;
  std::vector<uint8_t> latin1;
  std::vector<uint8_t> twobyte;
  uint32_t numRegisters = 0;
  uint32_t pairCount = 0;
};

// Pre-pass over a script tree collecting regex literal programs (the tree
// is already delazified). May GC; run before a walk takes raw heap
// addresses.
bool CollectRegexPrograms(JSContext* cx, JS::Handle<JSScript*> root,
                          std::set<std::pair<std::u16string, uint32_t>>& seen,
                          std::vector<NightRegexProgram>& out);

// Resolve the self-hosted allowlist against the live global, delazify each
// tree, and append it to the registration digest. Outputs the resolved
// scripts and their dotted paths (parallel vectors).
bool ResolveSelfHostedRoots(JSContext* cx,
                            JS::MutableHandleVector<JSScript*> shScripts,
                            std::vector<const char*>& shPaths);

}  // namespace night
}  // namespace js

#endif  // night_runtime_NightSnapshotExtras_h
