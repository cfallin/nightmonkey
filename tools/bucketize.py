#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Bucketize perf report output: compiled JS / night runtime helpers / SM internals / GC / strings / wasmtime / kernel."""
import collections
import re
import subprocess
import sys

data = sys.argv[1]
out = subprocess.run(
    [
        "perf",
        "report",
        "-i",
        data,
        "--stdio",
        "--no-children",
        "--percent-limit",
        "0.01",
    ],
    check=False,
    capture_output=True,
    text=True,
).stdout

buckets = collections.Counter()
syms = collections.Counter()
total = 0.0
for line in out.splitlines():
    m = re.match(r"\s+(\d+\.\d+)%\s+\S+\s+(\S+)\s+\[[.k]\]\s+(.*)", line)
    if not m:
        continue
    pct, dso, sym = float(m.group(1)), m.group(2), m.group(3)
    total += pct
    syms[sym] += pct
    if dso.startswith("[kernel"):
        b = "kernel"
    elif dso == "wasmtime" or "libc" in dso or dso.startswith("["):
        b = "wasmtime-host"
    elif (
        sym.startswith("night_script")
        or sym.startswith("night_toplevel")
        or sym.startswith("night_main")
    ):
        b = "compiled-js"
    elif sym.startswith("night_runtime_") or sym.startswith("night_"):
        b = "night-rt-helper"
    elif re.search(
        r"js::gc::|GCMarker|js::Nursery|TenuringTracer|StoreBuffer|GCRuntime|js::gc\b|Arena|Chunk.*sweep|::sweep|Sweep|Mark(?!er)",
        sym,
    ):
        b = "gc"
    elif re.search(
        r"String|Atomize|Rope|memcmp|Concat|Deflate|char16_t.*Compare|CompareChars|EqualChars|Dedup",
        sym,
    ):
        b = "strings"
    elif re.search(r"RegExp|irregexp", sym):
        b = "regexp"
    else:
        b = "sm-internals"
    buckets[b] += pct

print(f"total attributed: {total:.1f}%")
for b, p in buckets.most_common():
    print(f"  {b:15s} {p:6.2f}%")
print("\ntop symbols:")
for s, p in syms.most_common(40):
    print(f"  {p:6.2f}%  {s[:120]}")
