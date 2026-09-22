#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Executed-code footprint of the AOT-generated region.

Joins perf samples against wasmtime's perfmap: how many distinct 64B lines /
4K pages of our generated functions actually run, vs how many exist.
"""
import bisect
import collections
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(__file__))

data, mapf, cutoff = sys.argv[1], sys.argv[2], int(sys.argv[3])
starts, sizes, idxs = [], [], []
for line in open(mapf):
    a, s, name = line.split(None, 2)
    m = re.match(r"wasm\[0\]::function\[(\d+)\]", name.strip())
    if not m:
        continue
    starts.append(int(a, 16))
    sizes.append(int(s, 16))
    idxs.append(int(m.group(1)))
order = sorted(range(len(starts)), key=lambda i: starts[i])
starts = [starts[i] for i in order]
sizes = [sizes[i] for i in order]
idxs = [idxs[i] for i in order]

out = subprocess.run(
    ["perf", "script", "-i", data, "-F", "period,ip"],
    check=False,
    capture_output=True,
    text=True,
).stdout
pat = re.compile(r"^\s*(\d+)\s+([0-9a-f]+)\s*$")
line_w = collections.Counter()
func_w = collections.Counter()
tot = ours = 0
for ln in out.splitlines():
    m = pat.match(ln)
    if not m:
        continue
    p = int(m.group(1))
    ip = int(m.group(2), 16)
    tot += p
    j = bisect.bisect_right(starts, ip) - 1
    if j < 0 or ip >= starts[j] + sizes[j]:
        continue
    if idxs[j] < cutoff:
        continue
    ours += p
    line_w[ip >> 6] += p
    func_w[idxs[j]] += p

stat_lines = sum((sizes[i] + 63) // 64 for i in range(len(starts)) if idxs[i] >= cutoff)
stat_bytes = sum(sizes[i] for i in range(len(starts)) if idxs[i] >= cutoff)
stat_funcs = sum(1 for i in range(len(starts)) if idxs[i] >= cutoff)
print(f"samples: total {tot}, in generated code {ours} ({100*ours/max(tot,1):.1f}%)")
print(
    f"static generated: {stat_funcs} funcs, {stat_bytes/1024:.0f} KiB, {stat_lines} cache lines"
)
print(
    f"touched: {len(func_w)} funcs, {len(line_w)} lines = {len(line_w)*64/1024:.0f} KiB "
    f"({100*len(line_w)/max(stat_lines,1):.1f}% of static)"
)
pages = {ip6 >> 6 for ip6 in line_w}  # 64B line -> 4K page
hot_addrs = [k << 6 for k in line_w]
span = (max(hot_addrs) - min(hot_addrs) + 64) if hot_addrs else 0
print(
    f"hot span: {span/1024:.0f} KiB of address space, {len(pages)} distinct 4K pages "
    f"(compacted would be {(len(line_w)*64+4095)//4096} pages)"
)
ranked = line_w.most_common()
for pct in (50, 80, 90, 95, 99):
    need = ours * pct / 100
    c = 0
    k = 0
    for _, w in ranked:
        c += w
        k += 1
        if c >= need:
            break
    print(f"  {pct}% of cycles in {k} lines = {k*64/1024:>7.1f} KiB")
print()
print("top functions by cycles (generated only):")
fsize = {idxs[i]: sizes[i] for i in range(len(starts))}
for f, w in func_w.most_common(12):
    print(f"  func[{f}] {100*w/max(ours,1):>5.1f}%  size {fsize[f]:>7} B")
