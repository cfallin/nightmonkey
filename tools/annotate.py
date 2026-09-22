#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Annotate a jitted-*.so function with perf sample weights.

Usage: annotate.py <perf.jit.data> <symbol> <jitted.so> [--top N] [--all]
Prints the function disassembly with per-instruction cycle weights and a
hot-cluster summary (clusters of consecutive instructions holding >0.05%).
"""
import bisect
import re
import subprocess
import sys
from collections import defaultdict

perfdata, symbol, so = sys.argv[1], sys.argv[2], sys.argv[3]
topn = 40
show_all = "--all" in sys.argv
if "--top" in sys.argv:
    topn = int(sys.argv[sys.argv.index("--top") + 1])

# 1. Sample weights per offset within symbol.
out = subprocess.run(
    ["perf", "script", "-i", perfdata], check=False, capture_output=True, text=True
).stdout
w = defaultdict(int)
total_sym = 0
total_all = 0
# Event name varies by perf version: "cycles:", "cycles:P:", "cpu/cycles/P:".
pat = re.compile(r"(\d+)\s+\S*cycles\S*:\s+[0-9a-f]+\s+(\S+?)\+0x([0-9a-f]+)")
for line in out.splitlines():
    m = pat.search(line)
    if not m:
        continue
    period = int(m.group(1))
    total_all += period
    if m.group(2) == symbol:
        w[int(m.group(3), 16)] += period
        total_sym += period

# 2. Disassembly of the symbol.
dis = subprocess.run(
    ["objdump", "-d", so], check=False, capture_output=True, text=True
).stdout
lines = []
in_sym = False
sym_start = None
for line in dis.splitlines():
    m = re.match(r"^([0-9a-f]+) <(.+)>:$", line)
    if m:
        in_sym = m.group(2) == symbol
        if in_sym:
            sym_start = int(m.group(1), 16)
        continue
    if not in_sym:
        continue
    m = re.match(r"^\s+([0-9a-f]+):\s+(?:[0-9a-f]{2} )+\s*(.*)$", line)
    if m and m.group(2):
        lines.append((int(m.group(1), 16) - sym_start, m.group(2)))

offs = [o for o, _ in lines]

# Attribute each sample to the containing instruction (perf IP is the
# sampled instruction itself with precise events; close enough either way).
instw = defaultdict(int)
for off, weight in w.items():
    i = bisect.bisect_right(offs, off) - 1
    if i >= 0:
        instw[i] += weight

print(
    f"symbol {symbol}: {total_sym} cycles = "
    f"{100.0*total_sym/max(total_all,1):.1f}% of all samples; "
    f"{len(lines)} instructions"
)

# 3. Hot clusters: consecutive instructions each >= 0.05% of symbol time,
# merged; report clusters by total weight.
thr = total_sym * 0.0005
clusters = []
cur = None
for i in range(len(lines)):
    if instw.get(i, 0) >= thr:
        if cur and i - cur[1] <= 3:
            cur[1] = i
            cur[2] += instw.get(i, 0)
        else:
            if cur:
                clusters.append(cur)
            cur = [i, i, instw.get(i, 0)]
    # gap: allow up to 3 cold instructions inside a cluster
if cur:
    clusters.append(cur)
clusters.sort(key=lambda c: -c[2])

print(f"\n== top {topn} hot clusters ==")
for a, b, weight in clusters[:topn]:
    print(
        f"\n-- cluster {100.0*weight/max(total_sym,1):5.2f}% of fn "
        f"({100.0*weight/max(total_all,1):5.2f}% total) "
        f"@ +0x{offs[a]:x}..+0x{offs[b]:x}"
    )
    for i in range(max(0, a - 2), min(len(lines), b + 3)):
        pct = 100.0 * instw.get(i, 0) / max(total_sym, 1)
        mark = f"{pct:5.2f}" if instw.get(i, 0) else "     "
        print(f"  {mark}  +0x{lines[i][0]:<6x} {lines[i][1]}")

if show_all:
    print("\n== full annotated disassembly ==")
    for i, (off, txt) in enumerate(lines):
        pct = 100.0 * instw.get(i, 0) / max(total_sym, 1)
        mark = f"{pct:5.2f}" if instw.get(i, 0) else "     "
        print(f"  {mark}  +0x{off:<6x} {txt}")
