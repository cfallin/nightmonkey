#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Bytecode-level profile from op markers.

Usage: opprof.py <perf.jit.data> <opmap.txt> <so-dir> [--sites N] [--script SID]

Walks every hot jitted-*.so, attributes each sampled instruction to the
nearest preceding marker store `movl $imm,0xXX(%rbx)` (imm = sid<<16|pc) in
linear code order, joins with the opmap (sid pc op), and reports:
  - totals per JSOp kind
  - totals per script
  - top individual (script, pc, op) sites
Samples before the first marker in a symbol go to <prologue>; samples in
unmarked trailing regions attribute to the last marker (caveat: out-of-line
blocks inherit the linearly-preceding marker).
"""
import bisect
import os
import re
import subprocess
import sys
from collections import defaultdict

perfdata, opmapf, sodir = sys.argv[1], sys.argv[2], sys.argv[3]
nsites = 40
only_script = None
if "--sites" in sys.argv:
    nsites = int(sys.argv[sys.argv.index("--sites") + 1])
if "--script" in sys.argv:
    only_script = int(sys.argv[sys.argv.index("--script") + 1])

opname = {}
for line in open(opmapf):
    if line.startswith("opmap "):
        _, sid, pc, op = line.split()
        opname[(int(sid), int(pc))] = op

# 1. Sample weights per (symbol, offset) + symbol -> dso map.
out = subprocess.run(
    ["perf", "script", "-i", perfdata], check=False, capture_output=True, text=True
).stdout
w = defaultdict(lambda: defaultdict(int))
total_all = 0
sym_total = defaultdict(int)
sym_dso = {}
pat = re.compile(
    r"(\d+)\s+\S*cycles\S*:\s+[0-9a-f]+\s+(\S+?)\+0x([0-9a-f]+)\s+\((\S+)\)"
)
for line in out.splitlines():
    m = pat.search(line)
    if not m:
        continue
    period = int(m.group(1))
    total_all += period
    sym = m.group(2)
    if sym.startswith("night_script_"):
        w[sym][int(m.group(3), 16)] += period
        sym_total[sym] += period
        sym_dso[sym] = m.group(4)

# 2. For each hot symbol, find its .so, build marker map, attribute.
per_op = defaultdict(int)
per_script = defaultdict(int)
per_site = defaultdict(int)
mark_pat = re.compile(r"movl?\s+\$0x([0-9a-f]+),(0x[0-9a-f]+)\(%r\w+\)")
scratch_off = None  # auto-detected: the store target all markers share

hot_syms = sorted(sym_total, key=lambda s: -sym_total[s])
covered = 0
for sym in hot_syms:
    if sym_total[sym] < total_all * 0.002:
        break
    sofile = os.path.join(sodir, os.path.basename(sym_dso[sym]))
    if not os.path.exists(sofile):
        print(f"!! no .so for {sym} ({sofile})", file=sys.stderr)
        continue
    dis = subprocess.run(
        ["objdump", "-d", sofile], check=False, capture_output=True, text=True
    ).stdout
    in_sym = False
    sym_start = None
    marker_offs = []  # sorted (offset, (sid, pc))
    inst_offs = []
    for line in dis.splitlines():
        m = re.match(r"^([0-9a-f]+) <(.+)>:$", line)
        if m:
            in_sym = m.group(2) == sym
            if in_sym:
                sym_start = int(m.group(1), 16)
            continue
        if not in_sym:
            continue
        m = re.match(r"^\s+([0-9a-f]+):\s+(?:[0-9a-f]{2} )+\s*(.*)$", line)
        if not m or not m.group(2):
            continue
        off = int(m.group(1), 16) - sym_start
        inst_offs.append(off)
        mm = mark_pat.search(m.group(2))
        if mm:
            imm = int(mm.group(1), 16)
            marker_offs.append((off, (imm >> 16, imm & 0xFFFF), mm.group(2)))
    # The scratch word is the store target shared by (nearly) all marker
    # candidates; drop stores to other addresses (real code storing
    # constants).
    if marker_offs:
        from collections import Counter

        if scratch_off is None:
            scratch_off = Counter(t for _, _, t in marker_offs).most_common(1)[0][0]
        marker_offs = [(o, k) for o, k, t in marker_offs if t == scratch_off]
    mo = [o for o, _ in marker_offs]
    for off, weight in w[sym].items():
        i = bisect.bisect_right(mo, off) - 1
        if i < 0:
            key = (int(sym.rsplit("_", 1)[1]), -1)  # prologue
        else:
            key = marker_offs[i][1]
        sid, pc = key
        op = "<prologue>" if pc == -1 else opname.get((sid, pc), f"?{pc}")
        per_op[op] += weight
        per_script[sid] += weight
        per_site[(sid, pc, op, sym)] += weight
        covered += weight

print(
    f"attributed {covered} cycles = {100.0*covered/max(total_all,1):.1f}% "
    f"of all samples (rest = helpers/kernel/runtime)"
)

print("\n== by op kind ==")
for op, weight in sorted(per_op.items(), key=lambda kv: -kv[1])[:40]:
    print(f"  {100.0*weight/max(total_all,1):6.2f}%  {op}")

print("\n== by script ==")
for sid, weight in sorted(per_script.items(), key=lambda kv: -kv[1])[:12]:
    print(f"  {100.0*weight/max(total_all,1):6.2f}%  #{sid}")

print(f"\n== top {nsites} sites ==")
for (sid, pc, op, sym), weight in sorted(per_site.items(), key=lambda kv: -kv[1])[
    :nsites
]:
    if only_script and sid != only_script:
        continue
    print(
        f"  {100.0*weight/max(total_all,1):6.2f}%  #{sid} pc {pc:<5} {op:16} in {sym} ({sym_dso.get(sym,'?')})"
    )
