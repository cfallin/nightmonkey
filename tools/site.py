#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Dump the code region(s) for one (sid, pc) marker with sample weights.

Usage: site.py <perf.jit.data> <so> <symbol> <sid> <pc> [maxinst]
"""
import re
import subprocess
import sys
from collections import defaultdict

perfdata, so, symbol = sys.argv[1], sys.argv[2], sys.argv[3]
sid, pc = int(sys.argv[4]), int(sys.argv[5])
maxinst = int(sys.argv[6]) if len(sys.argv) > 6 else 80
want = (sid << 16) | pc

out = subprocess.run(
    ["perf", "script", "-i", perfdata], check=False, capture_output=True, text=True
).stdout
w = defaultdict(int)
total = 0
pat = re.compile(r"(\d+)\s+cycles:P?:\s+[0-9a-f]+\s+(\S+?)\+0x([0-9a-f]+)")
for line in out.splitlines():
    m = pat.search(line)
    if not m:
        continue
    total += int(m.group(1))
    if m.group(2) == symbol:
        w[int(m.group(3), 16)] += int(m.group(1))

dis = subprocess.run(
    ["objdump", "-d", so], check=False, capture_output=True, text=True
).stdout
in_sym = False
sym_start = None
lines = []
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
mark = re.compile(r"movl?\s+\$0x([0-9a-f]+),(0x[0-9a-f]+)\(%r\w+\)")
regions = []
for i, (off, txt) in enumerate(lines):
    m = mark.search(txt)
    if m and int(m.group(1), 16) == want:
        regions.append(i)

for r in regions:
    print(f"== region at +0x{lines[r][0]:x} ==")
    for i in range(r, min(len(lines), r + maxinst)):
        m = mark.search(lines[i][1])
        if m and i > r:
            imm = int(m.group(1), 16)
            print(f"  -- next marker: #{imm>>16} pc {imm&0xffff} --")
            break
        weight = w.get(lines[i][0], 0)
        # sum weights of any sampled address at this instruction
        pct = 100.0 * weight / max(total, 1)
        mk = f"{pct:5.2f}" if weight else "     "
        print(f"  {mk}  +0x{lines[i][0]:<6x} {lines[i][1]}")
    print()
