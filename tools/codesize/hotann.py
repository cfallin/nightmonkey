# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""hotann.py <perf.data> <perfmap> <cwasm> <funcidx> <name> <min%>: sample-annotated disassembly of one function (lines at or above min% of its samples)"""

import collections
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cwasm_syms import syms

data, mapf, cwasm, fi, fname, thr = (
    sys.argv[1],
    sys.argv[2],
    sys.argv[3],
    int(sys.argv[4]),
    sys.argv[5],
    float(sys.argv[6]),
)
rt = None
for line in open(mapf):
    a, s, name = line.split(None, 2)
    if name.strip() == fname:
        rt = (int(a, 16), int(s, 16))
fa, fs = syms(cwasm)[fi]
dis = subprocess.run(
    [
        "objdump",
        "-d",
        "--no-show-raw-insn",
        f"--start-address={fa}",
        f"--stop-address={fa+fs}",
        cwasm,
    ],
    check=False,
    capture_output=True,
    text=True,
).stdout
ins = []
for ln in dis.splitlines():
    m = re.match(r"^\s*([0-9a-f]+):\s+(.*)$", ln)
    if m:
        ins.append(
            (
                int(m.group(1), 16),
                re.sub(
                    r"<wasm\[0\]::function\[\d+\]::night_script_\d+\+", "<+", m.group(2)
                ),
            )
        )
out = subprocess.run(
    ["perf", "script", "-i", data, "-F", "period,ip"],
    check=False,
    capture_output=True,
    text=True,
).stdout
pat = re.compile(r"^\s*(\d+)\s+([0-9a-f]+)\s*$")
w = collections.Counter()
tot = 0
for ln in out.splitlines():
    m = pat.match(ln)
    if not m:
        continue
    p = int(m.group(1))
    ip = int(m.group(2), 16)
    if rt[0] <= ip < rt[0] + rt[1]:
        w[ip - rt[0] + fa] += p
        tot += p
n = 0
for a, txt in ins:
    pw = 100 * w[a] / tot
    if pw >= thr:
        n += 1
        print(f"{pw:5.2f} {a:x} {txt}")
print("insts printed:", n)
