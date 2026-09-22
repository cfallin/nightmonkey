# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""hotmix.py <perf.data> <perfmap> <cwasm> <funcidx> <name>: sample-weighted instruction-class mix of one function (name = the --keep-names perfmap entry, e.g. night_script_380)"""

import collections
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cwasm_syms import syms

data, mapf, cwasm, fi, fname = (
    sys.argv[1],
    sys.argv[2],
    sys.argv[3],
    int(sys.argv[4]),
    sys.argv[5],
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
ins = {}
for ln in dis.splitlines():
    m = re.match(r"^\s*([0-9a-f]+):\s+(\S+)\s*(.*)$", ln)
    if m:
        ins[int(m.group(1), 16)] = (m.group(2), m.group(3))
out = subprocess.run(
    ["perf", "script", "-i", data, "-F", "period,ip"],
    check=False,
    capture_output=True,
    text=True,
).stdout
pat = re.compile(r"^\s*(\d+)\s+([0-9a-f]+)\s*$")


def cls(mn, ops):
    if mn.startswith(("cvt", "vcvt")):
        return "fp-convert"
    if mn in ("ucomisd", "vucomisd", "comisd", "vcomisd"):
        return "fp-compare"
    if mn.startswith(
        (
            "vadd",
            "vsub",
            "vmul",
            "vdiv",
            "vsqrt",
            "addsd",
            "subsd",
            "mulsd",
            "divsd",
            "sqrtsd",
            "vxorpd",
            "xorpd",
            "vandpd",
            "andpd",
            "vmovq",
            "movq",
            "vmovd",
            "movd",
            "movaps",
            "movapd",
            "vmovsd",
            "movsd",
            "movdqu",
        )
    ):
        return "fp-arith/move"
    if "(%rsp)" in ops or "(%rbp)" in ops:
        return "stack-spill/reload"
    if mn.startswith("j"):
        return "branch"
    if mn in {"call", "ret"}:
        return "call/ret"
    if mn.startswith(("set", "cmov")):
        return "flags-materialize"
    if mn in ("cmp", "test"):
        return "cmp/test"
    if "(" in ops:
        return "heap load/store"
    if mn in ("mov", "movabs", "movslq", "movzx", "movsx", "movl", "movzbl"):
        return "reg move"
    return "alu"


w = collections.Counter()
tot = 0
miss = 0
for ln in out.splitlines():
    m = pat.match(ln)
    if not m:
        continue
    p = int(m.group(1))
    ip = int(m.group(2), 16)
    if not (rt[0] <= ip < rt[0] + rt[1]):
        continue
    a = ip - rt[0] + fa
    if a not in ins:
        miss += p
        continue
    tot += p
    w[cls(*ins[a])] += p
# static mix over the 90% hot set for comparison: count instructions of each class in the function
st = collections.Counter(cls(*v) for v in ins.values())
print(f"{fname}: {tot} weighted samples ({miss} unmapped); function {len(ins)} insts")
print(f"{'class':<22}{'%samples':>10}{'%static':>10}")
for c, p in w.most_common():
    print(f"{c:<22}{100*p/tot:>9.1f}%{100*st[c]/len(ins):>9.1f}%")
