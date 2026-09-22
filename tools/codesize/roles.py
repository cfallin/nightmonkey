#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Classify every generated basic block by role, then split hot vs cold.

  roles.py <dis.txt> <perf.data> <perfmap> <cwasm> <named.wasm> <cutoff>
"""
import bisect
import collections
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cwasm_syms import syms
from disan import parse
from wasmnames import names

dis, data, mapf, cwasm, namedwasm, cutoff = sys.argv[1:7]
cutoff = int(cutoff)
nm = names(namedwasm)
fa = {i: v[0] for i, v in syms(cwasm).items()}
rt = {}
for line in open(mapf):
    a, s, name = line.split(None, 2)
    m = re.match(r"wasm\[0\]::function\[(\d+)\]", name.strip())
    if m:
        rt[int(m.group(1))] = int(a, 16)
off = collections.Counter(rt[f] - fa[f] for f in rt if f in fa).most_common(1)[0][0]

insts = [i for i in parse(dis) if i[0] >= cutoff]
insts.sort(key=lambda i: i[1])
TGT = re.compile(r"^([0-9a-f]{4,})\s")
CALLT = re.compile(r"<wasm\[0\]::function\[(\d+)\]>")
starts = set()
prev = None
for k, (f, a, n, mn, ops) in enumerate(insts):
    if f != prev:
        starts.add(a)
        prev = f
    if mn.startswith("j") or mn in ("ret", "ud2", "call"):
        if k + 1 < len(insts):
            starts.add(insts[k + 1][1])
        if mn.startswith("j"):
            m = TGT.match(ops.strip())
            if m:
                starts.add(int(m.group(1), 16))
sb = sorted(starts)
blk = collections.defaultdict(list)
size = collections.Counter()
lo_ = {}
hi_ = {}
for f, a, n, mn, ops in insts:
    b = sb[bisect.bisect_right(sb, a) - 1]
    blk[b].append((mn, ops))
    size[b] += n
    lo_[b] = min(lo_.get(b, a), a)
    hi_[b] = max(hi_.get(b, a + n), a + n)

FP = re.compile(
    r"^(v?(xorpd|movsd|movapd|addsd|subsd|mulsd|divsd|sqrtsd|ucomisd|comisd|"
    r"cvtsi2sd|cvttsd2si|cvtsd2ss|roundsd|maxsd|minsd|andpd|orpd|pxor|movq|movd|"
    r"cvtsi2sdl|cvtsi2sdq|unpcklpd|shufpd))$"
)


def role(b):
    ins = blk[b]
    mns = [m for m, _ in ins]
    txt = " ".join(o for _, o in ins)
    for m, o in ins:
        cm = CALLT.search(o)
        if m == "call" and cm:
            n = nm.get(int(cm.group(1)), "")
            if n.startswith("night_runtime_"):
                return "helper: " + n[len("night_runtime_") :]
            return "call: other"
        if m == "call":
            return "call_indirect"
    if "9e3779b1" in txt or "0x9e3779b1" in txt:
        return "megamorphic probe"
    if any(FP.match(m) for m in mns):
        return "float arm"
    if "ud2" in mns:
        return "trap"
    if all(
        m in ("mov", "movl", "movq", "xor", "lea", "movabs", "jmp", "nop") for m in mns
    ):
        return "block-param shuffle"
    if mns and (mns[-1].startswith("j") and mns[-1] != "jmp"):
        return "guard / branch"
    if "ret" in mns:
        return "return"
    return "other straight-line"


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
    x = int(m.group(2), 16) - off
    j = bisect.bisect_right(sb, x) - 1
    if j < 0:
        continue
    b = sb[j]
    if b in size and lo_[b] <= x < hi_[b]:
        w[b] += p
        tot += p

R = collections.defaultdict(lambda: dict(n=0, b=0, hn=0, hb=0, w=0))
for b in blk:
    r = role(b)
    d = R[r]
    d["n"] += 1
    d["b"] += size[b]
    d["w"] += w[b]
    if w[b] > 0:
        d["hn"] += 1
        d["hb"] += size[b]
totb = sum(d["b"] for d in R.values())
print(
    f"{'role':<40}{'blocks':>9}{'KiB':>9}{'%code':>7}{'exec KiB':>10}{'exec%':>7}{'%cycles':>9}"
)
print("-" * 91)
for r, d in sorted(R.items(), key=lambda kv: -kv[1]["b"]):
    print(
        f"{r:<40}{d['n']:>9}{d['b']/1024:>9.1f}{100*d['b']/totb:>6.1f}%"
        f"{d['hb']/1024:>10.1f}{100*d['hb']/max(d['b'],1):>6.1f}%{100*d['w']/max(tot,1):>8.1f}%"
    )
print("-" * 91)
hb = sum(d["hb"] for d in R.values())
print(
    f"{'TOTAL':<40}{sum(d['n'] for d in R.values()):>9}{totb/1024:>9.1f}{'':>7}"
    f"{hb/1024:>10.1f}{100*hb/totb:>6.1f}%"
)
