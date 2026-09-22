#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Static analysis of the AOT-generated native code in a cwasm.

  disan.py <dis.txt> [perf.data map] ...
Reports: instruction mix, spill/reload traffic (rsp-relative moves), and --
when a perf profile is supplied -- the hot/cold basic-block byte split.
"""
import collections
import re
import sys

FN = re.compile(r"^([0-9a-f]+) <wasm\[0\]::function\[(\d+)\]>:")
IN = re.compile(r"^\s+([0-9a-f]+):\t([0-9a-f ]+)\t\s*(\S+)\s*(.*)$")
BR = re.compile(r"^(j\w+|call|ret|ud2|hlt)")
TGT = re.compile(r"\b([0-9a-f]{5,})\s+<")


def parse(path):
    """-> list of (func, addr, len, mnem, ops)"""
    insts = []
    cur = None
    for line in open(path):
        m = FN.match(line)
        if m:
            cur = int(m.group(2))
            continue
        m = IN.match(line)
        if not m or cur is None:
            continue
        addr = int(m.group(1), 16)
        nb = len(m.group(2).split())
        insts.append((cur, addr, nb, m.group(3), m.group(4)))
    return insts


RSP = re.compile(r"(-?0x[0-9a-f]+)?\(%rsp\)")
MOVS = (
    "mov",
    "movl",
    "movq",
    "movsd",
    "movss",
    "movups",
    "movaps",
    "movdqu",
    "movdqa",
    "movabs",
)


def main():
    insts = parse(sys.argv[1])
    nfun = len(set(i[0] for i in insts))
    tot = sum(i[2] for i in insts)
    print(f"{len(insts)} instructions, {nfun} functions, {tot/1024:.0f} KiB")

    mix = collections.Counter()
    mixb = collections.Counter()
    spill = reload_ = 0
    spillb = reloadb = 0
    for f, a, n, mn, ops in insts:
        if mn.startswith("j"):
            k = "branch"
        elif mn == "call":
            k = "call"
        elif mn.startswith("cmp") or mn.startswith("test"):
            k = "compare"
        elif mn.startswith("mov") and RSP.search(ops):
            k = "stackmove"
            src, _, dst = ops.rpartition(",")
            if RSP.search(dst):
                spill += 1
                spillb += n
            else:
                reload_ += 1
                reloadb += n
        elif mn.startswith("mov") and "(%" in ops:
            k = "memmove"
        elif mn.startswith("mov") or mn == "lea":
            k = "regmove"
        elif mn in ("push", "pop"):
            k = "pushpop"
        elif mn == "ret":
            k = "ret"
        elif mn == "ud2":
            k = "trap"
        else:
            k = "alu/other"
        mix[k] += 1
        mixb[k] += n
    print(f"\n{'class':<12}{'count':>9}{'%inst':>7}{'bytes':>10}{'%bytes':>8}")
    for k, c in mix.most_common():
        print(
            f"{k:<12}{c:>9}{100*c/len(insts):>6.1f}%{mixb[k]:>10}{100*mixb[k]/tot:>7.1f}%"
        )
    print(
        f"\nspills {spill} ({spillb} B), reloads {reload_} ({reloadb} B); "
        f"stack traffic = {100*(spill+reload_)/len(insts):.1f}% of instructions, "
        f"{100*(spillb+reloadb)/tot:.1f}% of bytes"
    )
    return insts


if __name__ == "__main__":
    main()
