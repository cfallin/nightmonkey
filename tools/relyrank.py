#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Reliance census: what the executed Opt fast forms rest on.

Consumes a run's stderr (census counts from a `--census --guard-census`
build) and, optionally, the compile's stderr (`--dump-ctxedge` emits one
`relysite` record per reliance site naming the provenance BITS, which the
census id has no room for). Reports, per family, how much Opt fast-form
execution rests on the analysis (claim), on emitter tag tests (the shadow
analysis), on both, or on the bytecode alone (intrinsic) -- then ranks the
test-backed and mixed sites by executions: those rows, in that order, are
the analysis gaps.

  relyrank.py <run-stderr.txt> [--compile <compile-stderr.txt>]
              [--sites N] [--all-tracks]
"""
import collections
import re
import sys

FAM = [
    "arith-i32",
    "arith-num",
    "string",
    "cmp",
    "prop-obj",
    "prop-cls",
    "elem",
    "iv-rung",
]
CLS = ["intr", "claim", "test", "mixed"]
BITS = [
    (0x0001, "entry"),
    (0x0002, "arg"),
    (0x0004, "callret"),
    (0x0008, "field"),
    (0x0010, "elem"),
    (0x0020, "arith-ev"),
    (0x0040, "gname"),
    (0x0080, "alias"),
    (0x0100, "T:arith"),
    (0x0200, "T:prop"),
    (0x0400, "T:elem"),
    (0x0800, "T:cmp"),
    (0x1000, "T:frame"),
    (0x2000, "T:call"),
]
RE = re.compile(r"^night: census kind (\d+) id (\d+) n (\d+)$")
RE_SITE = re.compile(
    r"^night: relysite sid#(\d+) pc (\d+) fam (\d+) prov ([0-9a-f]+) track (\w+)$"
)


def bits_str(p):
    return "+".join(name for bit, name in BITS if p & bit) or "-"


def main():
    args = sys.argv[1:]
    topn = int(args[args.index("--sites") + 1]) if "--sites" in args else 30
    all_tracks = "--all-tracks" in args
    comp = args[args.index("--compile") + 1] if "--compile" in args else None

    fam_cls = collections.Counter()
    per_site = collections.Counter()
    site_cls = {}
    for line in open(args[0]):
        m = RE.match(line.rstrip("\n"))
        if not m:
            continue
        k, ident, n = int(m.group(1)), int(m.group(2)), int(m.group(3))
        for bump, track in ((0, "Opt"), (200, "Side"), (400, "Dirty")):
            b = k - bump
            if 66 <= b <= 97:
                fam, cls = divmod(b - 66, 4)
                if track == "Opt" or all_tracks:
                    fam_cls[(FAM[fam], CLS[cls])] += n
                    sid, pc = ident >> 16, ident & 0xFFFF
                    per_site[(sid, pc, FAM[fam], CLS[cls])] += n
                    site_cls[(sid, pc, FAM[fam])] = CLS[cls]

    site_bits = {}
    if comp:
        for line in open(comp):
            m = RE_SITE.match(line.rstrip("\n"))
            if not m:
                continue
            sid, pc, fam, p = (
                int(m.group(1)),
                int(m.group(2)),
                int(m.group(3)),
                int(m.group(4), 16),
            )
            site_bits.setdefault((sid, pc, FAM[fam]), set()).add(p)

    total = sum(fam_cls.values())
    print(f"== Opt fast-form reliance (total ticks {total:,}) ==")
    fams = sorted(
        {f for f, _ in fam_cls}, key=lambda f: -sum(fam_cls[(f, c)] for c in CLS)
    )
    print(
        f"{'family':10} {'intr':>14} {'claim':>14} {'test':>14} {'mixed':>14}  test+mixed%"
    )
    for f in fams:
        row = [fam_cls[(f, c)] for c in CLS]
        t = sum(row)
        tm = (row[2] + row[3]) / t * 100 if t else 0
        print(f"{f:10} " + " ".join(f"{v:>14,}" for v in row) + f"  {tm:5.1f}%")

    print(f"\n== test-backed / mixed rows, by executions (top {topn}) ==")
    rows = [
        (n, sid, pc, fam, cls)
        for (sid, pc, fam, cls), n in per_site.items()
        if cls in ("test", "mixed")
    ]
    rows.sort(reverse=True)
    for n, sid, pc, fam, cls in rows[:topn]:
        bits = ""
        if site_bits:
            ps = site_bits.get((sid, pc, fam), set())
            bits = " bits[" + " | ".join(sorted(bits_str(p) for p in ps)) + "]"
        print(f"  {n:>14,}  {sid}:{pc:<6} {fam:10} {cls:6}{bits}")


if __name__ == "__main__":
    main()
