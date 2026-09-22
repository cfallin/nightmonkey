#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""The rejoin audit: which arms strip which facts when they join an Opt
version, from `nightmonkey --dump-ctxedge`'s `rejoinloss` records.

Each record is one slot one join weakened, with the pre-join fact's
provenance bits. The join law says an arm that loses an ANALYSIS fact does
not belong in Opt: the claim-backed rows are the violators; test-backed rows
are part-(i) analysis gaps (the fact was never the analysis's to lose);
intrinsic rows and interval-only widenings are the fixpoint converging.

  rejoin.py <compile-stderr.txt ...> [--rows N] [--all]

Interval-only weakenings (pre and post differ only in `:iv[...]`) are
dropped unless --all: they are loop-accumulator convergence, not arms.
"""
import collections
import re
import sys

RE = re.compile(
    r"^night: rejoinloss sid#(\d+) pc (\d+) op (\S+) at (\d+) slot (\S+) "
    r"pre (\S+) post (\S+) arr (\S+) prov ([0-9a-f]+)$"
)
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


def strip_iv(f):
    return re.sub(r":iv\[[^\]]*\]", "", f)


def bits_str(p):
    return "+".join(name for bit, name in BITS if p & bit) or "-"


def main():
    args = sys.argv[1:]
    topn = int(args[args.index("--rows") + 1]) if "--rows" in args else 40
    keep_iv = "--all" in args
    files = [a for a in args if not a.startswith("--") and not a.isdigit()]
    rows = collections.Counter()
    sites = collections.defaultdict(set)
    examples = {}
    for path in files:
        for line in open(path):
            m = RE.match(line.rstrip("\n"))
            if not m:
                continue
            sid, pc, op, at, slot, pre, post, arr, prov = m.groups()
            if not keep_iv and strip_iv(pre) == strip_iv(post):
                continue
            p = int(prov, 16)
            claim = "CLAIM" if p & 0xFF else ("test" if p & 0xFF00 else "intr")
            key = (claim, op, strip_iv(pre) + " -> " + strip_iv(post), bits_str(p))
            rows[key] += 1
            sites[key].add(f"{sid}:{pc}")
            examples.setdefault(key, f"{sid}:{pc} slot {slot} arr {arr}")
    print(
        f"== rejoin losses (records {sum(rows.values())}, "
        f"{len({s for ss in sites.values() for s in ss})} sites) =="
    )
    print(f"{'n':>7} {'sites':>6}  {'class':6} {'op':16} {'fact':44} bits / example")
    for key, n in rows.most_common(topn):
        claim, op, fact, bits = key
        print(
            f"{n:>7} {len(sites[key]):>6}  {claim:6} {op:16} {fact:44} "
            f"[{bits}]  e.g. {examples[key]}"
        )


if __name__ == "__main__":
    main()
