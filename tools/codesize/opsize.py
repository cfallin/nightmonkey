#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Static code-size attribution by JS opcode, from --dump-opsize."""
import collections
import re
import sys

# `dmerge` was added later; keep it optional so the tool reads both vintages.
RE = re.compile(
    r"^night: opsize sid#(\d+) pc (\d+) lpc (\d+) op (\S+) track (\S+) spliced (\d) "
    r"(?:dmerge (\S+) )?(?:rung (\S+) )?"
    r"blocks (\d+) params (\d+) insts (\d+) alu (\d+) load (\d+) store (\d+) "
    r"call (\d+) boxing (\d+) const (\d+) other (\d+)$"
)
FIELDS = "blocks params insts alu load store call boxing const other".split()


def load(path):
    recs = []
    for line in open(path):
        m = RE.match(line.rstrip("\n"))
        if m:
            g = m.groups()
            recs.append(
                dict(
                    sid=int(g[0]),
                    pc=int(g[1]),
                    op=g[3],
                    track=g[4],
                    spliced=int(g[5]),
                    dmerge=g[6],
                    rung=g[7],
                    **{f: int(v) for f, v in zip(FIELDS, g[8:])},
                )
            )
    return recs


def report(path, native_bytes=None, topn=25):
    recs = load(path)
    per = collections.defaultdict(lambda: collections.Counter())
    n = collections.Counter()
    for r in recs:
        n[r["op"]] += 1
        for f in FIELDS:
            per[r["op"]][f] += r[f]
    tot_insts = sum(per[o]["insts"] for o in per)
    tot_ops = sum(n.values())
    scale = (native_bytes / tot_insts) if native_bytes and tot_insts else None
    print(f"{path}: {tot_ops} op instances, {tot_insts} IR insts", end="")
    if scale:
        print(f", {native_bytes} native bytes -> {scale:.2f} bytes/IR-inst")
    else:
        print()
    hdr = f"{'JSOp':<28}{'count':>7}{'IRinsts':>10}{'share':>7}{'ins/op':>7}{'blk/op':>7}{'call':>6}{'load':>6}{'store':>6}{'const':>6}"
    if scale:
        hdr += f"{'B/op':>7}{'KiB tot':>9}"
    print(hdr)
    print("-" * len(hdr))
    for op, _ in sorted(per.items(), key=lambda kv: -kv[1]["insts"])[:topn]:
        c = per[op]
        k = n[op]
        row = (
            f"{op:<28}{k:>7}{c['insts']:>10}{100*c['insts']/tot_insts:>6.1f}%"
            f"{c['insts']/k:>7.1f}{c['blocks']/k:>7.1f}{c['call']/k:>6.1f}"
            f"{c['load']/k:>6.1f}{c['store']/k:>6.1f}{c['const']/k:>6.1f}"
        )
        if scale:
            row += f"{scale*c['insts']/k:>7.0f}{scale*c['insts']/1024:>9.1f}"
        print(row)
    return per, n, tot_insts


if __name__ == "__main__":
    nb = int(sys.argv[2]) if len(sys.argv) > 2 else None
    report(sys.argv[1], nb)
