#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Dynamic track census, from a run of a module built with `nightmonkey --census`.

The static censuses say how much *code* is on each track. This says how much
*execution* is, which is the number the Opt-track work is actually trying to
move.

  census.py <run-stderr.txt> [--sites N]

Counts are version ENTRIES, not cycles: one tick per version entered, so a
version doing a lot of work counts the same as a trivial one. That is the
honest reading, and it is why the instrumented build's own score is
meaningless -- a call per entry is a ~30x tax that falls on entries, not work.

Kinds: 1/2/3 = version entry on Opt/Side/Dirty. 48/49/50 = the effect-flag
fork's clean / keep-facts (stamps intact) / dirty arm. `id` packs
(sid << 16) | pc.
"""
import collections
import re
import sys

RE = re.compile(r"^night: census kind (\d+) id (\d+) n (\d+)$")
NAME = {
    1: "Opt",
    2: "Side",
    3: "Dirty",
    48: "fork-clean",
    49: "fork-stamp",
    50: "fork-dirty",
}


def main():
    path = sys.argv[1]
    topn = int(sys.argv[sys.argv.index("--sites") + 1]) if "--sites" in sys.argv else 12
    by_kind = collections.Counter()
    per_site = collections.defaultdict(collections.Counter)
    sites_seen = collections.defaultdict(set)
    for line in open(path):
        m = RE.match(line.rstrip("\n"))
        if not m:
            continue
        kind, ident, n = int(m.group(1)), int(m.group(2)), int(m.group(3))
        by_kind[kind] += n
        per_site[ident][kind] += n
        sites_seen[kind].add(ident)

    entries = sum(by_kind[k] for k in (1, 2, 3))
    if entries:
        print(f"version entries executed: {entries:,}")
        for k in (1, 2, 3):
            print(
                f"   {NAME[k]:<6}{by_kind[k]:>14,} ({100 * by_kind[k] / entries:>5.1f}%)   "
                f"over {len(sites_seen[k]):>6} distinct versions"
            )

    clean, stamp, dirty = by_kind[48], by_kind[49], by_kind[50]
    if clean or stamp or dirty:
        tot = clean + stamp + dirty
        print(f"\neffect-flag fork takes: {tot:,}")
        print(f"   clean (stayed on Opt) {clean:>14,} ({100 * clean / tot:>5.1f}%)")
        print(f"   stamps-intact (Opt)   {stamp:>14,} ({100 * stamp / tot:>5.1f}%)")
        print(f"   dirty                 {dirty:>14,} ({100 * dirty / tot:>5.1f}%)")
        rows = [
            (i, c[48] + c[49], c[50])
            for i, c in per_site.items()
            if c[48] or c[49] or c[50]
        ]
        print(
            f"\n{'fork site (sid:pc)':<22}{'clean+stamp':>14}{'dirty':>14}{'clean%':>9}"
        )
        for i, cl, dy in sorted(rows, key=lambda r: -(r[1] + r[2]))[:topn]:
            print(
                f"{f'{i >> 16}:{i & 0xffff}':<22}{cl:>14,}{dy:>14,}"
                f"{100 * cl / max(cl + dy, 1):>8.1f}%"
            )

    if entries:
        print(
            f"\n{'hottest versions (sid:pc)':<26}{'track':>7}{'entries':>14}{'% of all':>10}"
        )
        rows = [
            (i, k, n)
            for i, c in per_site.items()
            for k, n in c.items()
            if k in (1, 2, 3)
        ]
        for i, k, n in sorted(rows, key=lambda r: -r[2])[:topn]:
            print(
                f"{f'{i >> 16}:{i & 0xffff}':<26}{NAME[k]:>7}{n:>14,}{100 * n / entries:>9.2f}%"
            )


if __name__ == "__main__":
    main()
