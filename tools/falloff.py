#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Silent fall-off census: where lineages leave Opt without a departure tick.

Walks each script's version-entry counts (kinds 1/3) in pc order and reports
every pc where the Opt-entered mass of one pc becomes Dirty-entered mass at
the next entered pc, with NO departure event (kinds 150-158, the fork arms
48-50, or the keep 49) ticked at the earlier pc. Those are the merge-back
joins -- an in-version diamond that joined a helper arm's stepped state --
which the departure census cannot see and rootcause.py smears onto the last
real departure.

  falloff.py <run-stderr.txt> [--sites N] [--min M]

Needs a run with `--census --guard-census`. `id` packs (sid << 16) | pc.
"""
import collections
import re
import sys

RE = re.compile(r"^night: census kind (\d+) id (\d+) n (\d+)$")
DEPART = (
    set(range(150, 159)) | set(range(350, 359)) | set(range(550, 559)) | {48, 49, 50}
)


def main():
    path = sys.argv[1]
    topn = int(sys.argv[sys.argv.index("--sites") + 1]) if "--sites" in sys.argv else 25
    minm = int(sys.argv[sys.argv.index("--min") + 1]) if "--min" in sys.argv else 1000
    entries = collections.defaultdict(
        lambda: collections.defaultdict(collections.Counter)
    )
    kinds = collections.defaultdict(set)
    for line in open(path):
        m = RE.match(line.rstrip("\n"))
        if not m:
            continue
        kind, ident, n = int(m.group(1)), int(m.group(2)), int(m.group(3))
        sid, pc = ident >> 16, ident & 0xFFFF
        if kind in (1, 3):
            entries[sid][pc][kind] += n
        else:
            kinds[ident].add(kind)
    rows = []
    total_dirty = sum(c[3] for per in entries.values() for c in per.values())
    for sid, per in entries.items():
        pcs = sorted(per)
        for a, b in zip(pcs, pcs[1:]):
            opt_a, dirty_b = per[a][1], per[b][3]
            if opt_a < minm or dirty_b < minm:
                continue
            # Silent: the earlier pc's Opt mass reappears as Dirty mass at the
            # next pc, and nothing at the earlier pc ticked a departure.
            if dirty_b < 0.5 * opt_a or per[a][3] > 0.5 * opt_a:
                continue
            if kinds.get((sid << 16) | a, set()) & DEPART:
                continue
            rows.append((dirty_b, sid, a, b, opt_a))
    rows.sort(reverse=True)
    print(f"Dirty version entries: {total_dirty:,}")
    print(f"{'sid:pc -> pc':<22}{'Opt at pc':>14}{'Dirty at next':>16}")
    for dirty_b, sid, a, b, opt_a in rows[:topn]:
        print(f"{f'{sid}:{a} -> {b}':<22}{opt_a:>14,}{dirty_b:>16,}")


if __name__ == "__main__":
    main()
