#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Downstream-attribution census: executed version entries per departure site.

From a run of a module built with BOTH `--census` (version-entry ticks) and
`--guard-census` (departure ticks + the FRAME_PUSH/POP bracket). The runtime
attributes every Dirty/Side version entry to the most recent departure tick
in the same frame bracket and synthesizes kind 5 (Dirty) / kind 6 (Side)
records keyed by the owning departure site.

This is the measured form of the round's rule -- "recovering a departure pays
in proportion to how much executed code sits downstream of it". A site's
kind-5 count is the number of Dirty version entries that recovering that one
departure would (optimistically) flip to Opt.

  downstream.py <run-stderr.txt> [--sites N] [--csv out.csv]

`id` packs (sid << 16) | evidence pc, the same namespace as guards.py.
"""
import collections
import csv
import re
import sys

RE = re.compile(r"^night: census kind (\d+) id (\d+) n (\d+)$")

NO_OWNER = 0xFFFFFFFF

FAMILY = {
    150: "prop-read",
    151: "prop-write",
    152: "arith",
    153: "call",
    154: "other",
    155: "indirect-call",
}


def read(path):
    by_kind = collections.Counter()
    per_site = collections.defaultdict(collections.Counter)
    for line in open(path):
        m = RE.match(line.rstrip("\n"))
        if not m:
            continue
        kind, ident, n = int(m.group(1)), int(m.group(2)), int(m.group(3))
        by_kind[kind] += n
        per_site[ident][kind] += n
    return by_kind, per_site


def site_str(i):
    if i == NO_OWNER:
        return "(no owner)"
    return f"{i >> 16}:{i & 0xffff}"


def main():
    path = sys.argv[1]
    topn = int(sys.argv[sys.argv.index("--sites") + 1]) if "--sites" in sys.argv else 25
    csv_out = sys.argv[sys.argv.index("--csv") + 1] if "--csv" in sys.argv else None
    by_kind, per_site = read(path)

    entries = {k: by_kind[k] for k in (1, 2, 3)}
    total = sum(entries.values())
    if not total:
        sys.exit("no version-entry ticks: was the module built with --census?")
    down_total = sum(c[5] for c in per_site.values())
    if not down_total:
        sys.exit(
            "no downstream records: needs --guard-census too, and a shell "
            "with the attribution runtime"
        )
    print(f"version entries executed: {total:,}")
    for k, name in ((1, "Opt"), (2, "Side"), (3, "Dirty")):
        print(f"   {name:<6}{entries[k]:>14,} ({100 * entries[k] / total:>5.1f}%)")
    print(
        f"\nDirty entries attributed: {down_total:,} of {entries[3]:,} "
        f"({100 * down_total / max(entries[3], 1):.1f}%)"
    )
    unowned = per_site[NO_OWNER][5]
    if unowned:
        print(
            f"   no owning departure:  {unowned:>14,} "
            f"({100 * unowned / down_total:>5.1f}%)"
        )

    rows = []
    for i, c in per_site.items():
        down = c[5]
        if not down and not c[6]:
            continue
        # Departure ticks at this site, summed over the three track bumps.
        dep = sum(c[b + t] for b in FAMILY for t in (0, 200, 400))
        fams = [(sum(c[b + t] for t in (0, 200, 400)), f) for b, f in FAMILY.items()]
        fam = max(fams)[1] if dep else "-"
        rows.append((i, down, c[6], dep, fam))
    rows.sort(key=lambda r: -r[1])

    owned = down_total - unowned
    print(
        f"\n{'departure site':<16}{'family':<15}{'departures':>12}"
        f"{'downstream':>14}{'per-dep':>9}{'cum%':>7}"
    )
    cum = 0
    for i, down, _side, dep, fam in rows[:topn]:
        if i == NO_OWNER:
            continue
        cum += down
        per = f"{down / dep:.1f}" if dep else "-"
        print(
            f"{site_str(i):<16}{fam:<15}{dep:>12,}{down:>14,}{per:>9}"
            f"{100 * cum / max(owned, 1):>6.1f}%"
        )

    if csv_out:
        with open(csv_out, "w", newline="") as f:
            w = csv.writer(f)
            w.writerow(["sid", "pc", "family", "departures", "down_dirty", "down_side"])
            for i, down, side, dep, fam in rows:
                if i == NO_OWNER:
                    continue
                w.writerow([i >> 16, i & 0xFFFF, fam, dep, down, side])
        print(f"\nwrote {csv_out}")


if __name__ == "__main__":
    main()
