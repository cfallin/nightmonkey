#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Where Dirty execution begins, per script.

For each script, by Dirty version-entry mass: whether the body is ENTERED
Dirty (Dirty entries at pc 0 -- the callee's entry itself, so the cause is
at the caller or the entry validation), else the first pc with Dirty
entries and the census kinds ticked at the last Opt-entered pc before it
(the op that stepped the lineage). Unlike rootcause.py this does not trust
the departure attribution, which smears once a site departs and rejoins.

  dirtystart.py <run-stderr.txt> [--sites N]
"""
import collections
import re
import sys

RE = re.compile(r"^night: census kind (\d+) id (\d+) n (\d+)$")


def main():
    path = sys.argv[1]
    topn = int(sys.argv[sys.argv.index("--sites") + 1]) if "--sites" in sys.argv else 12
    ent = collections.defaultdict(lambda: collections.defaultdict(collections.Counter))
    kinds = collections.defaultdict(lambda: collections.defaultdict(dict))
    for line in open(path):
        m = RE.match(line.rstrip("\n"))
        if not m:
            continue
        kind, ident, n = int(m.group(1)), int(m.group(2)), int(m.group(3))
        sid, pc = ident >> 16, ident & 0xFFFF
        if kind in (1, 3):
            ent[sid][pc][kind] += n
        else:
            kinds[sid][pc][kind] = n
    total = max(1, sum(c[3] for per in ent.values() for c in per.values()))
    rows = sorted(ent.items(), key=lambda kv: -sum(c[3] for c in kv[1].values()))
    print(f"Dirty version entries: {total:,}")
    for sid, per in rows[:topn]:
        dirty = sum(c[3] for c in per.values())
        opt = sum(c[1] for c in per.values())
        pcs = sorted(per)
        entry = per[pcs[0]]
        head = f"sid {sid:<6} dirty {dirty:>13,} ({100 * dirty / total:4.1f}%) opt {opt:>13,}"
        if entry[3] and entry[3] >= entry[1]:
            print(
                f"{head}  ENTERED Dirty at pc {pcs[0]} ({entry[3]:,} of {entry[1] + entry[3]:,})"
            )
            continue
        first = next(
            (p for p in pcs if per[p][3] > 0.2 * max(per[p][1], 1) and per[p][3] > 0),
            None,
        )
        if first is None:
            print(f"{head}  (no dominant Dirty pc)")
            continue
        prev = [p for p in pcs if p < first and per[p][1] > 0]
        pv = prev[-1] if prev else None
        ks = sorted(kinds[sid].get(pv, {}).items()) if pv is not None else []
        print(
            f"{head}  Dirty from pc {first} ({per[first][3]:,}); last Opt pc {pv} kinds {ks}"
        )


if __name__ == "__main__":
    main()
