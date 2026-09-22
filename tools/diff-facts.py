#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

"""Parity diff for --dump-facts output (see likelier/dump.rs).

Usage: diff-facts.py OLD.dump NEW.dump [--table T] [--script SID] [--show N]

Reports, per table: sites only-old, only-new, agreeing, conflicting.
Quality is compared PER SITE, never by aggregate census.
"""

import argparse
import sys
from collections import defaultdict


def parse(path):
    tables = defaultdict(dict)
    meta = {}
    with open(path) as f:
        for raw in f:
            line = raw.rstrip("\n")
            if not line or line.startswith("#"):
                continue
            table, rest = line.split(" ", 1)
            if " = " in rest:
                key, val = rest.split(" = ", 1)
            else:
                key, val = rest, "1"
            if table == "meta":
                meta[key] = val
            else:
                tables[table][key] = val
    return meta, tables


def site_script(key):
    return key.split(":")[0]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("old")
    ap.add_argument("new")
    ap.add_argument("--table", help="restrict to one table")
    ap.add_argument("--script", help="restrict to one script id")
    ap.add_argument(
        "--show", type=int, default=0, help="print up to N example keys per bucket"
    )
    args = ap.parse_args()

    meta_a, a = parse(args.old)
    meta_b, b = parse(args.new)
    print(
        f"old: {args.old} (classes {meta_a.get('n_classes')}, "
        f"cons {meta_a.get('n_cons')})"
    )
    print(
        f"new: {args.new} (classes {meta_b.get('n_classes')}, "
        f"cons {meta_b.get('n_cons')})"
    )

    names = sorted(set(a) | set(b))
    if args.table:
        names = [t for t in names if t == args.table]

    hdr = f"{'table':<20} {'only-old':>9} {'only-new':>9} {'agree':>9} {'conflict':>9}"
    print(hdr)
    print("-" * len(hdr))
    for t in names:
        ta, tb = a.get(t, {}), b.get(t, {})
        keys_a, keys_b = set(ta), set(tb)
        if args.script:
            keys_a = {k for k in keys_a if site_script(k) == args.script}
            keys_b = {k for k in keys_b if site_script(k) == args.script}
        only_a = sorted(keys_a - keys_b)
        only_b = sorted(keys_b - keys_a)
        both = keys_a & keys_b
        agree = sorted(k for k in both if ta[k] == tb[k])
        conflict = sorted(k for k in both if ta[k] != tb[k])
        print(
            f"{t:<20} {len(only_a):>9} {len(only_b):>9} "
            f"{len(agree):>9} {len(conflict):>9}"
        )
        if args.show:
            for label, keys in (
                ("only-old", only_a),
                ("only-new", only_b),
                ("conflict", conflict),
            ):
                for k in keys[: args.show]:
                    if label == "conflict":
                        print(f"    {label} {t} {k}: old=[{ta[k]}] new=[{tb[k]}]")
                    else:
                        src = ta if label == "only-old" else tb
                        print(f"    {label} {t} {k}: [{src[k]}]")
    return 0


if __name__ == "__main__":
    sys.exit(main())
