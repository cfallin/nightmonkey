#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Ultimate-cause decomposition of Dirty execution.

Joins the ROOT downstream attribution (kind 7: every Dirty version entry
attributed to the Opt-track departure that STARTED its stretch) against the
per-site evidence of why that departure could not stay clean:

  - a non-call op family (prop read/write, arith, other): the op itself
    needed a may-run-user-code helper;
  - an indirect dispatch (kind 155 from Opt): the callee was unknown at the
    site -- split into guard-miss (a likely-direct arm exists and also
    fires, kind 153 at the same site) vs never-resolved;
  - a forked call whose dirty arm ran: FLAG_FORK_WHY / CTOR_FORK_WHY say
    which bits of the callee's returned word blocked the clean arm
    (folded-clean / MUT_THIS / MUT_OTHER / both / err);
  - an unforked call: the static `flagsite-miss` reason from a `--dump-bbv`
    run of the same snapshot.

Each cause row also reports its STAMPS-INTACT share: the fraction of its
downstream mass whose root departure crossed a call bracket during which no
stamp was invalidated (kind 13 vs kind 7) -- "heap written, but every
stamp-guarded fact still holds", the population a keep-facts fork arm could
recover with full context.

  rootcause.py <run-stderr.txt> <bbv-dump.txt> [--sites N]

Needs a run with BOTH `--census` and `--guard-census`.
"""
import collections
import re
import sys

RE = re.compile(r"^night: census kind (\d+) id (\d+) n (\d+)$")
RE_MISS = re.compile(r"^night: bbv flagsite-miss sid#(\d+) pc (\d+) why (\S+)")
RE_CMISS = re.compile(r"^night: bbv construct-fork-miss sid#(\d+) pc (\d+) why (\S+)")

NO_OWNER = 0xFFFFFFFF
FAMILY = {
    150: "prop-read",
    151: "prop-write",
    152: "arith",
    153: "call",
    154: "other-op",
    155: "indirect",
    156: "side-arm-step",
    158: "builtin-merge",
}
WHY = {0: "folded-clean", 1: "MUT_THIS", 2: "MUT_OTHER", 3: "MUT_both", 4: "err"}
# Prefer a causal static reason over the derivative "dirty".
MISS_PRIO = ["nolikely", "scan-storeonly", "noallow", "scan-fail", "dirty"]


def read_census(path):
    per_site = collections.defaultdict(collections.Counter)
    for line in open(path):
        m = RE.match(line.rstrip("\n"))
        if m:
            per_site[int(m.group(2))][int(m.group(1))] += int(m.group(3))
    return per_site


def read_bbv(path):
    miss = collections.defaultdict(set)
    for line in open(path):
        m = RE_MISS.match(line) or RE_CMISS.match(line)
        if m:
            miss[(int(m.group(1)) << 16) | int(m.group(2))].add(m.group(3))
    return miss


def classify(c, static_reasons):
    """Return [(bucket, weight_fraction)] for one root site's counters."""
    fam = collections.Counter()
    for b, name in FAMILY.items():
        fam[name] = sum(c[b + t] for t in (0, 200, 400))
    top = fam.most_common(1)[0][0] if fam.total() else None
    if top in ("prop-read", "prop-write", "arith", "other-op"):
        return [(f"helper:{top}", 1.0)]
    if top in ("side-arm-step", "builtin-merge"):
        return [(top, 1.0)]
    # A scripted call (direct or indirect). Fork dirty-arm evidence first:
    # a forked site's departure is owned by the callee's returned word, not
    # by how the callee was reached.
    why = collections.Counter()
    for i in range(5):
        why[WHY[i]] += sum(c[185 + i + t] for t in (0, 200, 400))
    ctor = sum(c[196 + i + t] for i in range(4) for t in (0, 200, 400))
    tot = why.total() + ctor
    if tot:
        out = [(f"fork-dirty:{k}", v / tot) for k, v in why.items() if v]
        if ctor:
            out.append(("fork-dirty:ctor-word", ctor / tot))
        return out
    if top == "indirect":
        kind = "indirect:guard-miss" if fam["call"] else "indirect:unresolved"
        return [(kind, 1.0)]
    reasons = static_reasons or set()
    for r in MISS_PRIO:
        if r in reasons:
            return [(f"unforked:{r}", 1.0)]
    if reasons:
        return [(f"unforked:{sorted(reasons)[0]}", 1.0)]
    return [("unforked:no-static-row", 1.0)]


def main():
    run, bbv = sys.argv[1], sys.argv[2]
    topn = int(sys.argv[sys.argv.index("--sites") + 1]) if "--sites" in sys.argv else 8
    per_site = read_census(run)
    miss = read_bbv(bbv)

    total_dirty = sum(c[3] for c in per_site.values())
    root_mass = {i: c[7] for i, c in per_site.items() if c[7]}
    attributed = sum(root_mass.values())
    print(
        f"Dirty version entries: {total_dirty:,}; root-attributed "
        f"{attributed:,} ({100 * attributed / max(total_dirty, 1):.1f}%)"
    )
    unowned = root_mass.pop(NO_OWNER, 0)
    if unowned:
        print(
            f"   no owning Opt-track departure: {unowned:,} "
            f"({100 * unowned / max(attributed, 1):.1f}%)"
        )

    buckets = collections.Counter()
    intact = collections.Counter()
    bucket_sites = collections.defaultdict(collections.Counter)
    for i, mass in root_mass.items():
        imass = per_site[i][13]
        for bucket, frac in classify(per_site[i], miss.get(i)):
            buckets[bucket] += mass * frac
            intact[bucket] += imass * frac
            bucket_sites[bucket][i] += mass * frac

    owned = sum(buckets.values())
    total_intact = sum(intact.values())
    if total_intact:
        print(
            f"stamps-intact root mass: {total_intact:,.0f} "
            f"({100 * total_intact / max(owned, 1):.1f}% of owned)"
        )
    print(
        f"\n{'ultimate cause':<28}{'Dirty entries':>16}{'share':>8}"
        f"{'stamps-intact':>15}"
    )
    for bucket, mass in buckets.most_common():
        ish = f"{100 * intact[bucket] / mass:.1f}%" if mass else "-"
        print(f"{bucket:<28}{mass:>16,.0f}{100 * mass / owned:>7.1f}%{ish:>15}")
        for i, m in bucket_sites[bucket].most_common(topn):
            dep = sum(per_site[i][b + t] for b in FAMILY for t in (0, 200, 400))
            si = per_site[i]
            d_int, d_brk = si[11], si[12]
            print(
                f"    {i >> 16}:{i & 0xffff:<12}{m:>14,.0f}   "
                f"({dep:,} departures, intact {d_int:,} / broken {d_brk:,})"
            )


if __name__ == "__main__":
    main()
