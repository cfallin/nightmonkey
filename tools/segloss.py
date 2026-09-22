#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Which arrival weakened a program point's prediction, by arrival KIND.

  segloss.py <ctxedge.txt> [--sites N] [--sid N]

`ctxdiff.py` attributes a weaker arrival to the op that emitted its edge,
which names the CARRIER: a `GetLocal` that hands on a fact something killed
twenty pcs earlier is what it reports. This asks a narrower question the
prediction step makes decisive: the prediction at a pc is the join of every
Opt arrival there, so ONE weak arrival erases a fact for every block at that
pc, however strong the others were. Which arrivals are those?

The kinds it separates, because they have different fixes:

  seg-return  the arrival is a spliced callee's `Return` edge -- the
              caller-frame facts it hands back. A `Return` arrival that is
              weaker than a fall-through sibling means the segment did not
              carry the caller's facts through.
  call-keep   a `Call`/`New` continuation: the flag fork's arms.
  loop-back   a back edge (successor pc <= the emitting pc).
  other       everything else.

A `cl<n>` / `ca<n>` slot in the fact list is the CALLER frame's local/arg as
the segment sees it (`--dump-ctxedge` prints them); a loss
on one of those inside a segment is the caller's fact dying in the callee.
"""
import collections
import re
import sys

RE = re.compile(
    r"^night: ctxedge sid#(\d+) pc (\d+) op (\S+) to (\d+) track (\S+) "
    r"nslots (\d+) nfacts (\d+) carried (\d+) facts \[(.*)\]$"
)


def strength(f):
    """Class-fact strength only: this file is about durable class facts."""
    if f is None:
        return -1
    return 1 if ":cls" in f else 0


def kind_of(e):
    if e["op"] in ("Return", "RetRval"):
        return "seg-return"
    if e["op"] in (
        "Call",
        "CallContent",
        "CallIgnoresRv",
        "CallIter",
        "CallContentIter",
        "New",
        "NewContent",
        "SuperCall",
    ):
        return "call-keep"
    if e["succ"] <= e["pc"]:
        return "loop-back"
    return "other"


def main():
    path = sys.argv[1]
    topn = int(sys.argv[sys.argv.index("--sites") + 1]) if "--sites" in sys.argv else 15
    only = int(sys.argv[sys.argv.index("--sid") + 1]) if "--sid" in sys.argv else None

    by_succ = collections.defaultdict(list)
    seen = collections.defaultdict(set)
    for ln in open(path):
        m = RE.match(ln.rstrip("\n"))
        if not m or m.group(5) != "Opt":
            continue
        sid = int(m.group(1))
        if only is not None and sid != only:
            continue
        facts = {}
        if m.group(9):
            for tok in m.group(9).split():
                k, _, v = tok.partition("=")
                facts[k] = v
        e = dict(
            sid=sid,
            pc=int(m.group(2)),
            op=m.group(3),
            succ=int(m.group(4)),
            facts=facts,
        )
        # The dump emits one record per walk that reached the edge, so the
        # same arrival appears several times; counting them would multiply
        # every total by the round count.
        key = (sid, e["succ"])
        sig = (e["pc"], e["op"], tuple(sorted(facts.items())))
        if sig in seen[key]:
            continue
        seen[key].add(sig)
        by_succ[key].append(e)

    by_kind = collections.Counter()  # kind -> class facts erased
    pts_by_kind = collections.Counter()  # kind -> program points poisoned
    caller_slot = collections.Counter()  # kind -> of those, caller-frame slots
    sites = collections.Counter()  # (sid, pc, op, succ) -> facts erased
    npoints = 0
    for (sid, succ), arr in by_succ.items():
        if len(arr) < 2:
            continue
        slots = {s for a in arr for s in a["facts"]}
        best = {}
        for s in slots:
            for a in arr:
                if strength(a["facts"].get(s)) > strength(best.get(s, None)):
                    best[s] = a["facts"].get(s)
        # A slot the join erases: some arrival proved a class, some arrival
        # (or an arrival that simply has no entry for it) did not.
        erased = [
            s
            for s in slots
            if strength(best.get(s)) == 1
            and any(strength(a["facts"].get(s)) < 1 for a in arr)
        ]
        if not erased:
            continue
        npoints += 1
        kinds_seen = set()
        for a in arr:
            lost = [s for s in erased if strength(a["facts"].get(s)) < 1]
            if not lost:
                continue
            k = kind_of(a)
            by_kind[k] += len(lost)
            caller_slot[k] += sum(1 for s in lost if s[:2] in ("cl", "ca"))
            if k not in kinds_seen:
                pts_by_kind[k] += 1
                kinds_seen.add(k)
            sites[(a["sid"], a["pc"], a["op"], a["succ"])] += len(lost)

    tot = sum(by_kind.values())
    print(
        f"{len(by_succ)} Opt successor pcs, "
        f"{sum(1 for v in by_succ.values() if len(v) > 1)} with >1 arrival"
    )
    print(
        f"{npoints} program points where the join ERASES a class fact "
        f"another arrival proved, {tot} (arrival, slot) erasures\n"
    )
    print(
        f"{'arrival kind':<14}{'erasures':>10}{'points':>9}"
        f"{'%':>7}{'caller-frame slots':>20}"
    )
    for k, v in by_kind.most_common():
        print(
            f"{k:<14}{v:>10}{pts_by_kind[k]:>9}{100*v/max(tot,1):>6.1f}%"
            f"{caller_slot[k]:>20}"
        )
    print("\ntop erasing edges")
    print(f"{'sid':>7}{'pc':>8}{'op':>16}{'to':>8}{'facts':>7}")
    for (sid, pc, op, succ), v in sites.most_common(topn):
        print(f"{sid:>7}{pc:>8}{op:>16}{succ:>8}{v:>7}")


if __name__ == "__main__":
    main()
