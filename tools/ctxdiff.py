#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Which continuation drops which fact, from `nightmonkey --dump-ctxedge`.

Every continuation edge records the ctx it hands to its successor pc. Group
the arrivals by successor: the strongest arrival is what that pc *could* have
been given, and every weaker arrival is a continuation that invalidated
something. Attribute the loss to the op that emitted the edge.

This is the half of the Opt-track question the `dmerge` audit cannot see.
`dmerge` finds a may-GC call merging back into the clean continuation; this
finds an arm that dropped a `likelier` claim and rejoined without calling
anything at all.

  ctxdiff.py <ctxedge.txt> [--ops N] [--slots N] [--pc SID:PC]

Two record types are read. `ctxedge` is one per continuation edge and answers
"this arrival is weaker than a sibling" -- useful, but 80%+ of those are
*carrying* a loss caused many pcs earlier. `ctxdelta` is one per op that
changed a durable slot's fact, in both directions, and answers "this op did
it", which is what a fix has to target. The direction order lives here rather
than in the emitter so it can be argued with.

"strongest" is per slot, not per ctx: a pc's best-known fact for slot `l3` is
the strongest any arrival carries, so the report is "what this arm lost
against what some other arm proved", which is the actionable form.
"""
import collections
import re
import sys

RE = re.compile(
    r"^night: ctxedge sid#(\d+) pc (\d+) op (\S+) to (\d+) track (\S+) "
    r"nslots (\d+) nfacts (\d+) carried (\d+) facts \[(.*)\]$"
)


# Fact strength, weakest first. A slot string is "prims[:range][:cls][:iv]";
# comparing whole strings would call every difference a loss, so score the
# pieces that actually carry a claim.
def strength(fact):
    if fact is None:
        return (0, 0, 0, 0)
    prims = fact.split(":")[0]
    # Fewer admitted prims is a stronger claim; "none" is strongest of all.
    n = 1 if prims == "none" else len(prims.split("|"))
    return (
        -n,
        1 if ":cls" in fact else 0,
        1 if ":iv[" in fact else 0,
        1 if re.search(r":(I53|I32|NonNeg|Small)", fact) else 0,
    )


def parse(path):
    edges = []
    for line in open(path):
        m = RE.match(line.rstrip("\n"))
        if not m:
            continue
        facts = {}
        if m.group(9):
            for tok in m.group(9).split():
                k, _, v = tok.partition("=")
                facts[k] = v
        edges.append(
            dict(
                sid=int(m.group(1)),
                pc=int(m.group(2)),
                op=m.group(3),
                succ=int(m.group(4)),
                track=m.group(5),
                nslots=int(m.group(6)),
                carried=int(m.group(8)),
                facts=facts,
            )
        )
    return edges


RK = re.compile(
    r"^night: ctxdelta sid#(\d+) pc (\d+) op (\S+) track (\S+) n (\d+) delta \[(.*)\]$"
)


def deltas(path):
    """Per-op durable-slot changes, split into weakenings and strengthenings."""
    weak = collections.Counter()
    strong = collections.Counter()
    kinds = collections.Counter()
    ex = collections.defaultdict(list)
    for line in open(path):
        m = RK.match(line.rstrip("\n"))
        if not m:
            continue
        op = m.group(3)
        for tok in m.group(6).split():
            slot, _, rest = tok.partition(":")
            was, _, now = rest.rpartition("->")
            if now == "gone":
                weak[op] += 1
                kinds["slot fact gone"] += 1
                if len(ex[op]) < 2:
                    ex[op].append(tok)
                continue
            sw, sn = strength(was), strength(now)
            if sn < sw:
                weak[op] += 1
                if ":cls" in was and ":cls" not in now:
                    kinds["class fact killed"] += 1
                elif ":iv[" in was and ":iv[" not in now:
                    kinds["interval killed"] += 1
                else:
                    kinds["prims widened"] += 1
                if len(ex[op]) < 2:
                    ex[op].append(tok)
            elif sn > sw:
                strong[op] += 1
    return weak, strong, kinds, ex


def report_deltas(path):
    weak, strong, kinds, ex = deltas(path)
    tw = sum(weak.values())
    if not tw:
        return
    print("\n--- per-op fact kills (the origin, not the carrier) ---")
    print(f"{tw} durable-slot facts weakened, {sum(strong.values())} strengthened")
    for k, v in kinds.most_common():
        print(f"   {k:<20}{v:>8} ({100 * v / tw:>5.1f}%)")
    print(f"\n{'op that killed the fact':<26}{'kills':>8}{'proves':>8}   example")
    for op, v in weak.most_common(12):
        print(f"{op:<26}{v:>8}{strong[op]:>8}   {ex[op][0] if ex[op] else ''}")


def main():
    path = sys.argv[1]
    topn = int(sys.argv[sys.argv.index("--ops") + 1]) if "--ops" in sys.argv else 20
    only = sys.argv[sys.argv.index("--pc") + 1] if "--pc" in sys.argv else None

    edges = parse(path)
    by_succ = collections.defaultdict(list)
    for e in edges:
        by_succ[(e["sid"], e["succ"])].append(e)

    # Per (sid, succ_pc, slot): the strongest fact any arrival carries.
    best = {}
    for key, arr in by_succ.items():
        for e in arr:
            for slot, f in e["facts"].items():
                k = (key, slot)
                if k not in best or strength(f) > strength(best[k]):
                    best[k] = f

    losses = collections.Counter()  # (op, track) -> slots lost
    per_op = collections.Counter()  # op -> edges that lost something
    per_op_edges = collections.Counter()
    kind = collections.Counter()  # what kind of fact was lost
    examples = collections.defaultdict(list)
    multi = 0
    for key, arr in by_succ.items():
        if len(arr) < 2:
            continue
        multi += 1
        for e in arr:
            lost = []
            for slot in {s for a in arr for s in a["facts"]}:
                b = best.get((key, slot))
                have = e["facts"].get(slot)
                if b is None or strength(have) >= strength(b):
                    continue
                lost.append((slot, have, b))
                sb, sh = strength(b), strength(have)
                if sh[0] > sb[0]:
                    kind["prims widened"] += 1
                if sb[1] and not sh[1]:
                    kind["class fact lost"] += 1
                if sb[2] and not sh[2]:
                    kind["interval lost"] += 1
                if sb[3] and not sh[3]:
                    kind["range bucket lost"] += 1
            per_op_edges[e["op"]] += 1
            if lost:
                per_op[e["op"]] += 1
                losses[(e["op"], e["track"])] += len(lost)
                if len(examples[e["op"]]) < 3:
                    examples[e["op"]].append(
                        (e["sid"], e["pc"], e["succ"], e["track"], lost[:3])
                    )

    print(
        f"{len(edges)} continuation edges, {len(by_succ)} distinct successor pcs, "
        f"{multi} of them reached by more than one arrival"
    )
    tl = sum(losses.values())
    print(
        f"{sum(per_op.values())} edges arrive weaker than a sibling, dropping {tl} slot facts\n"
    )
    print("what was lost:")
    for k, v in kind.most_common():
        print(f"   {k:<20}{v:>8} ({100 * v / max(tl, 1):>5.1f}%)")

    print(
        f"\n{'op that emitted the weaker edge':<30}{'edges':>8}{'weaker':>8}{'%':>7}{'facts lost':>12}"
    )
    rows = [
        (
            op,
            per_op_edges[op],
            per_op[op],
            sum(v for (o, _), v in losses.items() if o == op),
        )
        for op in per_op
    ]
    for op, tot, w, f in sorted(rows, key=lambda r: -r[3])[:topn]:
        print(f"{op:<30}{tot:>8}{w:>8}{100 * w / max(tot, 1):>6.1f}%{f:>12}")

    print("\nexamples (slot: what this arm carried <- what a sibling proved):")
    for op, _, _, _ in sorted(rows, key=lambda r: -r[3])[:6]:
        for sid, pc, succ, tr, lost in examples[op][:1]:
            det = "; ".join(f"{s}: {h or '-'} <- {b}" for s, h, b in lost)
            print(f"  {op} sid#{sid} pc {pc} -> {succ} [{tr}]  {det}")

    report_deltas(path)

    if only:
        sid, _, pc = only.partition(":")
        key = (int(sid), int(pc))
        print(f"\narrivals at sid#{sid} pc {pc}:")
        for e in by_succ.get(key, []):
            fs = " ".join(f"{k}={v}" for k, v in sorted(e["facts"].items()))
            print(f"  from pc {e['pc']:>6} {e['op']:<22} [{e['track']:<5}] {fs}")


if __name__ == "__main__":
    main()
