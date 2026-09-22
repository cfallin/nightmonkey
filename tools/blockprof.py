#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Executed emitted IR per executed bytecode op, by block role and by
instruction class -- the join of `--block-census`'s static `blockcen`
records (compile stderr) with its runtime ticks (run stderr).

  blockprof.py <compile.err> <run.err> [--track opt|gen] [--ops N]
               [--sites N] [--sid SID] [--site SID:PC] [--blocks] [--min N]

Every other census in this tree reports EMITTED IR per executed op (an op's
whole arm bundle, weighted by how often the op ran). This reports what RAN:
each block the lowering created carries a tick, so a block's contribution
is `count x insts`, and the op's entry tick is its execution count.

Roles (bbv/blockcen.rs): entry / fast / exit / merge are the fall-through
path; side / keep / num are `side_arm`-family arms; leave is a hand-rolled
arm that branches out of the op's block set.

`--site SID:PC` prints every block of every version at that pc with its
count, and the `viz loweri` instruction listing when the compile carried
`--viz --viz-lower` (blockprof.sh does). `--blocks` adds the block listing
to every site in the top-sites table.
"""
import collections
import re
import sys

BLK = re.compile(
    r"^night: blockcen id (\d+) sid#(\d+) pc (\d+) lpc (\d+) op (\S+) track (\S+) "
    r"spliced (\d) blk b(\d+) role (\S+) insts (\d+) alu (\d+) load (\d+) store (\d+) "
    r"call (\d+) boxing (\d+) const (\d+) other (\d+) term (\S+)"
    r"(?: dead (\d+) form (\S+) choke (\S+))?"
)
CEN = re.compile(r"^night: census kind (\d+) id (\d+) n (\d+)$")
LOWB = re.compile(
    r"^night: viz lowerb sid#(\d+) lpc (\d+) blk b(\d+) skip (\d+) params \[(.*?)\] "
    r"insts (\d+) term (.*)$"
)
LOWI = re.compile(r"^night: viz loweri sid#(\d+) lpc (\d+) blk b(\d+) k (\S+) d (.*)$")
LST = re.compile(r"^night: blockcen (params|inst|dead|term) id (\d+) (.*)$")
ROLES = ["entry", "fast", "exit", "merge", "side", "keep", "num", "leave"]
FALL = {"entry", "fast", "exit", "merge"}
CLASSES = ["alu", "load", "store", "call", "boxing", "const", "other"]
TRK = {"Opt": "opt", "Side": "gen", "Dirty": "gen"}


def parse_args(argv):
    o = {
        "track": None,
        "ops": 30,
        "sites": 25,
        "sid": None,
        "site": None,
        "blocks": False,
        "min": 0,
    }
    a = argv[3:]
    i = 0
    while i < len(a):
        if a[i] == "--track":
            o["track"] = a[i + 1]
            i += 2
        elif a[i] == "--ops":
            o["ops"] = int(a[i + 1])
            i += 2
        elif a[i] == "--sites":
            o["sites"] = int(a[i + 1])
            i += 2
        elif a[i] == "--sid":
            o["sid"] = int(a[i + 1])
            i += 2
        elif a[i] == "--site":
            s, p = a[i + 1].split(":")
            o["site"] = (int(s), int(p))
            i += 2
        elif a[i] == "--blocks":
            o["blocks"] = True
            i += 1
        elif a[i] == "--min":
            o["min"] = int(a[i + 1])
            i += 2
        else:
            sys.exit(f"unknown flag {a[i]}")
    return o


def main():
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    opt = parse_args(sys.argv)
    recs = {}
    lowb = {}
    lowi = collections.defaultdict(list)
    listing = collections.defaultdict(list)
    for ln in open(sys.argv[1], errors="replace"):
        m = BLK.match(ln)
        if m:
            g = m.groups()
            rid = int(g[0])
            recs[rid] = dict(
                id=rid,
                sid=int(g[1]),
                pc=int(g[2]),
                lpc=int(g[3]),
                op=g[4],
                track=TRK.get(g[5], g[5]),
                spliced=g[6] == "1",
                blk=int(g[7]),
                role=g[8],
                insts=int(g[9]),
                cls=[int(x) for x in g[10:17]],
                term=g[17],
                dead=int(g[18] or 0),
                form=g[19] or "-",
                choke=g[20] or "-",
            )
            continue
        m = LOWB.match(ln)
        if m:
            lowb[(int(m.group(1)), int(m.group(3)))] = m.group(7)
            continue
        m = LST.match(ln)
        if m:
            listing[int(m.group(2))].append((m.group(1), m.group(3)))
            continue
        m = LOWI.match(ln)
        if m:
            lowi[(int(m.group(1)), int(m.group(3)))].append((m.group(4), m.group(5)))
    counts = collections.Counter()
    ver = collections.Counter()
    for ln in open(sys.argv[2], errors="replace"):
        m = CEN.match(ln)
        if not m:
            continue
        k, i, n = int(m.group(1)), int(m.group(2)), int(m.group(3))
        if k == 70:
            counts[i] = n
        elif k in (1, 2, 3):
            ver[k] += n
    if not recs:
        sys.exit(
            "no blockcen records in the compile stderr (built with --block-census?)"
        )
    if not counts:
        sys.exit("no kind-70 ticks in the run stderr")

    # Group records by op instance: (sid, pc, track, entry block). An op
    # instance is the entry record plus the records that follow it with the
    # same (sid, pc) until the next entry -- ids are sequential per op.
    insts = []
    cur = None
    for rid in sorted(recs):
        r = recs[rid]
        if r["role"] == "entry":
            cur = {"entry": r, "blocks": [r]}
            insts.append(cur)
        elif (
            cur is not None
            and cur["entry"]["sid"] == r["sid"]
            and cur["entry"]["pc"] == r["pc"]
        ):
            cur["blocks"].append(r)
        else:
            cur = {"entry": r, "blocks": [r]}
            insts.append(cur)

    def n(r):
        return counts.get(r["id"], 0)

    # Aggregate.
    tot = collections.defaultdict(lambda: collections.Counter())
    per_op = collections.defaultdict(lambda: collections.Counter())
    per_form = collections.defaultdict(lambda: collections.Counter())
    per_site = collections.defaultdict(lambda: collections.Counter())
    site_insts = collections.defaultdict(list)
    for it in insts:
        e = it["entry"]
        trk = e["track"]
        if opt["track"] and trk != opt["track"]:
            continue
        if opt["sid"] is not None and e["sid"] != opt["sid"]:
            continue
        execs = n(e)
        emitted = sum(r["insts"] for r in it["blocks"])
        key_op = (e["op"], trk)
        key_form = (e["op"], e["form"], e["choke"], trk)
        key_site = (e["sid"], e["pc"], e["op"], trk)
        site_insts[key_site].append(it)
        for agg, key in (
            (tot, trk),
            (per_op, key_op),
            (per_form, key_form),
            (per_site, key_site),
        ):
            c = agg[key]
            c["execs"] += execs
            c["emitted"] += execs * emitted
            c["static"] += emitted
            c["instances"] += 1
            for r in it["blocks"]:
                cnt = n(r)
                c["exec"] += cnt * r["insts"]
                c["dead"] += cnt * r["dead"]
                c["role:" + r["role"]] += cnt * r["insts"]
                c["blocks_run"] += cnt
                if r["term"] == "condbr":
                    c["condbr"] += cnt
                for ci, cn in enumerate(CLASSES):
                    c["cls:" + cn] += cnt * r["cls"][ci]

    def fmt_row(c):
        ex = c["execs"] or 1
        return (
            f"{c['execs']:>14,} {c['exec']/ex:>7.2f} {(c['exec']-c['dead'])/ex:>7.2f} "
            f"{c['emitted']/ex:>7.2f} "
            f"{100*c['exec']/max(1,c['emitted']):>5.1f}% {c['condbr']/ex:>5.2f} "
            + " ".join(f"{c['role:'+r]/ex:>6.2f}" for r in ROLES)
            + "  "
            + " ".join(f"{c['cls:'+k]/ex:>5.2f}" for k in CLASSES)
        )

    hdr = (
        f"{'execs':>14} {'xIR/op':>7} {'live/op':>7} {'eIR/op':>7} {'x/e':>6} {'br/op':>5} "
        + " ".join(f"{r:>6}" for r in ROLES)
        + "  "
        + " ".join(f"{k:>5}" for k in CLASSES)
    )
    print(
        "version entries (kinds 1/2/3): opt", f"{ver[1]:,}", "gen", f"{ver[2]+ver[3]:,}"
    )
    print()
    print(
        "TOTALS by track  (xIR = executed IR, eIR = emitted IR carried, per executed op)"
    )
    print(f"{'track':<10}{hdr}")
    for trk in ("opt", "gen"):
        if trk in tot:
            print(f"{trk:<10}{fmt_row(tot[trk])}")
    if opt["site"]:
        print_site(opt["site"], site_insts, counts, lowb, lowi, listing, opt["min"])
        return
    print()
    print(f"PER OP (top {opt['ops']} by executed IR)")
    print(f"{'op':<20}{'trk':<5}{hdr}")
    rows = sorted(per_op.items(), key=lambda kv: -kv[1]["exec"])[: opt["ops"]]
    for (op, trk), c in rows:
        print(f"{op:<20}{trk:<5}{fmt_row(c)}")
    forms = [(k, c) for k, c in per_form.items() if k[1] != "-" or k[2] != "-"]
    if forms:
        print()
        print("PER FORM (property ops, by lowering form and store choke)")
        print(f"{'op':<14}{'form':<16}{'choke':<14}{'trk':<5}{hdr}")
        for (op, form, choke, trk), c in sorted(forms, key=lambda kv: -kv[1]["exec"]):
            print(f"{op:<14}{form:<16}{choke:<14}{trk:<5}{fmt_row(c)}")
    print()
    print(f"TOP SITES (top {opt['sites']} by executed IR)")
    print(f"{'sid:pc':<12}{'op':<18}{'trk':<5}{hdr}")
    rows = sorted(per_site.items(), key=lambda kv: -kv[1]["exec"])[: opt["sites"]]
    total_exec = sum(c["exec"] for c in tot.values()) or 1
    for (sid, pc, op, trk), c in rows:
        form = site_insts[(sid, pc, op, trk)][0]["entry"]["form"]
        print(
            f"{str(sid)+':'+str(pc):<12}{op:<18}{trk:<5}{fmt_row(c)}"
            f"   {100*c['exec']/total_exec:.1f}% of executed  {form}"
        )
        if opt["blocks"]:
            print_blocks(
                site_insts[(sid, pc, op, trk)],
                counts,
                lowb,
                lowi,
                listing,
                detail=False,
                min_n=opt["min"],
            )


def print_blocks(its, counts, lowb, lowi, listing, detail, min_n=0):
    for it in its:
        e = it["entry"]
        if counts.get(e["id"], 0) < min_n:
            continue
        print(
            f"    version at b{e['blk']} ({'spliced' if e['spliced'] else 'root'}) lpc {e['lpc']}"
            f"  form {e['form']} choke {e['choke']}"
        )
        for r in it["blocks"]:
            cnt = counts.get(r["id"], 0)
            if cnt < min_n:
                continue
            cl = " ".join(f"{k}={v}" for k, v in zip(CLASSES, r["cls"]) if v)
            term = lowb.get((r["sid"], r["blk"]), r["term"])
            print(
                f"      b{r['blk']:<6} {r['role']:<6} n {cnt:>12,}  insts {r['insts']:>4} "
                f"dead {r['dead']:>2}  x {cnt*r['insts']:>14,}  [{cl}]  -> {term}"
            )
            if detail and cnt:
                if r["id"] in listing:
                    for k, d in listing[r["id"]]:
                        print(f"          {k:<7} {d}")
                else:
                    for k, d in lowi.get((r["sid"], r["blk"]), []):
                        print(f"          {k:<8} {d}")


def print_site(site, site_insts, counts, lowb, lowi, listing, min_n):
    sid, pc = site
    keys = [k for k in site_insts if k[0] == sid and k[1] == pc]
    if not keys:
        sys.exit(f"no op instance at sid#{sid} pc {pc}")
    for k in keys:
        print()
        print(f"SITE sid#{k[0]} pc {k[1]} op {k[2]} track {k[3]}")
        print_blocks(
            site_insts[k], counts, lowb, lowi, listing, detail=True, min_n=min_n
        )


if __name__ == "__main__":
    main()
