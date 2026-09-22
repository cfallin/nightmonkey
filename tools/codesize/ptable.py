#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Table from pstat.py jsonl: FE/BE-bound, L1i/opcache/iTLB rates, per-work normalisation.

  ptable.py <jsonl> [more.jsonl ...]   (later files override same (bench,lane,group))
"""
import json
import sys

recs = {}
for p in sys.argv[1:]:
    for ln in open(p):
        r = json.loads(ln)
        recs[(r["bench"], r["lane"], r["group"])] = r

benches = []
for b, l, g in recs:
    if b not in benches:
        benches.append(b)
lanes = sorted({l for (_, l, _) in recs})


def g(b, l, grp, ev):
    r = recs.get((b, l, grp))
    if not r:
        return None
    return r["ev"].get(ev)


def work(b, l, grp):
    r = recs.get((b, l, grp))
    if not r or r["score"] is None:
        return None
    s = r["score"]
    return (1.0 / s) if b == "react-bench" else float(s)


def f(x, fmt):
    return "-" if x is None else fmt % x


print(
    f"{'bench':<14}{'lane':<5}{'score':>8}{'IPC':>6}{'FE%':>7}{'BE%':>7}{'ret%':>7}"
    f"{'Gins/wk':>9}{'Gcyc/wk':>9}{'L1i%':>7}{'L1iMPKI':>9}{'OC%':>7}{'dec%':>7}{'iTLBmiss/Mi':>12}{'L2miss/Mi':>11}{'brMPKI':>8}"
)
for b in benches:
    for l in lanes:
        cyc = g(b, l, "1", "cycles")
        ins = g(b, l, "1", "instructions")
        fe = g(b, l, "1", "de_no_dispatch_per_slot.no_ops_from_frontend")
        be = g(b, l, "1", "de_no_dispatch_per_slot.backend_stalls")
        ret = g(b, l, "1", "ex_ret_ops")
        w1 = work(b, l, "1")
        ipc = ins / cyc if cyc and ins else None
        fep = 100 * fe / (8 * cyc) if fe and cyc else None
        bep = 100 * be / (8 * cyc) if be and cyc else None
        rp = 100 * ret / (8 * cyc) if ret and cyc else None
        insw = ins / w1 / 1e9 if ins and w1 else None
        cycw = cyc / w1 / 1e9 if cyc and w1 else None
        ica = g(b, l, "2", "ic_tag_hit_miss.all_instruction_cache_accesses")
        icm = g(b, l, "2", "ic_tag_hit_miss.instruction_cache_miss")
        oca = g(b, l, "2", "op_cache_hit_miss.all_op_cache_accesses")
        ocm = g(b, l, "2", "op_cache_hit_miss.op_cache_miss")
        dec = g(b, l, "2", "de_src_op_disp.x86_decoder")
        ins2 = ins  # group 2 has no instructions counter; scale by group-1 ins via cycles ratio
        l1p = 100 * icm / ica if ica and icm else None
        mpki = icm / ins * 1000 if icm and ins else None
        ocp = 100 * ocm / oca if oca and ocm else None
        decp = 100 * dec / ret if dec and ret else None
        tl2h = g(b, l, "3", "bp_l1_tlb_miss_l2_tlb_hit")
        tl2m = g(b, l, "3", "bp_l1_tlb_miss_l2_tlb_miss.all")
        itlb = (
            (tl2h + tl2m) / ins * 1e6
            if tl2h is not None and tl2m is not None and ins
            else None
        )
        l2m = g(b, l, "3", "ic_cache_fill_sys")
        l2mi = l2m / ins * 1e6 if l2m is not None and ins else None
        brm = g(b, l, "3", "ex_ret_brn_misp")
        brk = brm / ins * 1000 if brm is not None and ins else None
        sc = recs.get((b, l, "1"), {}).get("score")
        print(
            f"{b:<14}{l:<5}{f(sc, '%8s'):>8}{f(ipc, '%.2f'):>6}{f(fep, '%.1f'):>7}{f(bep, '%.1f'):>7}{f(rp, '%.1f'):>7}"
            f"{f(insw, '%.3f'):>9}{f(cycw, '%.3f'):>9}{f(l1p, '%.1f'):>7}{f(mpki, '%.1f'):>9}{f(ocp, '%.1f'):>7}{f(decp, '%.1f'):>7}"
            f"{f(itlb, '%.0f'):>12}{f(l2mi, '%.0f'):>11}{f(brk, '%.2f'):>8}"
        )
