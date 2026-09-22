#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Per-arm guard census, from a run of a module built with `--guard-census`.

The static censuses say a guard was ARMED and that a miss arm exists behind
it. This says how often each arm actually RAN, which is the prediction
accuracy the whole reach question bottoms out in.

  guards.py <run-stderr.txt> [--sites N] [--csv out.csv]

`kind` is the arm; +200/+400 on the base kind means the version was on the
Side / Dirty track. `id` packs (sid << 16) | evidence pc.
"""
import collections
import re
import sys

RE = re.compile(r"^night: census kind (\d+) id (\d+) n (\d+)$")

BASE = {
    100: ("get", "L1a checkless", True),
    101: ("get", "L1b stamp hit", True),
    102: ("get", "L1b stamp MISS", False),
    103: ("get", "L1c slots hit", True),
    104: ("get", "L1c slots MISS", False),
    105: ("get", "L1d fused hit", True),
    106: ("get", "L1d fused MISS", False),
    110: ("get", "IC way hit, own fixed slot", None),
    111: ("get", "IC way hit, holder tail", None),
    112: ("get", "IC probe (past the ways)", None),
    113: ("get", "IC miss helper", None),
    114: ("get", "IC probe receiver (pc<<16|shape>>3)", None),
    115: ("get", "IC probe receiver shape flags", None),
    120: ("set", "L1a checkless", True),
    121: ("set", "L1 guard hit", True),
    122: ("set", "L1 guard MISS", False),
    130: ("set", "IC way0 (mono)", None),
    131: ("set", "IC mega", None),
    132: ("set", "IC add-transition", None),
    123: ("set", "IC add-transition, proto proof spent", None),
    181: ("gname", "value-fuse hit", None),
    182: ("gname", "guarded slot hit", None),
    183: ("gname", "resolve leaf", None),
    184: ("gname", "generic helper", None),
    133: ("set", "IC miss helper", None),
    140: ("arith", "total executions", None),
    141: ("arith", "generic helper arm", False),
    150: ("Opt->Dirty", "at a property READ", None),
    151: ("Opt->Dirty", "at a property WRITE", None),
    152: ("Opt->Dirty", "at ARITHMETIC", None),
    153: ("Opt->Dirty", "at a scripted CALL", None),
    154: ("Opt->Dirty", "at another op", None),
    155: ("Opt->Dirty", "at an INDIRECT call", None),
    156: ("Opt->Dirty", "at a side-arm track step", None),
    158: ("Opt->Dirty", "at a builtin-arm merge join", None),
    134: ("onramp", "loop header TRY", None),
    135: ("onramp", "loop header OK", True),
    136: ("onramp", "recovery twin TRY", None),
    137: ("onramp", "recovery twin OK", True),
    138: ("onramp", "call return TRY", None),
    139: ("onramp", "call return OK", True),
    142: ("fork-dirty why", "folded clean (recoverable)", None),
    143: ("fork-dirty why", "MUT_THIS", None),
    144: ("fork-dirty why", "MUT_OTHER", None),
    145: ("fork-dirty why", "MUT_THIS|MUT_OTHER", None),
    146: ("fork-dirty why", "callee errored", None),
    160: ("get miss why", "receiver not an object", None),
    161: ("get miss why", "receiver never stamped", None),
    162: ("get miss why", "WRONG class predicted", None),
    163: ("get miss why", "right class, SLOTS clear", None),
    164: ("get miss why", "(unreachable)", None),
    170: ("set miss why", "receiver not an object", None),
    171: ("set miss why", "receiver never stamped", None),
    172: ("set miss why", "WRONG class predicted", None),
    173: ("set miss why", "right class, SLOTS clear", None),
    174: ("set miss why", "(unreachable)", None),
}
TRACK = {0: "Opt", 200: "Side", 400: "Dirty"}
L1_GET = (100, 101, 102, 103, 104, 105, 106)
IC_GET = (110, 111, 112)
L1_SET = (120, 121, 122)
IC_SET = (130, 131, 132, 133)


def read(path):
    by_kind = collections.Counter()
    per_site = collections.defaultdict(collections.Counter)
    for line in open(path):
        m = RE.match(line.rstrip("\n"))
        if not m:
            continue
        kind, ident, n = int(m.group(1)), int(m.group(2)), int(m.group(3))
        if kind % 200 not in BASE and (kind - 400) not in BASE:
            continue
        base = kind % 200 if kind < 200 else (kind - 200 if kind < 400 else kind - 400)
        if base not in BASE:
            continue
        by_kind[kind] += n
        per_site[ident][kind] += n
    return by_kind, per_site


def pct(a, b):
    return f"{100 * a / b:5.1f}%" if b else "    --"


def main():
    path = sys.argv[1]
    topn = int(sys.argv[sys.argv.index("--sites") + 1]) if "--sites" in sys.argv else 20
    by_kind, per_site = read(path)

    def tot(base, track=None):
        if track is None:
            return sum(by_kind[base + t] for t in TRACK)
        return by_kind[base + track]

    print("=== arms, by track ===")
    print(f"{'kind':<24}{'Opt':>14}{'Dirty':>14}{'total':>14}{'Dirty%':>8}")
    for base in sorted(BASE):
        t = tot(base)
        if not t:
            continue
        fam, label, _ = BASE[base]
        print(
            f"{fam + ' ' + label:<24}{tot(base, 0):>14,}{tot(base, 400):>14,}"
            f"{t:>14,}{pct(tot(base, 400), t):>8}"
        )

    l1_hit = sum(tot(k) for k in (100, 101, 103, 105))
    l1_miss = sum(tot(k) for k in (102, 104, 106))
    ic_all = sum(tot(k) for k in IC_GET)
    ic_only = ic_all - l1_miss
    gets = l1_hit + l1_miss + ic_only
    print("\n=== GetProp: what served the read ===")
    print(f"total property reads            {gets:>14,}")
    print(
        f"  class-fact arm HIT            {l1_hit:>14,} {pct(l1_hit, gets)}"
        f"   <- the analysis predicted and was right"
    )
    print(
        f"  class-fact arm MISS -> IC     {l1_miss:>14,} {pct(l1_miss, gets)}"
        f"   <- predicted and was WRONG"
    )
    print(
        f"  no class-fact arm at all      {ic_only:>14,} {pct(ic_only, gets)}"
        f"   <- nothing predicted"
    )
    armed = l1_hit + l1_miss
    print(f"\naccuracy where armed            {pct(l1_hit, armed)} of {armed:,}")
    print(f"coverage (armed / all reads)    {pct(armed, gets)}")
    print(
        f"IC miss helper (the Dirty call) {tot(113):>14,} "
        f"({100 * tot(113) / gets:.4f}% of reads)"
    )

    sl_hit = sum(tot(k) for k in (120, 121))
    sl_miss = tot(122)
    sic = sum(tot(k) for k in IC_SET)
    sic_only = sic - sl_miss
    sets = sl_hit + sl_miss + sic_only
    if sets:
        print("\n=== SetProp ===")
        print(f"total property writes           {sets:>14,}")
        print(f"  class-fact arm HIT            {sl_hit:>14,} {pct(sl_hit, sets)}")
        print(f"  class-fact arm MISS -> IC     {sl_miss:>14,} {pct(sl_miss, sets)}")
        print(f"  no class-fact arm at all      {sic_only:>14,} {pct(sic_only, sets)}")
        print(f"accuracy where armed            {pct(sl_hit, sl_hit + sl_miss)}")
        print(f"IC miss helper                  {tot(133):>14,}")

    if tot(140):
        print("\n=== arithmetic ===")
        print(f"arith op executions             {tot(140):>14,}")
        print(
            f"  generic-helper arm taken      {tot(141):>14,} "
            f"({100 * tot(141) / tot(140):.6f}%)"
        )

    ent = {k: tot(k) for k in range(150, 155)}
    etot = sum(ent.values())
    if etot:
        print("\n=== Opt -> Dirty transitions EXECUTED, by op family ===")
        for k in range(150, 155):
            print(f"  {BASE[k][1]:<26}{ent[k]:>14,} {pct(ent[k], etot)}")
        print(f"  {'total':<26}{etot:>14,}")

    for fam, lo in (("GetProp", 160), ("SetProp", 170)):
        rows = [(k, by_kind[k]) for k in range(lo, lo + 5) if by_kind[k]]
        t = sum(v for _, v in rows)
        if not t:
            continue
        print(f"\n=== why the {fam} class-fact guard missed ===")
        for k, v in rows:
            print(f"  {BASE[k][1]:<28}{v:>14,} {pct(v, t)}")
        print(f"  {'total misses attributed':<28}{t:>14,}")

    print(f"\n=== top {topn} sites by class-fact MISSES ===")
    rows = []
    for ident, c in per_site.items():
        miss = sum(c[b + t] for b in (102, 104, 106, 122) for t in TRACK)
        hit = sum(c[b + t] for b in (100, 101, 103, 105, 120, 121) for t in TRACK)
        if miss:
            rows.append((miss, hit, ident))
    rows.sort(reverse=True)
    print(f"{'site (sid:pc)':<18}{'misses':>14}{'hits':>14}{'hit%':>8}")
    for miss, hit, ident in rows[:topn]:
        print(
            f"{f'{ident >> 16}:{ident & 0xffff}':<18}{miss:>14,}{hit:>14,}"
            f"{pct(hit, hit + miss):>8}"
        )

    print(f"\n=== top {topn} unpredicted (IC-only) sites by executions ===")
    rows = []
    for ident, c in per_site.items():
        l1 = sum(c[b + t] for b in L1_GET + L1_SET for t in TRACK)
        if l1:
            continue
        ic = sum(c[b + t] for b in IC_GET + IC_SET for t in TRACK)
        if ic:
            dirty = sum(c[b + 400] for b in IC_GET + IC_SET)
            rows.append((ic, dirty, ident))
    rows.sort(reverse=True)
    print(f"{'site (sid:pc)':<18}{'executions':>14}{'on Dirty':>14}{'Dirty%':>8}")
    for ic, dirty, ident in rows[:topn]:
        print(
            f"{f'{ident >> 16}:{ident & 0xffff}':<18}{ic:>14,}{dirty:>14,}"
            f"{pct(dirty, ic):>8}"
        )
    print(f"\ndistinct IC-only sites executed: {len(rows):,}")


main()
