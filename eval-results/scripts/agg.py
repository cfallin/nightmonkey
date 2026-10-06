#!/usr/bin/env python3
"""Aggregate abx batches: each variant vs the base of its own batch.

Per bench: median of the variant's kept scores / median of base's kept
scores (robust.py's rule: drop scores < 80% of own median, counted).
Geomean over benches (a bench where a variant failed is reported and left
out of that variant's geomean, with a note). Also: the min/max ratio over
seeds (pairing seed i of variant with seed i of base -- same placement
seed, different code), as a spread indicator.

usage: agg.py [--md] res/*.txt
"""
import sys, statistics as st, collections, math, os

md = '--md' in sys.argv
files = [a for a in sys.argv[1:] if not a.startswith('--') and a.endswith('.txt')
         and not os.path.basename(a).startswith(('excensus', 'vcensus', 'prof'))
         and '.cpu.' not in a]
BENCH = "box2d code-load crypto deltablue earley-boyer mandreel navier-stokes pdfjs raytrace regexp richards splay react".split()

def kept(xs):
    xs = [x for x in xs if x > 0]
    if not xs:
        return [], 0
    m = st.median(xs)
    k = [x for x in xs if x >= 0.8 * m]
    return k, len(xs) - len(k)

rows = []      # (batch, variant, {bench: ratio}, {bench: (lo,hi)}, drops, fails)
base_abs = {}  # batch -> {bench: base median}
for f in sorted(files):
    batch = os.path.basename(f)[:-4]
    d = collections.defaultdict(dict)
    order = []
    for l in open(f):
        p = l.split()
        if len(p) < 4:
            continue
        v, b, sd, s = p[0], p[1], p[2], int(p[3])
        d[(v, b)][sd] = s
        if v not in order:
            order.append(v)
    if 'base' not in order:
        continue
    base_abs[batch] = {}
    for b in BENCH:
        k, _ = kept(list(d[('base', b)].values()))
        if k:
            base_abs[batch][b] = st.median(k)
    for v in order:
        if v == 'base':
            continue
        rat, spread, drops, fails = {}, {}, 0, []
        for b in BENCH:
            if ('base', b) not in d:
                continue
            kb, _ = kept(list(d[('base', b)].values()))
            kv, dv = kept(list(d[(v, b)].values()))
            drops += dv
            if not kv or not kb:
                fails.append(b)
                continue
            rat[b] = st.median(kv) / st.median(kb)
            pr = [d[(v, b)][s] / d[('base', b)][s] for s in d[(v, b)]
                  if d[(v, b)][s] > 0 and d[('base', b)].get(s, 0) > 0]
            spread[b] = (min(pr), max(pr)) if pr else (None, None)
        rows.append((batch, v, rat, spread, drops, fails))

def gm(xs):
    return math.exp(sum(math.log(x) for x in xs) / len(xs)) if xs else float('nan')

def pct(x):
    return "%+.0f%%" % (100 * (x - 1))

hdr = ["variant", "batch", "geomean"] + BENCH + ["drops", "failed"]
if md:
    print("| " + " | ".join(hdr) + " |")
    print("|" + "---|" * len(hdr))
else:
    print("%-20s %-12s %8s " % tuple(hdr[:3]) + " ".join("%8s" % b[:8] for b in BENCH) + "  drops failed")
for batch, v, rat, spread, drops, fails in rows:
    g = gm(list(rat.values()))
    cells = [pct(rat[b]) if b in rat else ("FAIL" if b in fails else "") for b in BENCH]
    if md:
        print("| " + " | ".join([v, batch, pct(g)] + cells + [str(drops), ",".join(fails)]) + " |")
    else:
        print("%-20s %-12s %8s " % (v, batch, pct(g)) + " ".join("%8s" % c for c in cells) + "  %d %s" % (drops, ",".join(fails)))

if '--base' in sys.argv:
    print("\nbase medians per batch (drift check):")
    bs = sorted(base_abs)
    print("%-14s" % "bench" + "".join("%14s" % x[:13] for x in bs))
    for b in BENCH:
        print("%-14s" % b + "".join("%14s" % (int(base_abs[x][b]) if b in base_abs[x] else "-") for x in bs))
