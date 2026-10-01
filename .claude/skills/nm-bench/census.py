#!/usr/bin/env python3
# census.py out.txt map.txt : summarize MIR exit census (kind 90) and epoch-bump sites (kind 66).
import sys, re, collections
out, mp = sys.argv[1], sys.argv[2]
m = {}
for l in open(mp):
    r = re.match(r'night: mir exit (\d+) (.*)', l)
    if r: m[int(r.group(1))] = r.group(2)
k = collections.defaultdict(lambda: collections.Counter())
for l in open(out):
    r = re.match(r'night: census kind (\d+) id (\d+) n (\d+)', l)
    if r: k[int(r.group(1))][int(r.group(2))] += int(r.group(3))
ex = k[90]
print("exits total", sum(ex.values()))
for i, n in ex.most_common(int(sys.argv[3]) if len(sys.argv) > 3 else 15):
    print("  %8d  %s" % (n, m.get(i, "?%d" % i)))
bs = collections.Counter()
for i, n in k[66].items(): bs[i >> 16] += n
print("epoch bumps by site", dict(sorted(bs.items())))
for kk in sorted(k):
    if kk not in (90, 66): print("kind", kk, "total", sum(k[kk].values()))
