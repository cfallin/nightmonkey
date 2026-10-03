#!/usr/bin/env python3
# propw.py out.txt map.txt [--top N] [--sites]
#
# Generic property access weighted by executed cost: the value census's
# values (`--value-census`) at generic property ops (`getprop.data`,
# `setprop.data`, `js.getprop`, `js.setprop`) joined, by site, with the
# analysis's reason it gave the site no `prop_sites` row (`--dump-propgap`,
# in the same map). A site with no propgap line either has a row the
# builder did not use ("has-row") or no record at all.
#
# Reasons are folded to their first two words (`no-agreed-class
# objty=AnyObject`); --sites lists the heaviest sites with their full line.
import sys, re, collections

args = sys.argv[1:]
top = 25
if '--top' in args:
    top = int(args[args.index('--top') + 1])
sites_mode = '--sites' in args
out, mp = [a for a in args if not a.startswith('--') and not a.isdigit()][:2]

GENERIC = ('getprop.data', 'setprop.data', 'js.getprop', 'js.setprop')
blocks = {}
gap = {}
for l in open(mp, errors='replace'):
    r = re.match(r'night: mir vblock (\d+) sid#(\d+) (.*)', l)
    if r:
        rec = []
        for t in r.group(3).split():
            tag, _, n = t.rpartition(':')
            rec.append((tag, int(n)))
        blocks[int(r.group(1))] = rec
        continue
    r = re.match(r'night: propgap (\d+:\d+) why (.*)', l)
    if r:
        gap[r.group(1)] = r.group(2)

counts = collections.Counter()
for l in open(out, errors='replace'):
    r = re.match(r'night: census kind 94 id (\d+) n (\d+)', l)
    if r:
        counts[int(r.group(1))] += int(r.group(2))

total = 0
by_site = collections.Counter()
op_of = {}
for bid, n in counts.items():
    for tag, k in blocks.get(bid, []):
        total += k * n
        op, _, site = tag.partition('@')
        if op in GENERIC and site:
            by_site[site] += k * n
            op_of[site] = op

def fold(why):
    w = why.split()
    # "no-agreed-class recv var objty Empty kind get name x" -> reason + objty
    d = dict(zip(w[1::2], w[2::2]))
    return w[0] + (' objty=' + d['objty'] if 'objty' in d else '')

generic = sum(by_site.values())
print("values total %d, generic property ops %d (%.1f%%)" % (total, generic, 100.0 * generic / max(total, 1)))
reasons = collections.Counter()
for site, v in by_site.items():
    reasons[fold(gap[site]) if site in gap else 'no-propgap-line'] += v
for r, v in reasons.most_common(top):
    print("  %12d %5.1f%%  %s" % (v, 100.0 * v / max(generic, 1), r))
if sites_mode:
    print()
    for site, v in by_site.most_common(top):
        print("  %12d %5.1f%%  %-13s %-10s %s" % (v, 100.0 * v / max(generic, 1), op_of[site], site, gap.get(site, '(no propgap line)')))
