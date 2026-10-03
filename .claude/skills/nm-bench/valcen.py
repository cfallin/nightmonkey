#!/usr/bin/env python3
# valcen.py out.txt map.txt [--sites] [--top N] [--grep RE]
#
# Executed Wasm values by the MIR op that emitted them (`--value-census`):
# the compile's map lines `night: mir vblock <id> sid#<s> tag:n ...` give
# each lowered Wasm block's values by emitter, the run's census lines
# (`night: census kind 94 id <id> n <count>`) how often each block ran.
#
# By default tags are folded to their op (`getprop.data@12:34` counts as
# `getprop.data`); --sites keeps the site. --grep keeps only tags matching
# RE (after folding). Prints values, share of the total, and executions of
# the blocks holding them (an op's values / executions is its cost per
# block entry, not per op: a block may hold several of one op).
import sys, re, collections

args = sys.argv[1:]
sites = '--sites' in args
top = 40
pat = None
if '--top' in args:
    top = int(args[args.index('--top') + 1])
if '--grep' in args:
    pat = re.compile(args[args.index('--grep') + 1])
out, mp = [a for a in args if not a.startswith('--') and not a.isdigit() and (pat is None or a != pat.pattern)][:2]

blocks = {}
for l in open(mp, errors='replace'):
    r = re.match(r'night: mir vblock (\d+) sid#(\d+) (.*)', l)
    if not r:
        continue
    rec = []
    for t in r.group(3).split():
        tag, _, n = t.rpartition(':')
        rec.append((tag, int(n)))
    blocks[int(r.group(1))] = (int(r.group(2)), rec)

counts = collections.Counter()
for l in open(out, errors='replace'):
    r = re.match(r'night: census kind 94 id (\d+) n (\d+)', l)
    if r:
        counts[int(r.group(1))] += int(r.group(2))

vals = collections.Counter()
execs = collections.Counter()
total = 0
for bid, n in counts.items():
    if bid not in blocks:
        continue
    _, rec = blocks[bid]
    for tag, k in rec:
        key = tag if sites else tag.split('@')[0]
        vals[key] += k * n
        execs[key] += n
        total += k * n
print("values total %d (%d blocks mapped, %d executed)" % (total, len(blocks), len(counts)))
shown = 0
for key, v in vals.most_common():
    if pat and not pat.search(key):
        continue
    print("  %14d %6.2f%%  %12d  %s" % (v, 100.0 * v / max(total, 1), execs[key], key))
    shown += 1
    if shown >= top:
        break
