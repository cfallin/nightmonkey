#!/usr/bin/env python3
"""Build plot-ready CSVs from the ablation batches and the lanes table.

usage: make_csv.py <outdir>

Inputs ($W = ~/.cache/nm-bench):
  res/b*.txt     abx batches: "variant bench seed score" (best of 2 runs per
                 pad seed; each batch includes `base`, the default NM build)
  res/lanes.txt  lanes.sh table: best of 3 per (engine, bench)

Outputs:
  scores.csv     one row per bench (+ geomean): engines' scores, then every
                 NM variant. A variant's score = (its median / its own
                 batch's base median) x the pooled base median (median over
                 every batch's base runs), so drift between batches does not
                 leak into absolute numbers. nm_default = the pooled base.
  relative.csv   same layout, variant / same-batch base (1.0 = no change);
                 engines relative to nm_default.
  spread.csv     per bench x variant: ratio median, min, max over the 4 pad
                 seeds (seed i of variant / seed i of base, same batch).
  raw_long.csv   bench, config, batch, seed, score: every kept run.
"""
import sys, os, glob, math, re, csv, statistics as st, collections

W = os.path.expanduser('~/.cache/nm-bench')
out = sys.argv[1]
os.makedirs(out, exist_ok=True)
BENCH = "box2d code-load crypto deltablue earley-boyer mandreel navier-stokes pdfjs raytrace regexp richards splay react".split()
ENGINES = [('native-ion', 'native_ion'), ('native-baseline', 'native_baseline'),
           ('wasm-interp', 'wasm_interp'), ('weval', 'weval'), ('aot', 'nm_lanes_check')]

def kept(xs):
    xs = [x for x in xs if x > 0]
    if not xs:
        return []
    m = st.median(xs)
    return [x for x in xs if x >= 0.8 * m]

# --- abx batches
data = collections.defaultdict(dict)   # (batch, variant, bench) -> {seed: score}
order = []
for f in sorted(glob.glob(f'{W}/res/b*.txt')):
    if '.cpu.' in f:
        continue
    batch = os.path.basename(f)[:-4]
    for l in open(f):
        p = l.split()
        if len(p) < 4:
            continue
        v, b, sd, s = p[0], p[1], p[2], int(p[3])
        data[(batch, v, b)][sd] = s
        if v != 'base' and v not in order:
            order.append(v)
batches = sorted({k[0] for k in data})

pooled = {}
for b in BENCH:
    xs = []
    for bt in batches:
        xs += kept(list(data.get((bt, 'base', b), {}).values()))
    pooled[b] = st.median(xs) if xs else None

rel, spread = {}, {}
for bt in batches:
    for v in order:
        for b in BENCH:
            if (bt, v, b) not in data:
                continue
            kb = kept(list(data[(bt, 'base', b)].values()))
            kv = kept(list(data[(bt, v, b)].values()))
            if not kb:
                continue
            if not kv:
                rel[(v, b)] = 'FAIL'
                continue
            rel[(v, b)] = st.median(kv) / st.median(kb)
            pr = [data[(bt, v, b)][s] / data[(bt, 'base', b)][s]
                  for s in data[(bt, v, b)]
                  if data[(bt, v, b)][s] > 0 and data[(bt, 'base', b)].get(s, 0) > 0]
            spread[(v, b)] = (rel[(v, b)], min(pr), max(pr)) if pr else None

# --- lanes
eng = {}
lf = f'{W}/res/lanes.txt'
if os.path.exists(lf):
    lines = [l.split() for l in open(lf) if l.strip()]
    hdr = next((l for l in lines if l and l[0] == 'bench'), None)
    if hdr:
        short = {'ion': 'native-ion', 'baseline': 'native-baseline', 'wasm-int': 'wasm-interp',
                 'weval': 'weval', 'aot': 'aot'}
        cols = [short.get(h, h) for h in hdr[1:]]
        for l in lines:
            if l[0] in BENCH:
                for c, x in zip(cols, l[1:]):
                    if re.match(r'^[0-9.]+$', x) and '/' not in c:
                        eng[(c, l[0])] = float(x)

def gm(xs):
    xs = [x for x in xs if isinstance(x, float) and x > 0]
    return math.exp(sum(map(math.log, xs)) / len(xs)) if xs else ''

def fmt(x, d):
    return ('%.*f' % (d, x)) if isinstance(x, float) else x

cfg = [c for _, c in ENGINES] + ['nm_default'] + ['nm_' + v for v in order]

def row_abs(b):
    r = {c: eng.get((e, b), '') for e, c in ENGINES}
    r['nm_default'] = float(pooled[b]) if pooled[b] else ''
    for v in order:
        x = rel.get((v, b), '')
        r['nm_' + v] = x * pooled[b] if isinstance(x, float) and pooled[b] else x
    return r

def row_rel(b):
    r = {}
    for e, c in ENGINES:
        x = eng.get((e, b))
        r[c] = x / pooled[b] if x and pooled[b] else ''
    r['nm_default'] = 1.0
    for v in order:
        r['nm_' + v] = rel.get((v, b), '')
    return r

for name, fn, d in (('scores.csv', row_abs, 0), ('relative.csv', row_rel, 4)):
    rows = {b: fn(b) for b in BENCH}
    with open(f'{out}/{name}', 'w', newline='') as fh:
        w = csv.writer(fh)
        w.writerow(['bench'] + cfg)
        for b in BENCH:
            w.writerow([b] + [fmt(rows[b][c], d) for c in cfg])
        # geomean over benches where the config has a number; failures
        # are left out (and the count of benches used is in the next row)
        w.writerow(['geomean'] + [fmt(gm([rows[b][c] for b in BENCH]), d) for c in cfg])
        common = [b for b in BENCH if all(isinstance(rows[b][c], float) for c in cfg)]
        w.writerow(['geomean_common'] + [fmt(gm([rows[b][c] for b in common]), d) for c in cfg])
        w.writerow(['n_benches'] + [sum(isinstance(rows[b][c], float) for b in BENCH) for c in cfg])

with open(f'{out}/spread.csv', 'w', newline='') as fh:
    w = csv.writer(fh)
    w.writerow(['bench', 'variant', 'ratio_median', 'ratio_min_seed', 'ratio_max_seed'])
    for v in order:
        for b in BENCH:
            s = spread.get((v, b))
            if s:
                w.writerow([b, v] + ['%.4f' % x for x in s])
            elif rel.get((v, b)) == 'FAIL':
                w.writerow([b, v, 'FAIL', '', ''])

with open(f'{out}/raw_long.csv', 'w', newline='') as fh:
    w = csv.writer(fh)
    w.writerow(['bench', 'config', 'batch', 'seed', 'score'])
    for (bt, v, b), seeds in sorted(data.items()):
        for sd, s in sorted(seeds.items()):
            w.writerow([b, 'nm_default' if v == 'base' else 'nm_' + v, bt, sd, s])
    for (e, b), x in sorted(eng.items()):
        w.writerow([b, dict(ENGINES)[e], 'lanes', 'best_of_3', int(x)])
print('common benches:', [b for b in BENCH if all(isinstance(row_abs(b)[c], float) for c in cfg)])
print(f"wrote {out}: {len(order)} variants, {len(batches)} batches, {len(eng)} engine cells")
