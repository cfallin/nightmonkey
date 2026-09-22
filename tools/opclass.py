#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Dynamic emitted-IR anatomy: which INSTRUCTION CLASS the Opt track spends
its execution on, and which bytecode op emitted it.

  opclass.py <opsize.err> <census.err> [stat.json] [--ops N] [--track opt|gen]

`--dump-opsize` already splits each emitted op instance into alu / load /
store / call / boxing / const / other, and `--census` already counts how many
times each (sid, pc, track) was entered. Joining them -- the same join
`aot-metrics` does for `dIR/op` -- gives the class breakdown *weighted by
execution*, which is what a machine-counter ratio has to be read against.

The question it exists to answer: `machperf.sh <bench> ion <bin>` says
navier-stokes issues twice Ion's loads per instruction at 100% OPT residency.
Twice as many loads OF WHAT? This says which bytecode ops emitted them, so a
redundancy hypothesis has a subject before it has a mechanism.

Caveats it inherits from the join, and one of its own:
  - entries are per executed op (a version is keyed per pc), so a class count
    is `entries x mean class IR at that (sid, pc, track)`;
  - the census id packs (sid << 16) | (pc & 0xffff) and is 32 bits, so wide
    scripts alias; `resolve` re-derives them exactly as `metrics.py` does;
  - emitted IR is not native instructions. A `Load` here is one wasm load,
    which the backend may fold into an addressing mode or hoist. Read this to
    rank causes, and `machperf.sh` to size them.
"""
import collections
import json
import re
import sys

RED = re.compile(
    r"^night: redundant sid#(\d+) pc (\d+) lpc \d+ op (\S+) track (\S+) "
    r"boxround (\d+) deadbox (\d+) frameround (\d+) frameload (\d+) framestore (\d+) "
    r"stackload (\d+) stackstore (\d+) entryload (\d+) entrystore (\d+) insts (\d+) entryinsts (\d+)"
)
OPS = re.compile(
    r"^night: opsize sid#(\d+) pc (\d+) lpc \d+ op (\S+) track (\S+) spliced (\d) "
    r"(?:dmerge \S+ )?(?:rung \S+ )?blocks \d+ params \d+ insts (\d+) "
    r"alu (\d+) load (\d+) store (\d+) call (\d+) boxing (\d+) const (\d+) other (\d+)"
)
CEN = re.compile(r"^night: census kind (\d+) id (\d+) n (\d+)$")
TRK = {"Opt": "opt", "Side": "gen", "Dirty": "gen"}
KIND = {1: "opt", 2: "gen", 3: "gen"}
CLASSES = ["alu", "load", "store", "call", "boxing", "const", "other"]
RED_CLASSES = [
    "boxround",
    "deadbox",
    "frameround",
    "frameload",
    "framestore",
    "stackload",
    "stackstore",
    "entryload",
    "entrystore",
    "insts",
    "entryinsts",
]


def load_static(path, red=False):
    """(sid, pc, track) -> [instances, <one slot per class>], plus the op name
    seen at that key. The two dumps share their key, so the same join serves
    both: `--dump-opsize`'s instruction classes, or `--dump-redundant`'s
    findings."""
    rx, ncls, first = (RED, len(RED_CLASSES), 5) if red else (OPS, 1 + len(CLASSES), 6)
    st = collections.defaultdict(lambda: [0] * (1 + ncls))
    name = {}
    with open(path) as f:
        for ln in f:
            m = rx.match(ln)
            if not m:
                continue
            sid, pc, op, track = (
                int(m.group(1)),
                int(m.group(2)),
                m.group(3),
                m.group(4),
            )
            k = (sid, pc, TRK[track])
            r = st[k]
            r[0] += 1
            for i in range(ncls):
                r[1 + i] += int(m.group(first + i))
            name[k] = op
    return st, name


def resolve_fn(st):
    maxpc = collections.defaultdict(int)
    for sid, pc, _t in st:
        maxpc[sid] = max(maxpc[sid], pc)

    def resolve(sid, pc, t):
        for j in range(0, 4):
            for k in range(0, 64):
                s2, p2 = sid + (j << 16) - k, pc + (k << 16)
                if s2 < 0 or s2 not in maxpc or p2 > maxpc[s2]:
                    continue
                if (s2, p2, t) in st:
                    return (s2, p2, t)
                for u in ("opt", "gen"):
                    if (s2, p2, u) in st:
                        return (s2, p2, u)
        return None

    return resolve


def main():
    argv, args, nops, only, red = sys.argv[1:], [], 14, None, False
    i = 0
    while i < len(argv):
        if argv[i] == "--ops":
            nops, i = int(argv[i + 1]), i + 2
        elif argv[i] == "--track":
            only, i = argv[i + 1], i + 2
        elif argv[i] == "--redundant":
            red, i = True, i + 1
        else:
            args.append(argv[i])
            i += 1
    opsize, census = args[0], args[1]
    work = None
    if len(args) > 2:
        s = json.load(open(args[2]))
        work = s.get("work")

    st, name = load_static(opsize, red)
    resolve = resolve_fn(st)
    classes = RED_CLASSES if red else CLASSES
    base = 1 if red else 2  # opsize keeps total `insts` in slot 1

    # dyn[track][class], per_op[(track, opname)][class], entries[track]
    dyn = {t: collections.Counter() for t in ("opt", "gen")}
    per_op = collections.defaultdict(collections.Counter)
    entries = collections.Counter()
    unmatched = 0
    with open(census) as f:
        for ln in f:
            m = CEN.match(ln.rstrip("\n"))
            if not m:
                continue
            kind, ident, n = int(m.group(1)), int(m.group(2)), int(m.group(3))
            if kind not in KIND:
                continue
            t = KIND[kind]
            k = resolve(ident >> 16, ident & 0xFFFF, t)
            if k is None:
                unmatched += n
                continue
            entries[t] += n
            r = st[k]
            for i, c in enumerate(classes):
                w = n * r[base + i] / r[0]
                dyn[t][c] += w
                per_op[(t, name[k])][c] += w
            per_op[(t, name[k])]["_entries"] += n
            dyn[t]["_entries"] += n

    tot = sum(entries.values())
    print(
        f"executed ops {tot:,}   OPT {100*entries['opt']/tot:.1f}%   "
        f"unmatched {unmatched:,}" + (f"   work {work}" if work else "")
    )
    print()
    hdr = f"{'class':<8}" + "".join(
        f"{c:>12}" for c in ("OPT M", "OPT/op", "GEN M", "GEN/op")
    )
    if work:
        hdr += f"{'M/score pt':>12}"
    print(hdr)
    for c in classes + ["_entries"]:
        o, g = dyn["opt"][c], dyn["gen"][c]
        row = f"{c.strip('_'):<8}{o/1e6:>12.1f}"
        row += f"{o/entries['opt']:>12.2f}" if entries["opt"] else f"{'-':>12}"
        row += f"{g/1e6:>12.1f}"
        row += f"{g/entries['gen']:>12.2f}" if entries["gen"] else f"{'-':>12}"
        if work:
            row += f"{(o+g)/1e6/work:>12.3f}"
        print(row)

    for t in ("opt", "gen"):
        if only and t != only:
            continue
        key = "frameload" if red else "load"
        rows = sorted(
            ((v, op) for (tt, op), v in per_op.items() if tt == t),
            key=lambda r: -r[0][key],
        )
        if not rows:
            continue
        cols = RED_CLASSES if red else ("load", "store", "alu", "boxing", "call")
        print(
            f"\ntop {t.upper()} ops by dynamic emitted {key.upper()} "
            f"(M; share of that track's {key})"
        )
        print(
            f"{'op':<22}{'entries M':>11}{f'%{key}':>10}"
            + "".join(f"{c:>10}" for c in cols)
        )
        tl = dyn[t][key] or 1
        for v, op in rows[:nops]:
            print(
                f"{op:<22}{v['_entries']/1e6:>11.2f}{100*v[key]/tl:>10.1f}"
                + "".join(f"{v[c]/1e6:>10.2f}" for c in cols)
            )


if __name__ == "__main__":
    main()
