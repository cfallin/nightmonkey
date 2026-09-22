#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

"""Steady-state hot-loop extraction + composition histogram from perf data.

The expectation-vs-reality workflow: record a bench under perf with
wasmtime perfmap symbols, find the
hot symbol, extract its steady-state inner loop by back-edge + sample mass,
and histogram the loop body by instruction class.

Usage:
  hotloop.py record <cwasm> -o <perf.data> [-F freq] [-c core]
      taskset -c <core> perf record -F <freq> wasmtime run --allow-precompiled
      --profile=perfmap -W unknown-imports-trap <cwasm>
      Copies the cwasm to a private name first (per-file artifact-layout bias:
      re-copy per run) and prints the bench's stdout tail.
  hotloop.py top <perf.data> [-n N]
      Top N symbols by sample share.
  hotloop.py loop <perf.data> -s <symbol> [--thresh PCT] [--n-loops N] [--dump F]
      perf annotate the symbol, list top back-edge loops by contained sample
      mass, pick the SMALLEST loop containing >= PCT (default 90) of samples,
      and print its instruction-class histogram (static count + sample mass).
      --dump saves the raw annotate text for by-hand staring.

Caveats: sample percentages are relative to the SYMBOL, and nested loops
overlap (an outer loop "contains" its inner loop's mass). Fixed-time benches
burn identical cycles regardless of speed -- divide by score before comparing
per-work-unit numbers across builds.
"""
import argparse
import collections
import os
import re
import shutil
import subprocess
import sys

WASMTIME = os.environ.get("WASMTIME", os.path.expanduser("~/bin/wasmtime"))

ANN_RE = re.compile(r"\s*([\d.]+)?\s*:\s*([0-9a-f]+):\s+(\S+)(.*)")
MEM_RE = re.compile(r"\(%r")


def parse_annotate(lines):
    rows = []
    for line in lines:
        m = ANN_RE.match(line)
        if m:
            rows.append(
                (
                    int(m.group(2), 16),
                    float(m.group(1)) if m.group(1) else 0.0,
                    m.group(3),
                    m.group(4).strip(),
                )
            )
    return rows


def classify(op, rest):
    if op.startswith(("cvt", "vcvt")):
        return "cvt"
    if op in ("vmovq", "movq") and "xmm" in rest:
        return "gp<->xmm"
    if op.startswith(
        ("vadd", "vsub", "vmul", "vdiv", "vsqrt", "addsd", "subsd", "mulsd", "divsd")
    ):
        return "fp-arith"
    if op.startswith(("vucomis", "ucomis", "vcomis", "comis")):
        return "fp-cmp"
    if op.startswith(("cmov", "set")):
        return "cmov/set"
    if "0xffffff8" in rest:
        return "tag-cmp"
    if op.startswith("j"):
        return "branch"
    if op.startswith("call"):
        return "call"
    if op.startswith(("cmp", "test")):
        return "cmp/test"
    if op.startswith(("mov", "vmov", "lea")):
        if MEM_RE.search(rest):
            dst_is_mem = "," in rest and MEM_RE.search(rest.split(",")[-1])
            return "mem-store" if dst_is_mem else "mem-load"
        return "reg-mov"
    if op.startswith(
        (
            "add",
            "sub",
            "imul",
            "mul",
            "and",
            "or",
            "xor",
            "shl",
            "shr",
            "sar",
            "neg",
            "not",
            "inc",
            "dec",
        )
    ):
        return "int-arith"
    return "other"


def back_edges(rows):
    addrs = {a for a, _, _, _ in rows}
    pcts = [(a, p) for a, p, _, _ in rows]
    edges = []
    for a, p, op, rest in rows:
        if not op.startswith("j"):
            continue
        m = re.match(r"([0-9a-f]+)\b", rest)
        if not m:
            continue
        t = int(m.group(1), 16)
        if t < a and t in addrs:
            mass = sum(pp for aa, pp in pcts if t <= aa <= a)
            n = sum(1 for aa, _ in pcts if t <= aa <= a)
            edges.append((mass, t, a, a - t, n))
    return edges


def annotate(perfdata, symbol):
    out = subprocess.run(
        ["perf", "annotate", "-i", perfdata, "--stdio", "-s", symbol],
        check=False,
        capture_output=True,
        text=True,
    ).stdout
    return out


def cmd_record(args):
    # The copy stays alive: perf resolves jit symbols from the mmap'd cwasm
    # file at report time (and per-file artifact-layout bias demands a fresh
    # copy per run anyway).
    tmp = os.path.abspath(args.output) + ".cwasm"
    shutil.copy(args.cwasm, tmp)
    cmd = [
        "taskset",
        "-c",
        str(args.core),
        "perf",
        "record",
        "-o",
        args.output,
        "-F",
        str(args.freq),
        "--",
        WASMTIME,
        "run",
        "--allow-precompiled",
        "--profile=perfmap",
        "-W",
        "unknown-imports-trap",
        tmp,
    ]
    r = subprocess.run(cmd, check=False, capture_output=True, text=True)
    tail = (r.stdout.strip().splitlines() or [""])[-1]
    print(f"exit={r.returncode} last-stdout: {tail}")
    if r.returncode != 0:
        print(r.stderr[-2000:], file=sys.stderr)
        sys.exit(1)


def cmd_top(args):
    out = subprocess.run(
        ["perf", "report", "-i", args.perfdata, "--stdio"],
        check=False,
        capture_output=True,
        text=True,
    ).stdout
    shown = 0
    for line in out.splitlines():
        m = re.match(r"\s+([\d.]+)%\s+\S+\s+(\S+)\s+\S+\s+(?:\[[.k]\]\s+)?(.*)", line)
        if m:
            print(f"  {float(m.group(1)):6.2f}%  {m.group(3).strip() or m.group(2)}")
            shown += 1
            if shown >= args.n:
                break


def cmd_loop(args):
    text = annotate(args.perfdata, args.symbol)
    if args.dump:
        open(args.dump, "w").write(text)
    rows = parse_annotate(text.splitlines())
    if not rows:
        print(f"no annotate rows for symbol {args.symbol!r}", file=sys.stderr)
        sys.exit(1)
    edges = back_edges(rows)
    if not edges:
        print(f"no back-edges found; fn instrs={len(rows)}")
        sys.exit(1)
    edges.sort(reverse=True)
    print(
        f"fn instrs={len(rows)}  top back-edge loops "
        f"(samples%, target <- jump, bytes, instrs):"
    )
    for mass, t, a, sz, n in edges[: args.n_loops]:
        print(f"  {mass:6.1f}%  {t:#x} <- {a:#x}  {sz} bytes  {n} instrs")
    cands = sorted([e for e in edges if e[0] >= args.thresh], key=lambda e: e[3])
    if not cands:
        print(
            f"no loop holds >= {args.thresh}% of samples; "
            f"lower --thresh or read the list above"
        )
        sys.exit(1)
    mass, t, a, sz, n = cands[0]
    print(
        f"\nsteady-state loop: {t:#x}-{a:#x}, {n} instrs, {sz} bytes, "
        f"{mass:.1f}% of symbol samples"
    )
    cnt = collections.Counter()
    samp = collections.Counter()
    for aa, p, op, rest in rows:
        if t <= aa <= a:
            k = classify(op, rest)
            cnt[k] += 1
            samp[k] += p
    print(f"  {'class':<10} {'n':>6} {'samples%':>9}")
    for k in sorted(cnt, key=lambda k: -samp[k]):
        print(f"  {k:<10} {cnt[k]:>6} {samp[k]:>8.1f}%")


def main():
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("record")
    r.add_argument("cwasm")
    r.add_argument("-o", "--output", required=True)
    r.add_argument("-F", "--freq", type=int, default=2000)
    r.add_argument("-c", "--core", type=int, default=1)
    r.set_defaults(fn=cmd_record)
    t = sub.add_parser("top")
    t.add_argument("perfdata")
    t.add_argument("-n", type=int, default=10)
    t.set_defaults(fn=cmd_top)
    l = sub.add_parser("loop")
    l.add_argument("perfdata")
    l.add_argument("-s", "--symbol", required=True)
    l.add_argument("--thresh", type=float, default=90.0)
    l.add_argument("--n-loops", type=int, default=5)
    l.add_argument("--dump")
    l.set_defaults(fn=cmd_loop)
    args = ap.parse_args()
    args.fn(args)


if __name__ == "__main__":
    main()
