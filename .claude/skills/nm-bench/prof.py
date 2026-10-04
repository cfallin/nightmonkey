#!/usr/bin/env python3
"""Attribute a NightMonkey AOT profile: compiled code vs helpers vs engine C++.

Input: `perf script` output of `perf record -g wasmtime run --profile=perfmap
...` on a module compiled with `nightmonkey --keep-names` (see prof.sh).
Weights are the sample periods (cycles).

  prof.py stacks.txt [--tiers tiers.txt] [--top N]
      the split by leaf class, the top leaf functions, and helper time by
      calling script (the innermost compiled script on the stack, and the
      first non-script frame it called: the helper it entered)
  prof.py stacks.txt --under RE [--top N]
      for frames matching RE (outermost occurrence per sample): the
      immediate callees and the leaf functions under them, and the calling
      scripts

Leaf classes:
  script   night_script_<sid>: MIR or baseline compiled bodies
  regex    night_regex_*: compiled regexp matchers
  glue     night_adapter_*, night_call_classify, night_ic_*: compiled glue
  helper   night_runtime_* and other night_* C++ entry points
  engine   any other function in the wasm module (SpiderMonkey C++)
  host     wasmtime and the kernel
`--tiers` takes `nightmonkey --dump-tiers` output (its `night: script sid#N
name` lines) to name the scripts.
"""
import argparse
import collections
import re
import sys

FRAME = re.compile(r'^\s+[0-9a-f]+\s+(.*?)\s+\((.*)\)\s*$')
WASM = re.compile(r'wasm\[\d+\]::function\[\d+\]::(.*)')
HEADER = re.compile(r'^\S.*?:\s+(\d+)\s+\S+:\s*$')


def short(name):
    m = WASM.match(name)
    if not m:
        return None
    n = m.group(1)
    n = re.sub(r'\+0x[0-9a-f]+$', '', n)
    # Drop C++ parameter lists for readability.
    i = n.find('(')
    return n[:i] if i > 0 else n


def classify(fn):
    if fn is None:
        return 'host'
    if fn.startswith('night_script_'):
        return 'script'
    if fn.startswith('night_regex_'):
        return 'regex'
    if fn.startswith(('night_adapter_', 'night_call_classify', 'night_ic_')):
        return 'glue'
    if fn.startswith('night_') or fn.startswith('js::Night') or 'Night' in fn.split('::')[-1][:6]:
        return 'helper'
    return 'engine'


def samples(path):
    period = None
    frames = []
    with open(path, errors='replace') as f:
        for line in f:
            if not line.strip():
                if period is not None:
                    yield period, frames
                period, frames = None, []
                continue
            m = HEADER.match(line)
            if m and not line[0].isspace():
                period = int(m.group(1))
                frames = []
                continue
            m = FRAME.match(line)
            if m:
                frames.append(short(m.group(1)))
    if period is not None:
        yield period, frames


def load_names(path):
    names = {}
    if not path:
        return names
    for line in open(path, errors='replace'):
        m = re.match(r'night: script sid#(\d+) (.*)', line)
        if m:
            names[m.group(1)] = m.group(2).strip()
    return names


def script_label(fn, names):
    sid = fn[len('night_script_'):]
    return f'{fn} ({names.get(sid, "?")})'


def pct(w, tot):
    return f'{100.0 * w / tot:6.2f}%'


def report(rows, tot, top, title):
    print(f'\n== {title}')
    for k, w in rows.most_common(top):
        print(f'  {pct(w, tot)}  {k}')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('stacks')
    ap.add_argument('--tiers')
    ap.add_argument('--top', type=int, default=25)
    ap.add_argument('--under')
    a = ap.parse_args()
    names = load_names(a.tiers)

    tot = 0
    by_class = collections.Counter()
    leaves = collections.Counter()
    by_entry = collections.Counter()
    by_script_helper = collections.Counter()
    by_script_self = collections.Counter()
    under_re = re.compile(a.under) if a.under else None
    u_tot = 0
    u_callee = collections.Counter()
    u_leaf = collections.Counter()
    u_caller = collections.Counter()

    for w, frames in samples(a.stacks):
        if not frames:
            continue
        tot += w
        leaf = frames[0]
        cls = classify(leaf)
        by_class[cls] += w
        leaves[leaf or '[host]'] += w
        # Innermost compiled script, and the frame it called.
        si = next((i for i, f in enumerate(frames)
                   if f and f.startswith('night_script_')), None)
        if si is not None:
            s = script_label(frames[si], names)
            if si == 0:
                by_script_self[s] += w
            else:
                # The first non-glue frame above the script: what it entered.
                j = si - 1
                while j > 0 and classify(frames[j]) == 'glue':
                    j -= 1
                entry = frames[j] or '[host]'
                by_entry[entry] += w
                by_script_helper[f'{s} -> {entry}'] += w
        if under_re:
            ui = None
            for i in range(len(frames) - 1, -1, -1):
                if frames[i] and under_re.search(frames[i]):
                    ui = i
                    break
            if ui is not None:
                u_tot += w
                u_callee[(frames[ui - 1] or '[host]') if ui > 0 else '[self]'] += w
                u_leaf[leaf or '[host]'] += w
                ci = next((i for i in range(ui + 1, len(frames))
                           if frames[i] and frames[i].startswith('night_script_')), None)
                u_caller[script_label(frames[ci], names) if ci is not None else '[none]'] += w

    if not tot:
        print('no samples')
        return
    if under_re:
        print(f'{a.under}: {pct(u_tot, tot)} of all samples (inclusive)')
        report(u_callee, u_tot, a.top, 'immediate callees (share of the inclusive time)')
        report(u_leaf, u_tot, a.top, 'leaf functions')
        report(u_caller, u_tot, a.top, 'calling scripts')
        return
    print('== split by leaf class')
    for k in ('script', 'regex', 'glue', 'helper', 'engine', 'host'):
        print(f'  {pct(by_class[k], tot)}  {k}')
    report(leaves, tot, a.top, 'leaf functions (self)')
    report(by_entry, tot, a.top, 'entered from compiled scripts (inclusive)')
    report(by_script_self, tot, a.top, 'compiled scripts (self)')
    report(by_script_helper, tot, a.top, 'script -> entered function (inclusive)')


if __name__ == '__main__':
    main()
