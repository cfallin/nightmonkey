#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

"""Speculation visualizer for the NightMonkey BBV compiler.

Runs the AOT compiler on a wizer snapshot with --viz, parses the
per-version / per-event dump, and writes one self-contained HTML page
showing, per script and per bytecode op: the versions minted (Opt / Side /
Dirty track chips), the ctx facts each version holds, the carried unboxed
reprs, offramp events (may-GC helper calls that dirty a lineage) and onramp
events (conform sequences rejoining the Opt loop header), next to the JS
source.

Heap panels: the layout panel shows each predicted field's slot, value
mask and RANGE claim; the array panel lists the populations whose elements
carry a range, with the stamp key they fold against and where they are
stamped.

Every op also carries its LOWERING: click the op and a pane opens with the
mini-CFG it expands to -- blocks and their params (annotated with what the
params hold where the emitter knows it), guard conditions resolved to the
tag/stamp word being tested, boxing and unboxing, memory traffic by heap
kind, helper calls by name, and the continuation each side arm rejoins at
with its track. This is per-instruction data and dominates the page size
(crypto goes 5M -> 22M, and the biggest bundles are far worse), so
--no-lower drops it when a page gets unwieldy.

Usage:
  viz.py SNAPSHOT.wasm SOURCE.js -o OUT.html [--nmc PATH]
         [--stderr-cache FILE] [--title T] [--no-lower]

The compiler runs with --dump-bbv --viz --viz-lower, plus --viz-facts to
collect the analysis half of the trace from a file; --no-lower drops
--viz-lower.
"""

import argparse
import html
import json
import os
import re
import subprocess
import sys
import tempfile

RE_BEGIN = re.compile(r"^night: viz begin sid#(\d+)$")
RE_SCRIPT = re.compile(
    r"^night: viz script sid#(\d+) name (\S+) nargs (\d+) nlocals (\d+)"
    r" bclen (\d+) global (\d)$"
)
RE_LOOP = re.compile(r"^night: viz loop sid#(\d+) interval (\d+) (\d+)$")
RE_OP = re.compile(r"^night: viz op sid#(\d+) pc (\d+) op (\S+) args \[(.*)\]$")
RE_VER = re.compile(
    r"^night: viz ver sid#(\d+) pc (\d+) lpc (\d+) inline (\S+) site (\S+)"
    r" path (\S+) op (\S+) args \[(.*?)\] track (\S+) class (\d+) depth (\d+)"
    r" facts \[(.*)\] carried \[(.*)\]$"
)
RE_DIRTY = re.compile(
    r"^night: viz dirty sid#(\d+) pc (\d+) lpc (\d+) site (\S+) path (\S+)"
    r" op (\S+) helper (\S+) track (\S+)$"
)
RE_THIS = re.compile(r"^night: viz thislocal sid#(\d+) loc (\d+)$")
RE_LICM = re.compile(
    r"^night: viz licm sid#(\d+) pc (\d+) lpc (\d+) site (\S+) path (\S+)"
    r" kind (\S+)$"
)
RE_SITE = re.compile(r"^night: viz site sid#(\d+) pc (\d+) kind (\S+) pred (.*)$")
RE_LAYOUT = re.compile(r"^night: viz layout id (\d+) fields \[(.*)\]$")
RE_DEF = re.compile(r"^night: viz def sid#(\d+) lpc (\d+) path (\S+) ty (\S+)$")
RE_ARGTY = re.compile(r"^night: viz argty sid#(\d+) i (\d+) ty (\S+)$")
RE_ONRAMP = re.compile(
    r"^night: viz onramp (emit|decline \S+) sid#(\d+) hdr (\d+) pc (\d+)"
    r" site (\S+) guards \[(.*)\]$"
)
RE_ARRCLAIM = re.compile(
    r"^night: viz arrclaim root (\d+) key (\d+) mask (\S+) lo (-?\d+) hi (-?\d+)"
    r" allocs \[(.*)\] elemsites (\d+)$"
)
RE_HELPER = re.compile(r"^night: viz helper (\d+) (\S+)$")
RE_LOWER = re.compile(
    r"^night: viz lower sid#(\d+) lpc (\d+) entry b(\d+) blocks (\d+)$"
)
RE_LOWERB = re.compile(
    r"^night: viz lowerb sid#(\d+) lpc (\d+) blk b(\d+) skip (\d+) params \[(.*)\]"
    r" insts (\d+) term (.*)$"
)
RE_LOWERI = re.compile(
    r"^night: viz loweri sid#(\d+) lpc (\d+) blk b(\d+) k (\S+) d (.*)$"
)
RE_LOWERP = re.compile(
    r"^night: viz lowerp sid#(\d+) blk b(\d+) kind (\S+) reprs \[(.*)\]$"
)
RE_LOWERK = re.compile(
    r"^night: viz lowerk sid#(\d+) lpc (\d+) blk b(\d+) succ (\d+) track (\S+)$"
)


def run_compiler(nmc, snapshot, lower=True):
    # The translator half of the trace comes back on stderr; the analysis
    # half is asked for by file (--viz-facts) and appended, so both halves
    # reach the same parser in one text.
    with tempfile.TemporaryDirectory() as tmp:
        facts = os.path.join(tmp, "viz-facts.txt")
        argv = [
            nmc,
            snapshot,
            "-o",
            "/dev/null",
            "--dump-bbv",
            "--viz",
            "--viz-facts",
            facts,
        ]
        if lower:
            argv.append("--viz-lower")
        proc = subprocess.run(
            argv,
            check=False,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
        )
        if proc.returncode != 0:
            sys.stderr.write(proc.stderr.decode("utf-8", "replace")[-4000:])
            raise SystemExit(f"compiler exited {proc.returncode}")
        text = proc.stderr.decode("utf-8", "replace")
        if os.path.exists(facts):
            with open(facts, encoding="utf-8", errors="replace") as f:
                text += f.read()
        return text


def parse_dump(text):
    scripts = {}
    layouts = {}
    arrclaims = []
    helpers = {}
    # Merge-block param MEANINGS are emitted where the emitter knows them
    # (a diamond's params are the operand stack), keyed by block alone.
    blockmeaning = {}
    # Continuations are emitted DURING the op, before its lowering record
    # exists, so they are buffered and attached once the record lands.
    conts = {}

    def sc(sid):
        if sid not in scripts:
            scripts[sid] = {
                "sid": sid,
                "name": None,
                "nargs": 0,
                "nlocals": 0,
                "bclen": 0,
                "global": False,
                "loops": [],
                "ops": [],
                "defty": {},
                "argty": {},
                "vers": [],
                "dirties": [],
                "onramps": [],
                "thisloc": None,
                "sites": [],
                "licm": [],
                "lower": {},
            }
        return scripts[sid]

    for line in text.splitlines():
        m = RE_BEGIN.match(line)
        if m:
            s = sc(int(m.group(1)))
            # A new Code pass supersedes anything a prior rung emitted.
            s["vers"] = []
            s["dirties"] = []
            s["onramps"] = []
            s["licm"] = []
            continue
        m = RE_VER.match(line)
        if m:
            sc(int(m.group(1)))["vers"].append(
                {
                    "pc": int(m.group(2)),
                    "lpc": int(m.group(3)),
                    "inline": None if m.group(4) == "-" else int(m.group(4)),
                    "site": None if m.group(5) == "-" else int(m.group(5)),
                    "path": None if m.group(6) == "-" else m.group(6),
                    "op": m.group(7),
                    "args": m.group(8),
                    "track": m.group(9),
                    "class": int(m.group(10)),
                    "depth": int(m.group(11)),
                    "facts": m.group(12),
                    "carried": m.group(13),
                }
            )
            continue
        m = RE_DIRTY.match(line)
        if m:
            sc(int(m.group(1)))["dirties"].append(
                {
                    "pc": int(m.group(2)),
                    "lpc": int(m.group(3)),
                    "site": None if m.group(4) == "-" else int(m.group(4)),
                    "path": None if m.group(5) == "-" else m.group(5),
                    "op": m.group(6),
                    "helper": m.group(7),
                    "track": m.group(8),
                }
            )
            continue
        m = RE_LICM.match(line)
        if m:
            sc(int(m.group(1)))["licm"].append(
                {
                    "pc": int(m.group(2)),
                    "lpc": int(m.group(3)),
                    "site": None if m.group(4) == "-" else int(m.group(4)),
                    "path": None if m.group(5) == "-" else m.group(5),
                    "kind": m.group(6),
                }
            )
            continue
        m = RE_ONRAMP.match(line)
        if m:
            sc(int(m.group(2)))["onramps"].append(
                {
                    "what": m.group(1),
                    "hdr": int(m.group(3)),
                    "pc": int(m.group(4)),
                    "site": None if m.group(5) == "-" else int(m.group(5)),
                    "guards": m.group(6),
                }
            )
            continue
        m = RE_SCRIPT.match(line)
        if m:
            s = sc(int(m.group(1)))
            s["name"] = None if m.group(2) == "-" else m.group(2)
            s["nargs"] = int(m.group(3))
            s["nlocals"] = int(m.group(4))
            s["bclen"] = int(m.group(5))
            s["global"] = m.group(6) == "1"
            continue
        m = RE_LOOP.match(line)
        if m:
            iv = (int(m.group(2)), int(m.group(3)))
            s = sc(int(m.group(1)))
            if iv not in [tuple(x) for x in s["loops"]]:
                s["loops"].append(list(iv))
            continue
        m = RE_OP.match(line)
        if m:
            s = sc(int(m.group(1)))
            s["ops"].append([int(m.group(2)), m.group(3), m.group(4)])
            continue
        m = RE_DEF.match(line)
        if m:
            # Root-frame defs only (path "-"): inline-splice defs have
            # synthetic pcs the op listing does not show.
            if m.group(3) == "-":
                d = sc(int(m.group(1)))["defty"].setdefault(m.group(2), [])
                if m.group(4) not in d:
                    d.append(m.group(4))
            continue
        m = RE_ARGTY.match(line)
        if m:
            d = sc(int(m.group(1)))["argty"].setdefault(m.group(2), [])
            if m.group(3) not in d:
                d.append(m.group(3))
            continue
        m = RE_THIS.match(line)
        if m:
            sc(int(m.group(1)))["thisloc"] = int(m.group(2))
            continue
        m = RE_SITE.match(line)
        if m:
            e = {"pc": int(m.group(2)), "kind": m.group(3), "pred": m.group(4)}
            if e not in sc(int(m.group(1)))["sites"]:
                sc(int(m.group(1)))["sites"].append(e)
            continue
        m = RE_HELPER.match(line)
        if m:
            helpers[int(m.group(1))] = m.group(2)
            continue
        m = RE_ARRCLAIM.match(line)
        if m:
            arrclaims.append(
                {
                    "root": int(m.group(1)),
                    "key": int(m.group(2)),
                    "mask": m.group(3),
                    "lo": int(m.group(4)),
                    "hi": int(m.group(5)),
                    "allocs": [a for a in m.group(6).split(" ") if a],
                    "elemsites": int(m.group(7)),
                }
            )
            continue
        m = RE_LOWERP.match(line)
        if m:
            blockmeaning[int(m.group(2))] = {
                "kind": m.group(3),
                "reprs": [r for r in m.group(4).split(",") if r],
            }
            continue
        m = RE_LOWER.match(line)
        if m:
            s_ = sc(int(m.group(1)))
            # A later pass supersedes an earlier one for the same op.
            s_["lower"][int(m.group(2))] = {
                "entry": int(m.group(3)),
                "blocks": [],
                "conts": [],
            }
            continue
        m = RE_LOWERB.match(line)
        if m:
            lw = sc(int(m.group(1)))["lower"].get(int(m.group(2)))
            if lw is not None:
                lw["blocks"].append(
                    {
                        "id": int(m.group(3)),
                        "skip": int(m.group(4)),
                        "params": [t for t in m.group(5).split(",") if t],
                        "insts": int(m.group(6)),
                        "term": m.group(7),
                        "items": [],
                    }
                )
            continue
        m = RE_LOWERI.match(line)
        if m:
            lw = sc(int(m.group(1)))["lower"].get(int(m.group(2)))
            if lw is not None and lw["blocks"]:
                b = int(m.group(3))
                for blk in lw["blocks"]:
                    if blk["id"] == b:
                        blk["items"].append([m.group(4), m.group(5)])
                        break
            continue
        m = RE_LOWERK.match(line)
        if m:
            conts.setdefault((int(m.group(1)), int(m.group(2))), []).append(
                {
                    "blk": int(m.group(3)),
                    "succ": int(m.group(4)),
                    "track": m.group(5),
                }
            )
            continue
        m = RE_LAYOUT.match(line)
        if m:
            layouts[int(m.group(1))] = {
                "id": int(m.group(1)),
                "fields": m.group(2),
            }
            continue
    # Keep only scripts that produced a final op listing (compiled scripts).
    out = {sid: s for sid, s in scripts.items() if s["ops"]}
    for s in out.values():
        # Ladder retries reprint the listing; keep the last full listing.
        ops = s["ops"]
        starts = [i for i, o in enumerate(ops) if o[0] == 0]
        if starts:
            s["ops"] = ops[starts[-1] :]
    for s_ in out.values():
        for lpc, lw in s_["lower"].items():
            seen_c = []
            for c in conts.get((s_["sid"], lpc), []):
                if c not in seen_c:
                    seen_c.append(c)
            lw["conts"] = seen_c
            for blk in lw["blocks"]:
                mn = blockmeaning.get(blk["id"])
                if mn:
                    blk["meaning"] = mn
    return (
        out,
        sorted(layouts.values(), key=lambda e: e["id"]),
        arrclaims,
        helpers,
    )


def anchor_scripts(scripts, source_text):
    """Best-effort map: script -> source line of its function definition."""
    lines = source_text.split("\n")
    for s in scripts.values():
        s["srcline"] = None
        s["srcmatches"] = 0
        name = s["name"]
        if not name or s["global"]:
            continue
        pats = []
        if "." in name:
            parent, base = name.rsplit(".", 1)
            pats.append(
                re.compile(
                    re.escape(parent)
                    + r"\s*\.\s*(?:prototype\s*\.\s*)?"
                    + re.escape(base)
                    + r"\s*[:=]\s*function\s*(?:\w+\s*)?\(([^)]*)\)"
                )
            )
        else:
            base = name
        pats.append(
            re.compile(
                r"(?:\bfunction\s+" + re.escape(base) + r"\s*\(([^)]*)\)"
                r"|\b"
                + re.escape(base)
                + r"\s*[:=]\s*function\s*(?:\w+\s*)?\(([^)]*)\))"
            )
        )
        cands = []
        for pat in pats:
            for i, ln in enumerate(lines):
                m = pat.search(ln)
                if m:
                    params = next((g for g in m.groups() if g is not None), "")
                    n = 0 if not params.strip() else len(params.split(","))
                    cands.append((i + 1, n))
            if cands:
                break
        exact = [c for c in cands if c[1] == s["nargs"]]
        use = exact if exact else cands
        s["srcmatches"] = len(use)
        if use:
            s["srcline"] = use[0][0]


def build_html(scripts, layouts, arrclaims, helpers, source_text, source_name, title):
    data = {
        "title": title,
        "sourceName": source_name,
        "layouts": layouts,
        "arrclaims": arrclaims,
        "helpers": helpers,
        "scripts": sorted(
            scripts.values(),
            key=lambda s: (0 if s["srcline"] else 1, -len(s["vers"])),
        ),
    }
    payload = json.dumps(data, separators=(",", ":")).replace("</", "<\\/")
    src_json = json.dumps(source_text, ensure_ascii=False).replace("</", "<\\/")
    page_title = html.escape(title)
    css = """
:root {
  --bg: #fbfaf6; --panel: #ffffff; --ink: #1c1c1a; --ink2: #5b5a54;
  --muted: #8a897f; --hair: #e1e0d9; --axis: #c3c2b7;
  --opt: #0ca30c; --side: #fab219; --dirty: #d03b3b;
  --opt-bg: #e6f6e6; --side-bg: #fdf2d8; --dirty-bg: #fbe7e7;
  --sel: #eef0fa; --hdr-bg: #f4f3ec;
}
* { box-sizing: border-box; }
body { margin: 0; background: var(--bg); color: var(--ink);
  font: 13px/1.45 system-ui, sans-serif; }
#top { position: sticky; top: 0; z-index: 5; background: var(--panel);
  border-bottom: 1px solid var(--hair); padding: 8px 14px; }
#top h1 { font-size: 15px; margin: 0 0 4px; }
#legend { color: var(--ink2); font-size: 12px; display: flex;
  flex-wrap: wrap; gap: 14px; align-items: center; }
.lg { display: inline-flex; align-items: center; gap: 5px; }
#wrap { display: grid; grid-template-columns: 250px minmax(0,1fr) 40%;
  height: calc(100vh - 58px); }
#sidebar { overflow-y: auto; border-right: 1px solid var(--hair);
  background: var(--panel); }
#main { overflow: auto; padding: 0 8px 40px; }
#srcpane { overflow-y: auto; border-left: 1px solid var(--hair);
  background: var(--panel); }
.script-item { padding: 7px 10px; border-bottom: 1px solid var(--hair);
  cursor: pointer; }
.script-item:hover { background: var(--sel); }
.script-item.sel { background: var(--sel); box-shadow: inset 3px 0 0 var(--ink); }
.si-name { font-family: ui-monospace, monospace; font-size: 12px; }
.si-meta { color: var(--muted); font-size: 11px; display: flex;
  justify-content: space-between; }
.si-bar { display: flex; height: 4px; border-radius: 2px; overflow: hidden;
  margin-top: 4px; background: var(--hair); }
.si-bar span { height: 100%; }
table.bc { border-collapse: collapse; width: 100%;
  font-family: ui-monospace, monospace; font-size: 12px; }
table.bc th { text-align: left; font: 600 11px system-ui, sans-serif;
  color: var(--ink2); padding: 6px 8px 4px; position: sticky; top: 0;
  background: var(--bg); border-bottom: 1px solid var(--axis); z-index: 2; }
table.bc td { padding: 2px 8px; border-bottom: 1px solid var(--hair);
  vertical-align: top; }
tr.looph td { border-top: 2px solid var(--axis); background: var(--hdr-bg); }
td.pc { color: var(--muted); text-align: right; width: 1%; }
td.gut { width: 1%; padding: 2px 2px; white-space: nowrap; }
.gutbar { display: inline-block; width: 3px; height: 16px; margin-right: 2px;
  border-radius: 1px; background: var(--axis); vertical-align: middle; }
.lhdr-mark { color: var(--ink2); font-size: 10px; font-weight: 700; }
td.opn { white-space: nowrap; }
td.chips { max-width: 260px; }
.chip { display: inline-flex; align-items: center; justify-content: center;
  min-width: 16px; height: 16px; padding: 0 3px; margin: 1px;
  border-radius: 4px; font: 700 10px ui-monospace, monospace;
  cursor: default; border: 1px solid transparent; }
.chip.O { background: var(--opt-bg); color: #006300; border-color: var(--opt); }
.chip.S { background: var(--side-bg); color: #7a5200; border-color: var(--side); }
.chip.D { background: var(--dirty-bg); color: #8f1f1f; border-color: var(--dirty); }
.chip.inl { border-style: dashed; opacity: .85; }
.more { color: var(--muted); font-size: 10px; }
td.facts { color: var(--ink2); max-width: 260px; overflow: hidden;
  text-overflow: ellipsis; white-space: nowrap; }
td.ev { max-width: 240px; min-width: 130px; }
.oparg { color: var(--muted); margin-left: 7px; }
.pred { color: #4a5a9a; background: #eef1fa; border: 1px dotted #9aa7d4;
  border-radius: 4px; padding: 0 4px; margin-left: 7px;
  font-size: 11px; cursor: default; }
.clslink { color: #4a5a9a; text-decoration: underline dotted; cursor: pointer; }
#laypanel { padding: 8px 12px; font-family: ui-monospace, monospace;
  font-size: 12px; }
.lay-entry { padding: 6px 10px; border-bottom: 1px solid var(--hair);
  background: var(--panel); }
.lay-entry:last-child { border-bottom: none; }
.lay-entry.hl { background: var(--side-bg); }
.lay-id { display: inline-block; background: #eef1fa; color: #4a5a9a;
  border: 1px solid #9aa7d4; border-radius: 4px; padding: 0 5px;
  font-weight: 700; margin-right: 8px; }
.lay-fields { margin: 4px 0 0 26px; color: var(--ink2); }
.lay-fields .frange { color: #7a4a12; background: #fdf1e0; border-radius: 3px;
  padding: 0 4px; margin-left: 6px; font-size: 11px; }
.arr-entry { border: 1px solid var(--line); border-radius: 6px; padding: 8px 10px;
  margin: 6px 0; background: #fff; }
.arr-entry .arr-key { font-weight: 600; margin-right: 8px; }
.arr-entry .arr-r { color: #7a4a12; background: #fdf1e0; border-radius: 3px;
  padding: 0 5px; }
.arr-entry .arr-meta { color: var(--muted); font-size: 11px; margin-left: 8px; }
/* --- lowering pane --- */
#lowpane { position: fixed; top: 0; right: 0; width: 46%; max-width: 780px;
  height: 100%; overflow: auto; background: #fbfbfd; border-left: 2px solid var(--line);
  box-shadow: -3px 0 14px rgba(0,0,0,.10); padding: 12px 14px 40px; display: none;
  z-index: 40; }
#lowpane.open { display: block; }
#lowpane h3 { margin: 0 0 2px; font-size: 14px; }
#lowpane .lp-sub { color: var(--muted); font-size: 11px; margin-bottom: 10px; }
#lowpane .lp-close { position: absolute; top: 8px; right: 12px; cursor: pointer;
  color: var(--muted); font-size: 16px; }
.lp-blk { border: 1px solid var(--line); border-radius: 6px; margin: 8px 0;
  background: #fff; }
.lp-blk.entry { border-color: #9aa8d8; }
.lp-bh { padding: 5px 8px; background: #f2f4fa; border-bottom: 1px solid var(--line);
  font-size: 12px; display: flex; gap: 8px; align-items: baseline; flex-wrap: wrap; }
.lp-bid { font-weight: 600; }
.lp-params { color: #4a5a9a; }
.lp-term { margin-left: auto; color: var(--muted); font-size: 11px; }
.lp-items { padding: 4px 8px 6px; font-size: 11px; }
.lp-i { display: flex; gap: 6px; padding: 1px 0; }
.lp-k { flex: 0 0 62px; text-align: right; border-radius: 3px; padding: 0 4px;
  font-size: 10px; align-self: center; }
.lp-k.call { background: #fde8e8; color: #8a2b2b; }
.lp-k.load { background: #e8f1fd; color: #24518c; }
.lp-k.store { background: #e6f6ea; color: #1f6b34; }
.lp-k.box, .lp-k.unbox, .lp-k.reinterp, .lp-k.cvt { background: #f3ecfb; color: #5a3a8a; }
.lp-k.alu { background: #f0f0f2; color: #666; }
.lp-guard { background: #fff6db; border-left: 3px solid #d8a52a; padding: 3px 8px;
  font-size: 11px; }
.lp-cont { background: #eef7ff; border-left: 3px solid #4a86c8; padding: 3px 8px;
  font-size: 11px; margin-top: 4px; }
.lp-mean { color: #1f6b34; font-size: 11px; padding: 2px 8px; }
tr.op-clickable td.opcell { cursor: pointer; }
tr.op-clickable td.opcell:hover { background: #eef1fa; }
tr.lowsel td { background: #fff6db !important; }
.lay-fields .fslot { color: var(--muted); }
tr.grp-hdr td { background: #f0eee6; color: var(--ink2); cursor: pointer;
  font: 11px ui-monospace, monospace; padding: 3px 8px;
  border-bottom: 1px solid var(--hair); }
tr.grp-hdr:hover td { background: var(--sel); }
.caret { display: inline-block; width: 13px; }
.grp-name { font-weight: 600; }
.grp-meta { color: var(--muted); }
tr.inl-row td { background: #fdfcf8; }
tr.inl-row td.pc { font-style: italic; }
.badge { display: inline-block; margin: 1px 2px 1px 0; padding: 0 5px;
  border-radius: 4px; font: 11px ui-monospace, monospace; cursor: default; }
.badge.dirty { background: var(--dirty-bg); color: #8f1f1f;
  border: 1px solid var(--dirty); }
.badge.licm { background: var(--opt-bg); color: #0a5c0a;
  border: 1px solid var(--opt); }
.badge.onr { background: var(--opt-bg); color: #006300;
  border: 1px solid var(--opt); }
.badge.dec { background: var(--hdr-bg); color: var(--ink2);
  border: 1px solid var(--axis); }
.defty { display: inline-block; margin-left: 6px; padding: 0 4px;
  border-radius: 3px; font: 11px ui-monospace, monospace; cursor: default;
  color: #275d8b; background: #eef4fa; border: 1px solid #b9d2e8; }
.loopinfo { font: 11px system-ui, sans-serif; color: var(--ink2);
  display: inline-flex; gap: 6px; align-items: center; margin-left: 8px; }
.dshare { display: inline-block; width: 60px; height: 6px; background:
  var(--hair); border-radius: 3px; overflow: hidden; vertical-align: middle; }
.dshare span { display: block; height: 100%; background: var(--dirty); }
#src { font: 12px/1.5 ui-monospace, monospace; margin: 0; padding: 8px 0;
  counter-reset: ln; }
.srcln { display: flex; }
.srcln:target, .srcln.hl { background: var(--side-bg); }
.srcln .no { width: 46px; flex: none; text-align: right; padding-right: 10px;
  color: var(--muted); user-select: none; }
.srcln .tx { white-space: pre; padding-right: 12px; }
#scripthdr { position: sticky; top: 0; background: var(--bg); padding: 8px;
  font: 600 13px system-ui, sans-serif; z-index: 3;
  border-bottom: 1px solid var(--hair); }
#scripthdr .sub { font-weight: 400; color: var(--ink2); font-size: 12px; }
#tip { position: fixed; display: none; max-width: 480px; z-index: 10;
  background: var(--ink); color: #f6f5ef; padding: 6px 9px; border-radius: 6px;
  font: 11px/1.5 ui-monospace, monospace; white-space: pre-wrap;
  pointer-events: none; box-shadow: 0 2px 10px rgba(0,0,0,.25); }
"""
    js = r"""
const DATA = window.__VIZ_DATA__;
const SRC = window.__VIZ_SRC__;
const BYID = new Map(DATA.scripts.map((s) => [s.sid, s]));
let curSid = null;
let uidCounter = 0;
let collapsed = new Set();

function el(tag, cls, text) {
  const e = document.createElement(tag);
  if (cls) e.className = cls;
  if (text !== undefined) e.textContent = text;
  return e;
}
const TRACKS = { Opt: "O", Side: "S", Dirty: "D" };

function tip(target, text) {
  target.dataset.tip = text;
}
document.addEventListener("mouseover", (ev) => {
  const t = ev.target.closest("[data-tip]");
  const tipEl = document.getElementById("tip");
  if (!t) { tipEl.style.display = "none"; return; }
  tipEl.textContent = t.dataset.tip;
  tipEl.style.display = "block";
  const r = t.getBoundingClientRect();
  let x = r.left, y = r.bottom + 6;
  tipEl.style.left = "0px"; tipEl.style.top = "0px";
  const tr = tipEl.getBoundingClientRect();
  if (x + tr.width > innerWidth - 12) x = innerWidth - tr.width - 12;
  if (y + tr.height > innerHeight - 8) y = r.top - tr.height - 6;
  tipEl.style.left = x + "px"; tipEl.style.top = y + "px";
});

function relabel(str, thisloc) {
  if (thisloc === null || thisloc === undefined || !str) return str;
  return str.replace(new RegExp("(^| )l" + thisloc + "=", "g"), "$1this*=");
}
function opArgs(op, args, thisloc) {
  if (
    (op === "GetLocal" || op === "SetLocal") &&
    thisloc !== null &&
    thisloc !== undefined &&
    args === String(thisloc)
  )
    return "this*";
  return args;
}

function verTip(v, thisloc) {
  const a = v.args ? " " + opArgs(v.op, v.args, thisloc) : "";
  let t = `pc ${v.pc}  op ${v.op}${a}\ntrack ${v.track}  tok-class ${v.class}  stack-depth ${v.depth}`;
  if (v.inline !== null)
    t += `\ninlined copy of sid#${v.inline} (lpc ${v.lpc}) at splice path ${v.path || v.site}`;
  t += `\nfacts: ${relabel(v.facts, thisloc) || "(none)"}`;
  t += `\ncarried: ${relabel(v.carried, thisloc) || "(none)"}`;
  return t;
}

function siteIdx(sc) {
  if (!sc._siteIdx) {
    sc._siteIdx = new Map();
    for (const st of sc.sites || []) {
      if (!sc._siteIdx.has(st.pc)) sc._siteIdx.set(st.pc, []);
      sc._siteIdx.get(st.pc).push(st);
    }
  }
  return sc._siteIdx;
}

const KTIP = {
  call: "A helper call. May GC unless the effect map says otherwise -- a " +
        "GC point is what dirties a lineage and forces the offramp.",
  load: "A memory read, with the HEAP KIND it was tagged with. The kind is " +
        "the alias story: it decides what a later write invalidates.",
  store: "A memory write, with its heap kind.",
  box: "Boxing: a raw i32 widened into a NaN-boxed Value.",
  unbox: "Unboxing: the payload pulled out of a boxed Value.",
  reinterp: "A bit reinterpretation between the f64 and i64 views of a Value.",
  cvt: "A numeric conversion (int <-> float).",
  alu: "Plain arithmetic and address math, counted rather than listed.",
};

// The immediates that make a guard legible. A compare against one of
// these is not an anonymous test -- it is the tag check, the stamp fold
// or the class-idx guard that the whole speculation rests on.
const GUARD_IMM = {
  "-127": "TAG_INT32",
  "-126": "TAG_BOOLEAN",
  "-125": "TAG_UNDEFINED",
  "-124": "TAG_NULL",
  "-123": "TAG_MAGIC",
  "-122": "TAG_STRING",
  "-119": "TAG_BIGINT",
  "-116": "TAG_OBJECT",
  "-128": "TAG_CLEAR",
  "65536": "TYPES bit",
  "131072": "SLOTS bit",
  "196608": "TYPES|SLOTS",
  "1073741824": "RANGES bit",
  "1073807360": "TYPES|RANGES",
  "1073938432": "TYPES|SLOTS|RANGES",
  "32768": "flags-half RANGES",
  "1": "TYPES (flags half)",
  "2": "SLOTS (flags half)",
};

function guardLabel(term) {
  // term looks like "condbr I32Eq#-127 b5 b6"
  const m = /^condbr (\S+) b(\d+) b(\d+)$/.exec(term || "");
  if (!m) return null;
  const c = m[1];
  const im = /^(.*)#(-?\d+)$/.exec(c);
  let label = c;
  if (im) {
    const known = GUARD_IMM[im[2]];
    label = im[1] + " " + (known ? known : im[2]);
    if (!known && Math.abs(+im[2]) > 65535)
      label = im[1] + " 0x" + (im[2] >>> 0).toString(16);
  }
  return { label, t: +m[2], f: +m[3] };
}

function renderLowering(s, lpc, opname) {
  const pane = document.getElementById("lowpane");
  const lw = s.lower && s.lower[lpc];
  pane.innerHTML = "";
  const x = el("div", "lp-close", "\u00d7");
  x.onclick = () => pane.classList.remove("open");
  pane.appendChild(x);
  pane.appendChild(el("h3", null, `${opname} @ pc ${lpc}`));
  if (!lw) {
    pane.appendChild(el("div", "lp-sub",
      "No lowering recorded for this op \u2014 this page was built with " +
      "--no-lower, or the op emitted no code on the Code pass."));
    pane.classList.add("open");
    return;
  }
  pane.appendChild(el("div", "lp-sub",
    `${lw.blocks.length} block(s) — the mini-CFG this one bytecode op ` +
    `expands to. Entry b${lw.entry} is shared with the ops before it, so ` +
    `only this op's own contribution is listed there.`));
  const contsBy = new Map();
  for (const c of lw.conts || []) {
    if (!contsBy.has(c.blk)) contsBy.set(c.blk, []);
    contsBy.get(c.blk).push(c);
  }
  for (const b of lw.blocks) {
    const card = el("div", "lp-blk" + (b.id === lw.entry ? " entry" : ""));
    const h = el("div", "lp-bh");
    h.appendChild(el("span", "lp-bid", "b" + b.id));
    if (b.params.length)
      h.appendChild(el("span", "lp-params", `(${b.params.join(", ")})`));
    if (b.id === lw.entry) h.appendChild(el("span", "lp-term", "entry"));
    card.appendChild(h);
    if (b.meaning && b.meaning.reprs.length) {
      const mn = el("div", "lp-mean",
        `params hold the operand stack: ${b.meaning.reprs.join(", ")}`);
      tip(mn, "A diamond's merge params ARE the operand stack, in order, in " +
        "the reprs the arms agreed on. This is the emitter's knowledge -- " +
        "the IR itself only records wasm types.");
      card.appendChild(mn);
    }
    const items = el("div", "lp-items");
    for (const [k, d] of b.items) {
      const r = el("div", "lp-i");
      const kk = el("span", "lp-k " + k, k);
      tip(kk, KTIP[k] || k);
      r.appendChild(kk);
      let txt = d;
      const fm = /func(\d+)/.exec(d);
      if (k === "call" && fm && DATA.helpers[fm[1]])
        txt = DATA.helpers[fm[1]];
      else if (k === "alu") txt = d + " ops";
      r.appendChild(el("span", null, txt));
      items.appendChild(r);
    }
    if (b.items.length) card.appendChild(items);
    const g = guardLabel(b.term);
    if (g) {
      const gd = el("div", "lp-guard",
        `guard ${g.label} \u2192 taken b${g.t}, else b${g.f}`);
      tip(gd, "A fork. The taken arm continues refined; the other arm is " +
        "either a side arm (a continuation at the next pc under a weaker " +
        "ctx) or the slow path.");
      card.appendChild(gd);
    } else if (b.term && b.term !== "-") {
      card.appendChild(el("div", "lp-guard", b.term));
    }
    for (const c of contsBy.get(b.id) || []) {
      const cd = el("div", "lp-cont",
        `continuation \u2192 pc ${c.succ} (track ${c.track})`);
      tip(cd, "A SIDE ARM: this block rejoins the lineage at that pc with a " +
        "weaker fact context. Every non-fall-through arm comes through here, " +
        "which is what steps the track down.");
      card.appendChild(cd);
    }
    pane.appendChild(card);
  }
  pane.classList.add("open");
}

function renderArrays() {
  const main = document.getElementById("main");
  main.innerHTML = "";
  for (const it of document.querySelectorAll(".script-item"))
    it.classList.toggle("sel", it.id === "si-arrays");
  const hdr = el("div");
  hdr.id = "scripthdr";
  hdr.appendChild(document.createTextNode("Array range claims"));
  hdr.appendChild(el("div", "sub",
    `${DATA.arrclaims.length} claiming population(s). An array carries the ` +
    `same stamp word an object does; the claim is keyed on the class-region ` +
    `union-find ROOT, so sibling allocation sites that flowed together share ` +
    `one R. The claim covers a NON-HOLE element's value -- the dense read ` +
    `hole-checks before any value reaches a consumer.`));
  main.appendChild(hdr);
  if (!DATA.arrclaims.length) {
    main.appendChild(el("div", "sub",
      "Nothing claimed. Either no array population had a bounded int32 " +
      "element range, or the cost gate declined: a bundle whose unresolved " +
      "element WRITES outnumber its foldable element READS claims nothing, " +
      "because an element store has no name to be shown irrelevant by."));
    return;
  }
  for (const a of DATA.arrclaims) {
    const e = el("div", "arr-entry");
    e.appendChild(el("span", "arr-key", `stamp key ${a.key}`));
    e.appendChild(el("span", "arr-r", `R ${a.lo} .. ${a.hi}`));
    e.appendChild(el("span", "arr-meta",
      `mask ${a.mask} — root ${a.root} — ${a.elemsites} element site(s)`));
    const al = el("div", "lay-fields");
    al.appendChild(document.createTextNode(
      a.allocs.length
        ? "stamped at allocation sites: " + a.allocs.join(", ")
        : "no compiled allocation site (snapshot-created arrays stay unstamped)"));
    e.appendChild(al);
    main.appendChild(e);
  }
}

function renderLayouts(focusId) {
  curSid = null;
  for (const it of document.querySelectorAll(".script-item"))
    it.classList.toggle("sel", it.id === "si-layouts");
  const main = document.getElementById("main");
  main.innerHTML = "";
  const hdr = el("div", null);
  hdr.id = "scripthdr";
  hdr.appendChild(document.createTextNode("Heap layouts (likelier predictions)"));
  hdr.appendChild(el("div", "sub",
    `${DATA.layouts.length} layouts. ` +
    "cls ids are the stamped class-idx values the guards compare against. " +
    "Per field: its fixed slot, the numeric mask codegen claims, and the " +
    "range claim where it has one."));
  main.appendChild(hdr);
  const panel = el("div");
  panel.id = "laypanel";
  for (const l of DATA.layouts) {
    const e = el("div", "lay-entry");
    e.id = "lay-" + l.id;
    e.appendChild(el("span", "lay-id", "cls " + l.id));
    const f = el("div", "lay-fields");
    if (l.fields) {
      for (const part of l.fields.split(" ")) {
        const m = /^(.*)=slot(\d+):([^:]*):([^:]*)$/.exec(part);
        const row = el("div");
        if (m) {
          row.appendChild(document.createTextNode(m[1] + " "));
          row.appendChild(el("span", "fslot",
            `slot ${m[2]}` + (m[3] !== "0" ? ` mask ${m[3]}` : " (no mask claim)")));
          if (m[4] && m[4] !== "-") {
            const rg = el("span", "frange", `R ${m[4].replace("..", " .. ")}`);
            tip(rg, "RANGE claim: the field's predicted value interval. Rides " +
              "its OWN stamp bit (RANGES), not TYPES -- TYPES only asserts " +
              "numberness engine-wide, and a range is consumed checklessly. " +
              "Maintained by range-conformant compiled stores; any unchecked " +
              "write drops it.");
            row.appendChild(rg);
          }
        } else {
          row.textContent = part;
        }
        f.appendChild(row);
      }
    } else {
      f.textContent = "(no predicted fields)";
    }
    e.appendChild(f);
    panel.appendChild(e);
  }
  main.appendChild(panel);
  if (focusId !== undefined) {
    const e = document.getElementById("lay-" + focusId);
    if (e) {
      e.classList.add("hl");
      e.scrollIntoView({ block: "center" });
    }
  } else {
    main.scrollTop = 0;
  }
}

function showLayout(id) {
  renderLayouts(id);
}

function buildSidebar() {
  const sb = document.getElementById("sidebar");
  if (DATA.layouts.length) {
    const it = el("div", "script-item");
    it.id = "si-layouts";
    it.appendChild(el("div", "si-name", "Heap layouts"));
    const meta = el("div", "si-meta");
    meta.appendChild(el("span", null, `${DATA.layouts.length} layouts`));
    it.appendChild(meta);
    it.onclick = () => renderLayouts();
    sb.appendChild(it);
  }
  if (DATA.arrclaims && DATA.arrclaims.length) {
    const it = el("div", "script-item");
    it.id = "si-arrays";
    it.appendChild(el("div", "si-name", "Array range claims"));
    const meta = el("div", "si-meta");
    meta.appendChild(el("span", null, `${DATA.arrclaims.length} populations`));
    it.appendChild(meta);
    it.onclick = () => renderArrays();
    sb.appendChild(it);
  }
  for (const s of DATA.scripts) {
    const it = el("div", "script-item");
    it.id = "si-" + s.sid;
    const nm = s.name || (s.global ? "<global>" : "<anon>");
    it.appendChild(el("div", "si-name", `#${s.sid} ${nm}`));
    const meta = el("div", "si-meta");
    meta.appendChild(el("span", null, `${s.vers.length} vers`));
    meta.appendChild(el("span", null, `${s.bclen}b`));
    it.appendChild(meta);
    const counts = { Opt: 0, Side: 0, Dirty: 0 };
    for (const v of s.vers) counts[v.track]++;
    const bar = el("div", "si-bar");
    const tot = Math.max(1, s.vers.length);
    for (const [tr, col] of [["Opt", "var(--opt)"], ["Side", "var(--side)"], ["Dirty", "var(--dirty)"]]) {
      const seg = el("span");
      seg.style.width = (100 * counts[tr] / tot) + "%";
      seg.style.background = col;
      bar.appendChild(seg);
    }
    tip(bar, `versions: ${counts.Opt} Opt / ${counts.Side} Side / ${counts.Dirty} Dirty`);
    it.appendChild(bar);
    it.onclick = () => select(s.sid);
    sb.appendChild(it);
  }
}

function loopDepth(s, pc) {
  let d = 0;
  for (const [h, e] of s.loops) if (pc >= h && pc < e) d++;
  return d;
}

function select(sid) {
  curSid = sid;
  for (const it of document.querySelectorAll(".script-item"))
    it.classList.toggle("sel", it.id === "si-" + sid);
  const s = DATA.scripts.find((x) => x.sid === sid);
  renderScript(s);
  anchorSource(s);
}

function chipCell(td, vers, fallback, thisloc) {
  const order = { Opt: 0, Side: 1, Dirty: 2 };
  const direct = vers
    .slice()
    .sort((a, b) => order[a.track] - order[b.track] || a.class - b.class);
  const fb = (fallback || [])
    .slice()
    .sort((a, b) => order[a.track] - order[b.track]);
  const all = direct
    .map((v) => [v, false])
    .concat(fb.map((v) => [v, true]));
  const MAX = 14;
  all.slice(0, MAX).forEach(([v, isFb]) => {
    const c = el(
      "span",
      `chip ${TRACKS[v.track]}` + (isFb ? " inl" : ""),
      TRACKS[v.track] + (v.class ? "·" + v.class : "")
    );
    tip(c, verTip(v, isFb ? (BYID.get(v.inline) || {}).thisloc : thisloc));
    td.appendChild(c);
  });
  if (all.length > MAX)
    td.appendChild(el("span", "more", `+${all.length - MAX}`));
}

function factsCell(td, vers, thisloc) {
  if (!vers.length) return;
  const order = { Opt: 0, Side: 1, Dirty: 2 };
  const best = vers
    .slice()
    .sort((a, b) => order[a.track] - order[b.track])[0];
  let txt = relabel(best.facts, thisloc) || "";
  const car = relabel(best.carried, thisloc);
  if (car) txt += (txt ? "  " : "") + "carried{" + car + "}";
  linkify(td, txt);
  if (txt)
    tip(
      td,
      `${best.track} version facts:\n${relabel(best.facts, thisloc) || "(none)"}\ncarried: ${car || "(none)"}`
    );
}

function dirtyBadges(td, dirties) {
  for (const dv of dirties) {
    const b = el("span", "badge dirty", `dirties: ${dv.helper}`);
    tip(
      b,
      `offramp: may-GC helper call steps the ${dv.track} lineage down to Dirty\nop ${dv.op}  helper ${dv.helper}` +
        (dv.path !== null ? `\ninside inline splice path ${dv.path}` : "")
    );
    td.appendChild(b);
  }
}

function licmBadges(td, licms) {
  for (const lv of licms || []) {
    const b = el("span", "badge licm",
      lv.kind === "s4" ? "licm: s4-hoisted" : "licm: hoisted");
    tip(
      b,
      lv.kind === "s4"
        ? "step-4 hoist: this load now reads a tracer-covered frame hoist slot;\nthe chain is computed in the loop preheader and re-derived after every\nnon-quiet may-GC point in the loop"
        : "P5 LICM: this loop-invariant load was hoisted to the loop preheader"
    );
    td.appendChild(b);
  }
}

function opCell(td, opname, args, thisloc) {
  td.appendChild(document.createTextNode(opname));
  const a = opArgs(opname, args, thisloc);
  if (a) td.appendChild(el("span", "oparg", a));
}

function linkify(span, text) {
  const re = /cls\[?(\d+)(?:-\d+)?\]?/g;
  let last = 0, m;
  while ((m = re.exec(text)) !== null) {
    if (m.index > last)
      span.appendChild(document.createTextNode(text.slice(last, m.index)));
    const a = el("span", "clslink", m[0]);
    const id = parseInt(m[1], 10);
    a.onclick = (ev) => { ev.stopPropagation(); showLayout(id); };
    span.appendChild(a);
    last = m.index + m[0].length;
  }
  if (last < text.length)
    span.appendChild(document.createTextNode(text.slice(last)));
}

function decodeLit(hex) {
  try {
    const v = BigInt(hex);
    const tag = v >> 32n;
    const lo = Number(v & 0xffffffffn);
    if (tag === 0xffffff81n) return String(lo | 0);
    if (tag === 0xffffff83n) return "undefined";
    if (tag === 0xffffff82n) return "null";
    if ((v >> 48n) < 0xffffn) {
      const b = new DataView(new ArrayBuffer(8));
      b.setBigUint64(0, v);
      return String(b.getFloat64(0));
    }
  } catch (e) {}
  return hex;
}

const PRED_TIP = {
  prop: "SITE PREDICTION (likelier), not proven: the receiver is expected in this class range (guarded), the field at this fixed slot with this value mask. A wrong prediction misses to the IC.",
  val: "SITE PREDICTION (likelier): this read's value is expected numeric with this mask (value-tag-guarded).",
  call: "SITE PREDICTION (likelier): predicted callee script sid(s); guarded direct dispatch / splice.",
  gname: "Global-name site: fused-lit = reads fold to the predicted literal behind a fuse; slot-bid = resolved global binding slot.",
  this: "SITE PREDICTION (likelier): this frame's `this` is expected in this class range (validated shape guard).",
};

function predSpans(td, sites) {
  for (const st of sites) {
    let text = st.pred;
    const fm = /^fused-lit (0x[0-9a-f]+)$/.exec(text);
    if (fm) text = "fused-lit " + decodeLit(fm[1]);
    const span = el("span", "pred");
    linkify(span, st.kind + ": " + text);
    tip(span, (PRED_TIP[st.kind] || "site prediction") + "\npred " + text);
    td.appendChild(span);
  }
}

function renderScript(s) {
  const main = document.getElementById("main");
  main.innerHTML = "";
  collapsed = new Set();
  uidCounter = 0;
  const nm = s.name || (s.global ? "<global>" : "<anon>");
  const hdr = el("div", null);
  hdr.id = "scripthdr";
  hdr.appendChild(document.createTextNode(`sid#${s.sid} ${nm}`));
  const sub = el("div", "sub",
    `${s.nargs} args, ${s.nlocals} locals, ${s.bclen} bytecode bytes, ` +
    `${s.vers.length} versions, ${s.loops.length} loops` +
    (s.thisloc !== null ? ` — this* = local ${s.thisloc}` : "") +
    (s.srcline ? ` — source line ${s.srcline}` +
      (s.srcmatches > 1 ? ` (1 of ${s.srcmatches} name matches)` : "") : ""));
  hdr.appendChild(sub);
  if (s.argty && Object.keys(s.argty).length) {
    const al = el("div", "sub");
    al.appendChild(document.createTextNode("arg types (Opt entry): "));
    const keys = Object.keys(s.argty).map(Number).sort((a, b) => a - b);
    for (const i of keys) {
      const label = i === 0 ? "this" : `arg${i - 1}`;
      const b = el("span", "defty", `${label}=${s.argty[String(i)].join(" / ")}`);
      tip(b, "arg type at the LIKELY level (likelier This/Arg cells joined over live contexts)");
      al.appendChild(b);
    }
    hdr.appendChild(al);
  }
  main.appendChild(hdr);

  const rows = new Map();
  const row = (pc) => {
    if (!rows.has(pc))
      rows.set(pc, { vers: [], fallback: [], dirty: [], onr: [], licm: [] });
    return rows.get(pc);
  };
  const pcSet = new Set(s.ops.map((o) => o[0]));

  const groups = new Map();
  const byPath = new Map();
  const group = (path, callee) => {
    const k = path + "#" + callee;
    if (!groups.has(k)) {
      groups.set(k, { path, callee, rows: new Map(), nvers: 0, ndirty: 0 });
      if (!byPath.has(path)) byPath.set(path, []);
      byPath.get(path).push(k);
    }
    return groups.get(k);
  };
  const grow = (g, lpc) => {
    if (!g.rows.has(lpc)) g.rows.set(lpc, { vers: [], dirty: [], licm: [] });
    return g.rows.get(lpc);
  };

  for (const v of s.vers) {
    if (v.inline === null) {
      if (pcSet.has(v.pc)) row(v.pc).vers.push(v);
    } else if (v.path !== null && BYID.has(v.inline)) {
      const g = group(v.path, v.inline);
      grow(g, v.lpc).vers.push(v);
      g.nvers++;
      if (v.track === "Dirty") g.ndirty++;
    } else if (v.site !== null && pcSet.has(v.site)) {
      row(v.site).fallback.push(v);
    }
  }
  const seen = new Set();
  for (const d of s.dirties) {
    const k = JSON.stringify(d);
    if (seen.has(k)) continue;
    seen.add(k);
    if (d.path !== null) {
      const ks = byPath.get(d.path) || [];
      if (ks.length) {
        grow(groups.get(ks[0]), d.lpc).dirty.push(d);
        continue;
      }
    }
    const at = d.path === null && pcSet.has(d.pc) ? d.pc
      : d.site !== null && pcSet.has(d.site) ? d.site : null;
    if (at !== null) row(at).dirty.push(d);
  }
  for (const d of s.licm || []) {
    const k = "licm" + JSON.stringify(d);
    if (seen.has(k)) continue;
    seen.add(k);
    if (d.path !== null) {
      const ks = byPath.get(d.path) || [];
      if (ks.length) {
        grow(groups.get(ks[0]), d.lpc).licm.push(d);
        continue;
      }
    }
    const at = d.path === null && pcSet.has(d.pc) ? d.pc
      : d.site !== null && pcSet.has(d.site) ? d.site : null;
    if (at !== null) row(at).licm.push(d);
  }
  for (const o of s.onramps) {
    const k = JSON.stringify(o);
    if (seen.has(k)) continue;
    seen.add(k);
    if (pcSet.has(o.hdr)) row(o.hdr).onr.push(o);
  }

  const loopStats = s.loops.map(([h, e]) => {
    let tot = 0, dirty = 0;
    for (const [pc, r] of rows) {
      if (pc < h || pc >= e) continue;
      for (const v of r.vers.concat(r.fallback)) {
        tot++;
        if (v.track === "Dirty") dirty++;
      }
    }
    for (const g of groups.values()) {
      const root = parseInt(g.path.split("/")[0], 10);
      if (root < h || root >= e) continue;
      tot += g.nvers;
      dirty += g.ndirty;
    }
    return { h, e, tot, dirty };
  });

  const tbl = el("table", "bc");
  const thead = el("thead");
  const hr = el("tr");
  for (const h of ["pc", "loop", "op", "versions", "facts (best track)", "events"])
    hr.appendChild(el("th", null, h));
  thead.appendChild(hr);
  tbl.appendChild(thead);
  const tb = el("tbody");

  function toggle(gid) {
    if (collapsed.has(gid)) collapsed.delete(gid);
    else collapsed.add(gid);
    for (const tr of tb.querySelectorAll("tr[data-g]")) {
      const gs = tr.dataset.g.split(" ");
      tr.style.display = gs.some((g) => collapsed.has(g)) ? "none" : "";
    }
    for (const tr of tb.querySelectorAll("tr[data-toggle]")) {
      const c = tr.querySelector(".caret");
      if (c)
        c.textContent = collapsed.has(tr.dataset.toggle) ? "▸" : "▾";
    }
  }

  function groupOpRow(callee, entry, r, depth, gids) {
    const [lpc, opname, args] = entry;
    const trow = el("tr", "inl-row");
    trow.dataset.g = gids.join(" ");
    trow.appendChild(el("td", "pc", "." + lpc));
    const gut = el("td", "gut");
    const d = loopDepth(callee, lpc);
    for (let i = 0; i < Math.min(d, 6); i++)
      gut.appendChild(el("span", "gutbar"));
    trow.appendChild(gut);
    const opTd = el("td", "opn");
    opTd.style.paddingLeft = 8 + depth * 16 + "px";
    opCell(opTd, opname, args, callee.thisloc);
    const stx = siteIdx(callee).get(lpc);
    if (stx) predSpans(opTd, stx);
    trow.appendChild(opTd);
    const chips = el("td", "chips");
    if (r) chipCell(chips, r.vers, [], callee.thisloc);
    trow.appendChild(chips);
    const facts = el("td", "facts");
    if (r) factsCell(facts, r.vers, callee.thisloc);
    trow.appendChild(facts);
    const ev = el("td", "ev");
    if (r) {
      dirtyBadges(ev, r.dirty);
      licmBadges(ev, r.licm);
    }
    trow.appendChild(ev);
    tb.appendChild(trow);
  }

  function emitGroups(pathStr, depth, ancestors) {
    for (const k of byPath.get(pathStr) || []) {
      const g = groups.get(k);
      const callee = BYID.get(g.callee);
      if (!callee) continue;
      const gid = "g" + uidCounter++;
      const ghdr = el("tr", "grp-hdr");
      if (ancestors.length) ghdr.dataset.g = ancestors.join(" ");
      ghdr.dataset.toggle = gid;
      const td = el("td");
      td.colSpan = 6;
      td.style.paddingLeft = 8 + depth * 16 + "px";
      td.appendChild(el("span", "caret", "▾"));
      td.appendChild(
        el("span", "grp-name",
          ` inlined: ${callee.name || "<anon>"} (sid#${g.callee})`)
      );
      td.appendChild(el("span", "grp-meta", ` ${g.nvers} vers, ${g.ndirty} dirty`));
      ghdr.appendChild(td);
      tip(ghdr, `spliced callee body at path ${g.path}; click to collapse/expand`);
      ghdr.onclick = () => toggle(gid);
      tb.appendChild(ghdr);
      const gidsHere = ancestors.concat([gid]);
      for (const entry of callee.ops) {
        groupOpRow(callee, entry, g.rows.get(entry[0]) || null, depth, gidsHere);
        emitGroups(pathStr + "/" + entry[0], depth + 1, gidsHere);
      }
    }
  }

  for (const [pc, opname, args] of s.ops) {
    const r = rows.get(pc);
    const isHdr = s.loops.some(([h, _]) => h === pc);
    const trow = el("tr", isHdr ? "looph" : null);
    trow.id = `pc-${s.sid}-${pc}`;
    trow.appendChild(el("td", "pc", String(pc)));

    const gut = el("td", "gut");
    const d = loopDepth(s, pc);
    for (let i = 0; i < Math.min(d, 6); i++) gut.appendChild(el("span", "gutbar"));
    if (isHdr) gut.appendChild(el("span", "lhdr-mark", "▸"));
    trow.appendChild(gut);

    const opTd = el("td", "opn opcell");
    opCell(opTd, opname, args, s.thisloc);
    if (s.lower && s.lower[pc]) {
      trow.classList.add("op-clickable");
      const nb = s.lower[pc].blocks.length;
      const chip = el("span", "defty", `\u229e ${nb}b`);
      tip(chip, "This op lowers to a " + nb + "-block mini-CFG. Click the op " +
                "to see it: guards, boxing, memory kinds, helper calls and " +
                "the continuations each arm rejoins at.");
      opTd.appendChild(chip);
      opTd.onclick = () => {
        for (const t of document.querySelectorAll("tr.lowsel"))
          t.classList.remove("lowsel");
        trow.classList.add("lowsel");
        renderLowering(s, pc, opname);
      };
    }
    const dt = s.defty && s.defty[String(pc)];
    if (dt && dt.length) {
      const b = el("span", "defty", "\u2192 " + dt.join(" / "));
      tip(b, "result type on the Opt (likely) track, as the ctx proves it" +
             (dt.length > 1 ? " (one claim per Opt version reaching the op)" : ""));
      opTd.appendChild(b);
    }
    const stx = siteIdx(s).get(pc);
    if (stx) predSpans(opTd, stx);
    if (isHdr) {
      const st = loopStats.find((l) => l.h === pc);
      if (st && st.tot) {
        const info = el("span", "loopinfo");
        info.appendChild(document.createTextNode(`loop [${st.h},${st.e})`));
        const ds = el("span", "dshare");
        const fill = el("span");
        fill.style.width = (100 * st.dirty / st.tot) + "%";
        ds.appendChild(fill);
        info.appendChild(ds);
        info.appendChild(el("span", null,
          `${Math.round(100 * st.dirty / st.tot)}% dirty`));
        tip(info, `versions at pcs inside this loop (inlined bodies included): ${st.tot}, on the Dirty track: ${st.dirty}`);
        opTd.appendChild(info);
      }
    }
    trow.appendChild(opTd);

    const chips = el("td", "chips");
    if (r) chipCell(chips, r.vers, r.fallback, s.thisloc);
    trow.appendChild(chips);

    const facts = el("td", "facts");
    if (r) factsCell(facts, r.vers, s.thisloc);
    trow.appendChild(facts);

    const ev = el("td", "ev");
    if (r) {
      dirtyBadges(ev, r.dirty);
      licmBadges(ev, r.licm);
      for (const o of r.onr) {
        if (o.what === "emit") {
          const b = el("span", "badge onr", `conform → hdr ${o.hdr}`);
          tip(b, `onramp: non-Opt back edge from pc ${o.pc} re-guards and rejoins the Opt header at pc ${o.hdr}\nguards: ${relabel(o.guards, s.thisloc) || "(none)"}`);
          ev.appendChild(b);
        } else {
          const b = el("span", "badge dec", `declined: ${o.what.replace("decline ", "")}`);
          tip(b, `onramp declined (${o.what.replace("decline ", "")}) for the edge from pc ${o.pc} to header ${o.hdr}`);
          ev.appendChild(b);
        }
      }
    }
    trow.appendChild(ev);
    tb.appendChild(trow);
    emitGroups(String(pc), 1, []);
  }
  tbl.appendChild(tb);
  main.appendChild(tbl);
  main.scrollTop = 0;
}

function buildSource() {
  const pre = document.getElementById("src");
  const lines = SRC.split("\n");
  for (let i = 0; i < lines.length; i++) {
    const d = el("div", "srcln");
    d.id = "L" + (i + 1);
    d.appendChild(el("span", "no", String(i + 1)));
    d.appendChild(el("span", "tx", lines[i] === "" ? " " : lines[i]));
    pre.appendChild(d);
  }
}

function anchorSource(s) {
  for (const e of document.querySelectorAll(".srcln.hl")) e.classList.remove("hl");
  if (!s.srcline) return;
  const ln = document.getElementById("L" + s.srcline);
  if (!ln) return;
  ln.classList.add("hl");
  ln.scrollIntoView({ block: "center" });
}

buildSidebar();
buildSource();
if (location.hash === "#layouts" && DATA.layouts.length) renderLayouts();
else if (DATA.scripts.length) select(DATA.scripts[0].sid);
"""
    legend = (
        '<div id="legend">'
        '<span class="lg"><span class="chip O">O</span>Opt track</span>'
        '<span class="lg"><span class="chip S">S</span>Side track</span>'
        '<span class="lg"><span class="chip D">D</span>Dirty track '
        "(crossed a may-GC call)</span>"
        '<span class="lg"><span class="chip O inl">O</span>inlined copy '
        "(at its call site)</span>"
        '<span class="lg"><span class="badge dirty">dirties</span>offramp: '
        "helper call dirties the lineage</span>"
        '<span class="lg"><span class="badge onr">conform &#8594; hdr'
        "</span>onramp rejoins the Opt loop header</span>"
        '<span class="lg"><span class="badge dec">declined</span>onramp '
        "declined</span>"
        '<span class="lg"><span class="gutbar" style="height:12px"></span>'
        "loop nesting; &#9656; = loop header</span>"
        '<span class="lg">chip label O&#183;n = version\'s loop-token class'
        "</span>"
        '<span class="lg">&#8627; indented rows = inlined callee body '
        "(click its header to fold)</span>"
        '<span class="lg"><code>this*</code> = the bytecode\'s .this local '
        "binding (FunctionThis prologue)</span>"
        '<span class="lg"><span class="pred">prop: cls[5] slot 2</span>'
        "PREDICTED (site evidence, guarded) vs facts column = PROVEN "
        "(lineage); cls links jump to the layout panel</span>"
        '<span class="lg">hover anything for details</span>'
        "</div>"
    )
    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>{page_title}</title>
<style>{css}</style>
</head>
<body>
<div id="top"><h1>{page_title}</h1>{legend}</div>
<div id="wrap">
  <div id="sidebar"></div>
  <div id="main"></div>
  <aside id="lowpane"></aside>
  <div id="srcpane"><pre id="src"></pre></div>
</div>
<div id="tip"></div>
<script>
window.__VIZ_DATA__ = {payload};
window.__VIZ_SRC__ = {src_json};
</script>
<script>{js}</script>
</body>
</html>
"""


def default_compiler():
    """The compiler binary to drive: an explicit override, else whichever
    canonical build output exists."""
    env = os.environ.get("NIGHTMONKEY")
    if env:
        return env
    repo = os.path.abspath(
        os.path.join(os.path.dirname(__file__), "..", "..", "..", "..")
    )
    for rel in (
        "obj-nightmonkey-inprocess/dist/host/bin/nightmonkey",
        "obj-nightmonkey/dist/host/bin/nightmonkey",
        "js/src/night/nightmonkey/target/release/nightmonkey",
    ):
        cand = os.path.join(repo, rel)
        if os.path.exists(cand):
            return cand
    return "nightmonkey"


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("snapshot")
    ap.add_argument("source")
    ap.add_argument("-o", "--out", required=True)
    ap.add_argument(
        "--nmc",
        default=default_compiler(),
        help="the nightmonkey compiler binary (default: the first of "
        "$NIGHTMONKEY, the objdir dist/host/bin builds, or target/release)",
    )
    ap.add_argument(
        "--stderr-cache",
        help="reuse/store the compiler stderr dump at this path",
    )
    ap.add_argument(
        "--no-lower",
        action="store_true",
        help="skip the per-op LOWERING (--viz-lower), which is on by "
        "default: the mini-CFG each op expands to, with guards, boxing, "
        "memory kinds, helper calls and continuations. It is "
        "per-instruction data, so drop it when the page gets unwieldy -- "
        "crypto goes 5M -> 22M and the biggest bundles are far worse.",
    )
    # Accepted and ignored: lowering used to be opt-in via this flag.
    ap.add_argument("--lower", action="store_true", help=argparse.SUPPRESS)
    ap.add_argument("--title")
    args = ap.parse_args()

    if args.stderr_cache and os.path.exists(args.stderr_cache):
        text = open(args.stderr_cache, encoding="utf-8", errors="replace").read()
    else:
        text = run_compiler(args.nmc, args.snapshot, not args.no_lower)
        if args.stderr_cache:
            with open(args.stderr_cache, "w", encoding="utf-8") as f:
                f.write(text)

    scripts, layouts, arrclaims, helpers = parse_dump(text)
    if not scripts:
        raise SystemExit("no viz records in compiler output (is --viz plumbed?)")
    source_text = open(args.source, encoding="utf-8", errors="replace").read()
    anchor_scripts(scripts, source_text)
    title = args.title or (
        "NightMonkey speculation: " + os.path.basename(args.snapshot)
    )
    page = build_html(
        scripts,
        layouts,
        arrclaims,
        helpers,
        source_text,
        os.path.basename(args.source),
        title,
    )
    with open(args.out, "w", encoding="utf-8") as f:
        f.write(page)
    nver = sum(len(s["vers"]) for s in scripts.values())
    nlow = sum(len(s["lower"]) for s in scripts.values())
    print(
        f"wrote {args.out}: {len(scripts)} scripts, {nver} versions, "
        f"{sum(len(s['ops']) for s in scripts.values())} ops"
        + (f", {nlow} lowered ops" if nlow else "")
    )


if __name__ == "__main__":
    main()
