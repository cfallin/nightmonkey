#!/usr/bin/env python3
"""NightMonkey's compilation visualizer: source | JSOp bytecode | MIR | waffle IR.

Runs the AOT compiler with --viz on a program (or reads a --viz file made
earlier) and writes one self-contained HTML page. Per script, four columns
side by side (scroll horizontally): the JS source, its bytecode, the MIR it
compiled to (as optimized), and the lowered waffle IR. Everything is linked:
click a source line, a bytecode op, a MIR instruction or a waffle value, and
what corresponds to it in the other columns lights up and scrolls into
view. A MIR instruction inlined from another script names its origin.

The bytecode column also carries what the analysis knows: each op notes
the type of the value it pushed (its cell, joined over the script's
analyzed contexts) or its call's targets, and the Analysis column shows
the script's formals, receiver and return and, for the selected op, every
pushed value's type and every fact the analysis emitted at its site
(property slots and claims, call targets, method and element facts).
`sN` names script N (click to go to it); `L<k>` a predicted layout (hover
or see the list below it for its fields).

The links come from the compiler: the snapshot's per-script source
position and pc -> line table (the engine's source notes), each MIR
instruction's bytecode pc (recorded by the builder; instructions an
optimization made have none), and each waffle value's MIR instruction
(recorded by the lowering).

Usage:
  tools/viz.py SOURCE.js -o OUT.html [--viz FILE]
               [--nightmonkey PATH] [--shell PATH]
               [--only REGEX] [--self-hosted] [--title T]

SOURCE.js is what the compiler compiles (for Octane, the file without its
trailing `main();`). Without --viz the compiler runs here (build/bin's by
default). --only keeps the scripts whose name matches REGEX: a big program
(pdfjs, mandreel) makes a page of hundreds of megabytes otherwise.
"""

import argparse
import html
import json
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RE_MIR = re.compile(r" ;;@i(\d+) pc=(-?\d+) s=(\d+)$")
RE_WAFFLE = re.compile(r"\s*;;@i(\d+)\s*$")
RE_GUESS = re.compile(r"([\w$][\w$.]*)\s*[:=]\s*(?:async\s+)?function\b")


def run_compiler(args, source):
    nm = args.nightmonkey or os.path.join(ROOT, "build", "bin", "nightmonkey")
    js = args.shell or os.path.join(ROOT, "build", "bin", "js")
    fd, path = tempfile.mkstemp(suffix=".viz")
    os.close(fd)
    cmd = [nm, "--shell", js, source, "-o", os.devnull, "--viz", path]
    r = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
    if r.returncode != 0:
        sys.exit(f"viz.py: {' '.join(cmd)} failed:\n{r.stderr[-2000:]}")
    return path


def line_of_offset(starts, off):
    """1-based line of a source offset, by the sorted line-start offsets."""
    lo, hi = 0, len(starts)
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if starts[mid] <= off:
            lo = mid
        else:
            hi = mid
    return lo + 1


def guess_name(rec, src_lines):
    """The script's name, or for an anonymous function what its first line
    assigns it to (`X.prototype.m = function`, `m: function`), marked `~`."""
    name = rec.get("name") or ""
    pos = rec.get("pos")
    if not name and pos and pos["line"] <= len(src_lines):
        m = RE_GUESS.search(src_lines[pos["line"] - 1])
        name = "~" + m.group(1) if m else ""
    return name or f"<anonymous #{rec['sid']}>"


def prepare(rec, starts, src_lines):
    """A record's columns, linked, in the page's compact form."""
    sid = rec["sid"]
    # The script's source lines: from its offsets, else its line table.
    pos = rec.get("pos")
    table = rec.get("lines", [])
    line0 = line1 = None
    if pos and not rec["name"].startswith("[self-hosted]"):
        line0 = pos["line"]
        if pos["end"] > pos["start"] and starts:
            line1 = line_of_offset(starts, pos["end"])
        if line1 is None or line1 < line0:
            line1 = max([line0] + [l for (_, l, _) in table])
        line1 = min(line1, len(src_lines))
        if line0 > len(src_lines):
            line0 = line1 = None
    # Each op's line: the table's last entry at or before its pc.
    ops = []
    ti = 0
    cur = pos["line"] if pos else None
    for pc, name, args in rec["ops"]:
        while ti < len(table) and table[ti][0] <= pc:
            cur = table[ti][1]
            ti += 1
        ops.append([pc, name, args, cur if line0 is not None else None])
    mir = []
    for text in rec.get("mir", "").splitlines():
        m = RE_MIR.search(text)
        if m:
            mir.append([text[: m.start()], int(m.group(1)), int(m.group(2)), int(m.group(3))])
        else:
            mir.append([text, -1, -1, sid])
    wf = []
    for text in rec.get("waffle", "").splitlines():
        m = RE_WAFFLE.search(text)
        if m:
            wf.append([text[: m.start()].rstrip(), int(m.group(1))])
        else:
            wf.append([text, -1])
    facts = rec.get("facts", {})
    return {
        "sid": sid,
        "name": guess_name(rec, src_lines),
        "tier": rec["tier"],
        "nargs": rec["nargs"],
        "line0": line0,
        "line1": line1,
        "ops": ops,
        "mir": mir,
        "wf": wf,
        # The analysis: script-wide lines, and per pc [pushed, rows].
        "fs": facts.get("script", []),
        "fp": facts.get("sites", {}),
    }


PAGE = r"""<!doctype html>
<html><head><meta charset="utf-8"><title>__TITLE__</title>
<style>
:root { --bg:#fbfbf8; --fg:#1d1d1b; --muted:#8a8a82; --line:#e3e2dc; --hi:#ffe9a8; --hi2:#fff5d6;
        --side:#f3f2ec; --sel:#d9e8ff; --code:#24292f; --pc:#7a6a2f; --inl:#8350a0;
        --ty:#2f6f5e; --link:#1f5fbf; }
@media (prefers-color-scheme: dark) {
  :root { --bg:#17181a; --fg:#e4e3dd; --muted:#8b8b85; --line:#2c2d30; --hi:#5b4a14; --hi2:#3a3220;
          --side:#1f2023; --sel:#24364f; --code:#e4e3dd; --pc:#d0b866; --inl:#c79ae0;
          --ty:#7cc7b0; --link:#7fb0ff; }
}
* { box-sizing: border-box; }
body { margin:0; background:var(--bg); color:var(--fg); font:13px/1.45 system-ui, sans-serif;
       display:flex; height:100vh; overflow:hidden; }
#side { width:280px; flex:none; background:var(--side); border-right:1px solid var(--line);
        display:flex; flex-direction:column; }
#side h1 { font-size:14px; margin:10px 12px 4px; }
#side .sub { margin:0 12px 8px; color:var(--muted); font-size:12px; }
#filter { margin:0 12px 8px; padding:5px 8px; border:1px solid var(--line); border-radius:6px;
          background:var(--bg); color:var(--fg); }
#list { overflow:auto; flex:1; }
#list div { padding:3px 12px; cursor:pointer; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }
#list div:hover { background:var(--hi2); }
#list div.sel { background:var(--sel); }
#list .t { color:var(--muted); font-size:11px; }
#main { flex:1; display:flex; flex-direction:column; min-width:0; }
#head { padding:8px 14px; border-bottom:1px solid var(--line); }
#head b { font-size:14px; }
#head .t { color:var(--muted); margin-left:8px; }
#cols { flex:1; display:flex; overflow-x:auto; overflow-y:hidden; }
.col { flex:none; display:flex; flex-direction:column; border-right:1px solid var(--line); }
.col h2 { font-size:12px; text-transform:uppercase; letter-spacing:.05em; color:var(--muted);
          margin:0; padding:6px 10px; border-bottom:1px solid var(--line); }
.body { overflow:auto; flex:1; font:12px/1.45 ui-monospace, SFMono-Regular, Menlo, monospace;
        color:var(--code); white-space:pre; padding-bottom:40vh; }
.body div { padding:0 10px; cursor:pointer; min-height:1.45em; }
.body div:hover { background:var(--hi2); }
.body div.hi { background:var(--hi); }
.n { color:var(--muted); display:inline-block; min-width:4.5em; text-align:right; margin-right:1em; user-select:none; }
.pc { color:var(--pc); }
.inl { color:var(--inl); }
.dim { color:var(--muted); }
#c-src { width:72ch; } #c-ops { width:84ch; } #c-an { width:64ch; } #c-mir { width:110ch; } #c-wf { width:110ch; }
.ty { color:var(--ty); }
#b-an { white-space:normal; padding:6px 10px 40vh; cursor:default; }
#b-an div { padding:0; cursor:default; min-height:0; }
#b-an div:hover { background:none; }
#b-an h3 { font:600 11px system-ui, sans-serif; text-transform:uppercase; letter-spacing:.05em;
           color:var(--muted); margin:10px 0 4px; }
#b-an h3:first-child { margin-top:2px; }
#b-an ul { margin:0; padding-left:1.2em; }
#b-an li { margin:1px 0; overflow-wrap:anywhere; }
a.s { color:var(--link); cursor:pointer; text-decoration:underline dotted; }
span.L { color:var(--inl); text-decoration:underline dotted; cursor:help; }
.empty { padding:10px; color:var(--muted); font-family:system-ui, sans-serif; white-space:normal; }
</style></head>
<body>
<div id="side"><h1>__TITLE__</h1><div class="sub" id="count"></div>
<input id="filter" placeholder="filter scripts"><div id="list"></div></div>
<div id="main"><div id="head"></div>
<div id="cols">
<div class="col" id="c-src"><h2>Source</h2><div class="body" id="b-src"></div></div>
<div class="col" id="c-ops"><h2>Bytecode</h2><div class="body" id="b-ops"></div></div>
<div class="col" id="c-an"><h2>Analysis</h2><div class="body" id="b-an"></div></div>
<div class="col" id="c-mir"><h2>MIR</h2><div class="body" id="b-mir"></div></div>
<div class="col" id="c-wf"><h2>Waffle IR</h2><div class="body" id="b-wf"></div></div>
</div></div>
<script id="data" type="application/json">__DATA__</script>
<script>
const D = JSON.parse(document.getElementById('data').textContent);
const SRC = D.source, S = D.scripts;
const $ = id => document.getElementById(id);
let cur = null;

function esc(s) { return s.replace(/[&<>]/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;'}[c])); }

function list() {
  const f = $('filter').value.toLowerCase();
  const L = $('list'); L.innerHTML = '';
  S.forEach((s, k) => {
    if (f && !s.name.toLowerCase().includes(f)) return;
    const d = document.createElement('div');
    d.innerHTML = esc(s.name) + ' <span class="t">#' + s.sid + (s.line0 ? ' L' + s.line0 : '') +
      (s.tier !== 'mir' ? ' ' + esc(s.tier) : '') + '</span>';
    d.onclick = () => show(k);
    if (cur === k) d.className = 'sel';
    L.appendChild(d);
  });
}

function show(k) {
  cur = k; list(); setHash('');
  const s = S[k];
  $('head').innerHTML = '<b>' + esc(s.name) + '</b><span class="t">script #' + s.sid +
    ', ' + s.nargs + ' formals, ' + esc(s.tier) + (s.line0 ? ', lines ' + s.line0 + '-' + s.line1 : '') + '</span>';
  // Source.
  let h = '';
  if (s.line0) {
    for (let l = s.line0; l <= s.line1; l++)
      h += '<div data-l="' + l + '"><span class="n">' + l + '</span>' + esc(SRC[l - 1] || '') + '</div>';
  } else h = '<div class="empty">No source position (a self-hosted or generated script).</div>';
  $('b-src').innerHTML = h;
  // Bytecode.
  h = '';
  for (const [pc, name, args, line] of s.ops)
    h += '<div data-pc="' + pc + '"><span class="n">' + pc + '</span>' + esc(name) +
         (args ? ' <span class="dim">' + esc(args) + '</span>' : '') + note(s, pc) + '</div>';
  $('b-ops').innerHTML = h;
  analysis(null);
  // MIR.
  h = '';
  if (!s.mir.length) h = '<div class="empty">Not compiled by MIR (' + esc(s.tier) + ').</div>';
  s.mir.forEach(([text, i, pc, sid], n) => {
    let tag = '';
    if (i >= 0) tag = sid !== s.sid ? '<span class="inl">s' + sid + ':' + pc + '</span>' :
                      (pc >= 0 ? '<span class="pc">@' + pc + '</span>' : '');
    h += '<div data-i="' + i + '" data-n="' + n + '"><span class="n">' + tag + '</span>' + esc(text) + '</div>';
  });
  $('b-mir').innerHTML = h;
  // Waffle.
  h = '';
  s.wf.forEach(([text, i]) => {
    h += '<div data-i="' + i + '"><span class="n">' + (i >= 0 ? 'i' + i : '') + '</span>' + esc(text) + '</div>';
  });
  $('b-wf').innerHTML = h;
  for (const id of ['b-src', 'b-ops', 'b-mir', 'b-wf']) $(id).scrollTop = 0;
}

// What the analysis knows, in the bytecode column (a short note per op)
// and the Analysis column (everything, for the script and the selected op).
const L = D.layouts || {}, NAMES = D.names || {};
function sname(sid) { return NAMES[sid] || ('#' + sid); }
function short(t) {
  return t.replace(/  \[\d+ ctxs\]/, '').replace(/  \((this|constant|formal \d+|global [^)]*|closure slot \d+)\)$/, '');
}
function note(s, pc) {
  const f = s.fp[pc];
  if (!f) return '';
  const [pushed, rows] = f;
  let t = '';
  const call = rows.find(r => r.startsWith('call targets: '));
  if (call) t = '\u21d2 ' + call.slice(14).split(', ').map(x => sname(+x.slice(1))).join(', ');
  else if (pushed.length) t = '\u2192 ' + pushed.map(short).join(' , ').replace(/\bs(\d+)\b/g, (m, n) => sname(+n));
  if (!t) return '';
  if (t.length > 60) t = t.slice(0, 59) + '\u2026';
  return '  <span class="ty">' + esc(t) + '</span>';
}
// A fact line with its script names linked and its layouts explained.
function fact(t, seen) {
  return esc(t).replace(/\bs(\d+)\b|\bL(\d+)\b/g, (m, sid, k) => {
    if (sid !== undefined) return '<a class="s" data-sid="' + sid + '">' + esc(sname(+sid)) + ' (s' + sid + ')</a>';
    seen.add(k);
    return '<span class="L" title="' + esc(L[k] || '?').replace(/"/g, '&quot;') + '">L' + k + '</span>';
  });
}
function analysis(pc) {
  const s = S[cur], seen = new Set();
  const ul = a => '<ul>' + a.map(t => '<li>' + fact(t, seen) + '</li>').join('') + '</ul>';
  let h = '';
  if (pc !== null) {
    const op = s.ops.find(o => o[0] === pc);
    h += '<h3>pc ' + pc + (op ? ' ' + esc(op[1]) + (op[2] ? ' ' + esc(op[2]) : '') : '') + '</h3>';
    const f = s.fp[pc];
    if (!f) h += '<div class="dim">Nothing recorded at this op.</div>';
    else {
      if (f[0].length) h += '<h3>Pushes</h3>' + ul(f[0].map((t, k) => (f[0].length > 1 ? '#' + k + ' ' : '') + t));
      if (f[1].length) h += '<h3>Facts at this site</h3>' + ul(f[1]);
    }
  } else h += '<div class="dim">Click an op for what the analysis knows at it.</div>';
  if (s.fs.length) h += '<h3>Script</h3>' + ul(s.fs);
  if (seen.size) h += '<h3>Layouts</h3>' + ul([...seen].sort((a, b) => a - b).map(k => 'L' + k + ' = ' + (L[k] || '?')));
  $('b-an').innerHTML = h;
}
$('b-an').onclick = ev => {
  const a = ev.target.closest('a.s');
  if (!a) return;
  const k = S.findIndex(x => String(x.sid) === a.dataset.sid);
  if (k >= 0) show(k);
};

// The page's state in the URL (`#s=<sid>&line=<l>`, `&pc=`, `&i=`): a
// link to a script and a selection in it.
function setHash(kv) {
  history.replaceState(null, '', '#s=' + S[cur].sid + (kv ? '&' + kv : ''));
}
function fromHash() {
  const h = new URLSearchParams(location.hash.slice(1));
  const k = S.findIndex(s => String(s.sid) === h.get('s'));
  if (k < 0) return false;
  show(k);
  if (h.has('line')) select(new Set([+h.get('line')]), new Set(), new Set());
  else if (h.has('pc')) select(new Set(), new Set([+h.get('pc')]), new Set());
  else if (h.has('i')) select(new Set(), new Set(), new Set([+h.get('i')]));
  return true;
}

// The links: a selection is a set of source lines, op pcs and MIR insts.
function select(lines, pcs, insts) {
  const s = S[cur];
  const opLine = new Map(s.ops.map(o => [o[0], o[3]]));
  if (lines.size) for (const o of s.ops) if (lines.has(o[3])) pcs.add(o[0]);
  if (pcs.size) for (const [, i, pc, sid] of s.mir) if (i >= 0 && sid === s.sid && pcs.has(pc)) insts.add(i);
  for (const [, i, pc, sid] of s.mir) if (insts.has(i) && sid === s.sid && pc >= 0) {
    pcs.add(pc); const l = opLine.get(pc); if (l) lines.add(l);
  }
  for (const pc of pcs) { const l = opLine.get(pc); if (l) lines.add(l); }
  const first = [...pcs].sort((a, b) => a - b)[0];
  analysis(first === undefined ? null : first);
  mark('b-src', e => lines.has(+e.dataset.l));
  mark('b-ops', e => pcs.has(+e.dataset.pc));
  mark('b-mir', e => insts.has(+e.dataset.i));
  mark('b-wf', e => insts.has(+e.dataset.i));
}

function mark(id, pred) {
  let first = null;
  for (const e of $(id).children) {
    const on = pred(e);
    e.classList.toggle('hi', on);
    if (on && !first) first = e;
  }
  if (first) {
    const b = $(id), r = first.offsetTop - b.offsetTop;
    if (r < b.scrollTop || r > b.scrollTop + b.clientHeight - 40) b.scrollTop = r - 60;
  }
}

$('b-src').onclick = ev => { const e = ev.target.closest('div[data-l]'); if (e) { setHash('line=' + e.dataset.l); select(new Set([+e.dataset.l]), new Set(), new Set()); } };
$('b-ops').onclick = ev => { const e = ev.target.closest('div[data-pc]'); if (e) { setHash('pc=' + e.dataset.pc); select(new Set(), new Set([+e.dataset.pc]), new Set()); } };
const byInst = ev => { const e = ev.target.closest('div[data-i]'); if (e && +e.dataset.i >= 0) { setHash('i=' + e.dataset.i); select(new Set(), new Set(), new Set([+e.dataset.i])); } };
$('b-mir').onclick = byInst; $('b-wf').onclick = byInst;
$('filter').oninput = list;
$('count').textContent = S.length + ' scripts';
list();
if (!fromHash() && S.length) show(0);
window.onhashchange = fromHash;
</script></body></html>
"""


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("source")
    ap.add_argument("-o", "--output", required=True)
    ap.add_argument("--viz", help="a --viz file made earlier (else the compiler runs here)")
    ap.add_argument("--nightmonkey")
    ap.add_argument("--shell")
    ap.add_argument("--only", help="keep the scripts whose name matches this regex")
    ap.add_argument("--self-hosted", action="store_true", help="keep self-hosted scripts too")
    ap.add_argument("--title")
    args = ap.parse_args()

    with open(args.source, encoding="utf-8", errors="replace") as f:
        text = f.read()
    lines = text.split("\n")
    starts, off = [], 0
    for l in lines:
        starts.append(off)
        off += len(l) + 1

    path = args.viz or run_compiler(args, args.source)
    only = re.compile(args.only) if args.only else None
    scripts = []
    layouts = {}
    names = {}
    with open(path, encoding="utf-8") as f:
        for raw in f:
            if not raw.strip():
                continue
            rec = json.loads(raw)
            if "layouts" in rec:
                layouts = rec["layouts"]
                continue
            names[rec["sid"]] = guess_name(rec, lines)
            name = rec.get("name") or ""
            if name.startswith("[self-hosted]") and not args.self_hosted:
                continue
            if only and not only.search(name) and name:
                continue
            s = prepare(rec, starts, lines)
            # An anonymous script is kept by its guessed name too.
            if only and not only.search(s["name"].lstrip("~")):
                continue
            scripts.append(s)
    if not args.viz:
        os.unlink(path)
    scripts.sort(key=lambda s: (s["line0"] is None, s["line0"] or 0, s["sid"]))

    title = args.title or os.path.basename(args.source)
    data = json.dumps({"source": lines, "scripts": scripts, "layouts": layouts, "names": names},
                      separators=(",", ":"))
    page = (PAGE.replace("__TITLE__", html.escape(title))
                .replace("__DATA__", data.replace("</", "<\\/")))
    with open(args.output, "w", encoding="utf-8") as f:
        f.write(page)
    print(f"viz.py: {len(scripts)} scripts -> {args.output} ({len(page) // 1024} KiB)")


if __name__ == "__main__":
    main()
