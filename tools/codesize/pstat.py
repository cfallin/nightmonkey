#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""perf-stat the aot lane (and optionally ion) over event groups; JSON lines out.
react-bench ion lane needs $PSTAT_TMP/var/react-ion.js (make-harness.py 200 <out>).

  pstat.py <artdir> <out.jsonl> [--lanes aot,ion] [--benches a,b] [--groups 1,2,3]
"""
import json
import os
import re
import shutil
import subprocess
import sys

FX = os.path.abspath(os.path.join(os.path.dirname(__file__), *[".."] * 5))
WT = os.path.expanduser("~/bin/wasmtime")
SYS_JS = "/home/linuxbrew/.linuxbrew/bin/js"
S = os.environ.get("PSTAT_TMP", "/tmp")
GROUPS = {
    "1": [
        "cycles",
        "instructions",
        "de_no_dispatch_per_slot.no_ops_from_frontend",
        "de_no_dispatch_per_slot.backend_stalls",
        "ex_ret_ops",
    ],
    "2": [
        "ic_tag_hit_miss.all_instruction_cache_accesses",
        "ic_tag_hit_miss.instruction_cache_miss",
        "op_cache_hit_miss.all_op_cache_accesses",
        "op_cache_hit_miss.op_cache_miss",
        "de_src_op_disp.x86_decoder",
    ],
    "3": [
        "bp_l1_tlb_miss_l2_tlb_hit",
        "bp_l1_tlb_miss_l2_tlb_miss.all",
        "ic_cache_fill_l2",
        "ic_cache_fill_sys",
        "ex_ret_brn_misp",
    ],
    "4": [
        "instructions",
        "de_src_op_disp.op_cache",
        "de_src_op_disp.all",
        "de_op_queue_empty",
        "cycles",
    ],
}
OCT = "richards deltablue crypto raytrace earley-boyer navier-stokes splay regexp pdfjs mandreel code-load box2d".split()


def arg(name, default):
    if name in sys.argv:
        return sys.argv[sys.argv.index(name) + 1]
    return default


def run(cmd, stdin=None):
    p = subprocess.run(cmd, check=False, capture_output=True, text=True, stdin=stdin)
    return p.stdout, p.stderr


def metric(out, bench):
    if bench == "react-bench":
        m = re.findall(r"mean=([0-9.]+)ms", out)
        return float(m[-1]) if m else None
    m = re.findall(r"Score.*: (\d+)", out)
    return int(m[-1]) if m else None


def parse_stat(err):
    d = {}
    for ln in err.splitlines():
        parts = ln.split(",")
        if len(parts) >= 3 and parts[2]:
            try:
                d[parts[2]] = int(parts[0])
            except ValueError:
                d[parts[2]] = None
    return d


def main():
    art, outp = sys.argv[1], sys.argv[2]
    lanes = arg("--lanes", "aot").split(",")
    benches = arg("--benches", ",".join(OCT + ["react-bench"])).split(",")
    groups = arg("--groups", "1,2,3").split(",")
    core = arg("--core", "1")
    with open(outp, "a") as f:
        for b in benches:
            for lane in lanes:
                for g in groups:
                    ev = ",".join(GROUPS[g])
                    if lane == "aot":
                        src = f"{art}/{b}.cwasm"
                        if not os.path.exists(src):
                            print(b, lane, "MISSING")
                            continue
                        cw = f"{S}/pstat.run.cwasm"
                        shutil.copy(src, cw)
                        cmd = [
                            "taskset",
                            "-c",
                            core,
                            "perf",
                            "stat",
                            "-x,",
                            "-e",
                            ev,
                            "--",
                            WT,
                            "run",
                            "--allow-precompiled",
                            "-W",
                            "unknown-imports-trap",
                            cw,
                        ]
                        out, err = run(cmd)
                    else:
                        js = (
                            f"{FX}/octane/{b}.js"
                            if b != "react-bench"
                            else f"{S}/var/react-ion.js"
                        )
                        cmd = [
                            "taskset",
                            "-c",
                            core,
                            "perf",
                            "stat",
                            "-x,",
                            "-e",
                            ev,
                            "--",
                            SYS_JS,
                            js,
                        ]
                        out, err = run(cmd)
                    rec = {
                        "bench": b,
                        "lane": lane,
                        "group": g,
                        "score": metric(out, b),
                        "ev": parse_stat(err),
                    }
                    f.write(json.dumps(rec) + "\n")
                    f.flush()
                    print(
                        b, lane, g, rec["score"], {k: v for k, v in rec["ev"].items()}
                    )


main()
