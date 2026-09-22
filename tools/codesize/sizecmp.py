#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Generated-code size, baseline vs candidate.

  ART=<dir> NEW=<dir> sizecmp.py [bench ...]

ART holds the baseline `<bench>.cwasm` and the `<bench>.snap.wasm` the cutoff
index is read from; NEW holds `new-<bench>.cwasm`. Only functions at or above
`21 imports + the snapshot's defined-function count` are ours.
"""
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cwasm_syms import syms


def cut(w):
    o = subprocess.run(
        ["wasm-objdump", "-h", w], check=False, capture_output=True, text=True
    ).stdout
    return int(
        re.search(r"Function start=\S+ end=\S+ \(size=\S+\) count: (\d+)", o).group(1)
    ) + int(
        re.search(r"Import start=\S+ end=\S+ \(size=\S+\) count: (\d+)", o).group(1)
    )


ART = os.environ.get("ART", "viz-icache/art")
NEW = os.environ.get("NEW", "/tmp")
B = sys.argv[1:] or ["richards", "deltablue", "crypto", "box2d"]
print(f"{'bench':<14}{'baseline':>12}{'new':>12}{'delta':>11}{'%':>8}")
to = tn = 0
for b in B:
    nf = f"{NEW}/new-{b}.cwasm"
    if not os.path.exists(nf):
        continue
    c = cut(f"{ART}/{b}.snap.wasm")
    old = sum(v[1] for k, v in syms(f"{ART}/{b}.cwasm").items() if k >= c)
    new = sum(v[1] for k, v in syms(nf).items() if k >= c)
    to += old
    tn += new
    print(f"{b:<14}{old:>12}{new:>12}{new-old:>11}{100*(new-old)/old:>7.1f}%")
print(f"{'TOTAL':<14}{to:>12}{tn:>12}{tn-to:>11}{100*(tn-to)/to:>7.1f}%")
