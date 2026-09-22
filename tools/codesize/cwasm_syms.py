#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Per-wasm-function native code sizes from a wasmtime .cwasm (ELF symtab)."""
import re
import subprocess
import sys


def syms(path):
    out = subprocess.run(
        ["readelf", "-sW", path], check=False, capture_output=True, text=True
    ).stdout
    pat = re.compile(
        r"^\s*\d+:\s+([0-9a-f]+)\s+(0x[0-9a-f]+|\d+)\s+FUNC\s+\S+\s+\S+\s+\S+\s+wasm\[0\]::function\[(\d+)\]"
    )
    r = {}
    for line in out.splitlines():
        m = pat.match(line)
        if m:
            r[int(m.group(3 if not m.group(2).startswith("0x") else 3))] = (
                int(m.group(1), 16),
                int(m.group(2), 16) if m.group(2).startswith("0x") else int(m.group(2)),
            )
    return r


if __name__ == "__main__":
    s = syms(sys.argv[1])
    tot = sum(v[1] for v in s.values())
    print(f"{sys.argv[1]}: {len(s)} funcs, {tot} bytes text ({tot/1e6:.2f} MB)")
    idx = sorted(s)
    print(f"  index range {idx[0]}..{idx[-1]}")
