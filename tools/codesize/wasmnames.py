#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""func index -> name from a wasm 'name' custom section."""
import sys


def leb(b, i):
    r = 0
    s = 0
    while True:
        x = b[i]
        i += 1
        r |= (x & 0x7F) << s
        s += 7
        if not (x & 0x80):
            return r, i


def names(path):
    b = open(path, "rb").read()
    assert b[:4] == b"\0asm"
    i = 8
    out = {}
    while i < len(b):
        sid = b[i]
        i += 1
        size, i = leb(b, i)
        end = i + size
        if sid == 0:
            n, j = leb(b, i)
            nm = b[j : j + n].decode("utf8", "replace")
            j += n
            if nm == "name":
                while j < end:
                    ss = b[j]
                    j += 1
                    sz, j = leb(b, j)
                    se = j + sz
                    if ss == 1:
                        cnt, k = leb(b, j)
                        for _ in range(cnt):
                            idx, k = leb(b, k)
                            ln, k = leb(b, k)
                            out[idx] = b[k : k + ln].decode("utf8", "replace")
                            k += ln
                    j = se
        i = end
    return out


if __name__ == "__main__":
    n = names(sys.argv[1])
    print(len(n), "names")
    for k in sorted(n)[:5]:
        print(k, n[k])
    ours = {
        k: v
        for k, v in n.items()
        if v.startswith("night_script")
        or v.startswith("night_adapter")
        or v.startswith("night_regex")
    }
    print("night_script/adapter/regex funcs:", len(ours))
    for k in sorted(ours)[:8]:
        print(" ", k, ours[k])
