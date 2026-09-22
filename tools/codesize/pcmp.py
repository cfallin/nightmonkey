# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
import json
import sys


def ld(p):
    d = {}
    for ln in open(p):
        r = json.loads(ln)
        d[(r["bench"], r["lane"], r["group"])] = r
    return d


A = ld(sys.argv[1])
B = ld(sys.argv[2])
benches = sys.argv[3].split(",")
print(
    f"{'bench':<14}{'scoreA':>8}{'scoreB':>8}{'B/A':>7}{'ins/wk':>8}{'cyc/wk':>8}{'IPC A':>7}{'IPC B':>7}{'FE%A':>7}{'FE%B':>7}{'L1iMPKI A':>10}{'L1iMPKI B':>10}{'OC%A':>6}{'OC%B':>6}"
)
for b in benches:
    a1 = A[(b, "aot", "1")]
    b1 = B[(b, "aot", "1")]
    a2 = A[(b, "aot", "2")]
    b2 = B[(b, "aot", "2")]
    sa, sb = a1["score"], b1["score"]
    ins = (b1["ev"]["instructions"] / sb) / (a1["ev"]["instructions"] / sa)
    cyc = (b1["ev"]["cycles"] / sb) / (a1["ev"]["cycles"] / sa)
    ipa = a1["ev"]["instructions"] / a1["ev"]["cycles"]
    ipb = b1["ev"]["instructions"] / b1["ev"]["cycles"]
    fea = (
        100
        * a1["ev"]["de_no_dispatch_per_slot.no_ops_from_frontend"]
        / (8 * a1["ev"]["cycles"])
    )
    feb = (
        100
        * b1["ev"]["de_no_dispatch_per_slot.no_ops_from_frontend"]
        / (8 * b1["ev"]["cycles"])
    )
    ma = (
        1000
        * a2["ev"]["ic_tag_hit_miss.instruction_cache_miss"]
        / a1["ev"]["instructions"]
    )
    mb = (
        1000
        * b2["ev"]["ic_tag_hit_miss.instruction_cache_miss"]
        / b1["ev"]["instructions"]
    )
    oa = (
        100
        * a2["ev"]["op_cache_hit_miss.op_cache_miss"]
        / a2["ev"]["op_cache_hit_miss.all_op_cache_accesses"]
    )
    ob = (
        100
        * b2["ev"]["op_cache_hit_miss.op_cache_miss"]
        / b2["ev"]["op_cache_hit_miss.all_op_cache_accesses"]
    )
    print(
        f"{b:<14}{sa:>8}{sb:>8}{sb/sa:>7.3f}{ins:>8.3f}{cyc:>8.3f}{ipa:>7.2f}{ipb:>7.2f}{fea:>7.1f}{feb:>7.1f}{ma:>10.1f}{mb:>10.1f}{oa:>6.1f}{ob:>6.1f}"
    )
