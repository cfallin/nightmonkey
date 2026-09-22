#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
"""Class facts that were PROVED UPSTREAM and did not arrive.

  domfact.py <cfg.txt> <clsfact.txt> [opsize.err] [--sites N] [--clean]

`--dump-clsfact` says, at every consumer of a durable class fact, what the
site actually had: `full`, `idonly`, `outside` or `none`. It cannot say
whether the fact was ever available, because availability is a question about
paths and the emitter's lineage is not one.

`--dump-cfg` now publishes the dominator tree over the unified pc space
(`bbv/cfg.rs`), so the question can be asked: for each site with `have none`
on a NAMED slot, does a pc that DOMINATES it prove that same slot's class? If
one does, the fact existed on every path to this site and something between
them dropped it -- which is an analysis-precision question, the standing
lever, and not something a guard at this site can fix.

What a hit is not: proof of a bug. A dominating pc may legitimately have been
followed by a reassignment of the slot or by a may-GC call that killed the
fact. This ranks the candidates; `--dump-ctxedge` and `tools/ctxdiff.py` say
which arm dropped which fact, and `tools/rootcause.py` says whether a kill
was the cause.

Give it an `--dump-opsize` dump as a third argument and it also reports
whether a may-GC call, or a STORE to a frame slot, lies between the proof and
the consumer.

**Read neither column as evidence on its own:**

- a STORE between means the slot may have been RE-BOUND, so the proof says
  nothing about what the consumer holds -- and re-binding a slot from a
  same-class load wants the identical class range, so "wants the same range as
  the proof" is not evidence either. 82 of box2d's 108 hits were this.
- a CALL between means only that a call OP appears there. It cannot ask
  whether that call's keep arm restored the facts, and the keep arm is taken
  99.9-100% of executions with `flagsite-miss` at ZERO on the gate corpus, so
  a call between proof and consumer says nothing at all.

`--clean` filters to the rows with NEITHER, which are the only ones where the
fact provably held and was dropped. That is the column to work from.

Spliced sites are excluded (`seg 1`): inside a segment the emitter's
`source_id` is the CALLEE's, so a segment-interior record cannot be joined to
the caller's dominator tree without re-deriving the root sid, and reading it
under the callee's tree would silently answer a different question.
"""
import collections
import re
import sys

OPS = re.compile(r"^night: opsize sid#(\d+) pc (\d+) lpc \d+ op (\S+) ")
# A store to the slot itself. `--dump-opsize` names the op but not its
# operand, so this is the op FAMILY: any of these between the proof and the
# consumer means the slot may have been re-bound, and the dominating proof
# then says nothing about what the consumer holds.
STOREOPS = (
    "SetLocal",
    "SetArg",
    "InitLexical",
    "InitAliasedLexical",
    "SetAliasedVar",
    "PopN",
    "DefVar",
    "InitLocal",
)
CALLOPS = (
    "Call",
    "CallContent",
    "CallIgnoresRv",
    "CallIter",
    "CallContentIter",
    "New",
    "NewContent",
    "SuperCall",
    "SpreadCall",
    "SpreadNew",
    "SpreadSuperCall",
)
BLK = re.compile(r"^night: cfg sid#(\d+) blk (\d+)\.\.(\d+) idom (-?\d+) depth (\d+) ")
CLS = re.compile(
    r"^night: clsfact sid#(\d+) pc \d+ lpc (\d+) kind (\S+) have (\S+) src (\S+) "
    r"range (\d+)\.\.(\d+) track (\S+) seg (\d) "
)


def load_cfg(path):
    """sid -> (spans sorted by start, idom by block start pc, depth)."""
    spans = collections.defaultdict(list)
    idom, depth = collections.defaultdict(dict), collections.defaultdict(dict)
    for ln in open(path):
        m = BLK.match(ln)
        if not m:
            continue
        sid, s, e, d = (
            int(m.group(1)),
            int(m.group(2)),
            int(m.group(3)),
            int(m.group(4)),
        )
        spans[sid].append((s, e))
        idom[sid][s] = d
        depth[sid][s] = int(m.group(5))
    for v in spans.values():
        v.sort()
    return spans, idom, depth


def blk_of(spans, pc):
    import bisect

    i = bisect.bisect_right(spans, (pc, 1 << 62))
    if i == 0:
        return None
    s, e = spans[i - 1]
    return s if pc < e else None


def dominates(idom, a_blk, b_blk):
    """Walk b up the tree. -1 marks an unreachable block: it is dominated by
    nothing, which is the conservative answer this file wants."""
    seen = 0
    while b_blk is not None and b_blk != -1:
        if b_blk == a_blk:
            return True
        nxt = idom.get(b_blk)
        if nxt is None or nxt == b_blk:
            return False
        b_blk = nxt
        seen += 1
        if seen > 1 << 20:
            return False
    return False


def load_ops(path):
    """sid -> sorted [(pc, op)], for the between-the-two-pcs question."""
    by = collections.defaultdict(dict)
    for ln in open(path):
        m = OPS.match(ln)
        if m:
            by[int(m.group(1))][int(m.group(2))] = m.group(3)
    return {sid: sorted(d.items()) for sid, d in by.items()}


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    cfgf, clsf = args[0], args[1]
    ops = load_ops(args[2]) if len(args) > 2 else {}
    topn = int(sys.argv[sys.argv.index("--sites") + 1]) if "--sites" in sys.argv else 20
    spans, idom, depth = load_cfg(cfgf)

    # Per (sid, src slot): the pcs that PROVE a class there, and the pcs that
    # wanted one and had none.
    proved = collections.defaultdict(list)
    wanted = collections.defaultdict(list)
    rows = []
    for ln in open(clsf):
        m = CLS.match(ln)
        if not m:
            continue
        sid, pc, kind, have, src = (
            int(m.group(1)),
            int(m.group(2)),
            m.group(3),
            m.group(4),
            m.group(5),
        )
        lo, hi, track, seg = int(m.group(6)), int(m.group(7)), m.group(8), m.group(9)
        if seg != "0" or src == "stack":
            continue
        rows.append((sid, pc, kind, have, src, lo, hi, track))
        if have in ("full", "idonly"):
            proved[(sid, src)].append((pc, lo, hi))
        elif have in ("none", "outside"):
            wanted[(sid, src)].append((pc, lo, hi, kind, have, track))

    hits, misses, nocfg = [], 0, 0
    for key, ws in wanted.items():
        sid, src = key
        sp = spans.get(sid)
        if not sp:
            nocfg += len(ws)
            continue
        for pc, lo, hi, kind, have, track in ws:
            b = blk_of(sp, pc)
            if b is None:
                nocfg += 1
                continue
            dom = [
                (ppc, plo, phi)
                for (ppc, plo, phi) in proved.get(key, [])
                if ppc != pc
                and (pb := blk_of(sp, ppc)) is not None
                and (dominates(idom[sid], pb, b) if pb != b else ppc < pc)
            ]
            if dom:
                # The nearest dominating proof is the one worth chasing.
                ppc, plo, phi = max(dom, key=lambda t: t[0] if t[0] < pc else -1)
                same = plo == lo and phi == hi
                import bisect as _b

                o = ops.get(sid, [])
                lo_i = _b.bisect_right(o, (ppc, "\uffff"))
                hi_i = _b.bisect_left(o, (pc, ""))
                call = any(n in CALLOPS for _, n in o[lo_i:hi_i]) if o else None
                store = any(n in STOREOPS for _, n in o[lo_i:hi_i]) if o else None
                hits.append(
                    (
                        sid,
                        pc,
                        kind,
                        have,
                        src,
                        track,
                        ppc,
                        same,
                        depth[sid].get(b, 0),
                        call,
                        store,
                    )
                )
            else:
                misses += 1

    tot = len(hits) + misses + nocfg
    print(f"named-slot class-fact consumers with no fact: {tot}")
    print(
        f"  a DOMINATING pc proves that slot : {len(hits)}"
        + (f"  ({100*len(hits)/tot:.0f}%)" if tot else "")
    )
    print(f"  no dominating proof anywhere      : {misses}")
    print(f"  site not in the cfg dump          : {nocfg}")
    if not hits:
        return
    same = sum(1 for h in hits if h[7])
    print(
        f"  of the hits, {same} want the SAME class range as the proof, "
        f"{len(hits)-same} a different one"
    )
    if any(h[9] is not None for h in hits):
        withcall = sum(1 for h in hits if h[9])
        withstore = sum(1 for h in hits if h[10])
        neither = sum(1 for h in hits if not h[9] and not h[10])
        print(
            f"  a may-GC call lies between the proof and the consumer in "
            f"{withcall} of {len(hits)}"
        )
        print(
            f"  a STORE to a frame slot lies between in {withstore} "
            f"(the slot may be re-bound: the proof says nothing)"
        )
        print(
            f"  NEITHER a call nor a store between       : {neither} "
            f"-- the only rows where the fact provably held and was dropped"
        )
    if "--clean" in sys.argv:
        hits = [h for h in hits if not h[9] and not h[10]]
        print("\n--clean: only the rows with NEITHER a call nor a store between")
    print("\ntop sites (nearest dominating proof, deepest loop first)")
    print(
        f"{'sid':>7}{'pc':>8}{'kind':>6}{'have':>8}{'src':>9}{'track':>7}"
        f"{'proved at':>11}{'same':>6}{'loop':>6}{'call':>6}{'store':>7}"
    )
    for h in sorted(hits, key=lambda h: (-h[8], h[0], h[1]))[:topn]:
        sid, pc, kind, have, src, track, ppc, same, d, call, store = h
        c = "-" if call is None else ("yes" if call else "no")
        st = "-" if store is None else ("yes" if store else "no")
        print(
            f"{sid:>7}{pc:>8}{kind:>6}{have:>8}{src:>9}{track:>7}"
            f"{ppc:>11}{('yes' if same else 'no'):>6}{d:>6}{c:>6}{st:>7}"
        )


if __name__ == "__main__":
    main()
