#!/usr/bin/env bash
# EXECUTED emitted IR per executed bytecode op, by block role: the join of
# `--block-census` (one runtime tick per lowered block) with its static
# per-block records. Emitted IR is not executed IR -- an op's arm bundle is
# 80-87% of what it emits and an execution takes one path through it -- and
# this is the instrument that tells the two apart.
#
#   blockprof.sh <bench> [<binary>]      ITERS=<n>  SD=<dir>  then any
#                                        blockprof.py flags after `--`
#
# The work is pinned (`doDeterministic`, like natop.sh) so a slow census
# build completes a known iteration count; ITERS scales it down. The
# compile also carries --viz --viz-lower --dump-opsize so blockprof.py can
# print a hot block's instructions next to its execution count.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." || exit 1
B=${1:?usage: blockprof.sh <bench> [binary] [-- blockprof.py flags]}
shift
NM=js/src/night/nightmonkey/target/release/nightmonkey
if [ $# -gt 0 ] && [ "$1" != "--" ]; then NM=$1; shift; fi
[ "${1:-}" = "--" ] && shift
WASMTIME=${WASMTIME:-$HOME/bin/wasmtime}
NIGHT_JS=obj-nightmonkey/dist/bin/js
MEMCAP=${MEMCAP:-$HOME/bin/memcap}; [ -x "$MEMCAP" ] || MEMCAP=env
SD=${SD:-${TMPDIR:-/tmp}/night-blockprof}/$B; mkdir -p "$SD"
CPU=${CPU:-1}
RUN_TIMEOUT=${RUN_TIMEOUT:-600}

v=$SD/$B.js
if [ ! -f "$v" ]; then
  head -n -1 "octane/$B.js" > "$v"
  {
    echo 'BenchmarkSuite.config.doDeterministic = true;'
    if [ -n "${ITERS:-}" ]; then
      echo "BenchmarkSuite.suites.forEach(function(s){"
      echo "  s.benchmarks.forEach(function(b){ b.deterministicIterations = ${ITERS}; });"
      echo "});"
    fi
    # No trailing `main();`: the snapshot flow runs the top level during
    # wizening and the resumed snapshot calls `main()` itself. Calling it
    # here too runs the whole benchmark twice, and box2d's tearDown nulls
    # `Box2D`, so the second run died with "Common of null".
  } >> "$v"
fi

snap=$SD/snap.wasm
[ -f "$snap" ] || "$MEMCAP" 32G "$NM" --shell "$NIGHT_JS" "$v" --keep-snapshot "$snap" \
  --keep-names -o /dev/null >/dev/null 2>&1 || { echo "$B: snapshot failed"; exit 1; }

if [ ! -f "$SD/blk.cwasm" ]; then
  "$MEMCAP" 32G "$NM" "$snap" --census --block-census --viz --viz-lower --dump-opsize \
    -o "$SD/blk.wasm" 2> "$SD/blk.compile.err" >/dev/null \
    || { echo "$B: compile failed"; tail -5 "$SD/blk.compile.err"; exit 1; }
  "$WASMTIME" compile "$SD/blk.wasm" -o "$SD/blk.cwasm" 2>/dev/null
fi

if [ ! -f "$SD/blk.run.err" ]; then
  timeout "$RUN_TIMEOUT" taskset -c "$CPU" "$WASMTIME" run --allow-precompiled -W unknown-imports-trap \
    "$SD/blk.cwasm" > "$SD/blk.out" 2> "$SD/blk.run.err" \
    || { echo "$B: run failed or timed out (rc=$?)"; rm -f "$SD/blk.run.err"; exit 1; }
  grep -q 'census sites' "$SD/blk.run.err" || { echo "$B: no census in run"; exit 1; }
fi

python3 js/src/night/tools/blockprof.py "$SD/blk.compile.err" "$SD/blk.run.err" "$@"
