#!/usr/bin/env bash
# excensus-env.sh <variant> ["benches"]: excensus.sh honoring the variant's env/pipe.
set -uo pipefail
ROOT=/home/cfallin/work/nightmonkey-mir; SK=$ROOT/.claude/skills/nm-bench
. $SK/lib.sh
v=$1; d=$W/v/$v; mkdir -p $W/census
for b in ${2:-$ALL_BENCHES}; do
  ( o=$W/census/$v-$b
    [ -f $d/env ] && set -a && . $d/env && set +a
    "$d/nightmonkey" --shell "$d/js" "$W/src/$b.js" -o "$o.wasm" --mir-exit-census > "$o.map" 2>&1
    "$WASMTIME" run --dir / "$o.wasm" > "$o.out" 2>&1
    python3 "$SK/census.py" "$o.out" "$o.map" 8 > "$o.txt"
    rm -f "$o.wasm" ) &
done
wait
for b in ${2:-$ALL_BENCHES}; do printf "%-10s %-14s %s\n" "$v" "$b" "$(head -1 "$W/census/$v-$b.txt")"; done
