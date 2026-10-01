#!/usr/bin/env bash
# MIR exit census: how often each exit to baseline fires, per bench. An
# exit that fires on every execution (an "exit storm") passes every test
# and only moves scores.
#
#   excensus.sh <variant> ["benches"]    (variant as in ab.sh: $W/v/<name>)
#
# Writes $W/census/<variant>-<bench>.txt: "exits total N", then the top
# sites. Compare totals against a baseline variant's census.
set -uo pipefail
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"
HERE=$(dirname "${BASH_SOURCE[0]}")
v=${1:?usage: excensus.sh <variant> [benches]}; d=$W/v/$v
mkdir -p "$W/census"
for b in ${2:-$ALL_BENCHES}; do
  prep_src "$b" || exit 1
  ( o=$W/census/$v-$b
    "$d/nightmonkey" --shell "$d/js" "$W/src/$b.js" -o "$o.wasm" --mir-exit-census > "$o.map" 2>&1
    "$WASMTIME" run --dir / "$o.wasm" > "$o.out" 2>&1
    python3 "$HERE/census.py" "$o.out" "$o.map" 8 > "$o.txt"
    rm -f "$o.wasm" ) &
done
wait
for b in ${2:-$ALL_BENCHES}; do printf "%-14s %s\n" "$b" "$(head -1 "$W/census/$v-$b.txt")"; done
