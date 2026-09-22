#!/usr/bin/env bash
# One-bench instruction-count A/B for two compiler binaries: the fast loop
# for diagnosing a design step's cost. `metrics.sh` is the full three-axis
# read; this is the bisector you run twenty times.
#
#   quickperf.sh <bench> <binA> [<binB>]     # default binB = the cargo build
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." || exit 1
B=${1:?usage: quickperf.sh <bench> <binA> [binB]}
A=${2:?}
C=${3:-js/src/night/nightmonkey/target/release/nightmonkey}
N=${N:-3}
WASMTIME=${WASMTIME:-$HOME/bin/wasmtime}
NIGHT_JS=obj-nightmonkey/dist/bin/js
MEMCAP=${MEMCAP:-$HOME/bin/memcap}; [ -x "$MEMCAP" ] || MEMCAP=env
SD=${SD:-$(mktemp -d)}; mkdir -p "$SD"
v=$SD/$B.js
[ -f "$v" ] || head -n -1 "octane/$B.js" > "$v"
snap=$SD/$B.snap.wasm
[ -f "$snap" ] || "$MEMCAP" 32G "$A" --shell "$NIGHT_JS" "$v" --keep-snapshot "$snap" -o /dev/null >/dev/null 2>&1
run() { # $1=label $2=binary
  local out=$SD/$1.wasm
  "$MEMCAP" 32G "$2" "$snap" -o "$out" >/dev/null 2>&1 || { echo "$1: compile failed"; return; }
  "$WASMTIME" compile "$out" -o "$SD/$1.cwasm" 2>/dev/null
  local best="" bins="" bcyc=""
  for _ in $(seq "$N"); do
    taskset -c 1 perf stat -x, -e instructions,cycles -o "$SD/s.txt" -- \
      "$WASMTIME" run --allow-precompiled -W unknown-imports-trap "$SD/$1.cwasm" > "$SD/o.txt" 2>/dev/null
    local s; s=$(grep -oE 'Score.*: [0-9]+' "$SD/o.txt" | grep -oE '[0-9]+$' | tail -1)
    [ -n "$s" ] || continue
    local ins cyc
    ins=$(awk -F, '$3=="instructions"{print $1}' "$SD/s.txt")
    cyc=$(awk -F, '$3=="cycles"{print $1}' "$SD/s.txt")
    if [ -z "$best" ] || [ "$s" -gt "$best" ]; then best=$s; bins=$ins; bcyc=$cyc; fi
  done
  [ -n "$best" ] || { echo "$1: no score"; return; }
  printf '%-6s score %-8s bytes %-10s Mins/score %8.3f  ins %14s  IPC %.2f\n' "$1" "$best" \
    "$(stat -c%s "$out")" "$(echo "$bins/1e6/$best" | bc -l)" "$bins" \
    "$(echo "$bins/$bcyc" | bc -l)"
}
run base "$A"
run now  "$C"
