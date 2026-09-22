#!/usr/bin/env bash
# Paired, order-alternating A/B over a bench list.
#
#   pairab.sh <binA> <binB>        BENCHES=... N=... SDROOT=...
#
# `quickperf.sh` runs every rep of arm A and then every rep of arm B, which
# lets any machine drift during the run land entirely on one arm. This
# alternates the order per rep (A,B then B,A) so drift is shared, and reports
# BEST score and MEDIAN instructions per arm plus the B/A ratios.
#
# The score column is what Octane reports (time-budgeted, so higher is more
# work done in the budget); `Mins/score` is instructions per unit of work and
# is the comparable one.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." || exit 1
A=${1:?usage: pairab.sh <binA> <binB>}
B=${2:?}
N=${N:-5}
WASMTIME=${WASMTIME:-$HOME/bin/wasmtime}
NIGHT_JS=obj-nightmonkey/dist/bin/js
MEMCAP=${MEMCAP:-$HOME/bin/memcap}; [ -x "$MEMCAP" ] || MEMCAP=env
SDROOT=${SDROOT:-${TMPDIR:-/tmp}/night-pairab}
mkdir -p "$SDROOT"

med() { sort -n | awk '{a[NR]=$1} END{print (NR%2)?a[(NR+1)/2]:int((a[NR/2]+a[NR/2+1])/2)}'; }

for b in ${BENCHES:?set BENCHES}; do
  SD=$SDROOT/$b; mkdir -p "$SD"
  v=$SD/$b.js
  [ -f "$v" ] || head -n -1 "octane/$b.js" > "$v"
  snap=$SD/$b.snap.wasm
  [ -f "$snap" ] || "$MEMCAP" 32G "$A" --shell "$NIGHT_JS" "$v" --keep-snapshot "$snap" -o /dev/null >/dev/null 2>&1
  for arm in a b; do
    bin=$A; [ "$arm" = b ] && bin=$B
    [ -f "$SD/$arm.cwasm" ] && continue
    "$MEMCAP" 32G "$bin" "$snap" -o "$SD/$arm.wasm" >/dev/null 2>&1 || { echo "$b/$arm: compile failed"; continue 2; }
    "$WASMTIME" compile "$SD/$arm.wasm" -o "$SD/$arm.cwasm" 2>/dev/null
  done
  : > "$SD/a.scores"; : > "$SD/b.scores"; : > "$SD/a.ins"; : > "$SD/b.ins"
  one() { # $1 = arm
    taskset -c 1 perf stat -x, -e instructions -o "$SD/s.txt" -- \
      "$WASMTIME" run --allow-precompiled -W unknown-imports-trap "$SD/$1.cwasm" > "$SD/o.txt" 2>/dev/null
    local s; s=$(grep -oE 'Score.*: [0-9]+' "$SD/o.txt" | grep -oE '[0-9]+$' | tail -1)
    [ -n "$s" ] || return
    echo "$s" >> "$SD/$1.scores"
    awk -F, '$3=="instructions"{print $1}' "$SD/s.txt" >> "$SD/$1.ins"
  }
  for i in $(seq "$N"); do
    if [ $((i % 2)) = 1 ]; then one a; one b; else one b; one a; fi
  done
  as=$(sort -n < "$SD/a.scores" | tail -1); bs=$(sort -n < "$SD/b.scores" | tail -1)
  ai=$(med < "$SD/a.ins"); bi=$(med < "$SD/b.ins")
  [ -n "$as" ] && [ -n "$bs" ] || { echo "$b: no score"; continue; }
  printf '%-14s score A %-7s B %-7s  ratio %.4f   Mins/score A %8.3f B %8.3f  ratio %.4f\n' \
    "$b" "$as" "$bs" "$(echo "$bs/$as" | bc -l)" \
    "$(echo "$ai/1000000/$as" | bc -l)" "$(echo "$bi/1000000/$bs" | bc -l)" \
    "$(echo "($bi/$bs)/($ai/$as)" | bc -l)"
done
