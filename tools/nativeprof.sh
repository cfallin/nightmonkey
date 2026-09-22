#!/usr/bin/env bash
# Per-function EXECUTED NATIVE profile, A/B, normalised per score point.
#
#   nativeprof.sh <bench> <binA> [<binB>]
#
# The gap this closes: every other instrument in this tree counts emitted or
# executed *IR*. When the IR gets smaller and the machine gets slower, none
# of them can say where the extra
# native instructions are. This can: `--keep-names` puts `night_script_<sid>`
# in the module, wasmtime's `--profile=perfmap` publishes the compiled
# addresses, and perf attributes samples to the script.
#
# Columns are millions of instructions per score point, so the two arms are
# comparable even though Octane is time-budgeted and the arms complete
# different iteration counts.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." || exit 1
B=${1:?usage: nativeprof.sh <bench> <binA> [binB]}
A=${2:?}
C=${3:-js/src/night/nightmonkey/target/release/nightmonkey}
WASMTIME=${WASMTIME:-$HOME/bin/wasmtime}
NIGHT_JS=obj-nightmonkey/dist/bin/js
MEMCAP=${MEMCAP:-$HOME/bin/memcap}; [ -x "$MEMCAP" ] || MEMCAP=env
SD=${SD:-$(mktemp -d)}; mkdir -p "$SD"
CPU=${CPU:-1}
N=${N:-3}

v=$SD/$B.js
[ -f "$v" ] || head -n -1 "octane/$B.js" > "$v"
snap=$SD/$B.snap.wasm
[ -f "$snap" ] || "$MEMCAP" 32G "$A" --shell "$NIGHT_JS" "$v" --keep-snapshot "$snap" -o /dev/null >/dev/null 2>&1

run() { # $1=label $2=binary -> $SD/$1.prof of "share symbol"
  local out=$SD/$1.wasm
  "$MEMCAP" 32G "$2" "$snap" -o "$out" --keep-names >/dev/null 2>&1 || { echo "$1: compile failed" >&2; return 1; }
  "$WASMTIME" compile "$out" -o "$SD/$1.cwasm" 2>/dev/null
  local best=0
  for i in $(seq "$N"); do
    taskset -c "$CPU" perf record -q -e instructions:u -c "${PERIOD:-2000000}" -o "$SD/$1.$i.data" -- \
      "$WASMTIME" run --profile=perfmap --allow-precompiled -W unknown-imports-trap "$SD/$1.cwasm" \
      > "$SD/$1.out" 2>/dev/null
    local s; s=$(grep -oE 'Score.*: [0-9]+' "$SD/$1.out" | grep -oE '[0-9]+$' | tail -1)
    [ -n "$s" ] && [ "$s" -gt "$best" ] && { best=$s; cp "$SD/$1.$i.data" "$SD/$1.data"; }
  done
  [ "$best" -gt 0 ] || { echo "$1: no score" >&2; return 1; }
  # perf's own sample count times the period is the instruction total, so the
  # profile is self-normalising and needs no second stat run.
  perf report -q -i "$SD/$1.data" --no-children --sort symbol --percentage absolute 2>/dev/null \
    | sed -E 's/^ *([0-9.]+)% +\[.\] +([^ ]+).*/\1 \2/' \
    | awk -v s="$best" -v p="${PERIOD:-2000000}" -v t="$(perf report -q -i "$SD/$1.data" --stats 2>/dev/null | grep -oE 'SAMPLE events: *[0-9]+' | grep -oE '[0-9]+$')" \
        'NF==2{printf "%s %.4f\n", $2, $1/100*t*p/1e6/s}' \
    | sed -E 's/^wasm\[0\]::function\[[0-9]+\]:://' | sort > "$SD/$1.prof"
  echo "$1 score $best"
}

run base "$A" || exit 1
run now  "$C" || exit 1
echo
printf '%-34s %9s %9s %8s\n' "symbol (Mins per score point)" base now ratio
join -a1 -a2 -e 0 -o 0,1.2,2.2 "$SD/base.prof" "$SD/now.prof" \
  | awk '{d=$3-$2; printf "%-34s %9.4f %9.4f %8s %9.4f\n", substr($1,1,34), $2, $3, ($2>0?sprintf("%.3f",$3/$2):"-"), d}' \
  | sort -k5 -rn | head -"${TOP:-25}"
echo
join -a1 -a2 -e 0 -o 0,1.2,2.2 "$SD/base.prof" "$SD/now.prof" \
  | awk '{a+=$2;b+=$3} END{printf "TOTAL %.4f -> %.4f  (%.3fx)\n",a,b,b/a}'
