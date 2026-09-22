#!/usr/bin/env bash
# quickperf's sibling for the counters quickperf cannot see.
#
#   machperf.sh <bench> <binA> [<binB>]
#
# Either arm may be the literal `ion`, which selects the native lane: the
# system js on the FULL octane file, no wizer and no wasmtime. That is the
# ceiling, and it is the only way to read the AOT tier's instruction mix
# against Ion's. Everything is per score point for the reason below, which is
# also why a cross-compiler comparison may be read here and nowhere else:
# `nat/op` and anything else per-op is not comparable across compilers.
#
# `Mins/score` and IPC named richards' 1.18x as microarchitectural: the tier
# executes 18% more instructions for 31% more cycles. This reports what the
# machine was doing in those cycles -- branch prediction, instruction fetch,
# data fetch -- each normalised per score point, because Octane is
# time-budgeted and a raw count is a statement about the clock.
#
# Two perf groups per rep: this box schedules at most five of these events at
# once, and a sixth reads <not counted> silently. Both groups carry
# instructions and cycles so a mispaired rep is visible rather than averaged in.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." || exit 1
B=${1:?usage: machperf.sh <bench> <binA> [binB]}
A=${2:?}
C=${3:-js/src/night/nightmonkey/target/release/nightmonkey}
N=${N:-3}
WASMTIME=${WASMTIME:-$HOME/bin/wasmtime}
SYS_JS=${SYS_JS:-/home/linuxbrew/.linuxbrew/bin/js}
NIGHT_JS=obj-nightmonkey/dist/bin/js
MEMCAP=${MEMCAP:-$HOME/bin/memcap}; [ -x "$MEMCAP" ] || MEMCAP=env
SD=${SD:-$(mktemp -d)}; mkdir -p "$SD"
CPU=${CPU:-1}

GA=${GA:-instructions,cycles,branches,branch-misses,L1-icache-load-misses}
GB=${GB:-instructions,cycles,L1-dcache-load-misses,iTLB-load-misses,cache-misses}

# The wizer variant drops the driver's trailing invocation; the native lane
# wants the file whole.
v=$SD/$B.js
snap=$SD/$B.snap.wasm
if [ "$A" != ion ] || [ "$C" != ion ]; then
  [ -f "$v" ] || head -n -1 "octane/$B.js" > "$v"
  aotbin=$A; [ "$aotbin" = ion ] && aotbin=$C
  [ -f "$snap" ] || "$MEMCAP" 32G "$aotbin" --shell "$NIGHT_JS" "$v" --keep-snapshot "$snap" -o /dev/null >/dev/null 2>&1
fi

# The third, fourth and fifth slot of each group are whatever the caller asked
# for, so a hypothesis gets its own counters without a new script.
IFS=, read -r _ _ E1 E2 E3 <<<"$GA"
IFS=, read -r _ _ E4 E5 E6 <<<"$GB"

ev() { awk -F, -v k="$2" '$3==k{print ($1=="<not counted>")?"":$1}' "$1"; }

one() { # $1=events $2=statfile $3..=the command -> prints score
  local ev=$1 sf=$2; shift 2
  taskset -c "$CPU" perf stat -x, -e "$ev" -o "$sf" -- "$@" > "$SD/o.txt" 2>/dev/null
  grep -oE 'Score.*: [0-9]+' "$SD/o.txt" | grep -oE '[0-9]+$' | tail -1
}

run() { # $1=label $2=binary, or the literal `ion` for the native lane
  local -a cmd
  if [ "$2" = ion ]; then
    [ -x "$SYS_JS" ] || { echo "$1: no SYS_JS at $SYS_JS"; return; }
    cmd=("$SYS_JS" "octane/$B.js")
  else
    local out=$SD/$1.wasm
    "$MEMCAP" 32G "$2" "$snap" -o "$out" >/dev/null 2>&1 || { echo "$1: compile failed"; return; }
    "$WASMTIME" compile "$out" -o "$SD/$1.cwasm" 2>/dev/null
    cmd=("$WASMTIME" run --allow-precompiled -W unknown-imports-trap "$SD/$1.cwasm")
  fi
  local best=0 f
  for i in $(seq "$N"); do
    local sa sb
    sa=$(one "$GA" "$SD/$1.a$i.txt" "${cmd[@]}"); sb=$(one "$GB" "$SD/$1.b$i.txt" "${cmd[@]}")
    [ -n "$sa" ] && [ -n "$sb" ] || continue
    # Pair the two groups on the arithmetic mean of their scores; a rep whose
    # halves disagree by more than 5% saw contention and is not a measurement.
    local d; d=$(echo "($sa-$sb)/(($sa+$sb)/2)" | bc -l)
    d=${d#-}
    if (( $(echo "$d > 0.05" | bc -l) )); then continue; fi
    local s=$(( (sa + sb) / 2 ))
    if [ "$s" -gt "$best" ]; then best=$s; f=$i; fi
  done
  [ "$best" -gt 0 ] || { echo "$1: no paired rep"; return; }
  local ins cyc br bm ic dc it cm
  ins=$(ev "$SD/$1.a$f.txt" instructions); cyc=$(ev "$SD/$1.a$f.txt" cycles)
  br=$(ev "$SD/$1.a$f.txt" "$E1");         bm=$(ev "$SD/$1.a$f.txt" "$E2")
  ic=$(ev "$SD/$1.a$f.txt" "$E3"); dc=$(ev "$SD/$1.b$f.txt" "$E4")
  it=$(ev "$SD/$1.b$f.txt" "$E5"); cm=$(ev "$SD/$1.b$f.txt" "$E6")
  : "${ic:=0}" "${dc:=0}" "${it:=0}" "${cm:=0}"
  # Per score point in millions, except the two rates.
  printf '%-5s score %-7s Mins/s %7.3f Mcyc/s %7.3f IPC %.2f | %s/Kins %6.2f M%s/s %7.3f | M%s/s %7.3f M%s/s %7.3f K%s/s %8.3f M%s/s %7.3f\n' \
    "$1" "$best" \
    "$(echo "$ins/1000000/$best" | bc -l)" "$(echo "$cyc/1000000/$best" | bc -l)" \
    "$(echo "$ins/$cyc" | bc -l)" \
    "$E2" "$(echo "1000*$bm/$ins" | bc -l)" "$E1" "$(echo "$br/1000000/$best" | bc -l)" \
    "$E3" "$(echo "$ic/1000000/$best" | bc -l)" "$E4" "$(echo "$dc/1000000/$best" | bc -l)" \
    "$E5" "$(echo "$it/1000/$best" | bc -l)" "$E6" "$(echo "$cm/1000000/$best" | bc -l)"
}
run base "$A"
run now  "$C"
