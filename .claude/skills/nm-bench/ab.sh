#!/usr/bin/env bash
# A/B NightMonkey builds on Octane + react.
#
#   ab.sh snap <name>                       copy build/bin/{nightmonkey,js}
#                                           to $W/v/<name>
#   ab.sh run "<v1> <v2> ..." ["benches"] ["seeds"]
#
# A variant is a directory $W/v/<name>/ holding `nightmonkey` and `js` (the
# wasm shell carries the runtime, so a runtime change needs its own), and
# optionally `pipe` (the --pipeline, default mir) and `env` (lines of
# VAR=value exported to the compile).
#
# Phase 1 (parallel, CPAR jobs): per variant x bench x seed, AOT-compile with
# NIGHT_PAD_SEED=<seed> (code placement moves scores by up to 15%; seeds
# give placement medians), then `wasmtime compile` to a .cwasm.
# Phase 2 (serial by default): run each module R times (best of R) pinned
# to one core from CORES, in shuffled order, from a fresh copy of the
# .cwasm each time (its page layout is worth a stable 2-3%). Then
# robust.py prints per-bench medians (scores under 80% of the variant's
# own median dropped and counted) and each variant relative to the first.
#
# Env: CPAR (default 6), PAR (default 1), CORES (default "10"), R (default 2).
# Keep the machine quiet through phase 2: no lanes, builds or other jobs,
# and nothing on the SMT sibling (CPU N+16) of a CORES entry.
set -uo pipefail
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"
HERE=$(dirname "${BASH_SOURCE[0]}")

case "${1:-}" in
  snap)
    n=${2:?usage: ab.sh snap <name>}
    mkdir -p "$W/v/$n"
    cp "$ROOT/build/bin/nightmonkey" "$ROOT/build/bin/js" "$W/v/$n/"
    echo "snapped $W/v/$n ($(git -C "$ROOT" rev-parse --short HEAD)$(git -C "$ROOT" diff --quiet || echo +dirty))"
    exit 0
    ;;
  run) shift ;;
  *) sed -n '2,25p' "$0"; exit 2 ;;
esac

variants=${1:?variants}; benches=${2:-$ALL_BENCHES}; seeds=${3:-"1 2 3 4"}
for v in $variants; do
  [ -x "$W/v/$v/nightmonkey" ] && [ -f "$W/v/$v/js" ] || { echo "no variant $W/v/$v" >&2; exit 1; }
done
for b in $benches; do prep_src "$b" || exit 1; done
O=$W/ab; L=$O/locks
rm -rf "$O"; mkdir -p "$O/m" "$L"
export W O L WASMTIME CORES=${CORES:-10} R=${R:-2}

jobs=()
for b in $benches; do for sd in $seeds; do for v in $variants; do jobs+=("$v $b $sd"); done; done; done

compile() {
  local v=$1 b=$2 sd=$3 d=$W/v/$1 p=mir m=$O/m/$1-$2-$3
  [ -f "$d/pipe" ] && p=$(cat "$d/pipe")
  (
    [ -f "$d/env" ] && set -a && . "$d/env" && set +a
    NIGHT_PAD_SEED=$sd "$d/nightmonkey" --shell "$d/js" "$W/src/$b.js" -o "$m.wasm" --pipeline "$p" >/dev/null 2>&1
  ) && "$WASMTIME" compile "$m.wasm" -o "$m.cwasm" && rm -f "$m.wasm" \
    || echo "compile failed: $v $b $sd" >&2
}
run() {
  local v=$1 b=$2 sd=$3 cpu= s=0 t r
  while [ -z "$cpu" ]; do
    for c in $CORES; do mkdir "$L/$c" 2>/dev/null && { cpu=$c; break; }; done
    [ -z "$cpu" ] && sleep 0.2
  done
  for r in $(seq "$R"); do
    cp "$O/m/$v-$b-$sd.cwasm" "$O/m/run-$cpu.cwasm"
    t=$(taskset -c "$cpu" "$WASMTIME" run --allow-precompiled --dir / "$O/m/run-$cpu.cwasm" 2>/dev/null | score_of)
    [ "${t:-0}" -gt "$s" ] && s=$t
  done
  rm -f "$O/m/run-$cpu.cwasm"; rmdir "$L/$cpu"
  echo "$v $b $sd $s"
}
export -f compile run score_of

printf '%s\n' "${jobs[@]}" | xargs -P "${CPAR:-6}" -L 1 bash -c 'compile $0 $1 $2'
printf '%s\n' "${jobs[@]}" | shuf | xargs -P "${PAR:-1}" -L 1 bash -c 'run $0 $1 $2' > "$O/results.txt"
python3 "$HERE/robust.py" "$O/results.txt" "$(echo $variants | tr ' ' ,)"
