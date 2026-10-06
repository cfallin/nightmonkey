#!/usr/bin/env bash
# abx.sh <label> "<v1> <v2> ..." ["benches"] ["seeds"]
# ab.sh's method (pad seeds, shuffled serial runs, core locks, fresh .cwasm
# copy per run, best of R), plus: a module cache ($W/mc) so a variant's
# modules compile once across batches, and results kept per label in
# $W/res/<label>.txt.
set -uo pipefail
ROOT=/home/cfallin/work/nightmonkey-mir
. "$ROOT/.claude/skills/nm-bench/lib.sh"
label=$1 variants=$2 benches=${3:-$ALL_BENCHES} seeds=${4:-"1 2 3 4"}
for b in $benches; do prep_src "$b" || exit 1; done
O=$W/abx/$label; L=$W/abx-locks; MC=$W/mc
mkdir -p "$O" "$L" "$MC" "$W/res"; rm -rf "$L"/*
export W O L MC WASMTIME CORES=${CORES:-"2 10"} R=${R:-2}
jobs=()
for b in $benches; do for sd in $seeds; do for v in $variants; do jobs+=("$v $b $sd"); done; done; done
compile() {
  local v=$1 b=$2 sd=$3 d=$W/v/$1 p=mir m=$MC/$1-$2-$3
  [ -f "$m.cwasm" ] && return 0
  [ -f "$d/pipe" ] && p=$(cat "$d/pipe")
  (
    [ -f "$d/env" ] && set -a && . "$d/env" && set +a
    NIGHT_PAD_SEED=$sd ~/bin/memcap 20G timeout 900 "$d/nightmonkey" --shell "$d/js" "$W/src/$b.js" -o "$m.wasm" --pipeline "$p" >/dev/null 2>&1
  ) && ~/bin/memcap 20G "$WASMTIME" compile "$m.wasm" -o "$m.tmp.cwasm" && mv "$m.tmp.cwasm" "$m.cwasm" && rm -f "$m.wasm" \
    || echo "compile failed: $v $b $sd" >&2
}
run() {
  local v=$1 b=$2 sd=$3 cpu= s=0 t r
  while [ -z "$cpu" ]; do
    for c in $CORES; do mkdir "$L/$c" 2>/dev/null && { cpu=$c; break; }; done
    [ -z "$cpu" ] && sleep 0.2
  done
  for r in $(seq "$R"); do
    cp "$MC/$v-$b-$sd.cwasm" "$O/run-$cpu.cwasm"
    t=$(taskset -c "$cpu" "$WASMTIME" run --allow-precompiled --dir / "$O/run-$cpu.cwasm" 2>/dev/null | score_of)
    [ "${t:-0}" -gt "$s" ] && s=$t
  done
  rm -f "$O/run-$cpu.cwasm"; rmdir "$L/$cpu"
  echo "$v $b $sd $s $cpu"
}
export -f compile run score_of
t0=$(date +%s)
printf '%s\n' "${jobs[@]}" | xargs -P "${CPAR:-6}" -L 1 bash -c 'compile $0 $1 $2'
t1=$(date +%s)
printf '%s\n' "${jobs[@]}" | shuf | xargs -P "${PAR:-2}" -L 1 bash -c 'run $0 $1 $2' > "$O/results5.txt"
t2=$(date +%s)
cut -d' ' -f1-4 "$O/results5.txt" > "$W/res/$label.txt"
cp "$O/results5.txt" "$W/res/$label.cpu.txt"
echo "compile $((t1-t0))s run $((t2-t1))s" > "$W/res/$label.time"
python3 "$ROOT/.claude/skills/nm-bench/robust.py" "$W/res/$label.txt" "$(echo $variants | tr ' ' ,)" > "$W/res/$label.robust"
