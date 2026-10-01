#!/usr/bin/env bash
# The cross-engine table: Octane + react on every lane, best of N, one
# pinned core, then speedup ratios and a geomean row.
#
#   lanes.sh [N]          (N runs per cell, default 3)
#
# Lanes (LANES= picks; default all but aot-legacy):
#   native-ion       system js, full JIT: the ceiling
#   native-baseline  system js --no-ion: baseline interpreter + compiler
#   wasm-interp      SpiderMonkey's C++ interpreter built for wasm32-wasi:
#                    the wasm floor (configs/mozconfig-wasm)
#   weval            weval + PBL over the wizer shell: the peer wasm AOT
#                    (configs/mozconfig-weval)
#   aot              this build, --pipeline mir
#   aot-legacy       this build, --pipeline legacy (BBV)
#
# Every score is Octane's (higher is better; react's harness prints the
# same format), so every ratio column reads "A is Nx faster than B" and
# the geomean row covers all benches.
#
# Env: LANES, BENCHES, CORE (default 10), SYS_JS, WASM_JS, WEVAL_JS, WEVAL,
#      NIGHTMONKEY / NIGHT_JS (default this checkout's build/bin).
set -uo pipefail
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"
N=${1:-3}
LANES=${LANES:-"native-ion native-baseline wasm-interp weval aot"}
BENCHES=${BENCHES:-$ALL_BENCHES}
CORE=${CORE:-10}
SYS_JS=${SYS_JS:-/home/linuxbrew/.linuxbrew/bin/js}
WASM_JS=${WASM_JS:-$HOME/work/firefox/obj-wasm/dist/bin/js}
WEVAL_JS=${WEVAL_JS:-$HOME/work/firefox/obj-weval/dist/bin/js}
WEVAL=${WEVAL:-$HOME/.cargo/bin/weval}
NIGHTMONKEY=${NIGHTMONKEY:-$ROOT/build/bin/nightmonkey}
NIGHT_JS=${NIGHT_JS:-$ROOT/build/bin/js}
RATIO_COLS=${RATIO_COLS:-"aot/wasm-interp aot/weval native-ion/aot native-baseline/aot"}
O=$W/lanes; rm -rf "$O"; mkdir -p "$O"
pin() { taskset -c "$CORE" "$@"; }

# Build (once per lane x bench) what a lane runs; print its path.
module() {
  local lane=$1 b=$2 m=$O/$lane-$b
  [ -f "$m.cwasm" ] && { echo "$m.cwasm"; return; }
  case $lane in
    aot|aot-legacy)
      local p=mir; [ "$lane" = aot-legacy ] && p=legacy
      "$NIGHTMONKEY" --shell "$NIGHT_JS" "$W/src/$b.js" -o "$m.wasm" --pipeline $p >/dev/null 2>&1 || return 1 ;;
    weval)
      # The init function's name has a dot, unlike weval's default.
      "$WEVAL" weval -w --init-func wizer.initialize -i "$WEVAL_JS" -o "$m.wasm" < "$W/src/$b.js" >/dev/null 2>&1 || return 1 ;;
    wasm-interp)
      m=$O/wasm-interp; [ -f "$m.cwasm" ] && { echo "$m.cwasm"; return; }
      cp "$WASM_JS" "$m.wasm" ;;
  esac
  "$WASMTIME" compile "$m.wasm" -o "$m.cwasm" && rm -f "$m.wasm" && echo "$m.cwasm"
}

run1() {
  local lane=$1 b=$2 cw
  case $lane in
    native-ion) pin "$SYS_JS" "$W/src/$b.run.js" ;;
    native-baseline) pin "$SYS_JS" --no-ion "$W/src/$b.run.js" ;;
    *)
      cw=$(module "$lane" "$b") || { echo FAIL; return; }
      # A fresh copy per run: a .cwasm's page layout is worth 2-3%.
      cp "$cw" "$O/run.cwasm"
      if [ "$lane" = wasm-interp ]; then
        # This shell reads the program from stdin.
        pin "$WASMTIME" run --allow-precompiled "$O/run.cwasm" < "$W/src/$b.run.js"
      else
        pin "$WASMTIME" run --allow-precompiled --dir / "$O/run.cwasm"
      fi ;;
  esac 2>/dev/null
}

cell() {
  local best=0 s i
  for i in $(seq "$N"); do
    s=$(run1 "$1" "$2" | score_of)
    [ "${s:-0}" -gt "$best" ] && best=$s
  done
  [ "$best" -gt 0 ] && echo "$best" || echo -
}

num() { [[ "$1" =~ ^[0-9][0-9.]*$ ]]; }
short() { echo "$1" | sed 's/native-ion/ion/g; s/native-baseline/baseline/g; s/wasm-interp/wasm-int/g'; }
gm() { [ -s "$1" ] && awk '{s+=log($1);n++} END{printf "%.*f", '"$2"', exp(s/n)}' "$1" || echo -; }

for b in $BENCHES; do prep_src "$b" || exit 1; done
printf "%-14s" bench
for l in $LANES; do printf "%14s" "$(short "$l")"; done
for r in $RATIO_COLS; do printf "%14s" "$(short "$r")"; done; echo
declare -A CUR
for b in $BENCHES; do
  printf "%-14s" "$b"; CUR=()
  for l in $LANES; do
    v=$(cell "$l" "$b"); CUR[$l]=$v; printf "%14s" "$v"
    num "$v" && echo "$v" >> "$O/gm-$l"
  done
  for r in $RATIO_COLS; do
    a=${CUR[${r%%/*}]:--}; c=${CUR[${r##*/}]:--}
    if num "$a" && num "$c"; then v=$(awk -v x="$a" -v y="$c" 'BEGIN{printf "%.2f", x/y}'); echo "$v" >> "$O/gm-${r//\//_}"; else v=-; fi
    printf "%14s" "$v"
  done; echo
done
printf "%-14s" geomean
for l in $LANES; do printf "%14s" "$(gm "$O/gm-$l" 0)"; done
for r in $RATIO_COLS; do printf "%14s" "$(gm "$O/gm-${r//\//_}" 2)"; done; echo
echo "(Octane scores, higher is better; best of $N on CPU $CORE; ratio = A/B speedup)"
