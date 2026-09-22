#!/usr/bin/env bash
# Variant table: A/B several COMPILER binaries against each other (and
# against the plain legacy lane) from ONE snapshot set: build once, run
# interleaved with fresh-copy cwasm under taskset -c 1, and never compile
# during a measurement.
#
#   VARIANTS="base:$HOME/tmp/night-w6/nm.base new:$HOME/tmp/night-w6/nm.new" \
#     js/src/night/tools/var-table.sh build
#   ... run [reps]
#
# (Every variant is the BBV lane -- this script A/Bs COMPILER BINARIES, e.g.
# base vs patched nightmonkey builds.)
set -u
cd "$(dirname "$0")/../../../.." || exit 1
OUT=${OUT:-$HOME/tmp/night-w6}
SNAPS=${SNAPS:-$HOME/tmp/night-w5}
WASMTIME=${WASMTIME:-$HOME/bin/wasmtime}
BENCHES=${BENCHES:-"richards deltablue crypto raytrace earley-boyer navier-stokes splay regexp pdfjs mandreel code-load box2d"}
VARIANTS=${VARIANTS:?set VARIANTS="name:/path/to/nightmonkey ..."}
mkdir -p "$OUT"

case "${1:-run}" in
build)
  for b in $BENCHES; do
    snap="$SNAPS/$b.snap.wasm"
    [ -f "$snap" ] || { echo "NO-SNAP $b"; continue; }
    for v in $VARIANTS; do
      name=${v%%:*}; bin=${v#*:}
      [ -f "$OUT/$b.$name.cwasm" ] && continue
      "$bin" "$snap" -o "$OUT/$b.$name.wasm" 2>/dev/null \
        || { echo "AOT-FAIL $b $name"; continue; }
      "$WASMTIME" compile "$OUT/$b.$name.wasm" -o "$OUT/$b.$name.cwasm" \
        2>/dev/null || { echo "COMPILE-FAIL $b $name"; continue; }
      echo "built $b $name"
    done
  done
  ;;
run)
  reps=${2:-3}
  cd "$OUT" || exit 1
  for _ in $(seq 1 "$reps"); do
    for b in $BENCHES; do
      for v in $VARIANTS; do
        name=${v%%:*}
        [ -f "$b.$name.cwasm" ] || { echo "$b $name MISSING"; continue; }
        cp "$b.$name.cwasm" run.tmp.cwasm
        s=$(taskset -c 1 "$WASMTIME" run --allow-precompiled \
              -W unknown-imports-trap run.tmp.cwasm 2>/dev/null \
            | grep -oE 'Score.*: [0-9]+' | grep -oE '[0-9]+$' | tail -1)
        echo "$b $name ${s:-FAIL}"
        rm -f run.tmp.cwasm
      done
    done
  done
  ;;
esac
