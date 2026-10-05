#!/usr/bin/env bash
# Variant table: A/B several COMPILER binaries against each other from ONE
# snapshot set: build once, run
# interleaved with fresh-copy cwasm under taskset -c 1, and never compile
# during a measurement.
#
#   VARIANTS="base:/path/to/nm.base new:/path/to/nm.new" tools/var-table.sh build
#   OUT=<dir printed by build> VARIANTS=... tools/var-table.sh run [reps]
#
# `build` makes a fresh OUT in /tmp (or uses $OUT) and prints it; `run` needs
# it. Snapshots come from $SNAPS (`<bench>.snap.wasm`) if set, else the first
# variant wizens bench/octane with build/bin/js into $OUT/snaps.
#
# (This script A/Bs COMPILER BINARIES, e.g. base vs patched nightmonkey
# builds, each with its default pipeline.)
set -u
ROOT=$(git -C "$(dirname "${BASH_SOURCE[0]}")" rev-parse --show-toplevel) && cd "$ROOT" || exit 1
BENCHES=${BENCHES:-"richards deltablue crypto raytrace earley-boyer navier-stokes splay regexp pdfjs mandreel code-load box2d"}
VARIANTS=${VARIANTS:?set VARIANTS="name:/path/to/nightmonkey ..."}

case "${1:-run}" in
build)
  OUT=${OUT:-$(mktemp -d /tmp/night-vartable.XXXXXX)}; mkdir -p "$OUT"
  if [ -z "${SNAPS:-}" ]; then
    SNAPS=$OUT/snaps; mkdir -p "$SNAPS"
    first=${VARIANTS%% *}; first=${first#*:}
  fi
  for b in $BENCHES; do
    snap="$SNAPS/$b.snap.wasm"
    if [ ! -f "$snap" ] && [ -n "${first:-}" ]; then
      head -n -1 "bench/octane/$b.js" > "$SNAPS/$b.js"
      tools/memcap 32G "$first" --shell build/bin/js "$SNAPS/$b.js" \
        --keep-snapshot "$snap" -o /dev/null >/dev/null 2>&1
    fi
    [ -f "$snap" ] || { echo "NO-SNAP $b"; continue; }
    for v in $VARIANTS; do
      name=${v%%:*}; bin=${v#*:}
      [ -f "$OUT/$b.$name.cwasm" ] && continue
      "$bin" "$snap" -o "$OUT/$b.$name.wasm" 2>/dev/null \
        || { echo "AOT-FAIL $b $name"; continue; }
      wasmtime compile "$OUT/$b.$name.wasm" -o "$OUT/$b.$name.cwasm" \
        2>/dev/null || { echo "COMPILE-FAIL $b $name"; continue; }
      echo "built $b $name"
    done
  done
  echo "OUT=$OUT"
  ;;
run)
  reps=${2:-3}
  cd "${OUT:?set OUT to the directory var-table.sh build printed}" || exit 1
  for _ in $(seq 1 "$reps"); do
    for b in $BENCHES; do
      for v in $VARIANTS; do
        name=${v%%:*}
        [ -f "$b.$name.cwasm" ] || { echo "$b $name MISSING"; continue; }
        cp "$b.$name.cwasm" run.tmp.cwasm
        s=$(taskset -c 1 wasmtime run --allow-precompiled \
              -W unknown-imports-trap run.tmp.cwasm 2>/dev/null \
            | grep -oE 'Score.*: [0-9]+' | grep -oE '[0-9]+$' | tail -1)
        echo "$b $name ${s:-FAIL}"
        rm -f run.tmp.cwasm
      done
    done
  done
  ;;
esac
