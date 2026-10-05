#!/usr/bin/env bash
# Static size/shape comparison of two compiler binaries over Octane
# snapshots: emitted module bytes, and the compile time that produced them.
#
#   [NIGHT_FIXTURES=<dir>] sizecmp.sh <baseline-binary> [<now-binary>]
#
# NIGHT_FIXTURES holds `<bench>.wasm` snapshots (`nightmonkey
# --keep-snapshot`). Without it, the baseline binary makes them from
# bench/octane with build/bin/js, in the scratch directory.
set -uo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
NIGHT=$(dirname "$here")
BASE=${1:?usage: sizecmp.sh <baseline> [now]}
NOW=${2:-$NIGHT/build/bin/nightmonkey}
BENCHES=${BENCHES:-richards crypto deltablue raytrace navier-stokes regexp box2d}
out=$(mktemp -d /tmp/night-size.XXXXXX)
trap 'rm -rf "$out"' EXIT
FIXTURES=${NIGHT_FIXTURES:-}
if [ -z "$FIXTURES" ]; then
  FIXTURES=$out/fixtures; mkdir -p "$FIXTURES"
  for b in $BENCHES; do
    head -n -1 "$NIGHT/bench/octane/$b.js" > "$FIXTURES/$b.js"
    "$here/memcap" 32G "$BASE" --shell "$NIGHT/build/bin/js" "$FIXTURES/$b.js" \
      --keep-snapshot "$FIXTURES/$b.wasm" -o /dev/null >/dev/null 2>&1 \
      || echo "$b: snapshot FAILED"
  done
fi
printf '%-14s %12s %12s %8s %8s %8s\n' bench base now ratio base_s now_s
for b in $BENCHES; do
  snap=$FIXTURES/$b.wasm
  [ -f "$snap" ] || continue
  t0=$(date +%s.%N)
  "$BASE" "$snap" -o "$out/base.wasm" >/dev/null 2>&1 || { echo "$b base FAILED"; continue; }
  t1=$(date +%s.%N)
  "$NOW" "$snap" -o "$out/now.wasm" >/dev/null 2>&1 || { echo "$b now FAILED"; continue; }
  t2=$(date +%s.%N)
  a=$(stat -c%s "$out/base.wasm"); c=$(stat -c%s "$out/now.wasm")
  printf '%-14s %12d %12d %8.4f %8.1f %8.1f\n' "$b" "$a" "$c" \
    "$(echo "$c/$a" | bc -l)" "$(echo "$t1-$t0" | bc -l)" "$(echo "$t2-$t1" | bc -l)"
done
