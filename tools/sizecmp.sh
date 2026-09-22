#!/usr/bin/env bash
# Static size/shape comparison of two compiler binaries over a directory of
# Octane snapshots (`<bench>.wasm`, made with `nightmonkey --keep-snapshot`):
# emitted module bytes, and the compile time that produced them.
#
#   NIGHT_FIXTURES=<dir> sizecmp.sh <baseline-binary> [<now-binary>]
set -uo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
NIGHT=$(dirname "$here")
FIXTURES=${NIGHT_FIXTURES:-$HOME/.cache/night-fixtures}
BASE=${1:?usage: sizecmp.sh <baseline> [now]}
NOW=${2:-$NIGHT/nightmonkey/target/release/nightmonkey}
BENCHES=${BENCHES:-richards crypto deltablue raytrace navier-stokes regexp box2d}
out=$(mktemp -d "${TMPDIR:-/tmp}/night-size.XXXXXX")
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
rm -rf "$out"
