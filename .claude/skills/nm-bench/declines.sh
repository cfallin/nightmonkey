#!/usr/bin/env bash
# Scripts that silently fell back to baseline: a MIR validator rejection
# ("BUG: invalid MIR") or an op the wasm lowering lacks ("lowering: ...").
# Neither fails a test; both only lower scores. Must print only "total 0".
#
#   declines.sh [<nightmonkey> <js>]     (default: this checkout's build)
set -uo pipefail
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"
NM=${1:-$ROOT/build/bin/nightmonkey}; JS=${2:-$ROOT/build/bin/js}
D=$(mktemp -d)
for b in $ALL_BENCHES; do
  prep_src "$b" || exit 1
  ("$NM" --shell "$JS" "$W/src/$b.js" -o /dev/null --dump-tiers 2>&1 \
    | grep -E 'tier [0-9]+ baseline \[mir: (BUG: invalid MIR|lowering:)' > "$D/$b.txt") &
done
wait
tot=0
for x in "$D"/*.txt; do
  n=$(wc -l < "$x")
  [ "$n" != 0 ] && { echo "$(basename "$x" .txt) $n"; head -2 "$x"; }
  tot=$((tot + n))
done
echo "total $tot"; rm -rf "$D"
