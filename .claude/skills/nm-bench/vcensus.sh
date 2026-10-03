#!/usr/bin/env bash
# Fixed-work value census (`--value-census`): executed Wasm values by MIR
# op, for builds to compare by total, not just by share.
#
#   vcensus.sh <tag> "<benches>" [nightmonkey js]    (default: this checkout's build)
#
# Octane normally runs each benchmark for a fixed time, so a faster build
# does more iterations and a census's totals grow with speed. Here the
# source runs Octane's deterministic mode instead (warmup off, each
# benchmark's `deterministicIterations` divided by $DIV, default 20), so
# the same work runs in every build. Octane only (react has no such mode).
#
# XFLAGS adds compile flags (`--dump-propgap` for propw.py).
#
# Writes $W/vcensus/<tag>-<bench>.{map,out,txt}; prints each bench's total
# and top ops. `valcen.py` and `propw.py` read the .out/.map pairs.
set -uo pipefail
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"
HERE=$(dirname "${BASH_SOURCE[0]}")
tag=${1:?usage: vcensus.sh <tag> "<benches>" [nightmonkey js]}
benches=${2:-$OCTANE}
NM=${3:-$ROOT/build/bin/nightmonkey}; JS=${4:-$ROOT/build/bin/js}
DIV=${DIV:-20}
mkdir -p "$W/vcensus"
for b in $benches; do
  prep_src "$b" || exit 1
  src=$W/vcensus/$b.census.js
  { cat "$W/src/$b.js"; cat <<EOF

BenchmarkSuite.config.doWarmup = false;
BenchmarkSuite.config.doDeterministic = true;
for (var vcS = 0; vcS < BenchmarkSuite.suites.length; vcS++) {
  var vcB = BenchmarkSuite.suites[vcS].benchmarks;
  for (var vcI = 0; vcI < vcB.length; vcI++)
    vcB[vcI].deterministicIterations = Math.max(1, Math.round(vcB[vcI].deterministicIterations / $DIV));
}
EOF
  } > "$src"
  ( o=$W/vcensus/$tag-$b
    "$NM" --shell "$JS" "$src" -o "$o.wasm" --value-census ${XFLAGS:-} > "$o.map" 2>&1
    "$WASMTIME" run --dir / "$o.wasm" > "$o.out" 2>&1
    python3 "$HERE/valcen.py" "$o.out" "$o.map" --top 12 > "$o.txt"
    rm -f "$o.wasm" ) &
done
wait
for b in $benches; do echo "== $b"; head -13 "$W/vcensus/$tag-$b.txt"; done
