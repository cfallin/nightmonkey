#!/usr/bin/env bash
# prof.sh <bench> [tag] [nightmonkey js]: profile one benchmark's AOT module.
#
# Compiles $W/src/<bench>.js with --keep-names --dump-tiers (the MIR
# pipeline, or $PIPE), precompiles it, runs it under `perf record -g` on
# CPU ${CPU:-10} at ${FREQ:-4000} Hz, and leaves under $W/prof/<tag>-<bench>:
#   stacks.txt  `perf script` output     tiers.txt  the compile's tier log
# then prints prof.py's summary. Re-run prof.py with --under RE to break a
# helper down. Needs a quiet machine like any timing.
set -euo pipefail
. "$(dirname "$0")/lib.sh"
b=$1; tag=${2:-cur}
NM=${3:-$ROOT/build/bin/nightmonkey}; JS=${4:-$ROOT/build/bin/js}
d=$W/prof/$tag-$b; mkdir -p "$d"
prep_src "$b"
"$NM" --shell "$JS" "$W/src/$b.js" -o "$d/m.wasm" --pipeline "${PIPE:-mir}" \
  --keep-names --dump-tiers > "$d/tiers.txt" 2>&1
"$WASMTIME" compile "$d/m.wasm" -o "$d/m.cwasm"
rm -f "$d/m.wasm"
( cd "$d" && taskset -c "${CPU:-10}" perf record -F "${FREQ:-4000}" -o perf.data -g \
    "$WASMTIME" run --profile=perfmap --allow-precompiled --dir / m.cwasm ) 2>&1 \
  | grep -E 'Score|Error' || true
perf script -i "$d/perf.data" > "$d/stacks.txt" 2>/dev/null
rm -f "$d/perf.data"
python3 "$(dirname "$0")/prof.py" "$d/stacks.txt" --tiers "$d/tiers.txt" --top "${TOP:-25}"
