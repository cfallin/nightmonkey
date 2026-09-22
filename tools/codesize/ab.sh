#!/usr/bin/env bash
# A/B two sets of cwasm artifacts. Alternates arm order per rep (fixed order
# gives the first arm ~+0.6% on byte-identical pairs). Best-of-N per arm.
set -u
cd "$(git rev-parse --show-toplevel)"
WT=$HOME/bin/wasmtime
N=${N:-3}
A_DIR=${A_DIR:?set A_DIR to the baseline artifact dir}     # <bench>.cwasm
B_DIR=${B_DIR:-/tmp}                    # candidate: new-<bench>.cwasm
B_PRE=${B_PRE:-new-}
BENCHES=${BENCHES:-"richards deltablue crypto raytrace earley-boyer navier-stokes splay regexp pdfjs mandreel code-load box2d"}
run() { cp "$1" /tmp/ab.run.cwasm; taskset -c 1 $WT run --allow-precompiled -W unknown-imports-trap /tmp/ab.run.cwasm 2>/dev/null | grep -oE 'Score.*: [0-9]+' | grep -oE '[0-9]+$' | tail -1; }
printf "%-14s %10s %10s %8s\n" bench A B "B/A"
tot=0; n=0
for b in $BENCHES; do
  fa="$A_DIR/$b.cwasm"; fb="$B_DIR/$B_PRE$b.cwasm"
  [ -f "$fa" ] && [ -f "$fb" ] || { printf "%-14s %10s\n" "$b" "MISSING"; continue; }
  besta=0; bestb=0
  for i in $(seq 1 $N); do
    if [ $((i % 2)) -eq 1 ]; then x=$(run "$fa"); y=$(run "$fb"); else y=$(run "$fb"); x=$(run "$fa"); fi
    [ -n "$x" ] && [ "$x" -gt "$besta" ] && besta=$x
    [ -n "$y" ] && [ "$y" -gt "$bestb" ] && bestb=$y
  done
  r=$(python3 -c "print(f'{$bestb/max($besta,1):.4f}')")
  printf "%-14s %10d %10d %8s\n" "$b" "$besta" "$bestb" "$r"
  tot=$(python3 -c "import math;print($tot+math.log(max($r,1e-9)))"); n=$((n+1))
done
[ $n -gt 0 ] && printf "%-14s %10s %10s %8s\n" geomean "" "" "$(python3 -c "import math;print(f'{math.exp($tot/$n):.4f}')")"
