#!/usr/bin/env bash
# After the A/B queue: cross-engine lanes, then base-build censuses for the
# "what's left" analysis. Memory-safe: small parallel groups (a mandreel
# compile peaks ~9 GB + ~8.5 GB for wasmtime compile).
set -uo pipefail
ROOT=/home/cfallin/work/nightmonkey-mir
SK=$ROOT/.claude/skills/nm-bench
W=~/.cache/nm-bench
NM=$W/v/base/nightmonkey JS=$W/v/base/js
echo "== lanes $(date)"
LANES="native-ion native-baseline wasm-interp weval aot" \
  WASM_JS=~/work/firefox/obj-wasm/dist/bin/js WEVAL_JS=~/work/firefox/obj-weval/dist/bin/js \
  NIGHTMONKEY=$NM NIGHT_JS=$JS CORE=10 \
  $SK/lanes.sh 3 > $W/res/lanes.txt 2>&1
echo "== vcensus $(date)"
for g in "box2d code-load crypto deltablue" "earley-boyer navier-stokes raytrace regexp" "richards splay pdfjs" "mandreel"; do
  XFLAGS=--dump-propgap $SK/vcensus.sh base "$g" $NM $JS >> $W/res/vcensus-base.txt 2>&1
done
echo "== prof $(date)"
benches="box2d code-load crypto deltablue earley-boyer mandreel navier-stokes pdfjs raytrace regexp richards splay react"
printf '%s\n' $benches | xargs -P 3 -I{} bash -c '
  b={}; for c in 2 6 10; do mkdir '$W'/proflock-$c 2>/dev/null && break; done
  CPU=$c '$SK'/prof.sh $b base '$NM' '$JS' > '$W'/res/prof-base-$b.txt 2>&1
  rmdir '$W'/proflock-$c'
echo "== done $(date)"
