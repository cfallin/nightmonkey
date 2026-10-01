# Shared by the nm-bench scripts: paths, the benchmark list, and the two
# source forms of each benchmark. Source it; do not run it.
#
# Every benchmark defines a global `main()` that runs it and prints
# `Score (version N): S` (higher is better). Two forms:
#   $W/src/<b>.js      main() defined, NOT called. For the snapshot flows
#                      (aot, weval): the top level runs at wizen time, the
#                      resumed snapshot calls main(). A top-level main() call
#                      would also run the benchmark at wizen time: wasted
#                      work, a wizened heap that varies run to run (so the
#                      AOT output does too), and box2d/mandreel's tearDown
#                      breaks the second run.
#   $W/src/<b>.run.js  the same plus a `main();` line, for engines that just
#                      run a file (native js, the wasm interpreter).

ROOT=$(git -C "$(dirname "${BASH_SOURCE[0]}")" rev-parse --show-toplevel)
# Scratch: per-variant binaries, modules, results. Large (a .cwasm is
# ~100 MB); outside the repo.
W=${NM_BENCH_DIR:-$HOME/work/nm-bench}
OCTANE_DIR=${OCTANE_DIR:-$HOME/work/firefox-scratch/octane}
REACT_JS=${REACT_JS:-$HOME/work/nm-mir-scratch/bench/react.js}
WASMTIME=${WASMTIME:-$(command -v wasmtime || echo "$HOME/bin/wasmtime")}
OCTANE="box2d code-load crypto deltablue earley-boyer mandreel navier-stokes pdfjs raytrace regexp richards splay"
ALL_BENCHES="$OCTANE react"

# prep_src <bench>: write both forms under $W/src (idempotent).
prep_src() {
  local b=$1 src
  mkdir -p "$W/src"
  [ -f "$W/src/$b.js" ] && [ -f "$W/src/$b.run.js" ] && return 0
  if [ "$b" = react ]; then src=$REACT_JS; else src=$OCTANE_DIR/$b.js; fi
  [ -f "$src" ] || { echo "nm-bench: no source for $b ($src)" >&2; return 1; }
  # Octane files end with a `main();` line; react's harness defines main()
  # only. Drop a trailing bare call if there is one.
  if [ "$(tail -n 1 "$src" | tr -d '[:space:]')" = "main();" ]; then
    head -n -1 "$src" > "$W/src/$b.js"
  else
    cp "$src" "$W/src/$b.js"
  fi
  { cat "$W/src/$b.js"; echo; echo "main();"; } > "$W/src/$b.run.js"
}

# score_of: the last Octane-style score on stdin.
score_of() { grep -oE 'Score \(version [0-9]+\): [0-9]+' | grep -oE '[0-9]+$' | tail -1; }
