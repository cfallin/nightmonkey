#!/usr/bin/env bash
# TRUE native instructions per executed bytecode op, from two runs doing
# IDENTICAL work.
#
#   natop.sh <bench> [<binary>]        ITERS=<n>  SD=<dir>
#
# Why this exists. `aot-metrics` reports `nat/op` as
#
#     instructions (from the PRODUCTION perf run) / entries (from the CENSUS run)
#
# and Octane's loop is `for (i = 0; elapsed < 1000; i++)`, with the score
# derived from `usec = elapsed / runs` -- time PER ITERATION. So the score
# measures speed and the work done is whatever fits the budget. The `--census`
# artifact is 16-61x slower depending on the bench, completes correspondingly
# less work, and its entry count therefore does not describe the production
# run at all: the reported absolute is inflated by roughly that factor
# (tens of times too high).
#
# The ratio of two ARMS' `nat/op` stays sound -- both arms are slowed alike --
# which is why it has been useful and why the error went unnoticed. Only the
# absolute is wrong, and only the absolute answers "how good is our code".
#
# The fix is to pin the iteration count: `doDeterministic` makes both runs
# execute exactly `deterministicIterations` (plus an equal warmup pass), so
# instructions and entries describe the same work and their ratio is exact.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." || exit 1
B=${1:?usage: natop.sh <bench> [binary]}
NM=${2:-js/src/night/nightmonkey/target/release/nightmonkey}
WASMTIME=${WASMTIME:-$HOME/bin/wasmtime}
NIGHT_JS=obj-nightmonkey/dist/bin/js
MEMCAP=${MEMCAP:-$HOME/bin/memcap}; [ -x "$MEMCAP" ] || MEMCAP=env
SD=${SD:-${TMPDIR:-/tmp}/night-natop}/$B; mkdir -p "$SD"
CPU=${CPU:-1}
# A run that does not finish in this many seconds is a hang, not work; the
# whole pair is sized to finish in well under a minute per bench.
RUN_TIMEOUT=${RUN_TIMEOUT:-300}

v=$SD/$B.js
if [ ! -f "$v" ]; then
  head -n -1 "octane/$B.js" > "$v"
  # Pin the iteration count. ITERS overrides the benchmark's own
  # deterministicIterations so a slow census build stays affordable; the two
  # runs only have to agree with EACH OTHER.
  {
    echo 'BenchmarkSuite.config.doDeterministic = true;'
    if [ -n "${ITERS:-}" ]; then
      echo "BenchmarkSuite.suites.forEach(function(s){"
      echo "  s.benchmarks.forEach(function(b){ b.deterministicIterations = ${ITERS}; });"
      echo "});"
    fi
    # No trailing `main();`: the snapshot flow runs the top level during
    # wizening and the resumed snapshot calls `main()` itself. Calling it
    # here too runs the whole benchmark twice, and box2d's tearDown nulls
    # `Box2D`, so the second run died with "Common of null".
  } >> "$v"
fi

snap=$SD/snap.wasm
[ -f "$snap" ] || "$MEMCAP" 32G "$NM" --shell "$NIGHT_JS" "$v" --keep-snapshot "$snap" \
  --keep-names -o /dev/null >/dev/null 2>&1 || { echo "$B: snapshot failed"; exit 1; }

for arm in prod cen; do
  [ -f "$SD/$arm.cwasm" ] && continue
  flags=""; [ "$arm" = cen ] && flags="--census"
  # shellcheck disable=SC2086
  "$MEMCAP" 32G "$NM" "$snap" $flags -o "$SD/$arm.wasm" >/dev/null 2>&1 \
    || { echo "$B/$arm: compile failed"; exit 1; }
  "$WASMTIME" compile "$SD/$arm.wasm" -o "$SD/$arm.cwasm" 2>/dev/null
done

taskset -c "$CPU" perf stat -x, -e instructions -o "$SD/prod.stat" -- \
  timeout "$RUN_TIMEOUT" "$WASMTIME" run --allow-precompiled -W unknown-imports-trap "$SD/prod.cwasm" \
  > "$SD/prod.out" 2>/dev/null
ins=$(awk -F, '$3=="instructions"{print $1}' "$SD/prod.stat")

timeout "$RUN_TIMEOUT" taskset -c "$CPU" "$WASMTIME" run --allow-precompiled -W unknown-imports-trap \
  "$SD/cen.cwasm" > "$SD/cen.out" 2> "$SD/cen.err" \
  || { echo "$B: census run failed or timed out (rc=$?)"; exit 1; }

python3 - "$B" "$ins" "$SD/cen.err" <<'PY'
import re, sys, collections
bench, ins, cen = sys.argv[1], int(sys.argv[2]), sys.argv[3]
c = collections.Counter()
for ln in open(cen):
    m = re.match(r"^night: census kind ([123]) id (\d+) n (\d+)$", ln)
    if m:
        c[m.group(1)] += int(m.group(3))
opt, gen = c["1"], c["2"] + c["3"]
tot = opt + gen
if not tot:
    print(f"{bench}: no census entries"); raise SystemExit(1)
print(f"{bench}: {ins:,} instructions / {tot:,} executed bytecode ops")
print(f"  OPT {opt:,} ({100*opt/tot:.1f}%)   GEN {gen:,}")
print(f"  nat/op = {ins/tot:.2f}   (identical work in both runs)")
PY
