#!/usr/bin/env bash
# Run NightMonkey's own regression tests (tests/jit-test/**/*.js, plain
# scripts in the jit-test style) through the shell, in the AOT lane and,
# with NIGHT_INPROCESS_OFF=1, the baseline lane. A test passes when the shell
# exits 0.
#
#   scripts/run-night-tests.sh [build-dir]
set -uo pipefail

here=$(cd "$(dirname "$0")/.." && pwd)
build=${1:-$here/build}
fail=0
pass=0
for t in $(find "$here/tests/jit-test" -name '*.js' | sort); do
  if out=$("$build/bin/inproc-shell.sh" "$t" 2>&1); then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    echo "FAIL ${t#$here/}"
    echo "$out" | grep -v 'neither Wasm' | head -5
  fi
done
echo "night tests: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
