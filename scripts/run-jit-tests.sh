#!/usr/bin/env bash
# Run SpiderMonkey's jit-tests against the NightMonkey shell.
#
#   scripts/run-jit-tests.sh <firefox-checkout> [build-dir] [-- jit_test.py args...]
#
# Every lane skips tests/wasi-jit-test-excludes.txt (tests the wasm32-wasi
# shell cannot run at all). The compiled lanes (the default) compile every
# test in-process and also skips tests/jit-test-excludes.txt; NIGHT_INPROCESS_OFF=1
# runs the same shell with the tier off (the interpreter-only lane).
# NIGHT_OPTIONS passes compiler flags; with `--pipeline baseline` or `mir` the
# lane also skips tests/jit-test-excludes-baseline.txt.
set -euo pipefail

if [ $# -lt 1 ]; then
  echo "usage: $0 <firefox-checkout> [build-dir] [-- jit_test.py args...]" >&2
  exit 2
fi
firefox=$(cd "$1" && pwd)
shift
here=$(cd "$(dirname "$0")/.." && pwd)
build=$here/build
if [ $# -ge 1 ] && [ "$1" != "--" ]; then
  build=$(cd "$1" && pwd)
  shift
fi
if [ $# -ge 1 ] && [ "$1" = "--" ]; then
  shift
fi

# jit_test.py takes one --exclude-from; combine the lists.
combined=$(mktemp)
trap 'rm -f "$combined"' EXIT
cat "$here/tests/wasi-jit-test-excludes.txt" > "$combined"
if [ "${NIGHT_INPROCESS_OFF:-0}" != 1 ]; then
  cat "$here/tests/jit-test-excludes.txt" >> "$combined"
  # The baseline-tier lane: see tests/jit-test-excludes-baseline.txt.
  case " ${NIGHT_OPTIONS:-} " in
    *" --pipeline baseline "* | *" --pipeline mir "*)
      cat "$here/tests/jit-test-excludes-baseline.txt" >> "$combined" ;;
  esac
fi

python3 "$firefox/js/src/jit-test/jit_test.py" \
  --exclude-from "$combined" \
  "$build/bin/inproc-shell.sh" "$@"
