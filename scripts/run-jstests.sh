#!/usr/bin/env bash
# Run SpiderMonkey's jstests (the test262 and non262 suites) against the
# NightMonkey shell.
#
#   scripts/run-jstests.sh <firefox-checkout> [build-dir] [-- jstests.py args...]
#
# Both lanes skip tests/wasi-jstests-excludes.txt (tests the wasm32-wasi
# shell cannot run at all). The AOT lane (default) also skips
# tests/jstests-excludes.txt; NIGHT_INPROCESS_OFF=1 runs the tier-off
# baseline lane.
# The full suite takes hours; pass a path filter to narrow it.
set -euo pipefail

if [ $# -lt 1 ]; then
  echo "usage: $0 <firefox-checkout> [build-dir] [-- jstests.py args...]" >&2
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

excludes=(--exclude-file "$here/tests/wasi-jstests-excludes.txt")
if [ "${NIGHT_INPROCESS_OFF:-0}" != 1 ]; then
  excludes+=(--exclude-file "$here/tests/jstests-excludes.txt")
fi

exec python3 "$firefox/js/src/tests/jstests.py" \
  "${excludes[@]}" \
  --wpt=disabled \
  "$build/bin/inproc-shell.sh" "$@"
