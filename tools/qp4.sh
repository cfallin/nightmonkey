#!/usr/bin/env bash
# quickperf over the benches a policy question actually moves.
set -u
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
A=${1:?usage: qp4.sh <baseline-nightmonkey> [<now-nightmonkey>]}
C=${2:-$here/../build/bin/nightmonkey}
# SDROOT (kept) caches each bench's snapshot; by default a fresh directory
# in /tmp, removed on exit.
[ -n "${SDROOT:-}" ] || { SDROOT=$(mktemp -d /tmp/night-qp.XXXXXX); trap 'rm -rf "$SDROOT"' EXIT; }
for b in ${BENCHES:-navier-stokes richards crypto mandreel}; do
  echo "--- $b"
  SD=$SDROOT/$b "$here/quickperf.sh" "$b" "$A" "$C" 2>&1 | grep -E '^(base|now|.*failed)'
done
