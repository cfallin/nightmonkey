#!/usr/bin/env bash
# quickperf over the benches a policy question actually moves.
set -u
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
A=${1:?usage: qp4.sh <baseline-nightmonkey> [<now-nightmonkey>]}
C=${2:-$here/../nightmonkey/target/release/nightmonkey}
for b in ${BENCHES:-navier-stokes richards crypto mandreel}; do
  echo "--- $b"
  SD=${SDROOT:-${TMPDIR:-/tmp}/night-qp}/$b "$here/quickperf.sh" "$b" "$A" "$C" 2>&1 | grep -E '^(base|now|.*failed)'
done
