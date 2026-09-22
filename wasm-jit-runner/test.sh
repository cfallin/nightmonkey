#!/bin/sh
# Build the runner and the example guest, then run the example end-to-end.
set -e
DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$DIR"

cargo build
sh guest/example/build.sh
echo "--- running example guest ---"
exec ./target/debug/wasm-jit-runner guest/example/test_guest.wasm
