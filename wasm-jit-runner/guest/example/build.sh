#!/bin/sh
# Build the test guest into a wasip1 wasm module.
#
# No special linker flags are required: the runner stream-edits the module on
# load to export its memories/tables/globals and to make the indirect function
# table growable.
set -e
DIR="$(cd "$(dirname "$0")" && pwd)"
CC="${WASI_CC:-/opt/wasi-sdk/bin/wasm32-wasip1-clang}"

# The core/builder headers live one directory up.
"$CC" -I"$DIR/.." "$DIR/test_guest.c" -O2 -o "$DIR/test_guest.wasm"

echo "built $DIR/test_guest.wasm"
