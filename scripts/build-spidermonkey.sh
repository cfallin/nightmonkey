#!/usr/bin/env bash
# Build SpiderMonkey for NightMonkey: the wasm32-wasi JS shell with the
# external compiler hook surface (spidermonkey/mozconfig), from a checkout of
# the SpiderMonkey branch NightMonkey tracks.
#
#   scripts/build-spidermonkey.sh <firefox-checkout>
#
# Produces <firefox-checkout>/obj-nightmonkey-sm/dist, the SPIDERMONKEY_DIST
# the CMake build consumes.
set -euo pipefail

if [ $# -ne 1 ]; then
  echo "usage: $0 <firefox-checkout>" >&2
  exit 2
fi
firefox=$(cd "$1" && pwd)
here=$(cd "$(dirname "$0")/.." && pwd)

cd "$firefox"
MOZCONFIG="$here/spidermonkey/mozconfig" ./mach build
echo "SPIDERMONKEY_DIST=$firefox/obj-nightmonkey-sm/dist"
