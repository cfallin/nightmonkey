#!/usr/bin/env bash
# val1.sh <variant> <bench>: compile with --dump-tiers; write tiers log.
v=$1 b=$2 W=~/.cache/nm-bench d=$W/v/$1 p=mir
[ -f $d/pipe ] && p=$(cat $d/pipe)
[ -f $d/env ] && set -a && . $d/env && set +a
NIGHT_PAD_SEED=1 $d/nightmonkey --shell $d/js $W/src/$b.js -o /dev/null --pipeline $p --dump-tiers --stats > $W/val/$v-$b.log 2>&1
echo "rc=$?" >> $W/val/$v-$b.log
