#!/usr/bin/env bash
# queue.sh: run batches from $W/queue.txt ("label: v1 v2 ...") in order,
# skipping labels already done; re-reads the file after each batch, so
# lines may be appended while it runs. Waits while $W/PAUSE exists.
W=~/.cache/nm-bench
mkdir -p $W/res
while true; do
  while [ -e $W/PAUSE ]; do sleep 10; done
  next=
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    case "$line" in \#*) continue ;; esac
    l=${line%%:*}
    [ -e "$W/res/$l.done" ] && continue
    next=$line; break
  done < $W/queue.txt
  [ -z "$next" ] && { echo "queue empty $(date)"; break; }
  l=${next%%:*}; vs=${next#*:}
  echo "=== $l start $(date)"
  touch $W/RUNNING
  if ! $W/abx.sh "$l" "$vs" > $W/res/$l.log 2>&1; then
    echo "abx failed: $l"; rm -f $W/RUNNING; exit 1
  fi
  rm -f $W/RUNNING
  touch "$W/res/$l.done"
  echo "=== $l end $(date)"; cat $W/res/$l.time
done
