#!/bin/sh
# 024-14: run a job list one at a time; waits while the heavy lock's owner says "timing" (not ours)
L=$1
while read -r line; do
  while grep -q timing /Users/f/fl/bench/2026-11-11/heavy.lock/owner 2>/dev/null && ! grep -q "^thr" /Users/f/fl/bench/2026-11-11/heavy.lock/owner; do sleep 20; done
  /Users/f/fl/bench/2026-11-11/thr/tools/job.sh $line
done < $L
echo "SERIAL DONE $L $(date '+%H:%M:%S')"
