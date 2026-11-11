#!/bin/sh
# 024-14: the timed runs inside the both-slot hold taken at 12:23 (holdt2 stopped after a disturbance):
# wait for a quiet machine (no other java or treetest, 1-min load under 6; at most 6 minutes), run, release.
T=/Users/f/fl/bench/2026-11-11/thr
end=$(( $(date +%s) + 360 ))
while [ $(date +%s) -lt $end ]; do
  others=$(ps -Ao command | grep -E "^java|treetest" | grep -v "redhat.java" | grep -vc "bergdb.core.THR")
  load=$(uptime | sed 's/.*load averages: //' | cut -d' ' -f1 | cut -d. -f1)
  [ "$others" = 0 ] && [ "$load" -lt 6 ] && break
  sleep 10
done
echo "quiet wait end $(date '+%H:%M:%S') others=$others"; uptime
HEAP=-Xmx8g; export HEAP
while read -r line; do
  $T/tools/job.sh $line
  echo "job done $(date '+%H:%M:%S') $line"; uptime
done < $T/tools/jobs-T.txt
sh /Users/f/fl/bench/2026-11-11/slot.sh release /Users/f/fl/bench/2026-11-11/heavy.lock /Users/f/fl/bench/2026-11-11/heavy2.lock
echo "hold T end $(date '+%H:%M:%S')"; uptime
