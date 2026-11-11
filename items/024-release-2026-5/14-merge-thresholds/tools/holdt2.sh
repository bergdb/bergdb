#!/bin/sh
# 024-14 (since 10:51): a timing hold with BOTH slots (slot.sh take-timing), one JVM at a time.
# holdt2.sh JOBLIST NAME
S=/Users/f/fl/bench/2026-11-11/slot.sh
D=$(sh $S take-timing thr "$2: 10M runs one at a time, under 40 min")
echo "hold $2 start $(date '+%H:%M:%S') $D"; uptime; ps -Ao pcpu,comm -r | sed -n 2,6p
HEAP=-Xmx8g; export HEAP
while read -r line; do
  /Users/f/fl/bench/2026-11-11/thr/tools/job.sh $line
  echo "job done $(date '+%H:%M:%S') $line"; uptime
done < $1
sh $S release $D
echo "hold $2 end $(date '+%H:%M:%S')"; uptime
