#!/bin/sh
# 024-14 (since 11:21): a counting hold in ONE slot, at most 2 JVMs, one or two runs; release.
# hold3.sh JOBLIST NAME
S=/Users/f/fl/bench/2026-11-11/slot.sh
D=$(sh $S take thr "counts 10M $2, 2 JVMs, under 40 min")
echo "hold $2 start $(date '+%H:%M:%S') $D"; uptime
HEAP=-Xmx6g; export HEAP
xargs -L1 -P2 /Users/f/fl/bench/2026-11-11/thr/tools/job.sh < $1
sh $S release $D
echo "hold $2 end $(date '+%H:%M:%S')"; uptime
