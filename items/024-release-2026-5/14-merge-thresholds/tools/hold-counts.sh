#!/bin/sh
# 024-14: hold 1 (counts at 10M, 3 JVMs in parallel, not timing): take the lock, run, release.
L=/Users/f/fl/bench/2026-11-11/heavy.lock
until mkdir $L 2>/dev/null; do sleep 20; done
echo "thr counts at 10M (024-14), 3 JVMs in parallel, not timing; under 40 min $(date '+%H:%M:%S')" > $L/owner
echo "hold-counts start $(date '+%H:%M:%S')"; uptime
HEAP=-Xmx6g; export HEAP
xargs -L1 -P3 /Users/f/fl/bench/2026-11-11/thr/tools/job.sh < ${1:-/Users/f/fl/bench/2026-11-11/thr/tools/jobs-10m-counts.txt}
rm -rf $L
echo "hold-counts end $(date '+%H:%M:%S')"; uptime
