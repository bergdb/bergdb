#!/bin/sh
# bergdb 028-19: the second quiet session: SetLoop and CORE ABBA (old, main, sw), CCBench at 10M
# (jobs-cc.txt), then Perf write with reclaim for sw (jobs-times2.txt). Detached; each JVM after
# the quiet check (MINIDLE from the environment).
D=$(cd "$(dirname "$0")/.." && pwd)
sh "$D/tools/setloop.sh" "$D/out-setloop2" 30 old-a main-b sw-c sw-d main-e old-f
sh "$D/tools/core.sh" "$D/out-core" old-a main-b sw-c sw-d main-e old-f
QUIET=1 sh "$D/tools/run2.sh" "$D/tools/jobs-cc.txt" "$D/out-cc"
QUIET=1 sh "$D/tools/run2.sh" "$D/tools/jobs-times2.txt" "$D/out-times"
echo "QUIET SESSION 2 END $(date)" >> "$D/out-times/log.txt"
