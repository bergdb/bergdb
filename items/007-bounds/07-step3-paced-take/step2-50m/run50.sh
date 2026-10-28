#!/bin/sh
# 006-10 (r50): 007-07's step-2 runs at 50M keys on main (D4:B). As 007-06's run.sh, with
# 50M keys, windows of 2.5M puts, a 22 GB heap, nice 19, and no start at or after $CUTOFF.
# Usage: run50.sh NAME [-Dwb.x=y ...]   (later -D options win)
W=/Users/f/fl/bench/006-10/r50
cd "$W" || exit 1
name=$1; shift
[ "$(date +%H%M)" -lt "${CUTOFF:-2100}" ] || { echo "$(date '+%F %T') skip $name: cutoff" >> out/runs.txt; exit 1; }
echo "$(date '+%F %T') start $name: $*" >> out/runs.txt
nice -n 19 java -Xms${HEAP:-22g} -Xmx${HEAP:-22g} -XX:+UseParallelGC -cp cls-main:main/java/build/bergdb.jar \
    -Dwb.keys=50000000 -Dwb.updates=20000000 -Dwb.window=2500000 -Dwb.ring=1300000000 \
    -Dwb.rec=out/$name.rec "$@" bergdb.core.WriteBench > out/$name.txt 2>&1
echo "$(date '+%F %T') end $name: $(tail -1 out/$name.txt)" >> out/runs.txt
