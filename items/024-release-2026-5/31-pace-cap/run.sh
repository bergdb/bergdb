#!/bin/sh
# 007-06: one WriteBench run (005-49's, with the section and the debt per record).
# Usage: run.sh VARIANT NAME [-Dwb.x=y ...]
# VARIANT is head (today's take) or paced (005-49's paced-take.diff), a clone in $W/VARIANT with
# its jar built and WriteBench compiled into $W/cls-VARIANT. Defaults: 10M keys, 1,000 puts a
# transaction, 30M updates, windows of 1M puts, a ring of 1.3 GB, a 12 GB heap ($HEAP); later
# -D options win. Output: out/NAME.txt and out/NAME.rec. One JVM at a time, nice 10.
W=${W:-/Users/f/fl/bench/2026-11-12/pace/w}
cd "$W" || exit 1
v=$1; name=$2; shift 2
mkdir -p out
echo "$(date '+%F %T') start $name: $v $*" >> out/runs.txt
nice -n 10 java -Xms${HEAP:-12g} -Xmx${HEAP:-12g} -XX:+UseParallelGC -cp cls-$v:$v/java/build/bergdb.jar \
    -Dwb.keys=10000000 -Dwb.tx=500 -Dwb.updates=30000000 -Dwb.window=1000000 -Dwb.ring=1300000000 \
    -Dwb.rec=out/$name.rec "$@" bergdb.core.WriteBench > out/$name.txt 2>&1
echo "$(date '+%F %T') end $name: $(tail -1 out/$name.txt)" >> out/runs.txt
