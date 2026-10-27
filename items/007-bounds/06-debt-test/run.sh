#!/bin/sh
# 007-06: one WriteBench run (005-49's, with the section and the debt per record).
# Usage: run.sh VARIANT NAME [-Dwb.x=y ...]
# VARIANT is a clone in $W/VARIANT with its jar built and WriteBench compiled into $W/cls-VARIANT:
# head (today's take, 0f978f8), paced (005-49's paced-take.diff on it), paced2 (a link to paced,
# for the runs with wb.lowerGap), paced3 (paced with deadline-probe.diff) or step3 (007-07's
# step3.diff on 2eaaa45). Defaults: 10M keys, 1,000 puts a
# transaction, 30M updates, windows of 1M puts, a ring of 1.3 GB, a 12 GB heap ($HEAP); later
# -D options win. Output: out/NAME.txt and out/NAME.rec. One JVM at a time, nice 10.
W=${W:-/Users/f/fl/bench/006-09/w8}
cd "$W" || exit 1
v=$1; name=$2; shift 2
mkdir -p out
echo "$(date '+%F %T') start $name: $v $*" >> out/runs.txt
nice -n 10 java -Xms${HEAP:-12g} -Xmx${HEAP:-12g} -XX:+UseParallelGC -cp cls-$v:$v/java/build/bergdb.jar \
    -Dwb.keys=10000000 -Dwb.updates=30000000 -Dwb.window=1000000 -Dwb.ring=1300000000 \
    -Dwb.rec=out/$name.rec "$@" bergdb.core.WriteBench > out/$name.txt 2>&1
echo "$(date '+%F %T') end $name: $(tail -1 out/$name.txt)" >> out/runs.txt
