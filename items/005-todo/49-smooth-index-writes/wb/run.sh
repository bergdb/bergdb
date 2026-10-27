#!/bin/sh
# 005-49: WriteBench's update phase of 005-38's run3.sh (10M keys, 1,000 puts a transaction,
# then 30M random updates of the loaded keys), with every record logged (wb.rec).
# Usage: run.sh VARIANT SD_MB... ; VARIANT is head (today's take), deadline (007-03's step 3
# alone), paced (the paced take with the deadline) or pexp (paced, with the knobs
# -Dpace.target and -Dpace.floor in $JOPTS and a name suffix in $SUFFIX), each a scratch
# clone in $W with its jar built and WriteBench compiled into $W/cls-VARIANT.
# One JVM at a time, nice 10. Before 12:20 on 2026-10-27 the script had no JOPTS or SUFFIX.
W=${W:-/Users/f/fl/bench/006-09/w2}
cd "$W" || exit 1
v=$1; shift
mkdir -p out
for sd in "$@"; do
    name=$v$SUFFIX-sd$sd
    echo "$(date '+%F %T') start $name $JOPTS" >> out/runs.txt
    nice -n 10 java -Xms12g -Xmx12g -XX:+UseParallelGC $JOPTS -cp cls-$v:$v/java/build/bergdb.jar \
        -Dwb.keys=10000000 -Dwb.updates=30000000 -Dwb.window=1000000 -Dwb.ring=1300000000 \
        -Dwb.sd=${sd}000000 -Dwb.rec=out/$name.rec bergdb.core.WriteBench > out/$name.txt 2>&1
    echo "$(date '+%F %T') end $name: $(tail -1 out/$name.txt)" >> out/runs.txt
done
