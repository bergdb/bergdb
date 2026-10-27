#!/bin/sh
# 005-48: ReclaimReaders's "model was not published" failure. Usage: sh exp.sh NAME VARIANT ROUNDS JVMOPTS...
# VARIANT head|proto (the build), runs 3 JVMs at once (seeds 1-12, 13-24, and disk=1 1-12, as
# level3.sh's step 5) ROUNDS times, with the JVM options given.
D=/Users/f/fl/bench/006-09/gc48-rr
B=/Users/f/fl/bench/006-09/gc48/java/build/perf/builds
J=/opt/homebrew/opt/openjdk/bin/java
NAME=$1; V=$2; R=$3; shift 3
CP=$D/cls-$V:$B/$V-e718347/java/build/bergdb.jar
mkdir -p $D/logs/$NAME
cd $D/work 2>/dev/null || { mkdir -p $D/work; cd $D/work; }
i=1
while [ $i -le $R ]; do
    nice -n 10 $J -ea -Xmx2g "$@" -cp $CP bergdb.core.ReclaimReaders 1 12 > $D/logs/$NAME/r$i-a.txt 2>&1 &
    nice -n 10 $J -ea -Xmx2g "$@" -cp $CP bergdb.core.ReclaimReaders 13 12 > $D/logs/$NAME/r$i-b.txt 2>&1 &
    nice -n 10 $J -ea -Xmx2g -Ddisk=1 "$@" -cp $CP bergdb.core.ReclaimReaders 1 12 > $D/logs/$NAME/r$i-d.txt 2>&1 &
    wait
    i=$((i + 1))
done
echo "$NAME done: $(cat $D/logs/$NAME/*.txt | grep -c '^FAIL') FAIL lines, $(grep -l 'NOT PUBLISHED' $D/logs/$NAME/*.txt 2>/dev/null | wc -l | tr -d ' ') logs with NOT PUBLISHED"
