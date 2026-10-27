#!/bin/sh
# 005-48: ReclaimReaders under level3.sh's load for MINUTES: three loops at once (seeds 1-12,
# seeds 13-24, disk=1 seeds 1-12), each starting a new JVM until the time is up.
# Usage: sh expB.sh NAME head|proto MINUTES JVMOPTS...
D=/Users/f/fl/bench/006-09/gc48-rr
B=/Users/f/fl/bench/006-09/gc48/java/build/perf/builds
J=/opt/homebrew/opt/openjdk/bin/java
NAME=$1; V=$2; MIN=$3; shift 3
CP=$D/cls-$V:$B/$V-e718347/java/build/bergdb.jar
END=$(( $(date +%s) + MIN * 60 ))
mkdir -p $D/logs/$NAME $D/work
cd $D/work
loop() {    # $1 tag, $2 first seed, then JVM options
    tag=$1; first=$2; shift 2
    i=1
    while [ $(date +%s) -lt $END ]; do
        nice -n 10 $J -ea -Xmx2g "$@" -cp $CP bergdb.core.ReclaimReaders $first 12 > $D/logs/$NAME/$tag-$i.txt 2>&1
        i=$((i + 1))
    done
}
loop a 1 "$@" &
loop b 13 "$@" &
loop d 1 -Ddisk=1 "$@" &
wait
L=$D/logs/$NAME
echo "$NAME: $(ls $L | wc -l | tr -d ' ') JVMs, $(grep -h '^Done' $L/*.txt | wc -l | tr -d ' ') done, sessions $(grep -ho 'Sessions [0-9]*' $L/*.txt | awk '{s+=$2} END {print s}'), rescued $(grep -ho 'rescued [0-9]*' $L/*.txt | awk '{s+=$2} END {print s}'), FAIL lines $(cat $L/*.txt | grep -c '^FAIL'), NOT PUBLISHED $(cat $L/*.txt | grep -c 'NOT PUBLISHED')"
