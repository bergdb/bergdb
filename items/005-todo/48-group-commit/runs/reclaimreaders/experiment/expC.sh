#!/bin/sh
# 005-48: ReclaimReaders, fixed check counting rescues, under heavy load for MINUTES: HEAD and the
# prototype at the same time (for each: seeds 1-12, seeds 13-24, disk=1 seeds 1-12), and BURN
# CPU burners (yes), all at nice 10, beside whatever else runs.
# Usage: sh expC.sh NAME MINUTES BURN
D=/Users/f/fl/bench/006-09/gc48-rr
B=/Users/f/fl/bench/006-09/gc48/java/build/perf/builds
J=/opt/homebrew/opt/openjdk/bin/java
NAME=$1; MIN=$2; BURN=$3
END=$(( $(date +%s) + MIN * 60 ))
mkdir -p $D/logs/$NAME $D/work
cd $D/work
loop() {    # $1 build, $2 tag, $3 first seed, then JVM options
    v=$1; tag=$2; first=$3; shift 3
    CP=$D/cls-$v:$B/$v-e718347/java/build/bergdb.jar
    i=1
    while [ $(date +%s) -lt $END ]; do
        nice -n 10 $J -ea -Xmx2g -Dfixed=1 "$@" -cp $CP bergdb.core.ReclaimReaders $first 12 > $D/logs/$NAME/$v-$tag-$i.txt 2>&1
        i=$((i + 1))
    done
}
for v in head proto; do
    loop $v a 1 &
    loop $v b 13 &
    loop $v d 1 -Ddisk=1 &
done
k=0
while [ $k -lt $BURN ]; do
    nice -n 10 sh -c "while [ \$(date +%s) -lt $END ]; do yes > /dev/null & p=\$!; sleep 20; kill \$p; done" &
    k=$((k + 1))
done
wait
L=$D/logs/$NAME
for v in head proto; do
    echo "$NAME $v: $(ls $L/$v-* | wc -l | tr -d ' ') JVMs, $(grep -h '^Done' $L/$v-*.txt | wc -l | tr -d ' ') done, sessions $(grep -ho 'Sessions [0-9]*' $L/$v-*.txt | awk '{s+=$2} END {print s}'), rescued $(grep -ho 'rescued [0-9]*' $L/$v-*.txt | awk '{s+=$2} END {print s}'), FAIL lines $(cat $L/$v-*.txt | grep -c '^FAIL'), NOT PUBLISHED $(cat $L/$v-*.txt | grep -c 'NOT PUBLISHED')"
done
