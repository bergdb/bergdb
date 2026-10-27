#!/bin/sh
# 005-48: the committed ReclaimReaders (the clone's build: the change and the fixed test) under
# level3.sh's load for MINUTES, as expB.sh. Usage: sh expR.sh NAME MINUTES
D=/Users/f/fl/bench/006-09/gc48-rr
C=/Users/f/fl/bench/006-09/gc48/java/build
J=/opt/homebrew/opt/openjdk/bin/java
NAME=$1; MIN=$2
CP=$C/bergdb.jar:$C/stress
END=$(( $(date +%s) + MIN * 60 ))
mkdir -p $D/logs/$NAME $D/work
cd $D/work
loop() {
    tag=$1; first=$2; shift 2
    i=1
    while [ $(date +%s) -lt $END ]; do
        nice -n 10 $J -ea -Xmx2g "$@" -cp $CP bergdb.core.ReclaimReaders $first 12 > $D/logs/$NAME/$tag-$i.txt 2>&1
        i=$((i + 1))
    done
}
loop a 1 &
loop b 13 &
loop d 1 -Ddisk=1 &
wait
L=$D/logs/$NAME
echo "$NAME: $(ls $L | wc -l | tr -d ' ') JVMs, $(grep -h '^Done' $L/*.txt | wc -l | tr -d ' ') done, rounds $(grep -ho '^Done: [0-9]* rounds' $L/*.txt | awk '{s+=$2} END {print s}'), failures $(grep -ho ' [0-9]* failures' $L/*.txt | awk '{s+=$1} END {print s}')"
