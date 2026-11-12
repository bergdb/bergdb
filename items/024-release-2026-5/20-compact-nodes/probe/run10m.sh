#!/bin/sh
# 024-20: one 10M run in a slot. run10m.sh NAME args... (takes a slot, runs, releases)
C=/Users/f/fl/bench/2026-11-11/compact
S=/Users/f/fl/bench/2026-11-11/slot.sh
O=$C/out/10m
mkdir -p $O
N=$1; shift
L=$(sh $S take compact "counts: 10M stream $N (024-20)")
trap 'sh $S release $L' EXIT INT TERM
echo "$N slot $L $(date +%H:%M:%S)" >> $O/runs.log
java -Xmx12g -XX:ActiveProcessorCount=4 -cp $C/classes:$C/clone/java/build/bergdb.jar bergdb.core.CN n=10000000 "$@" dir=$C/data/10m-$N > $O/$N.txt 2>&1
echo "$N rc=$? $(date +%H:%M:%S)" >> $O/runs.log
