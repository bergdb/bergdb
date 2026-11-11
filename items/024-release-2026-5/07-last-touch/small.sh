#!/bin/sh
# 024-07: the last touch at small sizes: [LABEL=-x] [EXTRA="sd=1000000"] small.sh VARIANT [SIZES...]
# For each size N (keys): a fill in key order, then a FIFO (100 puts after every key and
# 100 deletes of the oldest a transaction), 024-03's method (section 7) at a smaller size.
B=/Users/f/fl/bench/2026-11-11/touch
HERE=$(cd "$(dirname "$0")" && pwd)
V=$1; shift
OUT=$HERE/out/small-$V$LABEL
mkdir -p $OUT
D=$B/data
for n in "$@"; do
    case $n in
        100000) tx=30000;;
        300000) tx=40000;;
        1000000) tx=60000;;
        3000000) tx=100000;;
        *) tx=50000;;
    esac
    echo "$(date '+%H:%M:%S') start $n" >> $OUT/steps.txt
    { echo "== $n $(date '+%H:%M:%S')"; uptime; ps -Ao pcpu,comm -r | sed -n 2,4p; } >> $OUT/env.txt
    $HERE/t7.sh $V fill dir=$D/s$V$n n=$n order=asc $EXTRA > $OUT/fill-$n.txt 2>&1
    $HERE/t7.sh $V log dir=$D/s$V$n n=$n maxdrive=$tx report=10000 $EXTRA > $OUT/fifo-$n.txt 2>&1
    echo "$(date '+%H:%M:%S') end $n rc=$?" >> $OUT/steps.txt
    rm -rf $D/s$V$n $D/s$V$n.time
done
echo "$(date '+%H:%M:%S') ALL DONE" >> $OUT/steps.txt
