#!/bin/sh
# 024-07: the FIFO of 10M live keys in time order, 024-03's method (section 7; its
# runs2.sh): [LABEL=-x] big.sh VARIANT [N [TX]]. A fill of N keys in key order, then TX transactions
# of 100 puts after every key so far and 100 deletes of the oldest. Reclaim.Stats is on,
# its touch counter off (it costs time).
B=/Users/f/fl/bench/2026-11-11/touch
HERE=$(cd "$(dirname "$0")" && pwd)
V=$1
N=${2:-10000000}
TX=${3:-200000}
OUT=$HERE/out/fifo-$N-$V$LABEL
mkdir -p $OUT
D=$B/data
step() {
    name=$1; shift
    { echo "== $name $(date '+%H:%M:%S')"; uptime; ps -Ao pcpu,comm -r | sed -n 2,4p; } >> $OUT/env.txt
    echo "$(date '+%H:%M:%S') start $name" >> $OUT/steps.txt
    $HERE/t7.sh "$@" > $OUT/$name.txt 2>&1
    rc=$?
    echo "$(date '+%H:%M:%S') end $name rc=$rc" >> $OUT/steps.txt
    [ $rc = 0 ] || echo "FAILED $name" >> $OUT/steps.txt
}
step fill $V fill dir=$D/f$V n=$N order=asc
step fifo $V log dir=$D/f$V n=$N maxdrive=$TX report=10000 $EXTRA
rm -rf $D/f$V $D/f$V.time
echo "$(date '+%H:%M:%S') ALL DONE" >> $OUT/steps.txt
