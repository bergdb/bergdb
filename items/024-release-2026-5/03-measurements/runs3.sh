#!/bin/sh
# PF1's extra runs (bergdb 024-03), 2026-11-11: a FIFO of 10M live keys in time order (CL7).
B=/Users/f/fl/bench/2026-11-11/pf1
cd $B || exit 1
OUT=$B/out/1m-fifo
mkdir -p $OUT
D=$B/data
step() {
    name=$1; shift
    { echo "== $name $(date '+%H:%M:%S')"; uptime; ps -Ao pcpu,comm -r | sed -n 2,4p; } >> $OUT/env.txt
    echo "$(date '+%H:%M:%S') start $name" >> $OUT/steps.txt
    ./pf1.sh "$@" > $OUT/$name.txt 2>&1
    rc=$?
    echo "$(date '+%H:%M:%S') end $name rc=$rc" >> $OUT/steps.txt
    [ $rc = 0 ] || echo "FAILED $name" >> $OUT/steps.txt
}
for v in 4; do
step fifofill$v $v fill dir=$D/f$v n=1000000 order=asc reads=0
step fifo$v $v log dir=$D/f$v n=1000000 frac=0 maxdrive=100000 report=5000
rm -rf $D/f$v
done
echo "$(date '+%H:%M:%S') ALL DONE" >> $OUT/steps.txt
