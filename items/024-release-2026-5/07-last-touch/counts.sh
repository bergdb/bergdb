#!/bin/sh
# 024-07: counts beside the queue, no timing: counts.sh VARIANT
#   drive   1M keys put in random order, then 30,000 transactions of 100 overwrites of
#           random keys: what a step makes dirty where most values are rewritten.
#   tail    the same with 10 new keys after every key in each transaction: keys put beyond
#           the scan's end beside a random drive.
#   heap    the queue of 1M keys with a heap of 256 MB and a startup distance of 5 MB:
#           the nodes that the last touch pins.
B=/Users/f/fl/bench/2026-11-11/touch
HERE=$(cd "$(dirname "$0")" && pwd)
V=$1
OUT=$HERE/out/counts-$V
mkdir -p $OUT
D=$B/data
$HERE/t7.sh $V fill dir=$D/d$V n=1000000 order=random > $OUT/drive-fill.txt 2>&1
$HERE/t7.sh $V drive dir=$D/d$V n=1000000 maxdrive=30000 report=10000 touchcount=1 > $OUT/drive.txt 2>&1
rm -rf $D/d$V $D/d$V.time
$HERE/t7.sh $V fill dir=$D/d$V n=1000000 order=random > $OUT/tail-fill.txt 2>&1
$HERE/t7.sh $V drive dir=$D/d$V n=1000000 maxdrive=30000 report=10000 tail=10 touchcount=1 > $OUT/tail.txt 2>&1
rm -rf $D/d$V $D/d$V.time
HEAP=256m $HERE/t7h.sh $V fill dir=$D/h$V n=1000000 order=asc sd=5000000 > $OUT/heap-fill.txt 2>&1
HEAP=256m $HERE/t7h.sh $V log dir=$D/h$V n=1000000 maxdrive=40000 report=10000 sd=5000000 > $OUT/heap-fifo.txt 2>&1
echo "heap rc=$?" >> $OUT/heap-fifo.txt
rm -rf $D/h$V $D/h$V.time
echo "$(date '+%H:%M:%S') ALL DONE" >> $OUT/steps.txt
