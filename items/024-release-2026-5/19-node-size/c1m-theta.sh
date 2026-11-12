#!/bin/sh
# 024-19, section 4.5: option 2's theta at node sizes 8, 14 and 62, forced by the measuring
# build's -Dnsize.theta=T (T = 0: option 2 off), on sets A (overwrites, 100 a transaction) and
# E (one a transaction). One JVM, one core each; two series at a time in one slot.
# Output: out/c1m-SET-nB-thT.txt.
B=/Users/f/fl/bench/2026-11-11/nsize
J=$B/clone/java/build/bergdb.jar
O=/Users/f/fl/repos/bergdb/items/024-release-2026-5/19-node-size/out
D=$(sh /Users/f/fl/bench/2026-11-11/slot.sh take nsize "counts 024-19 1M theta")
trap 'sh /Users/f/fl/bench/2026-11-11/slot.sh release $D' EXIT
echo "slot $D $(date +%H:%M:%S)"
run() { nice -n 5 java -Xmx4g -XX:+UseSerialGC -XX:ActiveProcessorCount=1 -Dnsize.theta=$1 \
    -cp $B/cls2:$J bergdb.core.NS run ns=$2 n=1000000 shape=k13 order=random vs=100 batch=100 \
    retain=1 $3 dir=$B/data/$4; }
series() {
  for x in $1; do
    th=${x%:*}; ns=${x#*:}
    run $th $ns "ups=1000000" a$2 > $O/c1m-A-n$ns-th$th.txt 2>&1
    run $th $ns "ubatch=1 ups=200000" e$2 > $O/c1m-E-n$ns-th$th.txt 2>&1
  done
}
series "0:8 2:8 3:8" x &
series "0:14 7:14 0:62 7:62 0:30" y &
wait
rm -rf $B/data/ax $B/data/ay $B/data/ex $B/data/ey   # its own only: 10M runs may be in data/
echo "done $(date +%H:%M:%S)"
