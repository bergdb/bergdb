#!/bin/sh
# 024-19's times at 1M keys, in a timing hold (slot.sh take-timing: both slots, the machine
# alone): per size one JVM after the other. Output: out/t1m-nB.txt, uptime's load in each.
B=/Users/f/fl/bench/2026-11-11/nsize
J=$B/clone/java/build/bergdb.jar
O=/Users/f/fl/repos/bergdb/items/024-release-2026-5/19-node-size/out
SIZES=${*:-8 14 30 62 126 254}
D=$(sh /Users/f/fl/bench/2026-11-11/slot.sh take-timing nsize "024-19 1M, 6 sizes, 6 min")
trap 'sh /Users/f/fl/bench/2026-11-11/slot.sh release $D' EXIT
for ns in $SIZES; do
  f=$O/t1m-n$ns.txt
  echo "load before: $(uptime) $(date +%H:%M:%S)" > $f
  java -Xms4g -Xmx4g -XX:+UseG1GC -cp $B/cls2:$J bergdb.core.NS run ns=$ns n=1000000 shape=k13 order=random vs=100 batch=100 ups=500000 retain=1 gets=1000000 scan=1 restart=1 dir=$B/data/t >> $f 2>&1
  echo "load after: $(uptime) $(date +%H:%M:%S)" >> $f
done
