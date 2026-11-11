#!/bin/sh
# 024-17, section 4.1, the counts (bytes, nodes, heap, record bytes): LimitProbe at 1M and
# 10M keys in ONE heavy-run slot (not timing; its times are not used). Usage: sh counts.sh SLOTDIR
B=/Users/f/fl/bench/2026-11-11/limits
OUT=/Users/f/fl/repos/bergdb/items/024-release-2026-5/17-limits
CP=$B/probe:$B/clone/java/build/bergdb.jar
for n in 1000000 10000000; do
  echo "# $(date +%H:%M:%S) n=$n main $(git -C $B/clone rev-parse --short HEAD), counts" > $OUT/count-$n.txt
  java -Xmx16g -XX:+UseZGC -XX:ActiveProcessorCount=4 -cp $CP bergdb.core.LimitProbe \
      $B/db-$n $n >> $OUT/count-$n.txt 2>&1
  echo "# exit $? $(date +%H:%M:%S)" >> $OUT/count-$n.txt
done
sh /Users/f/fl/bench/2026-11-11/slot.sh release "$1"
