#!/bin/sh
# 024-17, sections 4.1 and 4.2, the times: LimitProbe at 1M keys, ValueProbe, CsBench, with
# BOTH heavy-run slots (timing). Usage: sh timing.sh SLOTDIR1 SLOTDIR2
B=/Users/f/fl/bench/2026-11-11/limits
OUT=/Users/f/fl/repos/bergdb/items/024-release-2026-5/17-limits
CP=$B/probe:$B/clone/java/build/bergdb.jar
echo "# $(date +%H:%M:%S) n=1000000 main $(git -C $B/clone rev-parse --short HEAD), timing" > $OUT/time-1000000.txt
java -Xmx16g -XX:+UseZGC -cp $CP bergdb.core.LimitProbe $B/db-1000000 1000000 >> $OUT/time-1000000.txt 2>&1
echo "# exit $? $(date +%H:%M:%S)" >> $OUT/time-1000000.txt
echo "# $(date +%H:%M:%S) main $(git -C $B/clone rev-parse --short HEAD), timing" > $OUT/value.txt
java -Xmx8g -XX:+UseZGC -cp $CP bergdb.core.ValueProbe $B/db-value >> $OUT/value.txt 2>&1
java -cp $B/cs:$B/clone/java/build/bergdb.jar bergdb.core.CsBench >> $OUT/value.txt 2>&1
echo "# exit $(date +%H:%M:%S)" >> $OUT/value.txt
sh /Users/f/fl/bench/2026-11-11/slot.sh release $1 $2
