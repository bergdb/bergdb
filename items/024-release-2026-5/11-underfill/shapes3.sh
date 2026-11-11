#!/bin/sh
# 024-11: as shapes.sh at 1M keys, drive 12,000 (as P5's own 1M run), with merges, keep=2, 3, 10;
# Counts only. 2026-11-11.
B=/Users/f/fl/bench/2026-11-10/p5/runs/b-head4
O=/Users/f/fl/bench/2026-11-11/fill/out
cd $O
for K in 2 3 10; do
  java -ea -Xmx6g -cp $B/bergdb.jar:$B/stress bergdb.core.CleanupRule hello n=1000000 keep=$K drive=12000 > p5-1m-keep$K.txt 2>&1
  echo "exit=$?" >> p5-1m-keep$K.txt
done
echo done > shapes3.done
