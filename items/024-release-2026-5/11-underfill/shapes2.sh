#!/bin/sh
# 024-11: as shapes.sh, with a drive of 20,000 transactions, so that keep=2, 3 and 10 pass several
# reclaim iterations after the deletes. Counts only. 2026-11-11.
B=/Users/f/fl/bench/2026-11-10/p5/runs/b-head4
O=/Users/f/fl/bench/2026-11-11/fill/out
cd $O
for K in 2 3 10; do
  java -ea -cp $B/bergdb.jar:$B/stress bergdb.core.CleanupRule hello n=100000 keep=$K drive=20000 > p5-keep$K-d20k.txt 2>&1
  echo "exit=$?" >> p5-keep$K-d20k.txt
done
java -ea -Dbergdb.p5.merge=false -cp $B/bergdb.jar:$B/stress bergdb.core.CleanupRule hello n=100000 keep=2 drive=20000 > off-keep2-d20k.txt 2>&1
echo "exit=$?" >> off-keep2-d20k.txt
echo done > shapes2.done
