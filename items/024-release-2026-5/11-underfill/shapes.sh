#!/bin/sh
# 024-11: CleanupRule's "sparse" shape with other spacings (keep=K: every K-th key kept), counts
# only, on P5's frozen build b-head4 (789b1654), with merges and without (-Dbergdb.p5.merge=false,
# which is P4's delete path). 2026-11-11. One run after the other; a few seconds each.
B=/Users/f/fl/bench/2026-11-10/p5/runs/b-head4
O=/Users/f/fl/bench/2026-11-11/fill/out
cd $O
for K in 2 3 5 10 100 1000; do
  java -ea -cp $B/bergdb.jar:$B/stress bergdb.core.CleanupRule hello n=100000 keep=$K > p5-keep$K.txt 2>&1
  echo "exit=$?" >> p5-keep$K.txt
  java -ea -Dbergdb.p5.merge=false -cp $B/bergdb.jar:$B/stress bergdb.core.CleanupRule hello n=100000 keep=$K > off-keep$K.txt 2>&1
  echo "exit=$?" >> off-keep$K.txt
done
echo done > shapes.done
