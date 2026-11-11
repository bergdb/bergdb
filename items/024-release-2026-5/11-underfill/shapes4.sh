#!/bin/sh
# 024-11: the spacings with the deletes in descending and in random order (shape "after"), and
# with hashed keys (a fill in random key order, keys of 3 segments), with merges; hashed also
# without. 100,000 keys, counts only. 2026-11-11.
B=/Users/f/fl/bench/2026-11-10/p5/runs/b-head4
O=/Users/f/fl/bench/2026-11-11/fill/out
cd $O
for ORD in desc random; do
  for K in 2 3 10 30 100; do
    java -ea -cp $B/bergdb.jar:$B/stress bergdb.core.CleanupRule hello n=100000 keep=$K order=$ORD > p5-$ORD-keep$K.txt 2>&1
    echo "exit=$?" >> p5-$ORD-keep$K.txt
  done
done
for K in 2 10 30; do
  java -ea -cp $B/bergdb.jar:$B/stress bergdb.core.CleanupRule hello n=100000 keep=$K shape=hashed > p5-hashed-keep$K.txt 2>&1
  echo "exit=$?" >> p5-hashed-keep$K.txt
  java -ea -Dbergdb.p5.merge=false -cp $B/bergdb.jar:$B/stress bergdb.core.CleanupRule hello n=100000 keep=$K shape=hashed > off-hashed-keep$K.txt 2>&1
  echo "exit=$?" >> off-hashed-keep$K.txt
done
echo done > shapes4.done
