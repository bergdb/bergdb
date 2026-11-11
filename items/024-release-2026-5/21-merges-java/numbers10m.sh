#!/bin/sh
# 024-21, section 8: 10M keys on the branch (b1), two shapes at once: every second key kept
# (024-11's worst for m = B / 4) and 024-03's "sparse" (a random fill, every 30th kept). Counts.
M=/Users/f/fl/bench/2026-11-11/mgj
O=$M/runs/num10m; mkdir -p $O $M/data
job() {
  nm=$1; shift
  F=$O/$nm-br.txt; DD=$M/data/$nm-br
  echo "== $nm br $(date +%H:%M:%S) $*" > $F
  java -Xmx6g -XX:+UseG1GC -XX:ActiveProcessorCount=2 -cp $M/probe/thr-b1:$M/b1/bergdb.jar bergdb.core.THR "$@" dir=$DD >> $F 2>&1
  echo "rc=$? $(date +%H:%M:%S)" >> $F
  rm -rf $DD $DD-twin
}
job n10m-k2-asc run n=10000000 fill=seq shape=keep keep=2 order=asc drive=0 twin=1 &
job n10m-k30-rand run n=10000000 fill=random shape=keep keep=30 order=asc drive=0 twin=1 &
wait
echo "10M done $(date +%H:%M:%S)"
