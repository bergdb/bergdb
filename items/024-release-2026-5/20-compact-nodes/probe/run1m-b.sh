#!/bin/sh
# 024-20: the 1M runs at node sizes 14 and 62, after run1m.sh. run1m-b.sh OUTDIR
C=/Users/f/fl/bench/2026-11-11/compact
O=${1:-$C/out/1m}
mkdir -p $O
CP=$C/classes:$C/clone/java/build/bergdb.jar
r() {
  N=$1; shift
  [ -f $O/$N.txt ] && grep -q DONE $O/$N.txt && return
  java -Xmx3g -XX:ActiveProcessorCount=2 -cp $CP bergdb.core.CN "$@" dir=$C/data/$N > $O/$N.txt 2>&1
  echo "$N rc=$? $(date +%H:%M:%S)" >> $O/runs.log
}
# the node sizes 14 and 62 beside 30, for 024-19
for s in 14 62; do
  r over-b100-n$s  work=over batch=100 ns=$s
  r over-b1-n$s    work=over batch=1 ns=$s
  r rand-b100-n$s  work=rand batch=100 ns=$s
  r over-b100-sd5-n$s work=over batch=100 sd=5000000 ns=$s
done
r over-b100-sd5-n30 work=over batch=100 sd=5000000
echo "ALL DONE B $(date +%H:%M:%S)" >> $O/runs.log
