#!/bin/sh
# 024-20: the 1M runs, one at a time, one JVM, two cores. run1m.sh OUTDIR
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
r seq-b100      work=seq  batch=100
r rand-b100     work=rand batch=100
r over-b100     work=over batch=100
r del-b100      work=del  batch=100
r fifo-b100     work=fifo batch=100 ops=3000000 retain=4
r seq-b1        work=seq  batch=1
r rand-b1       work=rand batch=1
r over-b1       work=over batch=1
r del-b1        work=del  batch=1
r fifo-b1       work=fifo batch=1 ops=3000000 retain=400
for b in 100 1; do
  r over-b$b-s     work=over batch=$b key=short
  r over-b$b-v0    work=over batch=$b vsize=0
  r over-b$b-s-v0  work=over batch=$b key=short vsize=0
  r rand-b$b-s     work=rand batch=$b key=short
  r rand-b$b-v0    work=rand batch=$b vsize=0
  r rand-b$b-s-v0  work=rand batch=$b key=short vsize=0
  r over-b$b-sd5   work=over batch=$b sd=5000000
done
r seq-b100-s-v0  work=seq  batch=100 key=short vsize=0
r over-b100-v8   work=over batch=100 vsize=8
echo "ALL DONE $(date +%H:%M:%S)" >> $O/runs.log
