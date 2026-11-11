#!/bin/sh
# 024-19's counts at 1M keys: one JVM at a time, one core (no slot needed), FileStream in
# the bench directory. Usage: sh c1m.sh SET [SIZES]. Output: out/c1m-SET-nNS.txt.
B=/Users/f/fl/bench/2026-11-11/nsize
J=$B/clone/java/build/bergdb.jar
O=/Users/f/fl/repos/bergdb/items/024-release-2026-5/19-node-size/out
SET=$1; shift
SIZES=${*:-8 14 30 62 126 254}
run() { nice -n 5 java -Xmx4g -XX:+UseSerialGC -XX:ActiveProcessorCount=1 -cp $B/cls:$J bergdb.core.NS "$@"; }
for ns in $SIZES; do
  f=$O/c1m-$SET-n$ns.txt
  case $SET in
  A) run run ns=$ns n=1000000 shape=k13 order=random vs=100 batch=100 ups=1000000 retain=1 dir=$B/data/a > $f 2>&1 ;;
  B) run run ns=$ns n=1000000 shape=k24 order=random vs=0 batch=100 ups=1000000 retain=1 dir=$B/data/b > $f 2>&1 ;;
  C) run run ns=$ns n=1000000 shape=k13 order=asc vs=100 batch=100 ups=0 dir=$B/data/c > $f 2>&1 ;;
  D) run run ns=$ns n=1000000 shape=k13 order=queue vs=100 batch=100 ups=1000000 retain=1 dir=$B/data/d > $f 2>&1 ;;
  E) run run ns=$ns n=1000000 shape=k13 order=random vs=100 batch=100 ubatch=1 ups=200000 retain=1 dir=$B/data/e > $f 2>&1 ;;
  F) run run ns=$ns n=1000000 shape=k13 order=random vs=100 batch=100 ups=1000000 retain=0 dir=$B/data/f > $f 2>&1 ;;
  M) run mem ns=$ns n=1000000 shape=mem > $f 2>&1; run mem ns=$ns n=1000000 shape=k24 >> $f 2>&1 ;;
  esac
  grep -h "FILL\|UPD\|TREE\|MEM\|Exception\|Error" $f | head -8
done
