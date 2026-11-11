#!/bin/sh
# 024-19's counts at 1M keys, second series (as c1m.sh: one JVM, one core, no slot).
# G and H: sd 5 MB and 0.5 MB, stand-ins for 10M and 100M keys at sd 50 MB (the bytes a put
# depend on sd / K, 006-19, section 1). Usage: sh c1m2.sh SET [SIZES].
B=/Users/f/fl/bench/2026-11-11/nsize
J=$B/clone/java/build/bergdb.jar
O=/Users/f/fl/repos/bergdb/items/024-release-2026-5/19-node-size/out
SET=$1; shift
SIZES=${*:-8 14 30 62 126 254}
run() { nice -n 5 java -Xmx4g -XX:+UseSerialGC -XX:ActiveProcessorCount=1 -cp $B/cls2:$J bergdb.core.NS "$@"; }
for ns in $SIZES; do
  f=$O/c1m-$SET-n$ns.txt
  case $SET in
  C) run run ns=$ns n=1000000 shape=k13 order=asc vs=100 batch=100 ups=0 dir=$B/data/c > $f 2>&1 ;;
  D) run run ns=$ns n=1000000 shape=k13 order=queue vs=100 batch=100 ups=1000000 retain=1 dir=$B/data/d > $f 2>&1 ;;
  E) run run ns=$ns n=1000000 shape=k13 order=random vs=100 batch=100 ubatch=1 ups=200000 retain=1 dir=$B/data/e > $f 2>&1 ;;
  F) run run ns=$ns n=1000000 shape=k13 order=random vs=100 batch=100 ups=1000000 retain=0 dir=$B/data/f > $f 2>&1 ;;
  G) run run ns=$ns n=1000000 shape=k13 order=random vs=100 batch=100 ups=1000000 retain=1 sd=5000000 dir=$B/data/g > $f 2>&1 ;;
  H) run run ns=$ns n=1000000 shape=k13 order=random vs=100 batch=100 ups=1000000 retain=1 sd=500000 dir=$B/data/h > $f 2>&1 ;;
  I) run run ns=$ns n=1000000 shape=k13 order=random vs=0 batch=100 ups=1000000 retain=1 dir=$B/data/i > $f 2>&1 ;;
  esac
  grep -h "UPD\|Exception\|Error" $f | head -3
done
