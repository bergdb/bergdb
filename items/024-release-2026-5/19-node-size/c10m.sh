#!/bin/sh
# 024-19's counts at 10M keys, in one slot (slot.sh take), two JVMs at a time, each one
# core of work (ActiveProcessorCount=2 for its GC). Usage: sh c10m.sh SET "SIZES-A" "SIZES-B"
# Output: out/c10m-SET-nB.txt. The slot is released when both lines end, also on failure.
B=/Users/f/fl/bench/2026-11-11/nsize
J=$B/clone/java/build/bergdb.jar
O=/Users/f/fl/repos/bergdb/items/024-release-2026-5/19-node-size/out
SET=$1
D=$(sh /Users/f/fl/bench/2026-11-11/slot.sh take nsize "counts 024-19 10M set $SET")
trap 'sh /Users/f/fl/bench/2026-11-11/slot.sh release $D' EXIT
echo "slot $D $(date +%H:%M:%S) load: $(uptime)"
run() { java -Xmx6g -XX:+UseParallelGC -XX:ActiveProcessorCount=2 -cp $B/cls2:$J bergdb.core.NS "$@"; }
one() {
  for ns in $1; do
    f=$O/c10m-$SET-n$ns.txt
    case $SET in
    A) run run ns=$ns n=10000000 shape=k13 order=random vs=100 batch=100 ups=2000000 retain=1 gets=200000 scan=1 restart=1 dir=$B/data/m$2 > $f 2>&1 ;;
    B) run run ns=$ns n=10000000 shape=k24 order=random vs=0 batch=100 ups=2000000 retain=1 gets=200000 restart=1 dir=$B/data/m$2 > $f 2>&1 ;;
    M) run mem ns=$ns n=10000000 shape=k24 > $f 2>&1 ;;
    esac
    rm -rf $B/data/m$2
  done
}
one "$2" x &
one "$3" y &
wait
echo "done $(date +%H:%M:%S) load: $(uptime)"
