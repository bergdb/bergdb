#!/bin/sh
# 005-38 node-size study, phase A: 1M and 10M keys, one JVM of at most 6 GB at a time.
cd "$(dirname "$0")"
J=../bergdb/java/build/bergdb.jar
mkdir -p out
r() {   # r NAME HEAP FLAGS...
    name=$1; heap=$2; shift 2
    echo "$(date '+%F %T') start $name: $*" >> out/runs.txt
    nice -n 10 java -Xms$heap -Xmx$heap -XX:+UseParallelGC -cp cls:$J "$@" bergdb.core.NodeSizeBench > out/$name.txt 2>&1
    echo "$(date '+%F %T') end $name: $(tail -1 out/$name.txt)" >> out/runs.txt
}
for n in 8 14 30 62; do
    r n$n-sd50-1M 3g -Dwb.keys=1000000 -Dwb.window=100000 -Dwb.node=$n -Dwb.sd=50000000 -Dwb.updates=2000000 -Dwb.reach=true
    r n$n-sd200-1M 3g -Dwb.keys=1000000 -Dwb.window=100000 -Dwb.node=$n -Dwb.sd=200000000 -Dwb.updates=6000000 -Dwb.reach=true
done
echo "$(date '+%F %T') NS1 DONE" >> out/runs.txt
