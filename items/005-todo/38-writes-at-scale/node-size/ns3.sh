#!/bin/sh
# 005-38 node-size study, phase B: load + random updates (the steady state at a fixed size),
# 1M and 5M keys, one JVM of at most 4 GB at a time (until wb's RUN3 DONE).
cd "$(dirname "$0")"
J=../bergdb/java/build/bergdb.jar
mkdir -p out
r() {   # r NAME HEAP FLAGS...
    name=$1; heap=$2; shift 2
    echo "$(date '+%F %T') start $name: $*" >> out/runs.txt
    nice -n 10 java -Xms$heap -Xmx$heap -XX:+UseParallelGC -cp cls:$J "$@" bergdb.core.NodeSizeBench > out/$name.txt 2>&1
    echo "$(date '+%F %T') end $name: $(tail -1 out/$name.txt)" >> out/runs.txt
}
K1="-Dwb.keys=1000000 -Dwb.window=100000"
for n in 30 14 62 8; do
    r u-n$n-sd50-1M 4g $K1 -Dwb.node=$n -Dwb.sd=50000000 -Dwb.updates=5000000 -Dwb.reach=true
    r u-n$n-sd200-1M 4g $K1 -Dwb.node=$n -Dwb.sd=200000000 -Dwb.updates=12000000
done
K5="-Dwb.keys=5000000 -Dwb.window=250000"
for n in 30 14 62 8; do
    r u-n$n-sd50-5M 4g $K5 -Dwb.node=$n -Dwb.sd=50000000 -Dwb.updates=2000000 -Dwb.reach=true
done
for n in 30 14 62; do
    r u-n$n-sd200-5M 4g $K5 -Dwb.node=$n -Dwb.sd=200000000 -Dwb.updates=5000000
done
echo "$(date '+%F %T') NS3 DONE" >> out/runs.txt
