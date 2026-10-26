#!/bin/sh
# 005-38 node-size study, phase A2: 10M keys at sd 50, 200 and 1000 MB, then 1M with longer
# update phases; one JVM of at most 6 GB at a time. Node 30 at sd 1000 MB comes from wb/run2.sh.
cd "$(dirname "$0")"
J=../bergdb/java/build/bergdb.jar
mkdir -p out
r() {   # r NAME HEAP FLAGS...
    name=$1; heap=$2; shift 2
    echo "$(date '+%F %T') start $name: $*" >> out/runs.txt
    nice -n 10 java -Xms$heap -Xmx$heap -XX:+UseParallelGC -cp cls:$J "$@" bergdb.core.NodeSizeBench > out/$name.txt 2>&1
    echo "$(date '+%F %T') end $name: $(tail -1 out/$name.txt)" >> out/runs.txt
}
K10="-Dwb.keys=10000000 -Dwb.window=500000"
for n in 14 62 30; do
    r n$n-sd50-10M 6g $K10 -Dwb.node=$n -Dwb.sd=50000000 -Dwb.updates=2000000 -Dwb.reach=true
done
for n in 14 62 30; do
    r n$n-sd200-10M 6g $K10 -Dwb.node=$n -Dwb.sd=200000000 -Dwb.updates=4000000 -Dwb.reach=true
done
for n in 14 62; do
    r n$n-sd1000-10M 6g $K10 -Dwb.node=$n -Dwb.sd=1000000000 -Dwb.ring=1300000000 -Dwb.reach=true
done
r n8-sd50-10M 6g $K10 -Dwb.node=8 -Dwb.sd=50000000
r n8-sd200-10M 6g $K10 -Dwb.node=8 -Dwb.sd=200000000
K1="-Dwb.keys=1000000 -Dwb.window=100000"
for n in 8 14 30 62; do
    r n$n-sd50-1M 3g $K1 -Dwb.node=$n -Dwb.sd=50000000 -Dwb.updates=3000000 -Dwb.reach=true
    r n$n-sd200-1M 3g $K1 -Dwb.node=$n -Dwb.sd=200000000 -Dwb.updates=8000000 -Dwb.reach=true
done
echo "$(date '+%F %T') NS2 DONE" >> out/runs.txt
