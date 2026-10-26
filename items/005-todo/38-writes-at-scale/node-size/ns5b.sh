#!/bin/sh
# 005-38 node-size study, phase D2 (after ns5.sh, before ns6.sh): separate sizes with large
# inner nodes over leaves of 30, and random 24-byte keys at 1M; one JVM of at most 4 GB.
cd "$(dirname "$0")"
J=../bergdb/java/build/bergdb.jar
while ! grep -q "NS5 DONE" out/runs.txt; do sleep 20; done
r() {   # r NAME HEAP CP FLAGS...
    name=$1; heap=$2; cp=$3; shift 3
    echo "$(date '+%F %T') start $name: $*" >> out/runs.txt
    nice -n 10 java -Xms$heap -Xmx$heap -XX:+UseParallelGC -cp $cp:$J "$@" bergdb.core.NodeSizeBench > out/$name.txt 2>&1
    echo "$(date '+%F %T') end $name: $(tail -1 out/$name.txt)" >> out/runs.txt
}
K5="-Dwb.keys=5000000 -Dwb.window=250000"
r m-L30I62-sd50-5M 4g cls2:clsmixed $K5 -Dwb.node=62 -Dns.leaf=30 -Dwb.sd=50000000 -Dwb.updates=2000000
r m-L30I62-sd200-5M 4g cls2:clsmixed $K5 -Dwb.node=62 -Dns.leaf=30 -Dwb.sd=200000000 -Dwb.updates=5000000
for n in 30 14 62; do
    r rnd-n$n-sd50-1M 4g cls2 -Dwb.keys=1000000 -Dwb.window=100000 -Dwb.keytype=rnd24 -Dwb.node=$n -Dwb.sd=50000000 -Dwb.updates=3000000
done
echo "$(date '+%F %T') NS5B DONE" >> out/runs.txt
