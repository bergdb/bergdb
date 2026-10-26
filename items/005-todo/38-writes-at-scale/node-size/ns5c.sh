#!/bin/sh
# 005-38 node-size study, phase D3 (after ns5b.sh, before ns6.sh): sequential loads (the best
# case) at 10M keys; one JVM of at most 4 GB.
cd "$(dirname "$0")"
J=../bergdb/java/build/bergdb.jar
while ! grep -q "NS5B DONE" out/runs.txt; do sleep 20; done
r() {   # r NAME HEAP CP FLAGS...
    name=$1; heap=$2; cp=$3; shift 3
    echo "$(date '+%F %T') start $name: $*" >> out/runs.txt
    nice -n 10 java -Xms$heap -Xmx$heap -XX:+UseParallelGC -cp $cp:$J "$@" bergdb.core.NodeSizeBench > out/$name.txt 2>&1
    echo "$(date '+%F %T') end $name: $(tail -1 out/$name.txt)" >> out/runs.txt
}
for n in 30 14 62; do
    r seq-n$n-sd50-10M 4g cls2 -Dwb.keys=10000000 -Dwb.window=1000000 -Dwb.order=seq -Dwb.node=$n -Dwb.sd=50000000
done
echo "$(date '+%F %T') NS5C DONE" >> out/runs.txt
