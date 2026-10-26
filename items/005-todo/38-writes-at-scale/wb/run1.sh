#!/bin/sh
# 005-38 write-bytes matrix, sequential, in memory.
cd "$(dirname "$0")"
J=../bergdb/java/build/bergdb.jar
mkdir -p out
r() {   # r NAME HEAP FLAGS...
    name=$1; heap=$2; shift 2
    echo "$(date '+%F %T') start $name: $*" >> out/runs.txt
    nice -n 10 java -Xms$heap -Xmx$heap -XX:+UseParallelGC -cp cls:$J "$@" bergdb.core.WriteBench > out/$name.txt 2>&1
    echo "$(date '+%F %T') end $name: $(tail -1 out/$name.txt)" >> out/runs.txt
}
r base-10M 6g -Dwb.keys=10000000 -Dwb.window=500000
r sd50-10M 6g -Dwb.keys=10000000 -Dwb.window=500000 -Dwb.sd=50000000
r sd200-10M 6g -Dwb.keys=10000000 -Dwb.window=500000 -Dwb.sd=200000000
r n14-10M 6g -Dwb.keys=10000000 -Dwb.window=500000 -Dwb.node=14
r n62-10M 6g -Dwb.keys=10000000 -Dwb.window=500000 -Dwb.node=62
r seq-10M 6g -Dwb.keys=10000000 -Dwb.window=500000 -Dwb.order=seq
r tx100-10M 6g -Dwb.keys=10000000 -Dwb.window=500000 -Dwb.tx=100
r tx10k-10M 6g -Dwb.keys=10000000 -Dwb.window=500000 -Dwb.tx=10000
r rnd24-10M 12g -Dwb.keys=10000000 -Dwb.window=500000 -Dwb.keytype=rnd24
r base-50M 20g -Dwb.keys=50000000 -Dwb.window=2500000
r sd50-50M 20g -Dwb.keys=50000000 -Dwb.window=2500000 -Dwb.sd=50000000
echo "$(date '+%F %T') ALL DONE" >> out/runs.txt
