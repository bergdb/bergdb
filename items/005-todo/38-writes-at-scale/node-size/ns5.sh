#!/bin/sh
# 005-38 node-size study, phase D (after ns4.sh): separate leaf and inner sizes (the scratch
# Dag of mixed/, clsmixed: -Dns.leaf; inner nodes take the builder's size) at 5M keys, and a
# short sanity check; one JVM of at most 4 GB at a time.
cd "$(dirname "$0")"
J=../bergdb/java/build/bergdb.jar
while ! grep -q "NS4 DONE" out/runs.txt; do sleep 20; done
r() {   # r NAME HEAP FLAGS...
    name=$1; heap=$2; shift 2
    echo "$(date '+%F %T') start $name: $*" >> out/runs.txt
    nice -n 10 java -Xms$heap -Xmx$heap -XX:+UseParallelGC -cp cls2:clsmixed:$J "$@" bergdb.core.NodeSizeBench > out/$name.txt 2>&1
    echo "$(date '+%F %T') end $name: $(tail -1 out/$name.txt)" >> out/runs.txt
}
r mixcheck-L14-I62 1g -Dwb.keys=200000 -Dwb.window=100000 -Dwb.node=62 -Dns.leaf=14 -Dwb.sd=10000000
K5="-Dwb.keys=5000000 -Dwb.window=250000"
r m-L14I30-sd50-5M 4g $K5 -Dwb.node=30 -Dns.leaf=14 -Dwb.sd=50000000 -Dwb.updates=2000000
r m-L14I62-sd50-5M 4g $K5 -Dwb.node=62 -Dns.leaf=14 -Dwb.sd=50000000 -Dwb.updates=2000000
r m-L14I30-sd200-5M 4g $K5 -Dwb.node=30 -Dns.leaf=14 -Dwb.sd=200000000 -Dwb.updates=5000000
r m-L14I62-sd200-5M 4g $K5 -Dwb.node=62 -Dns.leaf=14 -Dwb.sd=200000000 -Dwb.updates=5000000
echo "$(date '+%F %T') NS5 DONE" >> out/runs.txt
