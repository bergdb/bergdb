#!/bin/sh
# 005-38 node-size study, phase C (after ns3.sh): the restart check, and runs that count the
# writes of replaced (old) node versions (cls2: wb.replaced); one JVM of at most 4 GB.
cd "$(dirname "$0")"
J=../bergdb/java/build/bergdb.jar
while ! grep -q "NS3 DONE" out/runs.txt; do sleep 20; done
echo "$(date '+%F %T') start restart-check" >> out/runs.txt
nice -n 10 java -Xmx1g -cp cls2:$J bergdb.core.RestartNodeSize > out/restart-check.txt 2>&1
echo "$(date '+%F %T') end restart-check" >> out/runs.txt
r() {   # r NAME HEAP FLAGS...
    name=$1; heap=$2; shift 2
    echo "$(date '+%F %T') start $name: $*" >> out/runs.txt
    nice -n 10 java -Xms$heap -Xmx$heap -XX:+UseParallelGC -cp cls2:$J "$@" bergdb.core.NodeSizeBench > out/$name.txt 2>&1
    echo "$(date '+%F %T') end $name: $(tail -1 out/$name.txt)" >> out/runs.txt
}
K1="-Dwb.keys=1000000 -Dwb.window=100000 -Dwb.replaced=true"
r r-n30-sd50-1M 4g $K1 -Dwb.node=30 -Dwb.sd=50000000 -Dwb.updates=3000000
r r-n14-sd50-1M 4g $K1 -Dwb.node=14 -Dwb.sd=50000000 -Dwb.updates=3000000
r r-n62-sd50-1M 4g $K1 -Dwb.node=62 -Dwb.sd=50000000 -Dwb.updates=3000000
r r-n30-sd200-1M 4g $K1 -Dwb.node=30 -Dwb.sd=200000000 -Dwb.updates=10000000
r r-n30-sd50-5M 4g -Dwb.keys=5000000 -Dwb.window=250000 -Dwb.replaced=true -Dwb.node=30 -Dwb.sd=50000000 -Dwb.updates=2000000
echo "$(date '+%F %T') NS4 DONE" >> out/runs.txt
