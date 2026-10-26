#!/bin/sh
# 005-38 node-size study, phase E (after wb's RUN3 DONE and ns5.sh): 10M keys + 30M updates
# and 50M keys + 20M updates (the coordinator's run3 setup), nodes 14, 62 (and 8, mixed);
# one JVM at a time, at most 22 GB; waits while another session's big JVM runs; starts
# nothing after 21:00 (another session's block at 22:30).
cd "$(dirname "$0")"
J=../bergdb/java/build/bergdb.jar
while ! grep -q "RUN3 DONE" ../wb/out/runs.txt || ! grep -q "NS5C DONE" out/runs.txt; do sleep 30; done
busy() { pgrep -f "ScaleBench|Soak|bergdb.dev.props|before-commit|level[1-4].sh|performance.sh|night.sh|bergdb.core.WriteBench" > /dev/null; }
r() {   # r NAME HEAP CP FLAGS...
    name=$1; heap=$2; cp=$3; shift 3
    while busy; do sleep 60; done
    if [ "$(date +%H)" -ge 21 ]; then echo "$(date '+%F %T') skipped $name (after 21:00)" >> out/runs.txt; return; fi
    echo "$(date '+%F %T') start $name: $*" >> out/runs.txt
    nice -n 10 java -Xms$heap -Xmx$heap -XX:+UseParallelGC -cp $cp:$J "$@" bergdb.core.NodeSizeBench > out/$name.txt 2>&1
    echo "$(date '+%F %T') end $name: $(tail -1 out/$name.txt)" >> out/runs.txt
}
R=-Dwb.ring=1300000000
K10="-Dwb.keys=10000000 -Dwb.window=1000000 -Dwb.updates=30000000 $R"
K50="-Dwb.keys=50000000 -Dwb.window=2500000 -Dwb.updates=20000000 $R"
for sd in 200 1000 50; do
    r u-n14-sd$sd-10M 14g cls2 $K10 -Dwb.node=14 -Dwb.sd=${sd}000000
    r u-n62-sd$sd-10M 12g cls2 $K10 -Dwb.node=62 -Dwb.sd=${sd}000000
done
for sd in 200 1000 50; do
    r u-n14-sd$sd-50M 22g cls2 $K50 -Dwb.node=14 -Dwb.sd=${sd}000000
done
for sd in 1000 200; do
    r u-n62-sd$sd-50M 16g cls2 $K50 -Dwb.node=62 -Dwb.sd=${sd}000000
done
r u-n8-sd200-10M 20g cls2 $K10 -Dwb.node=8 -Dwb.sd=200000000
r m-L14I62-sd200-10M 14g cls2:clsmixed $K10 -Dwb.node=62 -Dns.leaf=14 -Dwb.sd=200000000
r m-L14I62-sd1000-10M 14g cls2:clsmixed $K10 -Dwb.node=62 -Dns.leaf=14 -Dwb.sd=1000000000
echo "$(date '+%F %T') NS6 DONE" >> out/runs.txt
