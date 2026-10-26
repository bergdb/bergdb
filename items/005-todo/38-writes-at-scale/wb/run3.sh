#!/bin/sh
# 005-38, node size 30: load, then random updates of the loaded keys, at startup distances
# 50, 200 and 1000 MB; the updates measure the steady state at a fixed size.
cd "$(dirname "$0")"
J=../bergdb/java/build/bergdb.jar
r() {   # r NAME HEAP FLAGS...
    name=$1; heap=$2; shift 2
    echo "$(date '+%F %T') start $name: $*" >> out/runs.txt
    nice -n 10 java -Xms$heap -Xmx$heap -XX:+UseParallelGC -cp cls3:$J "$@" bergdb.core.WriteBench > out/$name.txt 2>&1
    echo "$(date '+%F %T') end $name: $(tail -1 out/$name.txt)" >> out/runs.txt
}
R=-Dwb.ring=1300000000
r u-sd50-10M 12g -Dwb.keys=10000000 -Dwb.updates=30000000 -Dwb.window=1000000 -Dwb.sd=50000000 $R
r u-sd200-10M 12g -Dwb.keys=10000000 -Dwb.updates=30000000 -Dwb.window=1000000 -Dwb.sd=200000000 $R
r u-sd1000-10M 12g -Dwb.keys=10000000 -Dwb.updates=30000000 -Dwb.window=1000000 -Dwb.sd=1000000000 $R
r u-sd50-50M 22g -Dwb.keys=50000000 -Dwb.updates=20000000 -Dwb.window=2500000 -Dwb.sd=50000000 $R
r u-sd200-50M 22g -Dwb.keys=50000000 -Dwb.updates=20000000 -Dwb.window=2500000 -Dwb.sd=200000000 $R
r u-sd1000-50M 22g -Dwb.keys=50000000 -Dwb.updates=20000000 -Dwb.window=2500000 -Dwb.sd=1000000000 $R
echo "$(date '+%F %T') RUN3 DONE" >> out/runs.txt
