#!/bin/sh
# 005-38, node size 30: startup distances 200 and 1000 MB; after run1.sh.
cd "$(dirname "$0")"
J=../bergdb/java/build/bergdb.jar
until grep -q "ALL DONE" out/runs.txt; do sleep 30; done
r() {   # r NAME HEAP FLAGS...
    name=$1; heap=$2; shift 2
    echo "$(date '+%F %T') start $name: $*" >> out/runs.txt
    nice -n 10 java -Xms$heap -Xmx$heap -XX:+UseParallelGC -cp cls:$J "$@" bergdb.core.WriteBench > out/$name.txt 2>&1
    echo "$(date '+%F %T') end $name: $(tail -1 out/$name.txt)" >> out/runs.txt
}
r sd1000-10M 8g -Dwb.keys=10000000 -Dwb.window=500000 -Dwb.sd=1000000000 -Dwb.ring=1300000000
r sd200-50M 20g -Dwb.keys=50000000 -Dwb.window=2500000 -Dwb.sd=200000000
r sd1000-50M 22g -Dwb.keys=50000000 -Dwb.window=2500000 -Dwb.sd=1000000000 -Dwb.ring=1300000000
echo "$(date '+%F %T') RUN2 DONE" >> out/runs.txt
