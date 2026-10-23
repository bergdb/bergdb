#!/bin/sh
# Probe P2 (cuts) in six configurations; outputs in runs/p2-*.txt.
# Usage: items/005-todo/11-replication/tools/p2-all.sh
set -e
cd "$(dirname "$0")/.."
T=tools/run.sh
R=runs
JO="java -ea -da:bergdb.stream.MemoryStream -Xmx2g"
CP=../../../java/build/bergdb.jar:../../../java/build/replicaprobe
$T cuts 3 10 0 > $R/p2-a-bt10.txt 2>&1
$T cuts 3 2000 0 > $R/p2-b-bt2000.txt 2>&1
$T cuts 3 10 1 > $R/p2-c-bt10-stall.txt 2>&1
$JO -Dsd=200000 -Dretain=10 -Dvalue=200 -cp $CP bergdb.core.ReplicaProbe cuts 3 10 0 \
    > $R/p2-d-bt10-sd200k.txt 2>&1
$JO -Dsd=1000000 -Dretain=60 -Dstep=100 -Dvalue=1000 -cp $CP bergdb.core.ReplicaProbe \
    cuts 2 2000 0 30000 > $R/p2-e-bt2000-sd1m.txt 2>&1
$JO -Dsd=1000000 -Dretain=60 -Dstep=100 -Dvalue=1000 -cp $CP bergdb.core.ReplicaProbe \
    cuts 2 20 0 30000 > $R/p2-f-bt20-sd1m.txt 2>&1
echo P2 ALL DONE
