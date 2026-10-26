#!/bin/sh
# Cross-check: the coordinator's WriteBench (wb/cls3) and NodeSizeBench give the same bytes.
cd "$(dirname "$0")"
J=../bergdb/java/build/bergdb.jar
F="-Dwb.keys=1000000 -Dwb.updates=3000000 -Dwb.window=100000 -Dwb.sd=50000000"
nice -n 10 java -Xms3g -Xmx3g -XX:+UseParallelGC -cp ../wb/cls3:$J $F bergdb.core.WriteBench > out/xcheck-wb.txt 2>&1
nice -n 10 java -Xms3g -Xmx3g -XX:+UseParallelGC -cp cls:$J $F -Dwb.node=30 bergdb.core.NodeSizeBench > out/xcheck-ns.txt 2>&1
