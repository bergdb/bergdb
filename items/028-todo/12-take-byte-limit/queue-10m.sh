#!/bin/sh
# 028-12: the real record limit, 10M keys, one JVM at a time: sd 1000 MB (the most
# setStartupDistance sets) and sd 2^31 - 1 (the most DbBuilder.startupDistance allows).
R=$(dirname "$0")
K="-Dtb.keys=10000000 -Dtb.ring=1300000000"
sh $R/run.sh r10m-sd1000 14g $K -Dtb.sd=1000000000 -Dtb.updates=30000000
sh $R/run.sh r10m-sdmax 16g $K -Dtb.sd=2147483647 -Dtb.updates=40000000
# Costly records of 33 MB at sd 1000 MB: the pace gives each a large share of D.
sh $R/run.sh r10m-big-sd1000 16g $K -Dtb.sd=1000000000 -Dtb.updates=20000000 -Dtb.big=33000000 -Dtb.bigEvery=200 -Dtb.bigCount=40
echo "$(date '+%F %T') 10M DONE" >> /Users/f/fl/bench/2026-11-13/takebytes/out/runs.txt
