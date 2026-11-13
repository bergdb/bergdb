#!/bin/sh
# 028-12: the real record limit (2^31 - 9), 1M keys: updates in transactions of 500 puts
# (L1), single puts, and costly records of 33 MB (L5's 32 MiB a transaction, in values of at
# most 8 MiB, L4), at most 50 or 60 of them (every version stays in memory).
R=$(dirname "$0")
K="-Dtb.keys=1000000 -Dtb.ring=1500000000"
sh $R/run.sh r1m-sd50 6g $K -Dtb.sd=50000000 -Dtb.updates=20000000
sh $R/run.sh r1m-sd1000 10g $K -Dtb.sd=1000000000 -Dtb.updates=20000000
sh $R/run.sh r1m-one-sd50 6g $K -Dtb.sd=50000000 -Dtb.utx=1 -Dtb.updates=5000000
sh $R/run.sh r1m-big-sd50 8g $K -Dtb.sd=50000000 -Dtb.updates=10000000 -Dtb.big=33000000 -Dtb.bigEvery=100 -Dtb.bigCount=50
sh $R/run.sh r1m-big-sd10 8g $K -Dtb.sd=10000000 -Dtb.updates=5000000 -Dtb.big=33000000 -Dtb.bigEvery=10 -Dtb.bigCount=60
echo "$(date '+%F %T') 1M DONE" >> /Users/f/fl/bench/2026-11-13/takebytes/out/runs.txt
