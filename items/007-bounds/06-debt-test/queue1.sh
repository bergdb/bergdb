#!/bin/sh
# 007-06, queue 1 on today's take: the first workload with the section and the debt, deletes, single puts.
cd /Users/f/fl/bench/006-09/w8
for sd in 50 200 1000; do sh run.sh head head-upd-sd$sd -Dwb.sd=${sd}000000; done
for sd in 50 200 1000; do sh run.sh head head-del-sd$sd -Dwb.sd=${sd}000000 -Dwb.op=delete -Dwb.updates=8000000; done
for sd in 50 200; do sh run.sh head head-one-sd$sd -Dwb.sd=${sd}000000 -Dwb.utx=1 -Dwb.updates=6000000; done
echo "$(date '+%F %T') QUEUE1 DONE" >> out/runs.txt
