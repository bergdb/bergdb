#!/bin/sh
# 007-06, queue 5: 007-07's step3.diff (on fc8f7c3, clone step3): the steady runs and the one-call
# decreases at the worst points. No run starts after 21:30 (F53's quiet block from 22:30; hard
# stop 21:45).
cd /Users/f/fl/bench/006-09/w8
r() { [ "$(date +%H%M)" -lt 2130 ] && sh run.sh step3 "$@"; }
for sd in 1000 200 50; do r step3-upd-sd$sd -Dwb.sd=${sd}000000; done
for sd in 50 200; do r step3-one-sd$sd -Dwb.sd=${sd}000000 -Dwb.utx=1 -Dwb.updates=6000000; done
a=$(python3 pick.py out/step3-upd-sd1000.rec 10000000 | cut -d' ' -f1)
r step3-low1000-100-once-w -Dwb.sd=1000000000 -Dwb.updates=$((a + 10000000)) -Dwb.lowerAt=$a -Dwb.lowerTo=100000000
a=$(python3 pick.py out/step3-upd-sd200.rec 10000000 | cut -d' ' -f1)
r step3-low200-50-once-w -Dwb.sd=200000000 -Dwb.updates=$((a + 10000000)) -Dwb.lowerAt=$a -Dwb.lowerTo=50000000
for sd in 50 200 1000; do r step3-del-sd$sd -Dwb.sd=${sd}000000 -Dwb.op=delete -Dwb.updates=8000000; done
echo "$(date '+%F %T') QUEUE5 DONE" >> out/runs.txt
