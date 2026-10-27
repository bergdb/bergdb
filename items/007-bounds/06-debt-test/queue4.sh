#!/bin/sh
# 007-06, queue 4: the paced take with a probe (paced3: TransSeq.deadlineDistance): one call to
# the new distance, so that the pace uses it at once, with the deadline at the lag, lowered every
# 10 update transactions to max(2 new sd, lag). Same points as queues 2 and 3.
cd /Users/f/fl/bench/006-09/w8
until grep -q "QUEUE3 DONE" out/runs.txt; do sleep 20; done
pace() {   # FROM_MB TO_MB TAG AT
    sh run.sh paced3 paced3-low$1-$2-pace-$3 -Dwb.sd=${1}000000 -Dwb.updates=$(($4 + 10000000)) \
        -Dwb.lowerAt=$4 -Dwb.lowerTo=${2}000000 -Dwb.lowerGap=10 -Dwb.lowerPace=true
}
pace 1000 100 w $(python3 pick.py out/paced-upd-sd1000.rec 10000000 | cut -d' ' -f1)
pace 200 50 w $(python3 pick.py out/paced-upd-sd200.rec 10000000 | cut -d' ' -f1)
pace 1000 100 t 20000000
pace 200 50 t 20000000
echo "$(date '+%F %T') QUEUE4 DONE" >> out/runs.txt
