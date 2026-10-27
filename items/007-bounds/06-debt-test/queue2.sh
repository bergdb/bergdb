#!/bin/sh
# 007-06, queue 2: the decreases on today's take, then the paced take (005-49's paced-take.diff).
# A decrease at 20M update puts (t) and before the record with the largest debt after 10M
# puts in the run without a decrease (w, from pick.py); 10M update puts after it; in one call
# (once) or in calls of at most 10 MB (steps).
cd /Users/f/fl/bench/006-09/w8
until grep -q "QUEUE1 DONE" out/runs.txt; do sleep 20; done
low() {   # VARIANT FROM_MB TO_MB TAG AT
    v=$1; from=$2; to=$3; tag=$4; at=$5
    sh run.sh $v $v-low$from-$to-once-$tag -Dwb.sd=${from}000000 -Dwb.updates=$((at + 10000000)) \
        -Dwb.lowerAt=$at -Dwb.lowerTo=${to}000000
    sh run.sh $v $v-low$from-$to-steps-$tag -Dwb.sd=${from}000000 -Dwb.updates=$((at + 10000000)) \
        -Dwb.lowerAt=$at -Dwb.lowerTo=${to}000000 -Dwb.lowerStep=10000000
}
low head 1000 100 w 28123000
low head 200 50 w 10877000
low head 1000 100 t 20000000
low head 200 50 t 20000000
echo "$(date '+%F %T') QUEUE2 HEAD DONE" >> out/runs.txt
for sd in 1000 200 50; do sh run.sh paced paced-upd-sd$sd -Dwb.sd=${sd}000000; done
low paced 1000 100 w $(python3 pick.py out/paced-upd-sd1000.rec 10000000 | cut -d' ' -f1)
low paced 200 50 w $(python3 pick.py out/paced-upd-sd200.rec 10000000 | cut -d' ' -f1)
low paced 1000 100 t 20000000
low paced 200 50 t 20000000
for sd in 50 200; do sh run.sh paced paced-one-sd$sd -Dwb.sd=${sd}000000 -Dwb.utx=1 -Dwb.updates=6000000; done
for sd in 50 200 1000; do sh run.sh paced paced-del-sd$sd -Dwb.sd=${sd}000000 -Dwb.op=delete -Dwb.updates=8000000; done
echo "$(date '+%F %T') QUEUE2 DONE" >> out/runs.txt
