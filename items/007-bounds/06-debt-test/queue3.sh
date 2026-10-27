#!/bin/sh
# 007-06, queue 3: the paced take, the decrease following the section down (wb.lowerGap: every
# 10 update transactions, sd = max(new sd, section / 2)), at the same points as queue 2.
cd /Users/f/fl/bench/006-09/w8
until grep -q "QUEUE2 DONE" out/runs.txt; do sleep 20; done
fol() {   # FROM_MB TO_MB TAG AT
    sh run.sh paced2 paced2-low$1-$2-follow-$3 -Dwb.sd=${1}000000 -Dwb.updates=$(($4 + 10000000)) \
        -Dwb.lowerAt=$4 -Dwb.lowerTo=${2}000000 -Dwb.lowerGap=10
}
fol 1000 100 w $(python3 pick.py out/paced-upd-sd1000.rec 10000000 | cut -d' ' -f1)
fol 200 50 w $(python3 pick.py out/paced-upd-sd200.rec 10000000 | cut -d' ' -f1)
fol 1000 100 t 20000000
fol 200 50 t 20000000
echo "$(date '+%F %T') QUEUE3 DONE" >> out/runs.txt
