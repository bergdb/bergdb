#!/bin/sh
# 024-31 queue 3: the span-based cap (c2s, branch head 09ec584a): the two decreases at main's
# worst points, then the steady run at 200 MB, to compare with main's byte for byte.
cd /Users/f/fl/bench/2026-11-12/pace/w || exit 1
low() {   # VARIANT FROM_MB TO_MB AT
    sh slotrun.sh $1 $1-low$2-$3-w -Dwb.sd=${2}000000 -Dwb.updates=$(($4 + 10000000)) \
        -Dwb.lowerAt=$4 -Dwb.lowerTo=${3}000000
}
low c2s 200 50 14774000
low c2s 1000 100 10027000
sh slotrun.sh c2s c2s-upd-sd200 -Dwb.sd=200000000
echo "$(date '+%F %T') Q3 DONE" >> out/runs.txt
