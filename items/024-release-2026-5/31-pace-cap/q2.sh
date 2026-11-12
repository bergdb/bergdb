#!/bin/sh
# 024-31 queue 2: the one-call decreases at main's worst points (pick.py on main's steady runs
# after 10M updates; 007-07, section 10.4), 10M more updates after the call; main, c2, c4.
# Then c2's steady run at 200 MB, to compare with main's byte for byte; then c4 at 1000 to 100.
cd /Users/f/fl/bench/2026-11-12/pace/w || exit 1
low() {   # VARIANT FROM_MB TO_MB AT
    sh slotrun.sh $1 $1-low$2-$3-w -Dwb.sd=${2}000000 -Dwb.updates=$(($4 + 10000000)) \
        -Dwb.lowerAt=$4 -Dwb.lowerTo=${3}000000
}
P200=$(python3 pick.py out/main-upd-sd200.rec 10000000 | cut -d' ' -f1)
P1000=$(python3 pick.py out/main-upd-sd1000.rec 10000000 | cut -d' ' -f1)
echo "$(date '+%F %T') picks: 200 MB at $P200, 1000 MB at $P1000" >> out/runs.txt
for v in main c2 c4; do low $v 200 50 $P200; done
for v in main c2; do low $v 1000 100 $P1000; done
sh slotrun.sh c2 c2-upd-sd200 -Dwb.sd=200000000
low c4 1000 100 $P1000
echo "$(date '+%F %T') Q2 DONE" >> out/runs.txt
