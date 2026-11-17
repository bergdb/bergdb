#!/bin/sh
# 007-07 (D4:B): 007-06's step-2 runs on the patched build (step3.diff and D4:B on a5ad51c,
# variant d4b): queue 5's steady runs (updates, single puts, deletes), then the one-call
# decreases at queue 4's points (the worst point after 10M updates, from pick.py on this
# build's steady run, and at 20M), which with D4:B in the code are 007-06's "pace".
# Waits for the gates (one 12 GB JVM at a time, not beside the level scripts). W holds
# 007-06's run.sh, pick.py, summary.py and tables.py (06-debt-test/), WriteBench compiled
# into cls-d4b, and the patched build's jar in d4b/java/build/. About 55 minutes on F53.
W=/Users/f/fl/bench/006-09/d2-007-07-runs/w8
cd $W || exit 1
export W
until grep -q "GATES DONE" ../gates/gates.log; do sleep 30; done
r() { sh run.sh d4b "$@"; }
for sd in 1000 200 50; do r d4b-upd-sd$sd -Dwb.sd=${sd}000000; done
for sd in 50 200; do r d4b-one-sd$sd -Dwb.sd=${sd}000000 -Dwb.utx=1 -Dwb.updates=6000000; done
for sd in 50 200 1000; do r d4b-del-sd$sd -Dwb.sd=${sd}000000 -Dwb.op=delete -Dwb.updates=8000000; done
low() {   # FROM_MB TO_MB TAG AT
    r d4b-low$1-$2-once-$3 -Dwb.sd=${1}000000 -Dwb.updates=$(($4 + 10000000)) \
        -Dwb.lowerAt=$4 -Dwb.lowerTo=${2}000000
}
low 1000 100 w $(python3 pick.py out/d4b-upd-sd1000.rec 10000000 | cut -d' ' -f1)
low 200 50 w $(python3 pick.py out/d4b-upd-sd200.rec 10000000 | cut -d' ' -f1)
low 1000 100 t 20000000
low 200 50 t 20000000
echo "$(date '+%F %T') QUEUE D4B DONE" >> out/runs.txt
