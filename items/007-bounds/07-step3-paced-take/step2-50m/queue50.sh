#!/bin/sh
# 006-10 (r50): 007-07's step-2 set at 50M keys on main (D4:B), most informative first.
# One 22 GB JVM at a time. A watchdog kills a run still going at 21:25 (hard stop 21:30).
cd /Users/f/fl/bench/006-10/r50 || exit 1
( until [ "$(date +%H%M)" -ge 2125 ]; do sleep 30; done
  pkill -f 'wb.rec=out/m50' && echo "$(date '+%F %T') watchdog killed a run" >> out/runs.txt ) &
wd=$!
r() { sh run50.sh "$@"; }
low() {   # FROM_MB TO_MB TAG AT
    r m50-low$1-$2-once-$3 -Dwb.sd=${1}000000 -Dwb.updates=$(($4 + 10000000)) \
        -Dwb.lowerAt=$4 -Dwb.lowerTo=${2}000000
}
r m50-upd-sd1000 -Dwb.sd=1000000000
low 1000 100 w $(python3 pick.py out/m50-upd-sd1000.rec 10000000 | cut -d' ' -f1)
r m50-del-sd1000 -Dwb.sd=1000000000 -Dwb.op=delete -Dwb.updates=40000000
r m50-upd-sd200 -Dwb.sd=200000000
low 200 50 w $(python3 pick.py out/m50-upd-sd200.rec 10000000 | cut -d' ' -f1)
r m50-upd-sd50 -Dwb.sd=50000000
for sd in 50 200; do r m50-del-sd$sd -Dwb.sd=${sd}000000 -Dwb.op=delete -Dwb.updates=8000000; done
for sd in 50 200; do r m50-one-sd$sd -Dwb.sd=${sd}000000 -Dwb.utx=1 -Dwb.updates=6000000; done
low 1000 100 t 20000000
low 200 50 t 20000000
echo "$(date '+%F %T') QUEUE50 DONE" >> out/runs.txt
kill $wd 2>/dev/null
