#!/bin/sh
# 028-12: scaled runs, the record limit lowered (StoredTrans.recordLimit) to 4.88, 1 and
# 0.5 MB, so that the debt is 1 to 50 times the room; 1M keys, sd 5 MB, transactions of 100
# puts (50 at 0.5 MB: 005-31's dirty limit refuses larger ones), or single puts. "big":
# costly records, up to 80 % of the limit, beyond what L5 allows at the real limit (1.6 %).
R=$(dirname "$0")
S="-Dtb.keys=1000000 -Dtb.sd=5000000 -Dtb.tx=100 -Dtb.utx=100 -Dtb.updates=10000000"
sh $R/run.sh s-r4.9 4g $S -Dtb.recordLimit=4880000
sh $R/run.sh s-r4.9-big78k 4g $S -Dtb.recordLimit=4880000 -Dtb.big=78000 -Dtb.bigEvery=10
sh $R/run.sh s-r1 4g $S -Dtb.recordLimit=1000000
sh $R/run.sh s-r1-big800k 4g $S -Dtb.recordLimit=1000000 -Dtb.big=800000 -Dtb.bigEvery=10
sh $R/run.sh s-r0.5 4g $S -Dtb.recordLimit=500000 -Dtb.utx=50 -Dtb.tx=50
sh $R/run.sh s-r0.5-big400k 4g $S -Dtb.recordLimit=500000 -Dtb.utx=50 -Dtb.tx=50 -Dtb.big=400000 -Dtb.bigEvery=10
sh $R/run.sh s-r1-one 4g $S -Dtb.recordLimit=1000000 -Dtb.utx=1 -Dtb.updates=2000000
sh $R/run.sh s-r1-one-big800k 4g $S -Dtb.recordLimit=1000000 -Dtb.utx=1 -Dtb.updates=2000000 -Dtb.big=800000 -Dtb.bigEvery=200
sh $R/run.sh s-r1-sd1-big850k 4g $S -Dtb.recordLimit=1000000 -Dtb.sd=1000000 -Dtb.big=850000 -Dtb.bigEvery=10
sh $R/run.sh s-r1-one-big850k 4g $S -Dtb.recordLimit=1000000 -Dtb.utx=1 -Dtb.updates=2000000 -Dtb.big=850000 -Dtb.bigEvery=20
echo "$(date '+%F %T') SCALED DONE" >> /Users/f/fl/bench/2026-11-13/takebytes/out/runs.txt
