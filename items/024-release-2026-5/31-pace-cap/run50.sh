#!/bin/sh
# 024-31: one decrease from 1000 to 100 MB at 50M keys with the cap (c = 2, the span-based
# rule of branch 024-31-pace-cap), for a later night step. Not run on 2026-11-12. At
# 007-07's fixed "20M" point (section 11.2: 15.36 MB records without the cap), so no steady
# run is needed first. One 22 GB JVM, one slot, nice 19; about
# 30 to 60 minutes (a guess: 007-07's set of 10 runs at 50M took 3 h 20 min). The work dir is
# 024-31's (w/, variant c2s: branch 024-31-pace-cap's jar and WriteBench compiled against it);
# VARIANT=main gives the run without the cap for comparison, with the same 500 puts a
# transaction (Db.MAX_OPERATIONS since 024-17).
W=/Users/f/fl/bench/2026-11-12/pace/w
cd $W || exit 1
v=${VARIANT:-c2s}
name=$v-50m-low1000-100-t
S=/Users/f/fl/bench/2026-11-11/slot.sh
d=$(sh $S take pace50 "024-31 WriteBench 50M keys 1000 to 100 MB $v")
echo "$(date '+%F %T') start $name" >> out/runs.txt
nice -n 19 java -Xms22g -Xmx22g -XX:+UseParallelGC -cp cls-$v:$v/java/build/bergdb.jar \
    -Dwb.keys=50000000 -Dwb.tx=500 -Dwb.updates=35000000 -Dwb.window=2500000 \
    -Dwb.ring=1300000000 -Dwb.sd=1000000000 -Dwb.lowerAt=20000000 -Dwb.lowerTo=100000000 \
    -Dwb.rec=out/$name.rec bergdb.core.WriteBench > out/$name.txt 2>&1
echo "$(date '+%F %T') end $name: $(tail -1 out/$name.txt)" >> out/runs.txt
sh $S release $d
python3 catchup.py out/$name.rec
python3 ratchet.py out/$name.rec
