#!/bin/sh
# 024-07: draining traces, beside level3.sh's reclaim set: reclaim traces with many deletes,
# so that deletes empty whole subtrees and segment trees before the cuts (the premise of the
# cut without a touch of a key range: a delete unlinks what it empties). Each trace is
# checked by the Lean checker: C-A (with touchPath), C-S, C-CUT at every cut.
# Usage: drain.sh CLONE [seeds]   (CLONE: a clone with java/build and lean/.lake built)
# A larger configuration (1,000 keys, 1,000 transactions) was dropped: the checker's C-CUT
# took more than 3 minutes on one trace of it.
C=$1
SEEDS=${2:-5}
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=$HERE/out/drain
mkdir -p $OUT
# Run once: a second call prints the first one's results (a trace takes 5 to 10 s, one core).
if [ -f $OUT/done.txt ]; then cat $OUT/summary.txt $OUT/done.txt; exit 0; fi
rm -f $OUT/*.trace $OUT/*.txt
cd $C/java || exit 1
CP=build/bergdb.jar:build/stress
configs() {
    echo "d-del60 -Dn=600 -Dkeys=200 -Dmaxnode=8 -Dsd=500 -Dops=8 -Ddel=60 -Dretain=1 -Dprobe=10"
    echo "d-del80 -Dn=800 -Dkeys=300 -Dmaxnode=8 -Dsd=500 -Dops=8 -Ddel=80 -Dretain=1 -Dprobe=10"
    echo "d-long  -Dn=600 -Dkeys=200 -Dmaxnode=8 -Dsd=500 -Dops=8 -Dlong=1 -Ddel=60 -Dretain=2 -Dprobe=10"
}
configs | while read name props; do
    s=1
    while [ $s -le $SEEDS ]; do
        java -ea $props -cp $CP bergdb.core.TraceExport $s $OUT/$name-$s.trace > $OUT/$name-$s.export.txt 2>&1
        ../lean/.lake/build/bin/tracecheck $OUT/$name-$s.trace > $OUT/$name-$s.check.txt 2>&1
        echo "$name-$s: cuts $(grep -c '^CUT ' $OUT/$name-$s.trace), ERROR lines $(grep -c '^ERROR' $OUT/$name-$s.trace), failing probes $(grep '^PROBE' $OUT/$name-$s.trace | grep -c ' fail '), $(grep '^C-CUT cuts' $OUT/$name-$s.check.txt | cut -c1-60), $(grep '^C-A assumptions' $OUT/$name-$s.check.txt | cut -c1-60), $(tail -1 $OUT/$name-$s.check.txt)"
        s=$((s + 1))
    done
done > $OUT/summary.txt
cat $OUT/summary.txt
rm -f $OUT/*.trace
echo "traces: $(wc -l < $OUT/summary.txt | tr -d ' '), not TRACECHECK OK: $(grep -vc 'TRACECHECK OK' $OUT/summary.txt), cuts: $(sed -E 's/.*: cuts ([0-9]+),.*/\1/' $OUT/summary.txt | awk '{s+=$1} END {print s}')" | tee $OUT/done.txt
