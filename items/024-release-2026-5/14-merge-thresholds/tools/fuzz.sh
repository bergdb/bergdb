#!/bin/sh
# 024-14: UnlinkFuzz strict (V1 with m of the set) on the frozen build b1, for one threshold set.
# Usage: fuzz.sh LABEL [m,h,c]   (no set: P5's formulas). P5's matrix (023-05) plus fault 12's modes.
B=/Users/f/fl/bench/2026-11-11/thr/b1
L=$1; T=$2
OUT=/Users/f/fl/bench/2026-11-11/thr/out/fuzz-$L.txt
P=""; [ -n "$T" ] && P="-Dbergdb.thr=$T"
: > $OUT
for sz in 8 14 30; do
  for cfg in "random 60 40 6 150 30" "random 60 70 6 150 30" "random 60 50 30 60 15" "fifo 40 0 6 100 8" "long 60 60 6 150 20" "random 400 50 60 100 6"; do
    set -- $cfg
    for mode in "-Dorder=sorted -Ddup=0" "-Dorder=shuffle -Ddup=20"; do
      java -ea $P -Dmaxnode=$sz -Dshape=$1 -Dkeys=$2 -Ddel=$3 -Dops=$4 -Dn=$5 -Dstrict=1 -Dquiet=1 $mode \
        -cp $B/bergdb.jar:$B/stress bergdb.dag.UnlinkFuzz 100 $6 2>&1 | tail -2 | sed "s/^/size=$sz shape=$1 keys=$2 del=$3 ops=$4 n=$5 $mode: /" >> $OUT
    done
  done
done
echo FUZZ DONE >> $OUT
