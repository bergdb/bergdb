#!/bin/sh
# bergdb 024-09, A3: more reclaim traces with draining workloads, export only, for cover.py.
cd /Users/f/fl/bench/2026-11-11/tie/clone/java
OUT=/Users/f/fl/bench/2026-11-11/tie/a3/traces
mkdir -p $OUT
cfgs() {
  echo "c-drain   -Dn=800 -Dkeys=30 -Dmaxnode=8 -Dsd=200 -Dops=6 -Ddel=60 -Dretain=1"
  echo "c-drain2  -Dn=800 -Dkeys=120 -Dmaxnode=8 -Dsd=300 -Dops=10 -Ddel=55 -Dretain=1"
  echo "c-long    -Dn=800 -Dkeys=120 -Dmaxnode=8 -Dsd=300 -Dops=10 -Ddel=55 -Dlong=2 -Dretain=1"
  echo "c-big     -Dn=600 -Dkeys=300 -Dmaxnode=8 -Dsd=500 -Dops=30 -Ddel=55 -Dlong=2 -Dretain=2"
  echo "c-14      -Dn=800 -Dkeys=400 -Dmaxnode=14 -Dsd=500 -Dops=20 -Ddel=52 -Dretain=1"
}
cfgs | while read name props; do
  s=1
  while [ $s -le 12 ]; do
    for k in 0 1 2 3; do
      ss=$((s + k))
      java -ea $props -cp build/bergdb.jar:build/stress bergdb.core.TraceExport $ss $OUT/$name-$ss.trace > $OUT/$name-$ss.export.txt 2>&1 &
    done
    wait
    s=$((s + 4))
  done
  echo "$name: $(python3 -I /Users/f/fl/bench/2026-11-11/tie/a3/cover.py $OUT/$name-*.trace | tail -1)"
  echo "   $(grep -h 'Dag counters' $OUT/$name-*.export.txt | awk '{u+=$4; t+=$7; c+=$13; r+=$NF} END {print "unlinked " u+0 ", taken back " t+0 ", collapses " c+0 ", empty keys pointed to the next child " r+0}'); errors $(grep -L ' 0 errors' $OUT/$name-*.export.txt | wc -l | tr -d ' ')"
done
echo MORE DONE
