#!/bin/sh
# fracm (024-29): one timing pass of workload a at 1/4, 3/8, 1/2 (puts a second), both slots.
S=/Users/f/fl/bench/2026-11-11/slot.sh
O=/Users/f/fl/bench/2026-11-12/fracm/out
D=$(sh $S take-timing fracm "024-29 FracRuns a, puts a second")
echo "slots $D $(date +%H:%M:%S)"
cd /Users/f/fl/bench/2026-11-12/fracm/clone/java || { sh $S release $D; exit 1; }
$JAVA_HOME/bin/java -Xmx4g --add-opens java.base/java.util=ALL-UNNAMED -cp build/bergdb.jar:build/stress \
  bergdb.core.FracRuns work=a fs=0.25,0.375,0.5 timing=1 dir=build/frac-data-t > $O/timing-a.txt 2>&1
echo "exit $? $(date +%H:%M:%S)"
rm -rf build/frac-data-t
sh $S release $D
grep -E "^PUTS|^RESULT" $O/timing-a.txt
