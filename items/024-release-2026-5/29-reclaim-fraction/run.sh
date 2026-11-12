#!/bin/sh
# fracm (024-29): build the clone, then FracRuns for workloads a to d, two JVMs at a time.
# Usage: sh run.sh [extra props...]   Output in ../out/.
cd /Users/f/fl/bench/2026-11-12/fracm/clone/java || exit 1
O=/Users/f/fl/bench/2026-11-12/fracm/out
JAVA=$JAVA_HOME/bin/java
./build.sh > $O/build.txt 2>&1 || { tail -20 $O/build.txt; echo BUILD FAILED; exit 1; }
r() { w=$1; shift
  $JAVA -Xmx4g --add-opens java.base/java.util=ALL-UNNAMED -cp build/bergdb.jar:build/stress \
    bergdb.core.FracRuns work=$w dir=build/frac-data-$w "$@" > $O/work-$w.txt 2>&1
  echo "work $w exit $? $(date +%H:%M:%S)"; }
echo "start $(date +%H:%M:%S)"
r a fs=0.25,0.375,0.4,0.5 "$@" & r b "$@" & wait
r c "$@" & r d fs=0.25,0.375,0.5 "$@" & wait
rm -rf build/frac-data-*
echo "end $(date +%H:%M:%S)"
