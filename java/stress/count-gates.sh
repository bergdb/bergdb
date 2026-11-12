#!/bin/sh
# Count gates of aims 2 and 3 of release 2026.5 at 1M keys (bergdb 024-30):
# stress/CountGates.java's three gates, each on counts (bytes, key nodes), not
# times (024-05, QF6):
#   G1 (BD1): the largest record, without the values in it, at most the larger
#      of 1 MB and 5 times the run's mean, under keys put in time order with
#      reclaim on (the last touch's shape, 024-07), then random overwrites.
#   G2 (BD13): the reachable key nodes at most 2 times a fresh twin's, after
#      every 30th key kept, and after a mass delete, and two reclaim iterations.
#   G3 (BD10): the stream kept, less the user's records within R, at most 6
#      times the twin's fresh stream, at its peak under steady overwrites.
#   G4 (back to empty, 023-03's T1): n keys put and deleted, then a drive of
#      40 R; kept, key nodes, dead klongs, resident objects, handles, the heap,
#      at most 2 times a hello-world twin's (the cache's table slots, ST6,
#      reported, not counted).
#   G5 (back to empty by maintain(), bergdb 024-32): as G4, with a drive of 20 R
#      of maintain() calls and no writes; kept at most 2 times the twin's plus
#      600 kB, the calls quiet in the last quarter, the rest as G4 (counts of
#      the tiny twin within twice it or it plus a_n = 10; dead klongs plus 30).
# A step of night.sh after level4; not in before-commit.sh (it takes minutes).
# About 2.5 minutes on F53 (2026-11-12). A 10M variant (n=10000000) is not a
# step; 024-30, section 6, notes it for later.
#
# Usage: java/stress/count-gates.sh [g1|g2|g3|g4|g5|all] [prop=value...]
#   the arguments go to CountGates (its class comment lists the properties).
# Output in java/build/count-gates/count-gates.txt. Prints the gate lines and
# COUNT GATES OK, or COUNT GATES FAILED and exits with status 1.

cd "$(dirname "$0")/.." || exit 1
JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi
OUT=build/count-gates
mkdir -p $OUT || exit 1

./build.sh > $OUT/build.txt 2>&1 ||
    { tail -20 $OUT/build.txt; echo "COUNT GATES FAILED: build"; exit 1; }

s=$(date +%s)
$JAVA -Xmx4g --add-opens java.base/java.util=ALL-UNNAMED \
    -cp build/bergdb.jar:build/stress bergdb.core.CountGates "$@" \
    dir=build/count-gates-data > $OUT/count-gates.txt 2>&1
status=$?
grep -E '^(G[0-9] |  G[0-9] )' $OUT/count-gates.txt
echo "Time: $(( $(date +%s) - s )) s"
last=$(tail -1 $OUT/count-gates.txt | sed 's/^\[[^]]*\] //')
if [ $status = 0 ] && [ "$last" = "COUNT GATES OK" ]; then
    echo "COUNT GATES OK"
else
    tail -5 $OUT/count-gates.txt
    echo "COUNT GATES FAILED (java/$OUT/count-gates.txt)"
    exit 1
fi
