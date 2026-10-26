#!/bin/sh
# The cost of reclaim over a grid (2026-10-13; bergdb 011-04, "Level 3 cost"):
# ReclaimCost for each workload, value size and K (updates per key within the
# retention duration), and a baseline without reclaim (K = 0) for each workload and
# value size. Prints WE and SE per run; the logs are in $OUT.
#
# Usage: java/stress/reclaimgrid.sh [extra -D options for every run]
#   P=N  runs in parallel (default 3); each takes up to 10 GB of heap.
#   LIVE=N  live user data in bytes (default 30000000).
#   WORK="uniform hot cold", SIZES="100 1000 10000", K="0 0.01 0.1 1 10": the grid;
#   K=0 is the baseline. The baselines and runs with K >= 10 use a FileStream on disk.
#   OUT=DIR  logs (default build/reclaimgrid).

cd "$(dirname "$0")/.."

JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi
P=${P:-3}
LIVE=${LIVE:-30000000}
WORK=${WORK:-"uniform hot cold"}
SIZES=${SIZES:-"100 1000 10000"}
K=${K:-"0 0.01 0.1 1 10"}
OUT=${OUT:-build/reclaimgrid}

./build.sh > /dev/null || { echo "build failed"; exit 1; }
mkdir -p $OUT
find $OUT -type f -delete

# Largest runs first, so that they do not end up last and alone.
for k in $(echo $K | tr ' ' '\n' | sort -rn); do
    for s in $SIZES; do
        for w in $WORK; do echo "$w $s $k"; done
    done
done | xargs -P $P -L 1 sh -c '
    D=""; case $2 in 0|10|10.*|[1-9][0-9]*) D="-Ddisk=1";; esac
    '"$JAVA"' -ea -Xmx10g -Dlive='"$LIVE"' -Dwork=$0 -Dvalsize=$1 -Dk=$2 $D '"$*"' \
        -cp build/bergdb.jar:build/stress bergdb.core.ReclaimCost > '"$OUT"'/$0-v$1-k$2.txt 2>&1
    grep -q "^RECLAIMCOST OK" '"$OUT"'/$0-v$1-k$2.txt || echo "FAILED: $0 valsize=$1 k=$2"'

for f in $OUT/*.txt; do
    grep '^RESULT' $f || echo "NO RESULT: $f"
done
