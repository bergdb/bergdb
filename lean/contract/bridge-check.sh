#!/bin/sh
# The bridge's clauses on Java's traces (bergdb 030-07): runs `bridgecheck`
# (BridgeCheck.lean) on the traces of format 3 that java/stress/treeconf.sh has
# written to java/build/traces/tree-SET/.
#
# Usage: lean/contract/bridge-check.sh [SET ...]     (default: small drain)
# Needs: the traces (as lean/contract/check.sh) and the checker
# (cd lean/contract && lake build bridgecheck).
# Prints the summary of each set, then BRIDGE OK or BRIDGE FAILED; the lines of
# every trace go to java/build/traces/tree-SET/bridge.txt. First the checker's own
# test, bridge-faults.sh, if the small and the reclaim set are there: faults made
# in a trace must fail it. About 6 minutes for the three sets.
cd "$(dirname "$0")"
CHECK=.lake/build/bin/bridgecheck
[ -x "$CHECK" ] || { echo "BRIDGE FAILED: no checker; run lake build in lean/contract/"; exit 1; }
if ls ../../java/build/traces/tree-small/mixed-1.trace ../../java/build/traces/tree-reclaim/r-del-1.trace > /dev/null 2>&1; then
    ./bridge-faults.sh > /dev/null 2>&1 || { echo "BRIDGE FAILED: the checker's own test, lean/contract/bridge-faults.sh"; exit 1; }
fi
SETS=${*:-small drain}
FAILED=0
for set in $SETS; do
    dir=../../java/build/traces/tree-$set
    ls $dir/*.trace > /dev/null 2>&1 || { echo "BRIDGE FAILED: no traces in $dir"; exit 1; }
    "$CHECK" $dir/*.trace > $dir/bridge.txt 2>&1 || FAILED=$((FAILED + 1))
    echo "tree-$set: $(grep '^total: ' $dir/bridge.txt | sed 's/^total: //')"
    grep 'first: ' $dir/bridge.txt | head -5
done
if [ $FAILED -eq 0 ]; then
    echo "BRIDGE OK"
else
    echo "BRIDGE FAILED: $FAILED sets"
    exit 1
fi
