#!/bin/sh
# The writer's contract and the bridge on a set of tree traces (bergdb 030-13):
# treeconf.sh writes the set's traces (format 3), with TREECHECK=none: no check
# by the old tree model (treecheck), which takes 10 to 30 minutes per trace of
# the medium set's m-d8, m-d30 and m-d62; TREE=1 runs it too. Then
# lean/contract/check.sh (contractcheck, bergdb 030-04, 030-09) and
# lean/contract/bridge-check.sh (bridgecheck, bergdb 030-07) check each trace,
# each after its own fault tests. level2.sh does the same on the small and
# drain sets inline, after treeconf.sh's tree check (its step 8b); night.sh
# runs this script on the medium set (9 configurations, 3 seeds, 120 to 800
# transactions, node sizes 8 to 62).
#
# Usage: [TREE=1] java/stress/contractconf.sh [small|drain|reclaim|medium|large] [seeds]
#   seeds: as treeconf.sh's (default 3 for medium).
# Builds the contract package with lake (lean/contract/, which builds the old
# package lean/ it uses; with Mathlib: if its .lake has no Mathlib, lake exe
# cache get fetches the Mathlib cache first: 7.6 GB, about 4 minutes). Needs
# java/build (java/build.sh). Logs go to build/contractconf/; the traces and
# the checkers' outputs to build/traces/tree-SET/. Prints the summary of each
# check, then CONTRACTCONF OK or CONTRACTCONF FAILED. Set JAVA_HOME or PATH for
# the JDK.

cd "$(dirname "$0")/.."

SET=${1:-medium}
SEEDS=$2
LOG=build/contractconf
mkdir -p $LOG
rm -f $LOG/$SET-*.txt
START=$(date +%s)

fail() {
    echo "CONTRACTCONF FAILED: $1 (log: $2)"
    exit 1
}

if [ "$TREE" = 1 ]; then
    (cd ../lean && lake build) > $LOG/$SET-lake-tree.txt 2>&1 \
        || fail "the Lean tree checker, lake build" $LOG/$SET-lake-tree.txt
    TC=../lean/.lake/build/bin/treecheck
else
    TC=none
fi
if [ ! -d ../lean/contract/.lake/packages/mathlib ]; then
    (cd ../lean/contract && lake exe cache get) > $LOG/$SET-lake-contract-cache.txt 2>&1 \
        || fail "the contract package, lake exe cache get" $LOG/$SET-lake-contract-cache.txt
fi
(cd ../lean/contract && lake build) > $LOG/$SET-lake-contract.txt 2>&1 \
    || fail "the contract package, lake build" $LOG/$SET-lake-contract.txt

s=$(date +%s)
TREECHECK=$TC sh stress/treeconf.sh $SET $SEEDS > $LOG/$SET-treeconf.txt 2>&1
grep -q '^TREECONF OK' $LOG/$SET-treeconf.txt || fail "treeconf.sh $SET" $LOG/$SET-treeconf.txt
if [ "$TREE" = 1 ]; then
    echo "treeconf $SET: $(grep ' transactions, ' $LOG/$SET-treeconf.txt | sed 's/^ *//'); $(( $(date +%s) - s )) s"
else
    echo "treeconf $SET: $(ls build/traces/tree-$SET/*.trace | wc -l | tr -d ' ') traces written, no tree check; $(( $(date +%s) - s )) s"
fi

s=$(date +%s)
sh ../lean/contract/check.sh $SET > $LOG/$SET-contract.txt 2>&1
grep -q '^CONTRACT OK' $LOG/$SET-contract.txt || fail "lean/contract/check.sh $SET" $LOG/$SET-contract.txt
echo "contract $(grep '^tree-' $LOG/$SET-contract.txt | cut -c1-150); $(( $(date +%s) - s )) s"

# bridge-check.sh runs its fault test only if a small and a reclaim trace are
# in build/traces/ (in night.sh, from level2.sh's step 8).
s=$(date +%s)
sh ../lean/contract/bridge-check.sh $SET > $LOG/$SET-bridge.txt 2>&1
grep -q '^BRIDGE OK' $LOG/$SET-bridge.txt || fail "lean/contract/bridge-check.sh $SET" $LOG/$SET-bridge.txt
echo "bridge $(grep '^tree-' $LOG/$SET-bridge.txt | cut -c1-150); $(( $(date +%s) - s )) s"

echo "Time: $(( $(date +%s) - START )) s"
echo "CONTRACTCONF OK"
