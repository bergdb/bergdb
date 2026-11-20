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
# Usage: [TREE=1] [ONLY=NAME] java/stress/contractconf.sh [small|drain|reclaim|medium|large] [seeds [first]]
#   seeds, first and ONLY: as treeconf.sh's (default 3 seeds for medium, from 1; first
#   needs seeds; bergdb 030-30): with a first other than 1 the traces go to build/traces/tree-SET-FIRST/ and
#   the checks run on them. A failing trace gets a line FAILED with its seed and the
#   command that runs it again, and its path in the set's failed.txt.
# Builds the checkers with lake (lean/contractcheck/: lean/contract/'s files,
# without Mathlib, bergdb 028-24; it builds the old package lean/ it uses). Needs
# java/build (java/build.sh). Logs go to build/contractconf/; the traces and
# the checkers' outputs to build/traces/tree-SET/. Prints the summary of each
# check, then CONTRACTCONF OK or CONTRACTCONF FAILED. Set JAVA_HOME or PATH for
# the JDK.
#
# Kind: functional (bergdb 028-23): the result does not depend on the machine's speed or
# load.

cd "$(dirname "$0")/.."
echo "Kind: functional"

SET=${1:-medium}
SEEDS=$2
FIRST=${3:-1}
# The set's directory, build/traces/tree-$D/, and its logs' prefix (bergdb 030-30).
if [ "$FIRST" = 1 ]; then D=$SET; else D=$SET-$FIRST; fi
LOG=build/contractconf
mkdir -p $LOG
rm -f $LOG/$D-*.txt
START=$(date +%s)

fail() {
    echo "CONTRACTCONF FAILED: $1 (log: $2)"
    exit 1
}

if [ "$TREE" = 1 ]; then
    (cd ../lean && lake build) > $LOG/$D-lake-tree.txt 2>&1 \
        || fail "the Lean tree checker, lake build" $LOG/$D-lake-tree.txt
    TC=../lean/.lake/build/bin/treecheck
else
    TC=none
fi
(cd ../lean/contractcheck && lake build) > $LOG/$D-lake-contract.txt 2>&1 \
    || fail "the contract checkers, lake build in lean/contractcheck" $LOG/$D-lake-contract.txt

s=$(date +%s)
if [ -n "$SEEDS" ]; then
    TREECHECK=$TC sh stress/treeconf.sh $SET $SEEDS $FIRST > $LOG/$D-treeconf.txt 2>&1
else
    TREECHECK=$TC sh stress/treeconf.sh $SET > $LOG/$D-treeconf.txt 2>&1
fi
if ! grep -q '^TREECONF OK' $LOG/$D-treeconf.txt; then
    grep '^   FAILED ' $LOG/$D-treeconf.txt
    fail "treeconf.sh $SET" $LOG/$D-treeconf.txt
fi
if [ "$TREE" = 1 ]; then
    echo "treeconf $SET: $(grep ' transactions, ' $LOG/$D-treeconf.txt | sed 's/^ *//'); $(( $(date +%s) - s )) s"
else
    echo "treeconf $SET: $(ls build/traces/tree-$D/*.trace | wc -l | tr -d ' ') traces written, no tree check; $(( $(date +%s) - s )) s"
fi

# The traces that a checker failed (as lean/contract/check.sh finds them), each with its
# seed and the command that runs it again, into the set's failed.txt (bergdb 030-30).
failed_traces() {
    dir=build/traces/tree-$D
    grep -h 'first: \|: not whole: \|: unreadable: \|: the verdict' $dir/contract.txt $dir/bridge.txt \
        2> /dev/null | sed -e 's/: .*//' -e 's|.*/||' | sort -u | while read t; do
        name=${t%-*}; seed=${t##*-}; seed=${seed%.trace}
        echo "$dir/$t" >> $dir/failed.txt
        echo "   FAILED $name-$seed, set $SET, seed $seed: $1; trace java/$dir/$t; rerun from the" \
            "repository's root: ${TREE:+TREE=1 }ONLY=$name sh java/stress/contractconf.sh $SET 1 $seed"
    done
}

s=$(date +%s)
sh ../lean/contract/check.sh $D > $LOG/$D-contract.txt 2>&1
if ! grep -q '^CONTRACT OK' $LOG/$D-contract.txt; then
    failed_traces "lean/contract/check.sh"
    fail "lean/contract/check.sh $D" $LOG/$D-contract.txt
fi
echo "contract, $(( $(date +%s) - s )) s: $(grep '^tree-' $LOG/$D-contract.txt | cut -c1-200)"

# bridge-check.sh runs its fault test only if a small and a reclaim trace are
# in build/traces/ (in night.sh, from level2.sh's step 8).
s=$(date +%s)
sh ../lean/contract/bridge-check.sh $D > $LOG/$D-bridge.txt 2>&1
if ! grep -q '^BRIDGE OK' $LOG/$D-bridge.txt; then
    failed_traces "lean/contract/bridge-check.sh"
    fail "lean/contract/bridge-check.sh $D" $LOG/$D-bridge.txt
fi
echo "bridge, $(( $(date +%s) - s )) s: $(grep '^tree-' $LOG/$D-bridge.txt | cut -c1-200)"

echo "Time: $(( $(date +%s) - START )) s"
echo "CONTRACTCONF OK"
