#!/bin/sh
# The writer's contract on Java's traces (bergdb 030-04, section 7.4 (d)): runs
# `contractcheck` (ContractCheck.lean) on the traces of format 3 that
# java/stress/treeconf.sh has written to java/build/traces/tree-SET/.
#
# Usage: lean/contract/check.sh [SET ...]     (default: small drain)
# Needs: the traces (java/build.sh; cd lean && lake build treecheck;
# java/stress/treeconf.sh small; java/stress/treeconf.sh drain) and the checker
# (cd lean/contract && lake build contractcheck).
# Prints the summary of each set, then CONTRACT OK or CONTRACT FAILED; the lines
# of every trace go to java/build/traces/tree-SET/contract.txt. First the checker's
# own test, faults.sh (bergdb 030-09): faults made in a trace must fail it.
cd "$(dirname "$0")"
CHECK=.lake/build/bin/contractcheck
[ -x "$CHECK" ] || { echo "CONTRACT FAILED: no checker; run lake build in lean/contract/"; exit 1; }
./faults.sh > /dev/null 2>&1 || { echo "CONTRACT FAILED: the checker's own test, lean/contract/faults.sh"; exit 1; }
SETS=${*:-small drain}
FAILED=0
for set in $SETS; do
    dir=../../java/build/traces/tree-$set
    ls $dir/*.trace > /dev/null 2>&1 || { echo "CONTRACT FAILED: no traces in $dir"; exit 1; }
    "$CHECK" $dir/*.trace > $dir/contract.txt 2>&1 || FAILED=$((FAILED + 1))
    echo "tree-$set: $(grep '^total: ' $dir/contract.txt | sed 's/^total: //')"
    grep 'first: ' $dir/contract.txt | head -5
done
if [ $FAILED -eq 0 ]; then
    echo "CONTRACT OK"
else
    echo "CONTRACT FAILED: $FAILED sets"
    exit 1
fi
