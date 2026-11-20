#!/bin/sh
# The tested writer against the proved writer (bergdb 030-28): runs pecmp
# (PeCmp.lean) on the traces of format 3 that java/stress/treeconf.sh has written
# to java/build/traces/tree-SET/. The tree checker compares Java with
# lean/SIS/Tree/Pe.lean, a copy of the proved writer
# (lean/contract/Contract/PeWriter.lean, bergdb 030-21); pecmp runs the copy and
# the proved writer on Java's structure before every transaction and fails if they
# write anything different: the writes in their order, the ids' order, the trees,
# the top node (PeCmp.lean's header). java/stress/level2.sh runs it on its tree
# sets, small, drain and reclaim.
#
# First pecmp's own tests, each must give PECMP FAILED: --cap-h (the proved writer
# with the cut size h, not M / 2) on the drain set's d-30 traces, which cut lists of
# node size 30 (seed 2 does, 2026-11-19), and --top-fault (a top one node longer)
# on the small set's mixed-1.
#
# Usage: lean/pecmp/check.sh [SET ...]     (default: small drain reclaim)
# Needs the traces (java/stress/treeconf.sh SET) and pecmp (cd lean/pecmp && lake
# build; no Mathlib). Prints a line a set and PECMP OK, or PECMP FAILED; each set's
# output goes to java/build/traces/tree-SET/pecmp.txt. A few seconds a set.
cd "$(dirname "$0")"
P=$(pwd)/.lake/build/bin/pecmp
[ -x "$P" ] || { echo "PECMP FAILED: no pecmp; run lake build in lean/pecmp/"; exit 1; }
cd ../../java/build/traces || { echo "PECMP FAILED: no traces in java/build/traces/"; exit 1; }
ls tree-drain/d-30-*.trace tree-small/mixed-1.trace > /dev/null 2>&1 \
    || { echo "PECMP FAILED: its own tests need tree-drain/d-30-*.trace and tree-small/mixed-1.trace"; exit 1; }
$P --cap-h tree-drain/d-30-*.trace > /dev/null 2>&1 \
    && { echo "PECMP FAILED: its own test --cap-h passed on tree-drain/d-30-*.trace"; exit 1; }
$P --top-fault tree-small/mixed-1.trace > /dev/null 2>&1 \
    && { echo "PECMP FAILED: its own test --top-fault passed on tree-small/mixed-1.trace"; exit 1; }
echo "pecmp's own tests: --cap-h and --top-fault fail, as they must"
FAILED=0
for set in ${*:-small drain reclaim}; do
    ls tree-$set/*.trace > /dev/null 2>&1 || { echo "tree-$set: no traces"; FAILED=1; continue; }
    $P tree-$set/*.trace > tree-$set/pecmp.txt 2>&1
    grep -q '^PECMP OK' tree-$set/pecmp.txt || FAILED=1
    echo "tree-$set: $(grep '^total: ' tree-$set/pecmp.txt | sed 's/^total: //'), $(tail -1 tree-$set/pecmp.txt)"
    grep -v ' 0 differ$' tree-$set/pecmp.txt | grep -v '^total: \|^PECMP' | head -5
done
if [ $FAILED -eq 0 ]; then echo "PECMP OK"; else echo "PECMP FAILED"; exit 1; fi
