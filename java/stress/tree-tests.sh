#!/bin/sh
# The tree model's small cases (bergdb 024-12, section 4.3): lake exe treetest
# (lean/TreeTest.lean) runs the Lean model of the key tree, without Java, on
# every sequence of single operations on a few keys to a depth, at node sizes
# 4, 6 and 8, from the primordial structure and from trees that a prefix
# built, on transactions of two operations, and on pseudo-random
# transactions; after every transaction it checks the stated properties that
# can be computed (the invariants, gets and scans against a reference map,
# the skip pointers' search, the bounds). Runs as a step of java/night.sh;
# not in before-commit.sh, as it takes minutes.
#
# Usage: java/stress/tree-tests.sh [treetest's arguments]
#   without arguments: treetest's own set, one core.
#
# Needs Lean (elan, with the toolchain of ../lean/lean-toolchain); builds the
# program with lake. Its output goes to java/build/tree-tests/treetest.txt.
# Prints one line per run and TREE TESTS OK, or TREE TESTS FAILED, and then
# exits with status 1.

cd "$(dirname "$0")/.." || exit 1
OUT=build/tree-tests
LEAN=../lean
mkdir -p $OUT || exit 1

(cd $LEAN && lake build treetest) > $OUT/lake.txt 2>&1 \
    || { tail -20 $OUT/lake.txt; echo "TREE TESTS FAILED: lake build (java/$OUT/lake.txt)"; exit 1; }

s=$(date +%s)
$LEAN/.lake/build/bin/treetest "$@" > $OUT/treetest.txt 2>&1
status=$?
grep -v '^  reached: ' $OUT/treetest.txt
echo "Time: $(( $(date +%s) - s )) s"
if [ $status = 0 ] && [ "$(tail -1 $OUT/treetest.txt)" = "TREETEST OK" ]; then
    echo "TREE TESTS OK"
else
    echo "TREE TESTS FAILED (java/$OUT/treetest.txt)"
    exit 1
fi
