#!/bin/sh
# The Lean model's test programs (bergdb 021-03): random runs that check the
# model by running, which lake build and the level scripts do not run.
#   sistest      the abstract model: the assumptions, T1, T2 with random
#                restarts, T13 (marking and testing), lemma M, for every
#                algorithm, with and without a virtual root
#   phystest     the physical layer: reads give P, canonical objects whole,
#                startups from prefixes of the stream, lazy restarts
#   reclaimtest  reclaim: random runs with cuts, T8, T12, T-SCHEME
# See lean/README.md, "Build and run" and "What to read". Runs as a step of
# java/night.sh; not in before-commit.sh, as it takes minutes (Frans,
# 2026-11-05).
#
# Usage: java/stress/lean-tests.sh [full]
#   default: sistest 5 40, phystest 5 40, reclaimtest 20 30 (seeds,
#            transactions), about 4.5 minutes on F53
#   full:    sistest 20 40, phystest 20 40, reclaimtest 20 30, the sizes of
#            lean/README.md, about 15 minutes
#
# Needs Lean (elan, with the toolchain of ../lean/lean-toolchain), as the
# level scripts' conformance steps do; builds the three programs with lake.
# Each program's output goes to java/build/lean-tests/NAME.txt. A program
# fails when its exit code is not 0 (it then prints "N failures") or its last
# line is not "all checks pass". Prints one line per program and LEAN TESTS OK,
# or LEAN TESTS FAILED with the programs that failed, and exits with status 1.

cd "$(dirname "$0")/.." || exit 1
OUT=build/lean-tests
LEAN=../lean
mkdir -p $OUT || exit 1

if [ "$1" = full ]; then N=20; else N=5; fi

(cd $LEAN && lake build sistest phystest reclaimtest) > $OUT/lake.txt 2>&1 \
    || { tail -20 $OUT/lake.txt; echo "LEAN TESTS FAILED: lake build (java/$OUT/lake.txt)"; exit 1; }

FAILED=""
run() {
    name=$1; shift
    s=$(date +%s)
    $LEAN/.lake/build/bin/$name "$@" > $OUT/$name.txt 2>&1
    status=$?
    t=$(( $(date +%s) - s ))
    last=$(tail -1 $OUT/$name.txt)
    if [ $status = 0 ] && [ "$last" = "all checks pass" ]; then
        result=ok
    else
        result=FAILED; FAILED="$FAILED $name"
    fi
    printf '%-18s %-6s %4d s   exit %d: %s\n' "$name $*" $result $t $status "$last"
}

run sistest $N 40
run phystest $N 40
run reclaimtest 20 30

if [ -z "$FAILED" ]; then
    echo "LEAN TESTS OK"
else
    echo "LEAN TESTS FAILED:$FAILED (outputs in java/$OUT/)"
    exit 1
fi
