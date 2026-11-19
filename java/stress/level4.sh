#!/bin/sh
# Level 4 regression check (bergdb 027-01, levels.md): eviction, data and index larger than
# memory. Not a commit gate (java/before-commit.sh is, since 2026-10-20); run it after
# larger changes. Written 2026-10-18 for bergdb item 001, WP J9.
#
# Usage: java/stress/level4.sh [quick]
#   full (default): about 16 minutes on 10 cores. quick: about 4 minutes. (Measured
#   2026-10-18 with other jobs on the machine.)
#
# Builds with ../java/build.sh, then runs, stopping at the first failure:
#   1. The unit tests (bergdb.dev.Unit; quick: the eviction tests only):
#      Eviction (the cases of bergdb 011-05, section 9, as twins with and
#      without eviction), EvictionReaderTester (readers under eviction, Q8),
#      CapacityTester (the capacity controller) and Residents; then the f-tests
#      of these classes (bergdb.dev.F), their full versions: every schedule,
#      larger databases (since 2026-10-20 the unit tests are small).
#   2. EvictionInvariance: the same transactions with each eviction schedule
#      (none, values, every, random, and the capacity controller with a small
#      budget) give the same stream, byte for byte, the same dirty set and the
#      same answers; without and with restarts and reclaim; the audit
#      (INV-CAN, the pins, INV-SLOT) on.
#   3. RestartInvariance, CrashTest and ReclaimStress with forced schedules
#      (every, random) and the audit: restarts, crashes and reclaim (on a
#      CutStream) after eviction.
#   4. ReclaimReaders with forced schedules: reader threads while slots change
#      between memory and stream and reclaim cuts, CutStream and FileStream; 8
#      readers; and the capacity controller with a small budget (since bergdb
#      item 009, step 3d).
#   5. Conformance with the Lean model, with eviction: conformance.sh evict
#      (TraceExport's run E with a forced schedule: its stream is run A's, its
#      slots meet INV-SLOT, the checker's C-P, and its handle state the model's
#      invariants with handles, C-H, since bergdb item 009, step 4c; 1 seed
#      quick, 3 full). It needs the checker (cd ../lean && lake build), which
#      the step builds.
#   6. LargerThanMemory: on disk, in a capped JVM, a database several times the
#      budget, its index larger than it: updates, gets, scans, reclaim, a cold
#      restart, every key checked; the live heap stays below three quarters of
#      the cap. Quick: 500,000 keys, a budget of 20 MB, -Xmx384m; full:
#      2,000,000 keys, 50 MB, -Xmx768m.
# Logs go to build/level4/. Set JAVA_HOME or PATH for the JDK; the build needs
# javac too.
#
# Kind: functional (bergdb 028-23): the result does not depend on the machine's speed or
# load; its time limits are hang guards, generous for a loaded machine.

cd "$(dirname "$0")/.."
echo "Kind: functional"

JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi

if [ "$1" = quick ]; then
    QUICK=1; INV_N=600; ROUNDS=6; CRASH_ROUNDS=2; READER_ROUNDS=2; CONF_SEEDS=1
    LTM="-Xmx384m -Dkeys=500000 -Dbudget=20 -Dsd=2000000 -Dupdates=20000 -Dgets=100000 -Dscans=5 -Drestarts=1"
else
    QUICK=0; INV_N=2000; ROUNDS=60; CRASH_ROUNDS=8; READER_ROUNDS=6; CONF_SEEDS=3
    LTM="-Xmx768m -Dkeys=2000000 -Dbudget=50 -Dsd=5000000 -Dupdates=50000 -Dgets=300000 -Dscans=10 -Drestarts=1"
fi

CP=build/bergdb.jar:build/stress
LOG=build/level4

fail() {
    echo "LEVEL 4 FAILED: $1 (log: $2)"
    exit 1
}

audited() { # file pattern
    grep -q "$2" $1 && grep -q '^AUDIT: .* 0 failed' $1
}

./build.sh > /dev/null || { echo "LEVEL 4 FAILED: build"; exit 1; }
# Removes old logs, files only (see build.sh about Finder).
mkdir -p $LOG
find $LOG -type f -delete

echo "1. Unit tests"
if [ $QUICK = 1 ]; then
    $JAVA -ea -cp build/bergdb.jar bergdb.dev.Unit -c '.*(Eviction|EvictionReaderTester|CapacityTester|Residents).*' \
        > $LOG/unit.txt 2>&1
else
    $JAVA -ea -cp build/bergdb.jar bergdb.dev.Unit > $LOG/unit.txt 2>&1
fi
grep -q '^SUCCESS' $LOG/unit.txt || fail "unit tests" $LOG/unit.txt
grep '^SUCCESS' $LOG/unit.txt
$JAVA -ea -cp build/bergdb.jar bergdb.dev.F -c '.*(Eviction|EvictionReaderTester|CapacityTester|Residents).*' \
    > $LOG/f.txt 2>&1
grep -q '^SUCCESS' $LOG/f.txt || fail "f-tests" $LOG/f.txt
grep '^SUCCESS' $LOG/f.txt

echo "2. EvictionInvariance, every schedule, the audit on"
E="-ea -Xmx3g -Ddel=1 -Daudit=5 -Dn=$INV_N"
ei() {
    name=$1; shift
    $JAVA $E "$@" -cp $CP bergdb.core.EvictionInvariance 1 > $LOG/ei-$name.txt 2>&1
}
ei node8 -Dsd=1000 -Dkeys=500 -Devery=100 -Dmaxnode=8 -Dlong=1 -Dbigtrans=10 &
ei node8-r -Drestarts=1 -Dsd=1000 -Dkeys=500 -Devery=100 -Dmaxnode=8 -Dlong=1 -Dbigtrans=10 &
ei rec-every1 -Drestarts=1 -Dretain=1 -Dsd=500 -Dkeys=100 -Devery=1 -Dlong=1 -Dn=$((INV_N / 2)) &
wait
if [ $QUICK = 0 ]; then
    ei node14 -Dsd=10000 -Dkeys=500 -Devery=200 -Dmaxnode=14 -Dlong=1 &
    ei node62-r -Drestarts=1 -Dsd=100000 -Dkeys=1000 -Devery=200 -Dmaxnode=62 -Dbigtrans=40 -Dvalsize=400 &
    ei idle-r -Drestarts=1 -Dsd=100 -Dkeys=100 -Devery=1 -Dlong=1 -Dempty=30 -Dnodel=20 -Dn=400 &
    wait
    ei rec-node8 -Dretain=1 -Dsd=1000 -Dkeys=500 -Devery=50 -Dmaxnode=8 -Dlong=1 -Dbigtrans=10 &
    ei rec-node62-r -Drestarts=1 -Dretain=1 -Dsd=10000 -Dkeys=1000 -Devery=100 -Dmaxnode=62 -Dbigtrans=40 -Dvalsize=400 &
    ei medium -Dsd=2000 -Dkeys=3000 -Devery=250 -Dmaxnode=30 -Dlong=1 -Dbigtrans=20 -Dn=5000 &
    wait
fi
for f in $LOG/ei-*.txt; do
    audited $f '^EVICTION INVARIANCE OK' || fail "EvictionInvariance" $f
    echo "   $(basename $f .txt): EVICTION INVARIANCE OK, $(grep '^AUDIT:' $f | sed -E 's/^AUDIT: ([0-9]+) audits.*, ([0-9]+) failed.*/\1 audits, \2 failed/')"
done

echo "3. RestartInvariance, CrashTest and ReclaimStress with forced schedules, the audit on"
for e in every random; do
    $JAVA -ea -Xmx2g -Daudit=1 -Devict=$e -Ddel=1 -Dn=$INV_N -Dsd=1000 -Dkeys=500 -Devery=100 \
        -Dmaxnode=8 -Dlong=1 -Dbigtrans=10 -Dretain=1 -cp $CP bergdb.core.RestartInvariance 1 \
        > $LOG/inv-$e.txt 2>&1 &
    $JAVA -ea -Xmx2g -Daudit=1 -Devict=$e -Dretain=1 -cp $CP bergdb.core.CrashTest 1 $CRASH_ROUNDS \
        > $LOG/crash-$e.txt 2>&1 &
    $JAVA -ea -Xmx2g -Daudit=1 -Devict=$e -cp $CP bergdb.core.ReclaimStress 1 $ROUNDS \
        > $LOG/reclaim-$e.txt 2>&1 &
done
wait
for f in $LOG/inv-*.txt; do
    audited $f '^STREAM: identical' || fail "RestartInvariance" $f
    echo "   $(basename $f .txt): stream identical, $(grep '^AUDIT:' $f | sed -E 's/^AUDIT: ([0-9]+) audits.*, ([0-9]+) failed.*/\1 audits, \2 failed/')"
done
for f in $LOG/crash-*.txt $LOG/reclaim-*.txt; do
    audited $f '^Done: .* 0 failures' || fail "$(basename $f .txt)" $f
    echo "   $(basename $f .txt): $(grep '^Done:' $f), $(grep '^AUDIT:' $f | sed -E 's/^AUDIT: ([0-9]+) audits.*, ([0-9]+) failed.*/\1 audits, \2 failed/')"
done

echo "4. ReclaimReaders with forced schedules"
$JAVA -ea -Xmx2g -Devict=every -cp $CP bergdb.core.ReclaimReaders 1 $READER_ROUNDS > $LOG/readers-every.txt 2>&1 &
$JAVA -ea -Xmx2g -Devict=random -cp $CP bergdb.core.ReclaimReaders 101 $READER_ROUNDS > $LOG/readers-random.txt 2>&1 &
$JAVA -ea -Xmx2g -Ddisk=1 -Devict=random -cp $CP bergdb.core.ReclaimReaders 201 $READER_ROUNDS \
    > $LOG/readers-disk.txt 2>&1 &
# More readers, and the capacity controller with a small budget, whose batches the readers'
# loads ask the eviction thread for while they follow pointers without a lock (bergdb item
# 009, step 3d; items/009-handles/02-implementation-plan.md, 3.5).
$JAVA -ea -Xmx2g -Dreaders=8 -Devict=random -cp $CP bergdb.core.ReclaimReaders 301 $READER_ROUNDS \
    > $LOG/readers-many.txt 2>&1 &
$JAVA -ea -Xmx2g -Dreaders=4 -Devict=budget -Devictbudget=20000 -cp $CP bergdb.core.ReclaimReaders 401 \
    $READER_ROUNDS > $LOG/readers-budget.txt 2>&1 &
wait
for f in $LOG/readers-*.txt; do
    grep -q '^Done: .* 0 failures' $f || fail "ReclaimReaders" $f
    echo "   $(basename $f .txt): $(tail -1 $f)"
done

echo "5. Conformance with the Lean model, with eviction"
(cd ../lean && lake build) > $LOG/lake.txt 2>&1 || fail "the Lean checker, lake build" $LOG/lake.txt
sh stress/conformance.sh evict $CONF_SEEDS > $LOG/conformance.txt 2>&1
grep -q '^CONFORMANCE OK' $LOG/conformance.txt || fail "conformance.sh evict" $LOG/conformance.txt
echo "   conformance: $(grep '^   traces:' $LOG/conformance.txt | sed 's/^ *//'); C-P $(grep '^   C-P:' $LOG/conformance.txt | sed 's/^ *C-P: //'); C-H $(grep '^   C-H:' $LOG/conformance.txt | sed 's/^ *C-H: //')"

echo "6. LargerThanMemory, on disk, a capped JVM"
$JAVA -ea $LTM -Ddir=build/level4/ltm -cp $CP bergdb.core.LargerThanMemory > $LOG/ltm.txt 2>&1
grep -q '^LARGER THAN MEMORY OK' $LOG/ltm.txt || fail "LargerThanMemory" $LOG/ltm.txt
echo "   $(grep 'the index:' $LOG/ltm.txt | head -1 | sed 's/^ *//')"
echo "   $(grep '^   at most:' $LOG/ltm.txt | sed 's/^ *//')"
rm -rf build/level4/ltm

echo "LEVEL 4 OK"
