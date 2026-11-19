#!/bin/sh
# Level 3 regression check (bergdb 027-01, levels.md): reclaim, which cuts the front
# of the stream. Not a commit gate (java/before-commit.sh is, since
# 2026-10-20); run it after larger changes.
#
# Usage: java/stress/level3.sh [quick]
#   full (default): about 5 minutes on 10 cores. quick: about 1 minute.
#
# Builds with ../java/build.sh, then runs, stopping at the first failure:
#   1. The unit tests (bergdb.dev.Unit), which include the reclaim tests in
#      Reclaim.Tester; then the f-tests (bergdb.dev.F): all of them, or, quick,
#      those of reclaim and of FileStream's power loss.
#   2. ReclaimStress, random configurations: retain durations of 1 to 5 s,
#      startup distances of 1000 to 20,000 bytes, node sizes 8 to 62, 5 to
#      3000 keys, long keys, deletes, restarts between sessions. The stream
#      refuses reads below the cut (CutStream). Every key at the latest time,
#      lookups from the first available lookup time and in the retention
#      window, and the retention guarantee are checked before and after every
#      restart.
#   3. RestartInvariance with reclaim: the same transactions with and without
#      restarts give the same stream, byte for byte, and the same cut, dirty
#      set, node identity and lookups. A restart after every transaction,
#      node sizes 8 to 62.
#   4. CrashTest with reclaim: the stream cut at the end at random positions
#      after the front was cut; the database must start in the state after
#      the last complete transaction, work on, and restart again.
#   5. ReclaimReaders: reader threads (gets and scans at old lookup times, on a cold
#      cache) while reclaim cuts the stream, CutStream and FileStream. An operation
#      returns what the model says or throws LookupTimeNotAvailableException (it expired
#      when a cut overtook it); the writer must never fail (bergdb 011-04, W1).
#   6. Full only: LoadTest with reclaim, 100,000 keys and 1,000,000 updates,
#      a startup distance of 20 MB (the default until 2026-10-13; with the 50 MB
#      default, the run reaches only one cut) and a retention of 1 s (about 8 MB
#      of stream), a strict stream in memory, and a restart and a check of
#      every key after every cut (6 or 7 cuts, 410 MB of stream). This
#      is the case where the cut must wait until the rewritten nodes are
#      written (Reclaim, pEnd); the small configurations above do not reach it.
#   7. PowerLossTest: production FileStream ordering with independent volatile
#      bytes, forced bytes and durable names, surviving deletion, partial tails,
#      cold recovery, and weakened data/directory-force negative controls; each
#      seed again with per-append forcing off (bergdb 005-47), with its negative
#      controls (no force before a new file, or before a cut's deletes) and hole
#      images, which are counted, not failed (a known limit, bergdb 014-01).
#   8. Conformance with the Lean model, with reclaim (bergdb item 001, K3,
#      2026-10-17; bergdb 001-07, section 8): conformance.sh reclaim,
#      the small reclaim set (2 seeds quick, 5 full): each trace's every record
#      against the model's step on the cut stream, CutOK at every cut Java
#      decides, the touch assumptions, and the probes after restarts from the
#      cut stream; since bergdb 030-27 also each step of reclaim against the
#      model of the steps (C-STEP, on STEP lines), after the check's own fault
#      test (lean/test-traces/step-faults.sh). It needs the checker (cd ../lean
#      && lake build, Lean 4 v4.34.1), which the step builds.
#   9. InterruptStress (bergdb 005-46): a writer with syncs, readers, reclaim's
#      cuts, eviction and restarts on a FileStream, while a thread interrupts
#      them at random every 100 microseconds and the storage threads every
#      100 ms. No interrupt may fail or hang the database, and every call keeps
#      the thread's interrupt flag. 10 s quick, 60 s full.
# Logs go to build/level3/. Set JAVA_HOME or PATH for the JDK; the build
# needs javac too.
#
# Kind: functional (bergdb 028-23): the result does not depend on the machine's speed or
# load; its time limits are hang guards, generous for a loaded machine (InterruptStress's
# 60 s for a worker to end).

cd "$(dirname "$0")/.."
echo "Kind: functional"

JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi

if [ "$1" = quick ]; then
    QUICK=1; ROUNDS=40; INV_N=800; CRASH_ROUNDS=4; READER_ROUNDS=3; POWER_ROUNDS=1; POWER_TRANS=600; POWER_EVENTS=1
    CONF_SEEDS=2; INTERRUPT_SEC=10
else
    QUICK=0; ROUNDS=200; INV_N=2000; CRASH_ROUNDS=20; READER_ROUNDS=12; POWER_ROUNDS=8; POWER_TRANS=1500; POWER_EVENTS=3
    CONF_SEEDS=5; INTERRUPT_SEC=60
fi

CP=build/bergdb.jar:build/stress
LOG=build/level3

fail() {
    echo "LEVEL 3 FAILED: $1 (log: $2)"
    exit 1
}

./build.sh > /dev/null || { echo "LEVEL 3 FAILED: build"; exit 1; }
# Removes old logs, files only (see build.sh about Finder).
mkdir -p $LOG
find $LOG -type f -delete

echo "1. Unit tests"
$JAVA -ea -cp build/bergdb.jar bergdb.dev.Unit > $LOG/unit.txt 2>&1
grep -q '^SUCCESS' $LOG/unit.txt || fail "unit tests" $LOG/unit.txt
grep '^SUCCESS' $LOG/unit.txt
if [ $QUICK = 0 ]; then
    $JAVA -ea -cp build/bergdb.jar bergdb.dev.F > $LOG/f.txt 2>&1
else
    $JAVA -ea -cp build/bergdb.jar bergdb.dev.F \
        -c '.*(Reclaim|ReclaimReaderTester|ReclaimRetentionTester|FileStreamPowerLossTester).*' \
        > $LOG/f.txt 2>&1
fi
grep -q '^SUCCESS' $LOG/f.txt || fail "f-tests" $LOG/f.txt
grep '^SUCCESS' $LOG/f.txt

echo "2. ReclaimStress, random configurations"
Q=$((ROUNDS / 4))
for i in 0 1 2 3; do
    $JAVA -ea -Xmx2g -cp $CP bergdb.core.ReclaimStress $((1 + i * Q)) $Q > $LOG/reclaim-$i.txt 2>&1 &
done
wait
for f in $LOG/reclaim-*.txt; do
    grep -q '^Done: .* 0 failures' $f || fail "ReclaimStress" $f
    echo "   $(basename $f .txt): $(tail -1 $f)"
done

echo "3. RestartInvariance with reclaim"
I="-ea -Xmx2g -Ddel=1 -Dretain=1 -Dn=$INV_N"
inv() {
    name=$1; shift
    $JAVA $I "$@" -cp $CP bergdb.core.RestartInvariance 1 > $LOG/inv-$name.txt 2>&1
}
inv every1 -Dsd=500 -Dkeys=100 -Devery=1 -Dlong=1 -Dn=$((INV_N / 2)) &
inv node8 -Dsd=1000 -Dkeys=500 -Devery=50 -Dmaxnode=8 -Dlong=1 -Dbigtrans=10 &
inv node14 -Dsd=3000 -Dkeys=50 -Devery=37 -Dmaxnode=14 &
inv node62 -Dsd=10000 -Dkeys=1000 -Devery=100 -Dmaxnode=62 -Dbigtrans=40 -Dvalsize=400 &
wait
for F in $LOG/inv-*.txt; do
    grep -q '^STREAM: identical' $F || fail "RestartInvariance, stream not byte for byte the same" $F
    grep -q '^CUT: .*, same' $F || fail "RestartInvariance, the cut differs" $F
    [ "$(grep -Ec '^(TRANSSEQ|KV CHECKSUM|IDENTITY .*|LOOKUP .*): 0 of' $F)" = 6 ] \
        || fail "RestartInvariance" $F
    echo "   $(basename $F .txt): stream identical, same cut, all checks OK"
done

echo "4. CrashTest with reclaim"
C=$((CRASH_ROUNDS / 4))
for i in 0 1 2 3; do
    $JAVA -ea -Xmx2g -Dretain=1 -cp $CP bergdb.core.CrashTest $((1 + i * C)) $C \
        > $LOG/crash-$i.txt 2>&1 &
done
$JAVA -ea -Xmx2g -Dretain=2 -Dmaxnode=8 -Dsd=500 -cp $CP bergdb.core.CrashTest 1001 $C \
    > $LOG/crash-node8.txt 2>&1 &
wait
for f in $LOG/crash-*.txt; do
    grep -q '^Done: .* 0 failures' $f || fail "CrashTest" $f
    echo "   $(basename $f .txt): $(tail -1 $f)"
done

echo "5. ReclaimReaders, readers while reclaim cuts"
$JAVA -ea -Xmx2g -cp $CP bergdb.core.ReclaimReaders 1 $READER_ROUNDS > $LOG/readers-0.txt 2>&1 &
$JAVA -ea -Xmx2g -cp $CP bergdb.core.ReclaimReaders $((1 + READER_ROUNDS)) $READER_ROUNDS \
    > $LOG/readers-1.txt 2>&1 &
$JAVA -ea -Xmx2g -Ddisk=1 -cp $CP bergdb.core.ReclaimReaders 1 $READER_ROUNDS \
    > $LOG/readers-disk.txt 2>&1 &
wait
for f in $LOG/readers-*.txt; do
    grep -q '^Done: .* 0 failures' $f || fail "ReclaimReaders" $f
    echo "   $(basename $f .txt): $(tail -1 $f)"
done

if [ $QUICK = 0 ]; then
    echo "6. LoadTest with reclaim, a restart at every cut"
    $JAVA -ea -Xmx8g -Dn=100000 -Dupdates=1000000 -Dsd=20000000 -Dretain=1 -Dtstep=1000 -Dmem=1 \
        -Dcutcheck=1 -Dgets=100000 -cp $CP bergdb.core.LoadTest > $LOG/load.txt 2>&1
    grep -q '^LOADTEST OK' $LOG/load.txt || fail "LoadTest with reclaim" $LOG/load.txt
    echo "   $(grep 'restarts with a full check' $LOG/load.txt | sed 's/^ *//')"
fi

echo "7. PowerLossTest, forced bytes and durable names before deletion"
$JAVA -ea -Xmx2g -cp $CP bergdb.core.PowerLossTest 1 $POWER_ROUNDS $POWER_TRANS $POWER_EVENTS \
    > $LOG/powerloss.txt 2>&1
grep -q '^POWERLOSS OK' $LOG/powerloss.txt || fail "PowerLossTest" $LOG/powerloss.txt
grep '^POWERLOSS OK' $LOG/powerloss.txt

echo "8. Conformance with the Lean model, with reclaim"
(cd ../lean && lake build) > $LOG/lake.txt 2>&1 || fail "the Lean checker, lake build" $LOG/lake.txt
sh ../lean/test-traces/step-faults.sh > $LOG/step-faults.txt 2>&1
grep -q '^STEP FAULTS OK' $LOG/step-faults.txt || fail "C-STEP's fault test, lean/test-traces/step-faults.sh" $LOG/step-faults.txt
echo "   C-STEP's fault test: $(grep -c ': fails, ' $LOG/step-faults.txt) faults found, STEP FAULTS OK"
sh stress/conformance.sh reclaim $CONF_SEEDS > $LOG/conformance.txt 2>&1
grep -q '^CONFORMANCE OK' $LOG/conformance.txt || fail "conformance.sh reclaim" $LOG/conformance.txt
echo "   conformance: $(grep '^   traces:' $LOG/conformance.txt | sed 's/^ *//'); C-CUT $(grep '^   C-CUT:' $LOG/conformance.txt | sed 's/^ *C-CUT: //')"
echo "   C-STEP: $(grep '^   C-STEP:' $LOG/conformance.txt | sed 's/^ *C-STEP: //')"

echo "9. InterruptStress, interrupts everywhere"
$JAVA -ea -Xmx2g -cp $CP bergdb.core.InterruptStress $INTERRUPT_SEC build/level3/interruptstress \
    > $LOG/interrupt.txt 2>&1
grep -q '^INTERRUPT STRESS OK' $LOG/interrupt.txt || fail "InterruptStress" $LOG/interrupt.txt
echo "   $(grep '^InterruptStress:' $LOG/interrupt.txt)"

echo "LEVEL 3 OK"
