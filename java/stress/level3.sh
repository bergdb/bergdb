#!/bin/sh
# Level 3 regression check (docs/levels.md): reclaim, which cuts the front
# of the stream. Run it, with level1.sh and level2.sh, before committing any
# change to java/; all three must pass.
#
# Usage: java/stress/level3.sh [quick]
#   full (default): about 4 minutes on 10 cores. quick: about 1 minute.
#
# Builds with ../java/build.sh, then runs, stopping at the first failure:
#   1. The unit tests (bergdb.dev.Unit), which include the reclaim tests in
#      Reclaim.Tester; full only, the f-tests (bergdb.dev.F) too.
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
#      when a cut overtook it); the writer must never fail (docs/levels.md, W1).
#   6. Full only: LoadTest with reclaim, 100,000 keys and 1,000,000 updates,
#      a startup distance of 20 MB (the default until 2026-10-13; with the 50 MB
#      default, the run reaches only one cut) and a retention of 1 s (about 8 MB
#      of stream), a strict stream in memory, and a restart and a check of
#      every key after every cut (6 or 7 cuts, 410 MB of stream). This
#      is the case where the cut must wait until the rewritten nodes are
#      written (Reclaim, pEnd); the small configurations above do not reach it.
# Logs go to build/level3/. Set JAVA_HOME or PATH for the JDK; the build
# needs javac too.

cd "$(dirname "$0")/.."

JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi

if [ "$1" = quick ]; then
    QUICK=1; ROUNDS=40; INV_N=800; CRASH_ROUNDS=4; READER_ROUNDS=3
else
    QUICK=0; ROUNDS=200; INV_N=2000; CRASH_ROUNDS=20; READER_ROUNDS=12
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
    grep -q '^SUCCESS' $LOG/f.txt || fail "f-tests" $LOG/f.txt
    grep '^SUCCESS' $LOG/f.txt
fi

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

echo "LEVEL 3 OK"
