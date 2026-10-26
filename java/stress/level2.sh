#!/bin/sh
# Level 2 regression check (docs/levels.md):
# restart with bounded startup, where startup reads only the tail of the
# stream. Not a commit gate (java/before-commit.sh is, since 2026-10-20);
# run it after larger changes.
#
# Usage: java/stress/level2.sh [quick]
#   full (default): about 17 minutes on 10 cores. quick: about 2 minutes.
#
# Builds with ../java/build.sh, then runs, stopping at the first failure:
#   1. The unit tests (bergdb.dev.Unit), which include small level 2 tests.
#   2. RestartStress, random configurations: startup distances from 100
#      bytes to the default 50 MB, node sizes 8 to 62, 5 to 3000 keys,
#      deletes, transactions of up to 40 keys, 2 to 26 restarts per round.
#      Latest and historical values are checked before and after every
#      restart.
#   3. RestartStress with a startup distance of 1000 bytes for each node
#      size, with 3000 keys and with 50 keys (small trees); and, full only,
#      the default settings on disk past 50 MB with deletes.
#   4. RestartInvariance: the same transactions with and without restarts
#      give the same stream, byte for byte (T2 in docs/sis-model.md), and
#      the same dirty set, node identity and lookups. Startup distances from
#      100 bytes up, node sizes 8 to 62, long keys, transactions of up to 40
#      keys, a restart after every transaction; mostly idle runs (30 percent
#      empty transactions, 20 percent deletes of missing keys, a restart
#      after every transaction), which caught the startup bug M18 of
#      bergdb 011-11; and, full only, about 100 MB with the
#      default startup distance.
#   5. CrashTest (INV-CRASH in bergdb 011-01): the stream cut at 100
#      positions per round, a third of them at or next to the end of a
#      transaction; then at 20 positions at or next to a meta block, and at
#      the end of each transaction that ends where a meta block starts
#      (bergdb 005-27). The database must start in the state after the last
#      complete transaction, work on, and restart again. Startup distance
#      2000 bytes, and 500 bytes with node size 8.
#   6. BryanRepro: the bug report of November 2015 (ISSUE151111). Start,
#      read, delete all, create 10000 objects and stop, repeated (15 times
#      quick, 40 full) with a retain duration of 10 s. The 2017 code fails
#      to start after about 12 cycles.
#   7. Conformance with the Lean model (bergdb 011-11, 12):
#      A2A3Check2 (a transaction meets the model's A2, A3 and A5, and Db
#      marks what the model marks; and, since bergdb 005-04, TREE, A6' and
#      A-COPY, the model's assumptions of stage 2) on three configurations;
#      and the trace checker on conformance.sh's small set (2 seeds quick, 10
#      full): every transaction must be a step of the model that meets its
#      assumptions, every restart invisible.
# Logs go to build/level2/. Set JAVA_HOME or PATH for the JDK; the build
# needs javac too. Step 7 needs Lean (elan, with the toolchain of
# ../lean/lean-toolchain); it builds the checker with lake.

cd "$(dirname "$0")/.."

JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi

if [ "$1" = quick ]; then
    QUICK=1; ROUNDS=40; SIZE_ROUNDS=3; INV_N=600; CRASH_ROUNDS=4; BRYAN_CYCLES=15
    CONF_SEEDS=2
else
    QUICK=0; ROUNDS=200; SIZE_ROUNDS=10; INV_N=2000; CRASH_ROUNDS=20; BRYAN_CYCLES=40
    CONF_SEEDS=10
fi

CP=build/bergdb.jar:build/stress
LOG=build/level2

fail() {
    echo "LEVEL 2 FAILED: $1 (log: $2)"
    exit 1
}

./build.sh > /dev/null || { echo "LEVEL 2 FAILED: build"; exit 1; }
# Removes old logs and databases, files only (see build.sh about Finder).
mkdir -p $LOG/disk
find $LOG -type f -delete

echo "1. Unit tests"
$JAVA -ea -cp build/bergdb.jar bergdb.dev.Unit > $LOG/unit.txt 2>&1
grep -q '^SUCCESS' $LOG/unit.txt || fail "unit tests" $LOG/unit.txt
grep '^SUCCESS' $LOG/unit.txt

echo "2. RestartStress, random configurations"
Q=$((ROUNDS / 4))
for i in 0 1 2 3; do
    $JAVA -ea -Xmx2g -cp $CP RestartStress $((1 + i * Q)) $Q > $LOG/random-$i.txt 2>&1 &
done
wait
for f in $LOG/random-*.txt; do
    grep -q '^Done: .* 0 failures' $f || fail "RestartStress" $f
    echo "   $(basename $f .txt): $(tail -1 $f)"
done

echo "3. RestartStress, small and default startup distances"
S1="-ea -Xmx2g -Dsd=1000 -Dsessions=20"
for m in 8 14 30 62; do
    $JAVA $S1 -Dmaxnode=$m -Dkeys=3000 -cp $CP RestartStress 1 $SIZE_ROUNDS \
        > $LOG/sd1000-node$m.txt 2>&1 &
    $JAVA $S1 -Dmaxnode=$m -Dkeys=50 -cp $CP RestartStress 1 $SIZE_ROUNDS \
        > $LOG/sd1000-keys50-node$m.txt 2>&1 &
done
if [ $QUICK = 0 ]; then
    $JAVA -ea -Xmx4g -Ddefaults=true -Dfile=true -Ddir=$LOG/disk -Dtrans=10000 -Dvalsize=8000 \
        -cp $CP RestartStress 1 2 > $LOG/default-disk.txt 2>&1 &
fi
wait
for f in $LOG/sd1000-*.txt $LOG/default-disk.txt; do
    [ -f $f ] || continue
    grep -q '^Done: .* 0 failures' $f || fail "RestartStress" $f
    echo "   $(basename $f .txt): $(tail -1 $f)"
done

echo "4. RestartInvariance"
I="-ea -Xmx2g -Ddel=1 -Dn=$INV_N"
inv() {
    name=$1; shift
    $JAVA $I "$@" -cp $CP bergdb.core.RestartInvariance 1 > $LOG/inv-$name.txt 2>&1
}
inv sd100 -Dsd=100 -Dkeys=500 -Devery=100 -Dlong=1 -Dbigtrans=20 &
inv sd1000-node8 -Dsd=1000 -Dkeys=500 -Devery=100 -Dmaxnode=8 -Dlong=1 -Dbigtrans=10 &
inv sd10000-node14 -Dsd=10000 -Dkeys=500 -Devery=200 -Dmaxnode=14 -Dlong=1 &
inv sd100000-node62 -Dsd=100000 -Dkeys=1000 -Devery=200 -Dmaxnode=62 -Dbigtrans=40 -Dvalsize=400 &
inv every1 -Dsd=500 -Dkeys=100 -Devery=1 -Dlong=1 -Dn=$((INV_N / 5)) &
for s in 1 2; do
    $JAVA $I -Dsd=100 -Dkeys=100 -Devery=1 -Dlong=1 -Dn=400 -Dempty=30 -Dnodel=20 \
        -cp $CP bergdb.core.RestartInvariance $s > $LOG/inv-idle-$s.txt 2>&1 &
done
wait
if [ $QUICK = 0 ]; then
    $JAVA -ea -Xmx9g -Dsd=0 -Dn=12000 -Dkeys=3000 -Dvalsize=8000 -Devery=4000 -Ddel=1 \
        -cp $CP bergdb.core.RestartInvariance 1 > $LOG/inv-default-100MB.txt 2>&1
fi
for F in $LOG/inv-*.txt; do
    grep -q '^STREAM: identical' $F || fail "RestartInvariance, stream not byte for byte the same" $F
    [ "$(grep -Ec '^(TRANSSEQ|KV CHECKSUM|IDENTITY .*|LOOKUP .*): 0 of' $F)" = 6 ] \
        || fail "RestartInvariance" $F
    echo "   $(basename $F .txt): stream identical, all checks OK"
done

echo "5. CrashTest, the stream cut at random positions"
C=$((CRASH_ROUNDS / 4))
for i in 0 1 2 3; do
    $JAVA -ea -Xmx2g -cp $CP bergdb.core.CrashTest $((1 + i * C)) $C > $LOG/crash-$i.txt 2>&1 &
done
$JAVA -ea -Xmx2g -Dmaxnode=8 -Dsd=500 -cp $CP bergdb.core.CrashTest 1001 $C > $LOG/crash-node8.txt 2>&1 &
wait
for f in $LOG/crash-*.txt; do
    grep -q '^Done: .* 0 failures' $f || fail "CrashTest" $f
    echo "   $(basename $f .txt): $(tail -1 $f)"
done

echo "6. BryanRepro, the bug report of 2015 (restarts with deletes and reclaim)"
mkdir -p $LOG/bryan
$JAVA -ea -Xmx2g -cp $CP bergdb.core.BryanRepro $BRYAN_CYCLES 0 $LOG/bryan > $LOG/bryan.txt 2>&1
grep -q '^Done: .* 0 failures' $LOG/bryan.txt || fail "BryanRepro" $LOG/bryan.txt
echo "   bryan: $(tail -1 $LOG/bryan.txt)"

echo "7. Conformance with the Lean model"
n=0
for cfg in "-Dops=4 -Ddel=25 -Dlong=1" \
    "-Dops=40 -Dexact=1 -Dn=50 -Dkeys=1000 -Ddel=25 -Dlong=1" \
    "-Dmaxnode=62 -Dkeys=1000 -Dn=2000 -Dops=40 -Ddel=20 -Dseeds=3"; do
    n=$((n + 1))
    F=$LOG/a2a3-$n.txt
    $JAVA -ea $cfg -cp $CP bergdb.dag.A2A3Check2 > $F 2>&1
    grep -q 'violating A3 0, A5 0;' $F && grep -q 'NET (A2): .* not current 0 ' $F \
        && grep -q 'in step 3 only 0, in model only 0 ' $F \
        && grep -q 'adopted index nodes not below the old parent 0 (transactions 0)' $F \
        && grep -q 'nodes without exactly one 0 (transactions 0)' $F \
        && grep -q 'A-COPY .* failing 0 (transactions 0)' $F || fail "A2A3Check2" $F
    echo "   a2a3-$n: $(grep -o '^  transactions [0-9]*' $F | sed 's/^ *//'): A2, A3, A5, marking," \
        "TREE, A6' and A-COPY OK; adoptions below the old parent (A6' allows them, A6 not)" \
        "$(grep -o 'does not (bergdb 005-04), [0-9]*' $F | sed 's/.*, //')"
done
(cd ../lean && lake build) > $LOG/lake.txt 2>&1 || fail "the Lean checker, lake build" $LOG/lake.txt
sh stress/conformance.sh small $CONF_SEEDS > $LOG/conformance.txt 2>&1
grep -q '^CONFORMANCE OK' $LOG/conformance.txt || fail "conformance.sh small" $LOG/conformance.txt
echo "   conformance: $(grep '^   traces:' $LOG/conformance.txt | sed 's/^ *//')"

echo "LEVEL 2 OK"
