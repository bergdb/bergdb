#!/bin/sh
# Level 2 regression check (bergdb 027-01, levels.md):
# restart with bounded startup, where startup reads only the tail of the
# stream. Not a commit gate (java/before-commit.sh is, since 2026-10-20);
# run it after larger changes.
#
# Usage: java/stress/level2.sh [quick]
#   full (default): 17 minutes on F53 (2026-11-17, other runs going), step 8b
#   about 80 s of it (bergdb 030-13); 55 minutes under a heavier load. quick:
#   about 2 minutes (an older measure).
#
# Builds with ../java/build.sh, then runs, stopping at the first failure:
#   0. The pins (bergdb 030-28): lean/contract/pins.sh, every file pinned in
#      lean/contract/statements.pin (the main theorems' statements, the tree
#      checker's writer lean/SIS/Tree/Pe.lean, pecmp) has its pinned hash; no
#      build, about a second. First its own test: a changed and a removed pinned
#      file must fail.
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
#      give the same stream, byte for byte (T2 in bergdb 027-01, sis-model.md), and
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
#   8. The tree model against Java (bergdb 024-12; run before step 7, and
#      written before it here, so that changes of step 7 merge): treeconf.sh
#      on its small, drain and reclaim sets (2 seeds quick, 10 full; reclaim
#      1 and 3): the Lean model of the key tree (lean/SIS/Tree) gives Java's
#      change of every traced transaction, node by node and klong by klong,
#      and Java's answers to gets and scans; the tree's invariants hold.
#  8b. The writer's contract on the same traces (bergdb 030-04, 030-13):
#      lean/contract/check.sh on the small and drain sets, with both checkers on
#      each trace: contractcheck (each transaction meets the contract, the
#      trace is whole, the LIVE lines are Java's searches) and bridgecheck (the
#      bridge's clauses to the abstract model, bergdb 030-07); first their fault
#      tests, faults.sh, faults-top.sh and bridge-faults.sh (on a small and a
#      reclaim trace). Until 2026-11-20 lean/contract/bridge-check.sh then ran
#      bridgecheck and bridge-faults.sh a second time on the same sets (bergdb
#      028-37). About 80 s.
#      It builds the checkers in lean/contractcheck/, a Lake package without
#      Mathlib that builds them from lean/contract/'s files (bergdb 028-24).
#  8c. The tested writer is the proved writer (bergdb 030-28): lean/pecmp/check.sh
#      on the small, drain and reclaim sets of step 8: pecmp runs the tree
#      checker's writer (lean/SIS/Tree/Pe.lean, a copy) and the proved writer
#      (lean/contract/Contract/PeWriter.lean, bergdb 030-21) on Java's structure
#      before every transaction, and they must write the same: the writes in
#      their order, the ids' order, the trees, the top node. So Java, which step 8
#      compares with the copy node for node, writes what the proved writer
#      writes. First pecmp's own tests (--cap-h, --top-fault) must fail. Builds
#      pecmp in lean/pecmp/ (no Mathlib); a few seconds a set.
#   7. Conformance with the Lean model (bergdb 011-11, 12):
#      A2A3Check2 (a transaction meets the model's A2, A3 and A5, and Db
#      marks what the model marks; and, since bergdb 005-04, TREE, A6' and
#      A-COPY, the model's assumptions of stage 2, and since bergdb 024-09
#      A6 itself: no adoption below the old parent) on three configurations;
#      and the trace checker on conformance.sh's small set (2 seeds quick, 10
#      full): every transaction must be a step of the model that meets its
#      assumptions, every restart invisible.
#      Since bergdb 024-09 (step A1) also the draining configurations, which
#      reach the delete path's joins (merges) and root collapse: A2A3Check2
#      on seven of them, five with its own keys and two with shape=long,
#      UnlinkFuzz's long keys, where segment trees come and go; and the
#      trace checker on conformance.sh's drain set (2 seeds quick, 10 full).
#      A draining configuration whose writer joins no node fails the step:
#      it no longer reaches the mechanism. Until record format 8 (bergdb
#      026-25) the mechanism was the take-back (a node that a transaction
#      made and emptied again was taken back, never written; bergdb 023-05),
#      and a klong left to a node taken back (fault 12 of bergdb 023-08)
#      failed A-COPY; the writer of format 8 makes no such node, and
#      A2A3Check2 counts any node made and replaced in a transaction.
#      And TakeCheck check (bergdb 024-09, step A4): Java's take gives, on 300
#      generated cases, the numbers that lake build compares with the
#      model's javaTake (lean/SIS/BoundExample.lean), and its integer share
#      and dither those of the model's shareFp and ditherFp.
# Logs go to build/level2/. Set JAVA_HOME or PATH for the JDK; the build
# needs javac too. Steps 7, 8, 8b and 8c need Lean (elan, with the toolchain of
# ../lean/lean-toolchain, ../lean/contractcheck/lean-toolchain and
# ../lean/pecmp/lean-toolchain); they build the checkers with lake.
#
# Kind: functional (bergdb 028-23): the result does not depend on the machine's speed or
# load; its time limits are hang guards, generous for a loaded machine.

cd "$(dirname "$0")/.."
echo "Kind: functional"

JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi

if [ "$1" = quick ]; then
    QUICK=1; ROUNDS=40; SIZE_ROUNDS=3; INV_N=600; CRASH_ROUNDS=4; BRYAN_CYCLES=15
    CONF_SEEDS=2; DRAIN_SEEDS=2
else
    QUICK=0; ROUNDS=200; SIZE_ROUNDS=10; INV_N=2000; CRASH_ROUNDS=20; BRYAN_CYCLES=40
    CONF_SEEDS=10; DRAIN_SEEDS=10
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

echo "0. The pins (bergdb 030-28)"
sh ../lean/contract/pins.sh > $LOG/pins.txt 2>&1
grep -q '^PINS OK' $LOG/pins.txt || fail "lean/contract/pins.sh: $(grep -A3 '^changed\|^PINS FAILED' $LOG/pins.txt | head -4 | tr '\n' ' ')" $LOG/pins.txt
echo "   $(grep 'files have their pinned hashes' $LOG/pins.txt)"

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

echo "8. The tree model against Java (bergdb 024-12)"
(cd ../lean && lake build) > $LOG/lake-tree.txt 2>&1 || fail "the Lean tree checker, lake build" $LOG/lake-tree.txt
for set in small drain reclaim; do
    seeds=$CONF_SEEDS
    if [ $set = reclaim ]; then seeds=$((1 + CONF_SEEDS / 4)); fi
    sh stress/treeconf.sh $set $seeds > $LOG/treeconf-$set.txt 2>&1
    grep -q '^TREECONF OK' $LOG/treeconf-$set.txt || fail "treeconf.sh $set" $LOG/treeconf-$set.txt
    echo "   treeconf $set: $(grep ' transactions, ' $LOG/treeconf-$set.txt | sed 's/^ *//')"
done

echo "8b. The writer's contract and the bridge on the tree traces (bergdb 030-13)"
# The checkers, built without Mathlib (lean/contractcheck/, bergdb 028-24).
(cd ../lean/contractcheck && lake build) > $LOG/lake-contract.txt 2>&1 \
    || fail "the contract checkers, lake build in lean/contractcheck" $LOG/lake-contract.txt
# check.sh runs bridge-faults.sh only if a small and a reclaim trace are there.
[ -f build/traces/tree-reclaim/r-del-1.trace ] \
    || fail "no reclaim trace for lean/contract/bridge-faults.sh" build/traces/tree-reclaim
sh ../lean/contract/check.sh small drain > $LOG/contract.txt 2>&1
grep -q '^CONTRACT OK' $LOG/contract.txt || fail "lean/contract/check.sh small drain" $LOG/contract.txt
grep -q '^(bridge-faults.sh not run' $LOG/contract.txt \
    && fail "lean/contract/check.sh did not run bridge-faults.sh" $LOG/contract.txt
grep '^tree-' $LOG/contract.txt | sed 's/^/   /' | cut -c1-150

echo "8c. The tested writer against the proved writer (bergdb 030-28)"
(cd ../lean/pecmp && lake build) > $LOG/lake-pecmp.txt 2>&1 \
    || fail "pecmp, lake build in lean/pecmp" $LOG/lake-pecmp.txt
sh ../lean/pecmp/check.sh small drain reclaim > $LOG/pecmp.txt 2>&1
grep -q '^PECMP OK' $LOG/pecmp.txt || fail "lean/pecmp/check.sh small drain reclaim" $LOG/pecmp.txt
grep '^tree-' $LOG/pecmp.txt | sed 's/^/   pecmp, /' | cut -c1-150

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
        && grep -q 'does not (bergdb 005-04), 0 (transactions 0)' $F \
        && grep -q 'nodes without exactly one 0 (transactions 0)' $F \
        && grep -q 'A-COPY .* failing 0 (transactions 0)' $F || fail "A2A3Check2" $F
    echo "   a2a3-$n: $(grep -o '^  transactions [0-9]*' $F | sed 's/^ *//'): A2, A3, A5, marking," \
        "TREE, A6 and A-COPY OK"
done
# The draining configurations (bergdb 024-09, step A1).
# a2a3_failing FILE: the first rule that A2A3Check2's output does not show to hold, with
# its counts; nothing if all hold.
a2a3_failing() {
    grep -q '^  transactions ' $1 || { echo "no result ($(tail -1 $1))"; return; }
    grep -q 'violating A3 0, A5 0;' $1 \
        || { echo "A3 or A5: $(grep -o 'violating A3 [0-9]*, A5 [0-9]*' $1)"; return; }
    grep -q 'NET (A2): .* not current 0 ' $1 \
        || { echo "A2: $(grep -o 'nodes with a klong at tt not current [0-9]* (transactions [0-9]*)' $1)"; return; }
    grep -q 'in step 3 only 0, in model only 0 ' $1 \
        || { echo "marking: $(grep -o 'in step 3 only [0-9]*, in model only [0-9]*' $1)"; return; }
    grep -q 'adopted index nodes not below the old parent 0 (transactions 0)' $1 \
        || { echo "A6': $(grep -o 'adopted index nodes not below the old parent [0-9]* (transactions [0-9]*)' $1)"; return; }
    grep -q 'does not (bergdb 005-04), 0 (transactions 0)' $1 \
        || { echo "A6: adopted below the old parent $(grep -o 'does not (bergdb 005-04), [0-9]* (transactions [0-9]*)' $1 | sed 's/.*, //')"; return; }
    grep -q 'nodes without exactly one 0 (transactions 0)' $1 \
        || { echo "TREE: $(grep -o 'nodes without exactly one [0-9]* (transactions [0-9]*)' $1)"; return; }
    grep -q 'A-COPY .* failing 0 (transactions 0)' $1 \
        || { echo "A-COPY: new pointers $(grep -o 'failing [0-9]* (transactions [0-9]*)' $1)"; return; }
}
n=0
for cfg in "-Dops=40 -Dexact=1 -Dn=200 -Dkeys=300 -Ddel=60 -Dlong=1" \
    "-Dmaxnode=14 -Dops=60 -Dexact=1 -Dn=200 -Dkeys=600 -Ddel=50" \
    "-Dmaxnode=8 -Dops=20 -Dexact=1 -Dn=400 -Dkeys=25 -Ddel=65" \
    "-Dmaxnode=8 -Dops=60 -Dexact=1 -Dn=300 -Dkeys=80 -Ddel=60 -Dlong=1" \
    "-Dmaxnode=8 -Dops=40 -Dn=400 -Dkeys=50 -Ddel=70" \
    "-Dshape=long -Dops=40 -Dexact=1 -Dn=30 -Dkeys=60 -Ddel=40 -Dseeds=300" \
    "-Dshape=long -Dops=40 -Dn=30 -Dkeys=60 -Ddel=40 -Dseeds=300 -Dunsorted=1"; do
    n=$((n + 1))
    F=$LOG/a2a3-drain-$n.txt
    $JAVA -ea $cfg -cp $CP bergdb.dag.A2A3Check2 > $F 2>&1
    R=$(a2a3_failing $F)
    [ -z "$R" ] || fail "A2A3Check2, draining configuration $n ($cfg): $R" $F
    TB=$(sed -n 's/^  made and replaced in a transaction .* \([0-9]*\)$/\1/p' $F)
    [ "${TB:-1}" -eq 0 ] || fail "A2A3Check2, draining configuration $n ($cfg): nodes made and replaced in a transaction: ${TB:-none counted}" $F
    JN=$(sed -n 's/^  joins (merges) of the writer //p' $F)
    [ "${JN:-0}" -gt 0 ] || fail "A2A3Check2, draining configuration $n ($cfg) joins no node: it does not reach the merges" $F
    echo "   a2a3-drain-$n: $(grep -o '^  transactions [0-9]*' $F | sed 's/^ *//'): A2, A3, A5, marking," \
        "TREE, A6 and A-COPY OK; joins $JN"
done
(cd ../lean && lake build) > $LOG/lake.txt 2>&1 || fail "the Lean checker, lake build" $LOG/lake.txt
sh stress/conformance.sh small $CONF_SEEDS > $LOG/conformance.txt 2>&1
grep -q '^CONFORMANCE OK' $LOG/conformance.txt || fail "conformance.sh small" $LOG/conformance.txt
echo "   conformance: $(grep '^   traces:' $LOG/conformance.txt | sed 's/^ *//')"
sh stress/conformance.sh drain $DRAIN_SEEDS > $LOG/conformance-drain.txt 2>&1
grep -q '^CONFORMANCE OK' $LOG/conformance-drain.txt \
    || fail "conformance.sh drain: $(grep '^CONFORMANCE FAILED' $LOG/conformance-drain.txt | cut -c1-300)" $LOG/conformance-drain.txt
echo "   conformance, drain: $(grep '^   traces:' $LOG/conformance-drain.txt | sed 's/^ *//');" \
    "$(grep '^   Dag counters' $LOG/conformance-drain.txt | sed -e 's/^ *//' -e 's/ (.*):/:/' -e 's/; of .*//')"

$JAVA -ea -cp $CP bergdb.core.TakeCheck check > $LOG/takecheck.txt 2>&1
grep -q '^TAKECHECK OK' $LOG/takecheck.txt || fail "TakeCheck check: Java's take against the Lean model's numbers" $LOG/takecheck.txt
echo "   take: $(tail -1 $LOG/takecheck.txt)"

echo "LEVEL 2 OK"
