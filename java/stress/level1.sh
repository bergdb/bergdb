#!/bin/sh
# Level 1 regression check (docs/levels.md): BergDB as a multiversion map
# in memory, with restart by replaying the whole stream. Run it before
# committing any change to java/; it must pass.
#
# Usage: java/stress/level1.sh [quick]
#   full (default): about 2.5 minutes on 10 cores (F53, 2026-10-19). quick:
#   about 75 s.
#
# Builds with ../java/build.sh, then runs, stopping at the first failure:
#   1. The unit tests (bergdb.dev.Unit).
#   2. DagFuzz: the Dag alone, transactions with many keys (two new space
#      roots in one transaction, bug fixed 2026-10-12), node sizes 8 to 62.
#   3. DeleteRepro, the delete bug fixed 2026-10-12.
#   4. RestartStress with restarts by full replay: deletes, 7-byte keys,
#      several keys per transaction, 25 restarts per round, default node
#      size (30); also node sizes 8, 14 and 62, 50 keys (small trees, more
#      splits of the root), on disk, and without restarts (level 0).
#   5. RestartInvariance: the same transactions with and without restarts
#      give the same stream, byte for byte (T2 in docs/sis-model.md), and
#      the same dirty set, node ids and lookups.
#   6. Props, the 2014-2017 property suite (bergdb.dev.props; bergdb item
#      006-02): MEM, heap bytes per KV, and SS, stream bytes per user byte,
#      checked against the limits below; CORE, the speed of four Core tests,
#      printed and not checked (full only).
# The startup distance is set to 200 MB, larger than any stream here, so
# startup always replays the whole stream. Logs go to build/level1/.
# Set JAVA_HOME or PATH for the JDK; the build needs javac too.

cd "$(dirname "$0")/.."

JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi

if [ "$1" = quick ]; then
    ROUNDS=10; SIZE_ROUNDS=3; DISK_ROUNDS=2; INV_N=3000; FUZZ_ROUNDS=50
else
    ROUNDS=100; SIZE_ROUNDS=10; DISK_ROUNDS=5; INV_N=12000; FUZZ_ROUNDS=300
fi

SD=200000000
CP=build/bergdb.jar:build/stress
LOG=build/level1
L1="-ea -Xmx2g -Dsd=$SD -Dsessions=25 -Dkeys=3000 -Dmaxnode=0"

fail() {
    echo "LEVEL 1 FAILED: $1 (log: $2)"
    exit 1
}

./build.sh > /dev/null || { echo "LEVEL 1 FAILED: build"; exit 1; }
# Removes old logs and databases, files only (see build.sh about Finder).
mkdir -p $LOG/disk
find $LOG -type f -delete

echo "1. Unit tests"
$JAVA -ea -cp build/bergdb.jar bergdb.dev.Unit > $LOG/unit.txt 2>&1
grep -q '^SUCCESS' $LOG/unit.txt || fail "unit tests" $LOG/unit.txt
grep '^SUCCESS' $LOG/unit.txt

echo "2. DagFuzz"
$JAVA -ea -Dquiet=1 -Dmaxnode=8 -Dkeys=10 -Dn=40 -cp $CP bergdb.dag.DagFuzz 1 $FUZZ_ROUNDS \
    > $LOG/fuzz-8.txt 2>&1 &
$JAVA -ea -Dquiet=1 -Dmaxnode=14 -Dops=12 -Dkeys=12 -Dn=60 -cp $CP bergdb.dag.DagFuzz 1 $FUZZ_ROUNDS \
    > $LOG/fuzz-14.txt 2>&1 &
$JAVA -ea -Dquiet=1 -Dmaxnode=30 -Dops=20 -Dkeys=20 -Dn=40 -cp $CP bergdb.dag.DagFuzz 1 $FUZZ_ROUNDS \
    > $LOG/fuzz-30.txt 2>&1 &
$JAVA -ea -Dquiet=1 -Dmaxnode=62 -Dops=50 -Dkeys=50 -Dn=40 -cp $CP bergdb.dag.DagFuzz 1 $FUZZ_ROUNDS \
    > $LOG/fuzz-62.txt 2>&1 &
wait
for f in $LOG/fuzz-*.txt; do
    grep -q '^Done: .* 0 failures' $f || fail "DagFuzz" $f
    echo "   $(basename $f .txt): $(tail -1 $f)"
done

echo "3. DeleteRepro"
$JAVA -ea -cp $CP bergdb.core.DeleteRepro /k/1000 > $LOG/delete-repro.txt 2>&1
grep -q '^second restart OK' $LOG/delete-repro.txt || fail "DeleteRepro" $LOG/delete-repro.txt

echo "4. RestartStress"
Q=$((ROUNDS / 4))
for i in 0 1 2 3; do
    $JAVA $L1 -cp $CP RestartStress $((1 + i * Q)) $Q > $LOG/stress-$i.txt 2>&1 &
done
for m in 8 14 62; do
    $JAVA $L1 -Dmaxnode=$m -cp $CP RestartStress 1 $SIZE_ROUNDS > $LOG/stress-node$m.txt 2>&1 &
done
for m in 8 14 30; do
    $JAVA $L1 -Dmaxnode=$m -Dkeys=50 -cp $CP RestartStress 1 $SIZE_ROUNDS \
        > $LOG/stress-keys50-node$m.txt 2>&1 &
done
$JAVA $L1 -Dfile=true -Ddir=$LOG/disk -cp $CP RestartStress 101 $DISK_ROUNDS \
    > $LOG/stress-disk.txt 2>&1 &
$JAVA $L1 -Drestart=0 -cp $CP RestartStress 1 $Q > $LOG/stress-norestart.txt 2>&1 &
wait

for f in $LOG/stress-*.txt; do
    grep -q '^Done: .* 0 failures' $f || fail "RestartStress" $f
    echo "   $(basename $f .txt): $(tail -1 $f)"
done

echo "5. RestartInvariance"
$JAVA -ea -Xmx9g -Dsd=$SD -Dn=$INV_N -Dkeys=3000 -Dvalsize=8000 -Devery=$((INV_N / 3)) \
    -Ddel=1 -cp $CP bergdb.core.RestartInvariance 1 > $LOG/invariance.txt 2>&1
F=$LOG/invariance.txt
grep -q '^STREAM: identical' $F || fail "RestartInvariance, stream not byte for byte the same" $F
[ "$(grep -Ec '^(TRANSSEQ|KV CHECKSUM|IDENTITY .*|LOOKUP .*): 0 of' $F)" = 6 ] \
    || fail "RestartInvariance" $F
grep -E '^(STREAM: [is]|TRANSSEQ|KV|IDENTITY|LOOKUP)' $F | sed 's/^/   /'

echo "6. Props"
# Run as in 2014 to 2017, without -ea; numbers to compare with the history in
# src-dev/bergdb/dev/props and bergdb item 006-02. MEM and SS do not depend on
# the machine. The limits are the values of 2026-10-19 (11ea2f6) on JDK 27 with
# its default compact object headers, plus one step for MEM's noise (226 to
# 227 in 31 runs) and for SS on other machines (0.01). When a change improves
# MEM or SS, lower the limit; a change that needs a higher one needs a reason
# in docs/log.md. Without compact object headers (older JDKs, or
# -XX:-UseCompactObjectHeaders) MEM is about 18 bytes higher for this code: it
# is then printed, not checked. CORE (1.00 = cissi, July 2013) depends on the machine
# and on what else runs: printed only.
MEM_MAX=228
SS_MAX="1.51 1.11 1.20 1.63 2.38"   # SS, then SS1 to SS4
$JAVA -cp build/bergdb.jar bergdb.dev.props.Mem > $LOG/props-mem.txt 2>&1 &
$JAVA -cp build/bergdb.jar bergdb.dev.props.SS > $LOG/props-ss.txt 2>&1 &
wait
MEM=$(sed -n 's/^MEM:\([0-9]*\).*/\1/p' $LOG/props-mem.txt)
[ -n "$MEM" ] || fail "Props MEM" $LOG/props-mem.txt
if $JAVA -XX:+PrintFlagsFinal -version 2>/dev/null | grep -Eq ' UseCompactObjectHeaders .*= true'; then
    [ "$MEM" -le $MEM_MAX ] || fail "Props MEM $MEM, more than $MEM_MAX bytes per KV" $LOG/props-mem.txt
    echo "   MEM:$MEM (at most $MEM_MAX)"
else
    echo "   MEM:$MEM (not checked: no compact object headers)"
fi
SS=$(grep '^SS:' $LOG/props-ss.txt)
[ -n "$SS" ] || fail "Props SS" $LOG/props-ss.txt
echo "$SS" | sed -e 's/[^0-9. ]//g' | awk -v max="$SS_MAX" '
    { n = split(max, m, " "); if (NF != n) exit 1
      for (i = 1; i <= n; i++) if ($i > m[i] + 1e-9) exit 1 }' \
    || fail "Props $SS, more than $SS_MAX" $LOG/props-ss.txt
echo "   $SS (at most $SS_MAX)"
if [ "$1" != quick ]; then
    $JAVA -cp build/bergdb.jar bergdb.dev.props.Core > $LOG/props-core.txt 2>&1
    CORE=$(grep -o 'CORE:[0-9.]* ([^)]*)' $LOG/props-core.txt)
    [ -n "$CORE" ] || fail "Props CORE" $LOG/props-core.txt
    echo "   $CORE (get, get4t, getmany, set; not checked)"
fi

echo "LEVEL 1 OK"
