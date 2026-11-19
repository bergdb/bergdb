#!/bin/sh
# The user applications as regression tests (bergdb 028-23): programs that agents wrote as
# new users of BergDB from the README and the Javadoc only, each with an oracle of its own
# that checks every result (024-26, against 2026.5; 026-13, against 2026.6; both items have
# the scenarios in full and the runs' records). Compiled with javac against
# build/bergdb-release.jar, the jar for users; the apps at node sizes 8, 14 and 62 reach
# them through bergdb.core.TestNodeSize, which that jar has (since 026-08 no Core API method
# sets a node size). Kind: functional: the result does not depend on speed (the checks
# that wait for something have limits that only a hang meets, or give a NOTE). Not a commit
# gate.
#
# Usage: java/stress/apps.sh [quick]   each app once, small (about 6 minutes on F53)
#        java/stress/apps.sh soak N    round N of the long runs, new seeds per N
#                                      (about 40 minutes)
#        java/stress/apps.sh kill N    round N of the kill runs (about 30 minutes)
# Round N of soak or kill takes the seeds of the items' round N (024-26 and 026-13,
# section 3), and soak's node sizes are 024-26's, so a round of the records reruns as it
# was; a new N gives new seeds. The times are F53's from the items' records.
#
# The apps (sources in stress/apps/, by item: a1 to a7 024-26's, b1 to c2 026-13's):
#   DeleteHeavy (a1)   bulk loads of six key shapes, scattered, ranged and near-total
#                      deletes, refills, builders whose last call wins (Core API, file
#                      streams, node sizes 8 to 62, some with a cache below the data):
#                      every state against the oracle (scans, gets, ranges forward and
#                      backward, prefixes, older times, getTrans) and through restarts.
#   Churn (a2)         overwrite and delete churn, a queue, large values, with a clock that
#                      the app moves and reclaim: the latest state, reads inside and before
#                      the retain duration, getFirstAvailableLookupTime's promise, getTrans
#                      through reclaim's copies, the retain duration kept by restarts.
#   Limits (a3)        Pub and Core transactions near and over the limits L1 to L6: taken up
#                      to each limit, refused beyond it, and a refusal writes nothing.
#   WorstCase (a3)     at each node size, transactions of 500 keys of 111 bytes that make
#                      the most index nodes dirty that the limits allow: all taken.
#   Kill (a4)          SIGKILL of a child JVM during deletes and reclaim: each recovery has
#                      the last synced transaction, and no fewer than the one before.
#   Readers (a5)       3 reader threads at older times while a writer deletes: each read
#                      against the oracle at its actual time; a cut read only before the
#                      first available time.
#   IndexChurn (a6)    Pub objects with two indexes, long keys and levels, reclaim and
#                      restarts: primary and index scans against the oracle, also at older
#                      times.
#   Upgrade (a7)       a database of 2026.4 (its jar built from the tag release-2026.4,
#                      once, into build/apps/; skipped with a note if that fails) is refused
#                      by this jar's open() and create() with no file changed, and 2026.4
#                      still reads all of it.
#   BackToEmpty (b1)   loads, mass deletes and a slow drive with a moved clock: every cut
#                      keeps the oldest available state whole (P8), and the stream kept comes
#                      back near a fresh twin's.
#   Transform (b2)     transformer threads beside plain writers and readers: value and key
#                      transformations that throw or pass a limit refuse their transaction,
#                      which writes nothing and gives back its KVs; counters exact.
#   GivenBack (b2)     a refused transaction gives its time back: a read at a time taken
#                      during it never sees the next transaction's write.
#   Buffers (b3)       many: 60 to 150 Pub databases with bursty writers, reopens, a spare
#                      pool; every key checked, and the write buffers shrink after the writes
#                      (the heap 3.5 s after the syncs, or with a NOTE 10 s after, within
#                      500 kB a database of a reopened one); kill: SIGKILLs of a child that
#                      writes bursts to 8 to 12 databases, each recovery at or after the last
#                      sync (a transaction lost 2 s after its commit is a NOTE, LATE).
#   Huge (b3)          transactions of 7 to 31 MB through the grown and the shrunk buffer.
#   KeyLimits (b4)     Limits.keyBytes and checkKey against an oracle and against every put
#                      and delete of keys of odd characters near 111 bytes.
#   KillEmpty (b5)     SIGKILLs in cycles of load, delete all and drive, with refused poison
#                      transactions: recoveries as Kill's, and no refusal fails the database.
#   OldNodeSize (c1)   a node-size-62 database made by an earlier jar is refused, no file
#                      changed; runs only if build/apps/old-dbs/b2-node62 exists (026-13's,
#                      not in the repository), else a note.
# Not in a mode: c2 SlowDrive (U13-4's reproduction, 026-13 section 4) and b3 OneBuffer (a
# measurement of one buffer's shrink); run them by hand on the classes in build/apps/.
#
# The modes:
#   quick   the union of the two items' quick modes: each app once, small; Kill 10 kills,
#           KillEmpty 12, Buffers kill 6.
#   soak N  024-26's soak (DeleteHeavy 18 runs at node sizes 8 to 62, Churn 16, Readers 4
#           of 60 s, IndexChurn 3, Limits, WorstCase at 100,000 keys) and 026-13's
#           (BackToEmpty 14, Transform 4 of 90 s, Buffers many at 150 databases for 90 s,
#           KeyLimits 3, Readers of 20,000 keys, GivenBack 2, Huge 16 rounds).
#   kill N  Kill 300 kills (024-26's Kill at scale), KillEmpty 250 kills, Buffers kill 60.
#
# Environment: JAVA_HOME (the JDK; the PATH's otherwise). Builds with build.sh, then runs on
# a copy of build/bergdb-release.jar in build/apps/MODE-N/ (classes, data, out.txt), so that
# build.sh may run meanwhile and runs of other modes or rounds share nothing. The output of
# every app is in build/apps/MODE-N/out.txt; a failure keeps the data there. A line that
# starts with FAIL (after a time or not), an uncaught exception or a nonzero exit is a
# failure. Prints "Kind: functional" first and APPS OK last, or APPS FAILED and exits 1.

echo "Kind: functional"
cd "$(dirname "$0")/.." || exit 1

if [ -n "${JAVA_HOME:-}" ]; then
    JAVA=$JAVA_HOME/bin/java; JAVAC=$JAVA_HOME/bin/javac; JARTOOL=$JAVA_HOME/bin/jar
else
    JAVA=java; JAVAC=javac; JARTOOL=jar
fi
mode=${1:-quick}
case $mode in
    quick) round=1 ;;
    soak|kill) round=${2:?"usage: apps.sh soak N | kill N"} ;;
    *) echo "APPS FAILED: usage: apps.sh [quick] | soak N | kill N"; exit 1 ;;
esac
case $round in *[!0-9]*|'') echo "APPS FAILED: N must be a number"; exit 1 ;; esac
[ $mode = quick ] && W=build/apps/quick || W=build/apps/$mode-$round
JAR=$W/bergdb-release.jar
D=$W/data
LOG=$W/out.txt
TMP=$W/app.txt
APPS=stress/apps

./build.sh > /dev/null || { echo "APPS FAILED: build"; exit 1; }
rm -rf $W
mkdir -p $W/classes $D
cp build/bergdb-release.jar $JAR
echo "Apps $mode${2:+ $round}: $(date '+%Y-%m-%d %H:%M'), log java/$LOG" | tee $LOG
$JAVAC --release 17 -nowarn -Xlint:-options -encoding UTF-8 -cp $JAR -d $W/classes \
    $(find $APPS -name '*.java') >> $LOG 2>&1 || { echo "APPS FAILED: javac (java/$LOG)"; exit 1; }

J="$JAVA -ea -Xmx2g -XX:+ExitOnOutOfMemoryError -cp $JAR:$W/classes"
NOISE='^..:..:.. (round|tx)|^..:..:..   drive'
BAD='^FAIL|^..:..:.. FAIL|Exception in thread'
failed=

# Runs one app: its output into the log, its last OK or FAIL line printed (or its last line);
# a failure is remembered.
run() {
    echo "== $*" >> $LOG
    "$@" > $TMP 2>&1
    code=$?
    grep -vE "$NOISE" $TMP >> $LOG
    last=$(grep -E "^OK|^..:..:.. OK|FAIL" $TMP | tail -1)
    echo "${last:-$(grep -vE "$NOISE" $TMP | tail -1)}"
    if [ $code != 0 ] || grep -qE "$BAD" $TMP; then
        echo "FAILED (exit $code): $*" | tee -a $LOG
        failed="$failed $(echo "$*" | sed 's/.*-cp [^ ]* //' | cut -d' ' -f1-3)"
    fi
}
r() { run $J "$@"; }

# 2026.4's jar for Upgrade: built once from the tag's java/src into build/apps/.
OLDJAR=build/apps/bergdb-2026.4.jar
oldjar() {
    [ -f $OLDJAR ] && return 0
    o=build/apps/old-$$
    rm -rf $o
    mkdir -p $o/classes
    if git -C .. archive release-2026.4 java/src 2>> $LOG | tar -x -C $o 2>> $LOG &&
        $JAVAC --release 17 -nowarn -Xlint:-options -encoding UTF-8 -d $o/classes \
            $(find $o/java/src -name '*.java') >> $LOG 2>&1 &&
        $JARTOOL cf $o/bergdb-2026.4.jar -C $o/classes . >> $LOG 2>&1; then
        mv $o/bergdb-2026.4.jar $OLDJAR
    fi
    rm -rf $o
    [ -f $OLDJAR ]
}

upgrade() {
    if ! oldjar; then echo "Upgrade: skipped, no 2026.4 jar" | tee -a $LOG; return; fi
    run $JAVA -cp $OLDJAR:$W/classes Upgrade write $D/a7
    run $JAVA -cp $JAR:$W/classes Upgrade open $D/a7
    run $JAVA -cp $OLDJAR:$W/classes Upgrade check $D/a7
}

oldnodesize() {
    if [ -d build/apps/old-dbs/b2-node62 ]; then
        cp -R build/apps/old-dbs/b2-node62 $D/c1
        r OldNodeSize $D/c1
    else
        echo "OldNodeSize: skipped, no build/apps/old-dbs/b2-node62" | tee -a $LOG
    fi
}

b=$((round * 100))
if [ $mode = quick ]; then
    # 024-26's quick
    r DeleteHeavy 1 8 3000 2 $D/a1
    r Churn 1 30 3000 4000 $D/a2
    r Churn 2 8 2000 8000 $D/a2 1000 20 0.25 0 400000 queue
    r Limits $D/a3
    r WorstCase $D/wc 5000
    r Kill parent 1 $D/a4 10 5 1500
    r Readers 1 8 4000 20 3 $D/a5 1000
    r IndexChurn 1 2000 $D/a6 1000
    upgrade
    # 026-13's quick (its IndexChurn is the one above)
    oldnodesize
    r BackToEmpty 1 30 20000 3 $D/b1 8000
    r Transform 1 20 $D/b2 30
    r Buffers many 1 60 30 $D/b3
    r KeyLimits 1 5000 $D/b4
    r GivenBack $D/gb 50
    r -Xmx3g Huge $D/huge 4
    r KillEmpty parent 1 $D/b5 12 6 2500
    r Buffers kill 1 $D/b3k 6 8
elif [ $mode = soak ]; then
    # 024-26's soak
    for s in 1 2 3 4; do
        for ns in 8 14 30 62; do r DeleteHeavy $((b + s)) $ns 6000 4 $D/a1; done
    done
    r DeleteHeavy $((b + 9)) 8 20000 3 $D/a1 400000
    r DeleteHeavy $((b + 10)) 30 30000 2 $D/a1 1000000
    for s in 1 2 3; do
        r Churn $((b + s)) 8 3000 20000 $D/a2 1000 20 0.25 0 400000
        r Churn $((b + s)) 30 8000 20000 $D/a2 2000 10 0.1 2000000 400000
        r Churn $((b + s)) 62 5000 15000 $D/a2 1000 50 0.9 0 400000
        r Churn $((b + s)) 8 5000 40000 $D/a2 1000 20 0.25 0 400000 queue
        r Churn $((b + s)) 30 20000 30000 $D/a2 1000 5 0.25 0 400000 queue
    done
    for s in 1 2; do
        r Readers $((b + s)) 8 5000 60 3 $D/a5 0
        r Readers $((b + s + 10)) 30 5000 60 3 $D/a5 1000
        r IndexChurn $((b + s)) 6000 $D/a6 1000 2000
    done
    r IndexChurn $((b + 5)) 4000 $D/a6 0 1000
    r Churn $((b + 7)) 30 30 300 $D/a2 1000 500 0.25 0 400000 big
    r Limits $D/a3
    r WorstCase $D/wc 100000
    # 026-13's soak (its IndexChurn and first Readers are as 024-26's above)
    for s in 1 2 3 4; do
        for sd in 200000 400000 1000000; do
            r BackToEmpty $((b + s * 10 + sd / 200000)) 30 30000 4 $D/b1 8000 0 $sd
        done
    done
    r BackToEmpty $((b + 5)) 30 200000 2 $D/b1 8000 4000000
    r BackToEmpty $((b + 6)) 30 300000 2 $D/b1 16000 10000000 2000000
    for s in 1 2; do
        r Transform $((b + s)) 90 $D/b2 30 2 3 2
        r Transform $((b + s + 10)) 90 $D/b2 30 3 4 1
    done
    r Buffers many $((b + 1)) 150 90 $D/b3
    for s in 1 2 3; do r KeyLimits $((b + s)) 30000 $D/b4; done
    r Readers $((b + 2)) 30 20000 60 3 $D/a5 1000
    r GivenBack $D/gb 300
    r GivenBack $D/gb 300 moving
    r -Xmx3g Huge $D/huge 16
else
    r Kill parent $((b + 3)) $D/a4 300 10 2500
    r KillEmpty parent $((b + 1)) $D/b5 250 10 2500
    r Buffers kill $((b + 2)) $D/b3k 60 12
fi
rm -f $TMP

if [ -z "$failed" ]; then
    rm -rf $D
    echo "APPS OK" | tee -a $LOG
else
    echo "APPS FAILED:$failed (log: java/$LOG, data kept in java/$D)" | tee -a $LOG
    exit 1
fi
