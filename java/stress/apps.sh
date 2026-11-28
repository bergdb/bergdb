#!/bin/sh
# The user applications as regression tests (bergdb 028-23): programs that agents wrote as
# new users of BergDB from the README and the Javadoc only, each with an oracle of its own
# that checks every result (024-26, against 2026.5; 026-13, against 2026.6; 026-26, an
# independent hunt on the Pub API alone; 031-02 and 031-08, against main before 2026.7; the
# items have the scenarios in full and the runs' records). Compiled with javac against build/bergdb-release.jar, the jar for users; the
# apps at node sizes 8, 14 and 62 reach them through bergdb.core.TestNodeSize, which that
# jar has (since 026-08 no Core API method sets a node size). Kind: functional: the result
# does not depend on speed (the checks that wait for something have limits that only a
# hang meets, or give a NOTE). Not a commit gate.
#
# Usage: java/stress/apps.sh [quick]   each app once, small (about 6 minutes on F53)
#        java/stress/apps.sh soak N    round N of the long runs, new seeds per N
#                                      (about 40 minutes)
#        java/stress/apps.sh kill N    round N of the kill runs (about 30 minutes)
# Round N of soak or kill takes the seeds of the items' round N (024-26 and 026-13,
# section 3), and soak's node sizes are 024-26's, so a round of the records reruns as it
# was; a new N gives new seeds (d1 to d8's too, 100 N + 11 and 12; 026-26's records used
# other seeds; g1 to g11's are 031-02's run.sh's plus 100 N, so round 0 has its seeds, at
# smaller sizes). The times are F53's from the items' records, g1 to g11's from 2026-11-28.
#
# The apps (sources in stress/apps/, by item: a1 to a7 024-26's, b1 to c2 026-13's, d1 to
# d8 026-26's, f1 to f5 031-08's part B, g1 to g11 031-02's, its e1 to e11; e is kept for
# 031-08's part A):
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
#   D1Ledger (d1)      writer threads transfer between accounts, readers check saved views:
#                      every balance and the journal against a replay in commit order, the
#                      views again after a restart (Pub API, as all of d1 to d8).
#   D2ScanHistory (d2) each key's versions: gets and scans both ways at the latest and older
#                      times, odd and supplementary characters; a moved clock and maintain()
#                      drive reclaim, the first available time kept and refused just before.
#   D3ObjectIndex (d3) objects with compound indexes of long, double, string, bytes and
#                      nested fields: index scans against the oracle, indexes deleted and
#                      made again, pinned builders, restarts; with "retain", reclaim too.
#   D4CrashBatches (d4)
#                      SIGKILLs of a child JVM before, during and after writes and syncs:
#                      each recovery a whole prefix of the batches, at least to the last
#                      sync and at most to the last one started.
#   D5ContractEdges (d5)
#                      the Pub limits taken at the limit and refused one beyond, a refusal
#                      changing nothing; spoiled builders, nesting, ownership refusals.
#   D6SchemaValues (d6)
#                      stored values read through twelve field types (numbers' extremes,
#                      NaN, text, bytes) against an oracle, before and after a restart.
#   D7RwConflicts (d7) RW conflicts forced with latches (write skew, absent reads, retries):
#                      each outcome and the committed directory as the oracle has them.
#   D8OnlineIndex (d8) index builds beside a writer, cancelled, renamed and joined by the
#                      next start; a build that must fail on an old object, then succeed.
#   SameBytes (f1)     the README's "One stream" with the Core API: one list of actions
#                      (transactions, settings, maintain(budget) at a set clock) run in ten
#                      ways (restarts, a stop after every action, a cache of 1 MB with
#                      readers, no forces, maintain's calls split or stopped, a copy, a
#                      memory stream), each stream byte for byte the ref's.
#   KillBytes (f2)     f1's actions in child JVMs killed between actions, before a sync and
#                      at random: each kill leaves a prefix of the ref's stream, a start at
#                      an action's end writes nothing, a chain ends with the ref's files.
#   PubSameBytes (f3)  "One stream" with the Pub API and a TestClock: runs fast, slow, with
#                      restarts, with a cache and readers, on a copy: the ref's bytes.
#   FileHandling (f4)  a stopped database's files deleted, cut, swapped with another's, put
#                      back, left with gaps or read-only: each start accepted or refused as
#                      Database's Javadoc says, a refusal changing no file.
#   LiveCopy (f5)      copies of a running database's files (FileStream's procedure, cp of
#                      the files, cp -R): each accepted copy the state after k transactions,
#                      k between the last sync before it and the last commit in it.
#   StmBank (g1)       transfers between accounts (Pub objects, an index on the balance),
#                      hot counters, slow rw() actions, noise that wraps STM's record of
#                      recent writes; with "retain", maintain() calls beside: every rw()
#                      read the state just before it in a replay in commit order; older
#                      states, index scans and frozen readers against the replay.
#   CoreTransform (g2) Core transactions of 1 to 520 KVs with key and value transformations
#                      near the limits, ones that throw, collide or pass 8 MiB: refused
#                      ones write nothing and give their KVs back; optimistic counters
#                      exact; scans both ways at older times, restarts.
#   RetainChurn (g3)   a moved clock, a retain duration of 5 to 24 s, fill, churn, empty,
#                      then maintain() until the stream kept stops shrinking: every version
#                      of every key read back, the first available time's rules; prints the
#                      disk and stream kept after emptying (RB-011).
#   KillWriter (g4)    SIGKILLs of a child JVM that writes values, objects with indexes,
#                      rw() counters, large values, refused transactions and maintain():
#                      each recovery a whole prefix, at least to the last sync, the oracle's
#                      state at it, older states and an index built across kills.
#   ReplaceLimits (g5) key replace (${transactionTime}) in w() and rw() near the limits of
#                      500 operations, 56 KiB of keys and L6: each transaction taken whole
#                      or refused whole, the largest taken below the smallest refused.
#   IndexQuery (g6)    indexes of four level types, compound and nested, over objects that
#                      two writers change; -0.0, NaN, names outside the BMP; indexes made
#                      and deleted under writes: scans and queries at older times, restarts.
#   TreeShaper (g7)    Core patterns that reshape the index (bulk in order, reverse, random,
#                      every other deleted, ranges, all), keys around 7, 14 and 21 bytes, a
#                      cache budget of 4 MB, a retain duration with maintain(): every scan
#                      and get against the oracle at the latest and older times.
#   StmWindow (g8)     the edge of STM's record of recent writes: a reader of a key written
#                      after its read time refused whatever the writes between (0 to
#                      200,000); refused for age only past 96,000 writes.
#   StmBins (g9)       every position of the record: readers one unit before their key's
#                      write refused, readers at the write's time taken.
#   BufferBurst (g10)  bursts of 2 to 40 MB from one to three threads, pauses, closes and
#                      stops right after a burst or in a pause: every key after each restart.
#   RwReplace (g11)    rw() increments that conflict and run again, each logged at a key
#                      with ${transactionTime}: every log whole, in order, at its run's time.
# Not in a mode: c2 SlowDrive (U13-4's reproduction, 026-13 section 4) and b3 OneBuffer (a
# measurement of one buffer's shrink); run them by hand on the classes in build/apps/.
# 031-02's ZeroTailProbe, a test of the system's appends and not of BergDB, stays in the
# item.
#
# The modes:
#   quick   the union of the items' quick modes: each app once, small; Kill 10 kills,
#           KillEmpty 12, Buffers kill 6, D4CrashBatches 10; d1 to d8 at 026-26's seeds,
#           about 30 seconds in all; f1 to f5 at 031-08's apps-b.md's sizes (f1 without
#           -Df1.big, f2 30 kills; about FQTIME); g1 to g11 once each, smaller than
#           031-02's run.sh quick, KillWriter 10 kills (about QTIME).
#   soak N  024-26's soak (DeleteHeavy 18 runs at node sizes 8 to 62, Churn 16, Readers 4
#           of 60 s, IndexChurn 3, Limits, WorstCase at 100,000 keys) and 026-13's
#           (BackToEmpty 14, Transform 4 of 90 s, Buffers many at 150 databases for 90 s,
#           KeyLimits 3, Readers of 20,000 keys, GivenBack 2, Huge 16 rounds) and 026-26's
#           full runs of d1 to d8 but d4 (about 35 seconds), 031-08's f1 at four seeds of
#           700 to 1,800 actions, f3 at three of 900 to 1,500, f4 at four seeds (without
#           its database of 2026.6), f5 at two of 100 copies (about FSTIME), and 031-02's
#           run.sh runs but
#           KillWriter's, with its seeds plus 100 N, smaller (StmBank 2 of 120 s,
#           RetainChurn 2 of 2 rounds, RwReplace 90 s; about STIME).
#   kill N  Kill 300 kills (024-26's Kill at scale), KillEmpty 250 kills, Buffers kill 60,
#           D4CrashBatches 60 kills (about 95 seconds); 031-08's f2 at three seeds of 250
#           kills and one with -Df1.big=true, 200 actions and 120 kills (about FKTIME);
#           031-02's KillWriter with run.sh's three
#           options, 100 kills each, its seeds plus 100 N (about KTIME).
# ONLY=LETTERS runs only the apps of those letters' items (a: 024-26's, b: 026-13's b and
# c, d: 026-26's, f: 031-08's part B, g: 031-02's), for a trial of some; unset, all run.
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
    case ${ONLY:-all} in all|*$grp*) ;; *) return 0 ;; esac
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

# 031-02's and 031-08's apps: each in a directory of its own, $D/TAG, removed before the run
# and after one that passed; a failed run's directory (and TAG.out, TAG.snap) is kept as
# TAG.failed.K.
gk=0
g() {
    tag=$1; shift
    rm -rf $D/$tag $D/$tag.out $D/$tag.snap
    before=$failed
    r "$@"
    if [ "$failed" = "$before" ]; then
        rm -rf $D/$tag $D/$tag.out $D/$tag.snap
    else
        gk=$((gk + 1))
        for x in $D/$tag $D/$tag.out $D/$tag.snap; do [ -e $x ] && mv $x $x.failed.$gk; done
    fi
}

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
    case ${ONLY:-all} in all|*$grp*) ;; *) return 0 ;; esac
    if ! oldjar; then echo "Upgrade: skipped, no 2026.4 jar" | tee -a $LOG; return; fi
    run $JAVA -cp $OLDJAR:$W/classes Upgrade write $D/a7
    run $JAVA -cp $JAR:$W/classes Upgrade open $D/a7
    run $JAVA -cp $OLDJAR:$W/classes Upgrade check $D/a7
}

oldnodesize() {
    case ${ONLY:-all} in all|*$grp*) ;; *) return 0 ;; esac
    if [ -d build/apps/old-dbs/b2-node62 ]; then
        cp -R build/apps/old-dbs/b2-node62 $D/c1
        r OldNodeSize $D/c1
    else
        echo "OldNodeSize: skipped, no build/apps/old-dbs/b2-node62" | tee -a $LOG
    fi
}

b=$((round * 100))
if [ $mode = quick ]; then
    grp=a   # 024-26's quick
    r DeleteHeavy 1 8 3000 2 $D/a1
    r Churn 1 30 3000 4000 $D/a2
    r Churn 2 8 2000 8000 $D/a2 1000 20 0.25 0 400000 queue
    r Limits $D/a3
    r WorstCase $D/wc 5000
    r Kill parent 1 $D/a4 10 5 1500
    r Readers 1 8 4000 20 3 $D/a5 1000
    r IndexChurn 1 2000 $D/a6 1000
    upgrade
    grp=b   # 026-13's quick (its IndexChurn is the one above)
    oldnodesize
    r BackToEmpty 1 30 20000 3 $D/b1 8000
    r Transform 1 20 $D/b2 30
    r Buffers many 1 60 30 $D/b3
    r KeyLimits 1 5000 $D/b4
    r GivenBack $D/gb 50
    r -Xmx3g Huge $D/huge 4
    r KillEmpty parent 1 $D/b5 12 6 2500
    r Buffers kill 1 $D/b3k 6 8
    grp=d   # 026-26's: the final runs' seeds, D4's smoke run
    r -Xmx512m D1Ledger $D/d1 601 4 250
    r -Xmx512m D2ScanHistory $D/d2 601 1800
    r -Xmx512m D3ObjectIndex $D/d3 601 1500 retain
    r -Xmx512m D3ObjectIndex $D/d3i 607 1000
    r -Xmx512m D4CrashBatches $D/d4 101 10
    r -Xmx768m D5ContractEdges $D/d5 601
    r -Xmx512m D6SchemaValues $D/d6 601
    r -Xmx512m D7RwConflicts $D/d7 601 120
    r -Xmx512m D8OnlineIndex $D/d8 601 6 3000
    grp=f   # 031-08's part B, its apps-b.md's sizes (section 5)
    g f1 SameBytes 1 300 $D/f1 all
    g f2 KillBytes 1 300 $D/f2 30
    g f3 PubSameBytes 1 300 $D/f3
    g f4 FileHandling 1 $D/f4
    g f5 LiveCopy 1 $D/f5 20
    grp=g   # 031-02's run.sh quick, smaller
    g g1 StmBank $D/g1 1 6 4 1000
    g g2 CoreTransform $D/g2 1 300
    g g3 RetainChurn $D/g3 11 1
    g g4 KillWriter parent $D/g4 1 10
    g g5 ReplaceLimits mem 2 300
    g g6 IndexQuery $D/g6 1 3
    g g7 TreeShaper $D/g7 1 25 4
    g g8 StmWindow $D/g8 1 15
    g g9 StmBins 1 3
    g g10 BufferBurst $D/g10 1 4
    g g11 RwReplace mem 1 10 8
elif [ $mode = soak ]; then
    grp=a   # 024-26's soak
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
    grp=b   # 026-13's soak (its IndexChurn and first Readers are as 024-26's above)
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
    grp=d   # 026-26's full runs (D4's is in kill)
    r -Xmx512m D1Ledger $D/d1 $((b + 11)) 8 300
    r -Xmx512m D2ScanHistory $D/d2 $((b + 11)) 6000
    r -Xmx512m D3ObjectIndex $D/d3 $((b + 11)) 4000 retain
    r -Xmx512m D3ObjectIndex $D/d3i $((b + 12)) 1800
    r -Xmx768m D5ContractEdges $D/d5 $((b + 11))
    r -Xmx512m D6SchemaValues $D/d6 $((b + 11))
    r -Xmx512m D7RwConflicts $D/d7 $((b + 11)) 200
    r -Xmx512m D8OnlineIndex $D/d8 $((b + 11)) 6 4000
    grp=f   # 031-08's part B but f2 (in kill), apps-b.md's sizes, its seeds plus 100 N
    g f1 SameBytes $((b + 30)) 700 $D/f1 all
    g f1 SameBytes $((b + 31)) 1100 $D/f1 all
    g f1 SameBytes $((b + 32)) 1400 $D/f1 all
    g f1 SameBytes $((b + 33)) 1800 $D/f1 all
    g f3 PubSameBytes $((b + 1)) 900 $D/f3
    g f3 PubSameBytes $((b + 2)) 1200 $D/f3
    g f3 PubSameBytes $((b + 3)) 1500 $D/f3
    for s in 7 8 9 10; do g f4 FileHandling $((b + s)) $D/f4; done
    g f5 LiveCopy $((b + 1)) $D/f5 100
    g f5 LiveCopy $((b + 2)) $D/f5 100
    grp=g   # 031-02's run.sh but KillWriter (in kill), smaller, its seeds plus 100 N
    g g1 -DnoiseSleep=30 StmBank $D/g1 $((b + 11)) 120 8 3000
    g g1 -DnoiseSleep=1 -DnoiseSpace=250000 -Dretain=3 StmBank $D/g1 $((b + 21)) 120 12 400
    g g2 CoreTransform $D/g2 $((b + 6)) 800
    g g3 RetainChurn $D/g3 $((b + 2)) 2
    g g3 -DretainChanges=true RetainChurn $D/g3 $((b + 5)) 2
    g g5 ReplaceLimits $D/g5 $((b + 4)) 600
    g g6 IndexQuery $D/g6 $((b + 4)) 12
    g g7 TreeShaper $D/g7 $((b + 7)) 100 4
    g g8 StmWindow $D/g8 $((b + 12)) 100
    g g9 StmBins $((b + 9)) 40
    g g10 BufferBurst $D/g10 $((b + 1)) 15
    g g11 RwReplace $D/g11 $((b + 2)) 90 16
else
    grp=a; r Kill parent $((b + 3)) $D/a4 300 10 2500
    grp=b; r KillEmpty parent $((b + 1)) $D/b5 250 10 2500
    r Buffers kill $((b + 2)) $D/b3k 60 12
    grp=d; r -Xmx512m D4CrashBatches $D/d4 $((b + 11)) 60
    grp=f   # 031-08's f2, apps-b.md's sizes, its seeds plus 100 N
    g f2 KillBytes $((b + 2)) 800 $D/f2 250
    g f2 KillBytes $((b + 3)) 800 $D/f2 250
    g f2 KillBytes $((b + 4)) 800 $D/f2 250
    g f2 -Df1.big=true KillBytes $((b + 20)) 200 $D/f2 120
    grp=g   # 031-02's KillWriter, run.sh's three options, its seeds plus 100 N
    g g4 KillWriter parent $D/g4 $((b + 63)) 100
    g g4 -DearlyKill=true KillWriter parent $D/g4 $((b + 61)) 100
    g g4 -DearlyKill=true -Didle=true KillWriter parent $D/g4 $((b + 81)) 100
fi
rm -f $TMP

if [ -z "$failed" ]; then
    rm -rf $D
    echo "APPS OK" | tee -a $LOG
else
    echo "APPS FAILED:$failed (log: java/$LOG, data kept in java/$D)" | tee -a $LOG
    exit 1
fi
