#!/bin/sh
# The user applications' workloads against the Lean model (bergdb 030-31): the apps of
# apps.sh (stress/apps/, 028-23) run with AppRecord, which records the Core transactions that
# each database of the run commits (their times, keys and values, the node size, the startup
# distance and reclaim's settings, the restarts); TraceExport replays each recording
# (workload=F) and writes its trace; the checkers of the model check it: tracecheck (the
# model's algorithm on every record, C-A and C-S; with reclaim C-CUT and, on STEP lines,
# C-STEP; the app's restarts with RESTART and RESUME lines, STEP-resume), and on a trace
# replayed without the restarts (whose lines the contract's grammar does not have; the
# records are the same) the contract checker and the bridge checker (lean/contractcheck,
# contractcheck and bridgecheck). Why a recording and a replay: AppRecord's class comment.
# The apps' own checks run as in apps.sh: an app that fails fails this script.
#
# Usage: java/stress/apptraces.sh [night|week]
#   night (default): nine apps once, small (DeleteHeavy, Churn twice, Readers, IndexChurn,
#         BackToEmpty, Transform, KeyLimits, GivenBack), each database's first 60 to 400
#         user transactions (TraceExport's apptx; the check's time grows with the
#         transactions and the keys' segments); about 3 minutes on F53.
#   week: the same apps larger, DeleteHeavy at node sizes 8 to 62, BackToEmpty with
#         maintain() after each transaction, and WorstCase (500 keys of 111 bytes a
#         transaction, node sizes 8 to 62), with seeds of the day (as runlib.sh's DAY), the
#         first 10 to 800 user transactions; about 15 minutes on F53.
# Not in it: the apps whose writes are in a child JVM that is killed (Kill, KillEmpty,
# Buffers kill: a kill loses the record of what it lost), Buffers many (60 to 150
# databases), Huge (values of megabytes), Upgrade and OldNodeSize (other jars).
#
# PAR=N runs N exports and tracechecks at once (default 4); the contract checkers run in
# PAR parts each (lean/contract/par.sh). Builds with build.sh and lake (lean/ and
# lean/contractcheck/). Recordings, traces and outputs go to build/apptraces/MODE/. Prints
# a line per trace, the sums, and APPTRACES OK, or APPTRACES FAILED and exits 1.
# Set JAVA_HOME or PATH for the JDK.
#
# Kind: functional (bergdb 028-23): the result does not depend on the machine's speed or
# load (an app's time-based runs, Readers and Transform, commit more or fewer transactions
# on a faster machine; the checks are the same).

cd "$(dirname "$0")/.." || exit 1
if [ -n "${JAVA_HOME:-}" ]; then
    JAVA=$JAVA_HOME/bin/java; JAVAC=$JAVA_HOME/bin/javac
else
    JAVA=java; JAVAC=javac
fi
# one W REC MAX (internal, as a job of step 2): the recording REC replayed, its first MAX
# user transactions: the trace for tracecheck (with STEP lines if the database ran
# reclaim) and, with reclaim or restarts, one without the restarts and the STEP lines for
# the contract's checkers (else the same trace).
XCP=build/bergdb.jar:build/stress
one() {
    rec=$1; max=$2
    b=$(basename $rec .rec)
    t=$W/traces/$b.trace
    steps=
    grep -q '^SET [0-9]* [0-9]' $rec && steps=-Dsteps=1
    $JAVA -ea -Dworkload=$rec -Dapptx=$max -Dtree=1 $steps -cp $XCP bergdb.core.TraceExport 1 $t \
        > $W/traces/$b.export.txt 2>&1 || echo "TraceExport failed: $(tail -1 $W/traces/$b.export.txt)" \
        > $W/traces/$b.check.txt
    [ -f $t ] && ../lean/.lake/build/bin/tracecheck $t > $W/traces/$b.check.txt 2>&1
    if [ -n "$steps" ] || grep -q '^RESTART' $rec; then
        $JAVA -ea -Dworkload=$rec -Dapptx=$max -Dapprestarts=0 -Dtree=1 -cp $XCP bergdb.core.TraceExport 1 \
            $W/traces/$b.c.trace > $W/traces/$b.c.export.txt 2>&1
    else
        ln $t $W/traces/$b.c.trace
    fi
}

if [ "${1:-}" = one ]; then
    W=$2
    one $3 $4
    exit 0
fi

echo "Kind: functional"
MODE=${1:-night}
case $MODE in night|week) ;; *) echo "APPTRACES FAILED: usage: apptraces.sh [night|week]"; exit 1 ;; esac
PAR=${PAR:-4}
W=build/apptraces/$MODE
START=$(date +%s)

fail() {
    echo "APPTRACES FAILED: $1"
    exit 1
}

./build.sh > /dev/null || fail "build"
(cd ../lean && lake build) > /dev/null 2>&1 || fail "lake build in lean/"
(cd ../lean/contractcheck && lake build) > /dev/null 2>&1 || fail "lake build in lean/contractcheck/"
CHECK=../lean/.lake/build/bin/tracecheck
CCHECK=../lean/contractcheck/.lake/build/bin/contractcheck
BCHECK=../lean/contractcheck/.lake/build/bin/bridgecheck
rm -rf $W
mkdir -p $W/classes $W/data $W/rec $W/traces
$JAVAC --release 17 -nowarn -Xlint:-options -encoding UTF-8 -cp build/bergdb.jar -d $W/classes \
    $(find stress/apps -name '*.java') > $W/javac.txt 2>&1 || fail "javac of the apps ($W/javac.txt)"
CP=build/bergdb.jar:build/stress
D=$W/data

# The apps, one a line: a name, the first user transactions replayed, the class (after a
# system property for the app's JVM, if any) and its arguments (apps.sh's, smaller).
night() {
    echo "a1   400 DeleteHeavy 1 8 300 1 $D/a1"
    echo "a2   200 Churn 1 8 100 300 $D/a2"
    echo "a2q  200 Churn 2 8 100 300 $D/a2q 1000 20 0.25 0 400000 queue"
    echo "a5   200 Readers 1 8 300 1 2 $D/a5 1000"
    echo "a6    60 IndexChurn 1 120 $D/a6 1000 40"
    echo "b1   400 BackToEmpty 1 30 300 1 $D/b1 300"
    echo "b2   100 Transform 1 1 $D/b2 30"
    echo "b4   400 KeyLimits 1 300 $D/b4"
    echo "gb   400 GivenBack $D/gb 5"
}

week() {
    # Seeds of the day (runlib.sh's DAY), so that each run has new ones.
    s=$(( $(date +%s) / 86400 * 10 ))
    for ns in 8 14 30 62; do
        echo "a1-$ns 400 DeleteHeavy $((s + ns)) $ns 500 2 $D/a1-$ns"
    done
    echo "a2-8  250 Churn $((s + 1)) 8 300 500 $D/a2-8"
    echo "a2-30 250 Churn $((s + 2)) 30 1000 500 $D/a2-30 2000 10 0.1 2000000 400000"
    echo "a2q   250 Churn $((s + 3)) 8 300 500 $D/a2q 1000 20 0.25 0 400000 queue"
    echo "a5    400 Readers $((s + 4)) 30 1000 1 3 $D/a5 1000"
    echo "a6    100 IndexChurn $((s + 5)) 150 $D/a6 1000 100"
    echo "b1    800 -Dmaintain=true BackToEmpty $((s + 6)) 30 300 2 $D/b1 1500"
    echo "b2    250 Transform $((s + 7)) 2 $D/b2 30 2 3 2"
    echo "b4    800 KeyLimits $((s + 8)) 1000 $D/b4"
    echo "gb    800 GivenBack $D/gb 20"
    echo "wc     10 WorstCase $D/wc 300"
}

# 1. The apps, recorded.
$MODE > $W/apps.txt
APPFAILED=
while read name max cls args; do
    opt=
    case $cls in -D*) opt=$cls; cls=${args%% *}; args=${args#* } ;; esac
    $JAVA -ea -Xmx2g -XX:+ExitOnOutOfMemoryError $opt -cp $CP:$W/classes bergdb.core.AppRecord \
        $W/rec/$name $cls $args > $W/rec/$name.out 2>&1
    code=$?
    if [ $code != 0 ] || grep -qE '^FAIL|^..:..:.. FAIL|Exception in thread' $W/rec/$name.out; then
        echo "FAILED (exit $code): $cls $args (java/$W/rec/$name.out)"
        APPFAILED="$APPFAILED $name"
    fi
    echo "$name $max" >> $W/max.txt
done < $W/apps.txt

# 2. Each recording replayed and checked (one, above), PAR at once, the largest
# recordings first.
for rec in $W/rec/*.rec; do
    [ -f $rec ] || continue
    grep -q '^TX ' $rec || continue
    app=$(basename $rec .rec | sed 's/-[0-9]*$//')
    echo "$(wc -c < $rec) $rec $(awk -v a=$app '$1 == a {print $2}' $W/max.txt)"
done | sort -k1,1nr | awk '{print $2, $3}' > $W/jobs.txt
xargs -P $PAR -L 1 sh stress/apptraces.sh one $W < $W/jobs.txt

# 3. The contract's checkers on the traces without restarts and STEP lines.
CT=$(ls $W/traces/*.c.trace 2>/dev/null)
[ -n "$CT" ] || fail "no trace"
sh ../lean/contract/par.sh $CCHECK $W/contract.txt $CT
cstatus=$?
sh ../lean/contract/par.sh $BCHECK $W/bridge.txt $CT
bstatus=$?

# 4. The report.
FAILED=$APPFAILED
for f in $W/traces/*.check.txt; do
    b=$(basename $f .check.txt)
    line=$(grep '^TraceExport seed' $W/traces/$b.export.txt | sed 's/.*(workload [^:]*: //; s/): .*//')
    echo "   $b: $(tail -1 $f); $line"
    grep -q '^TRACECHECK OK' $f || FAILED="$FAILED $b"
done
echo "Summed over the traces:"
# The exports' own lines, without the replays for the contract's checkers.
grep -h '^TraceExport seed' $W/traces/*.export.txt | grep -v '(not replayed)' > $W/exports.txt
sum() { sed -nE "s/.*$1.*/\1/p" $W/exports.txt | awk '{s+=$1} END {print s+0}'; }
echo "   workloads: $(ls $W/traces/*.check.txt | wc -l | tr -d ' ') traces of $(wc -l < $W/apps.txt | tr -d ' ') apps; $(sum ': ([0-9]+) user transactions') user transactions, $(sum ' ([0-9]+) operations') operations, $(sum 'operations, ([0-9]+) restarts') restarts replayed; maintain()'s records: the apps' $(sum "maintain...s records: the application.s ([0-9]+)"), the replays' $(sum "the replay.s ([0-9]+)"); the app's time $(sum "the application.s time ([0-9]+) of") times, the app's record's bytes at its position $(sum "at its position ([0-9]+) of") times"
echo "   tracecheck: $(grep -l '^TRACECHECK OK' $W/traces/*.check.txt | wc -l | tr -d ' ') of $(ls $W/traces/*.check.txt | wc -l | tr -d ' ') TRACECHECK OK; transactions checked: $(grep -h '^C-S steps' $W/traces/*.check.txt | sed -E 's/.*of ([0-9]+) transactions.*/\1/' | awk '{s+=$1} END {print s+0}')"
echo "   C-STEP: $(grep -h '^C-STEP' $W/traces/*.check.txt | sed -E 's/.*: ([0-9]+) of ([0-9]+) transactions fail.*; ([0-9]+) STEP lines, ([0-9]+) iterations.*, ([0-9]+) old KVs.*, ([0-9]+) CUT lines.*/\1 \2 \3 \4 \5 \6/' | awk '{f+=$1; t+=$2; s+=$3; i+=$4; o+=$5; c+=$6} END {print f+0 " of " t+0 " transactions fail; " s+0 " STEP lines, " i+0 " iterations, " o+0 " old KVs met and checked put again with the value read, " c+0 " CUT lines"}'); restarts: $(grep -h '^C-STEP' $W/traces/*.check.txt | sed -nE 's/.*; ([0-9]+) restarts.*/\1/p' | awk '{s+=$1} END {print s+0}') with a RESUME line"
echo "   contract: $(grep '^total: ' $W/contract.txt | sed 's/^total: //')"
echo "   bridge: $(grep '^total: ' $W/bridge.txt | sed 's/^total: //')"
[ $cstatus = 0 ] || FAILED="$FAILED contract"
[ $bstatus = 0 ] || FAILED="$FAILED bridge"
echo "Time: $(( $(date +%s) - START )) s"
if [ -n "$FAILED" ]; then
    echo "APPTRACES FAILED:$FAILED (java/$W)"
    exit 1
fi
echo "APPTRACES OK"
