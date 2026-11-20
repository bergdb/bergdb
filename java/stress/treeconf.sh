#!/bin/sh
# The tree model against Java (bergdb 024-12, section 2.7): runs TraceExport
# with tree=1 (trace format 3) on a set of configurations, and checks each
# trace with the Lean tree checker (lean/, lake exe treecheck): the model's
# writer (PE since record format 8, lean/SIS/Tree/Pe.lean; bergdb 026-25) gives
# Java's change and Java's klongs, transaction by transaction,
# the model's get and scan give Java's answers, its touch is Java's, the
# model's invariants hold on Java's tree, and the model's own run from R(0),
# the tree with the model's step, writes Java's records (the checks C-T1 to
# C-T9, in lean/TreeCheck.lean's header).
#
# Usage: [ONLY=NAME] java/stress/treeconf.sh [small|drain|reclaim|all|medium|large] [seeds [first]]
#   small (default): conformance.sh's small set, with tree=1.
#   drain: draining workloads, which reach the joins (merges) and root
#   collapse (until record format 8, bergdb 026-25: the upward unlink, LE-b,
#   root collapse and the take-back): batches with many deletes, UnlinkFuzz's
#   shapes (fifo, long3, random with 40 percent deletes), bulk loads deleted
#   again.
#   reclaim: conformance.sh's reclaim set, with tree=1 (the steps' puts).
#   all: the three. medium: conformance.sh's medium set and larger draining
#   runs, node sizes 8 to 62, 500 transactions. large: conformance.sh's large
#   set, up to 5,000 transactions (the two l-big62 traces take long).
#   seeds: per configuration (default 10 small, 10 drain, 3 reclaim, 3 medium,
#   1 large).
#   first: the first seed (default 1), as in conformance.sh (bergdb 030-30): the seeds are
#   first to first + seeds - 1, a trace's seed is in its name, and with a first other than
#   1 the traces go to build/traces/tree-SET-FIRST/. ONLY=NAME runs only the configuration
#   NAME. A failing trace gets a line FAILED with its seed and the command that runs it
#   again, and its path in the set's failed.txt.
#   hot (small) and d-random (drain) run with live=1: their LIVE lines (Java's
#   searches and top search at every time) are for lean/contract/check.sh
#   (bergdb 030-09).
#
# PAR=N runs N traces at once (default 4), each an export and its check.
# TREECHECK=none writes the traces only, with no tree check (bergdb 030-13: for
# java/stress/contractconf.sh, which checks them with the contract package; the
# tree check of the medium set takes about 10 to 30 minutes per trace of m-d8,
# m-d30 and m-d62); a trace passes if TraceExport wrote it.
# Needs java/build (java/build.sh) and the checker (cd lean && lake build).
# Traces and outputs go to java/build/traces/tree-SET/. Prints one line per
# trace, then what the traces reached, summed, and TREECONF OK or TREECONF
# FAILED. Set JAVA_HOME or PATH for the JDK.
#
# Kind: functional (bergdb 028-23): the result does not depend on the machine's speed or
# load.

cd "$(dirname "$0")/.."
echo "Kind: functional"
JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi
CP=build/bergdb.jar:build/stress
SET=${1:-small}
PAR=${PAR:-4}
# The first seed, and the suffix of the sets' directories (bergdb 030-30).
FIRST=${3:-1}
if [ "$FIRST" = 1 ]; then SUF=; else SUF=-$FIRST; fi
CHECK=${TREECHECK:-../lean/.lake/build/bin/treecheck}
[ "$CHECK" = none ] || [ -x "$CHECK" ] || { echo "TREECONF FAILED: no checker; run lake build in lean/"; exit 1; }

small() {
    # conformance.sh's small set.
    echo "mixed   -Dn=60 -Dkeys=20 -Dmaxnode=8 -Dsd=200 -Dops=4 -Ddel=25 -Dnodel=10 -Dempty=10"
    echo "long    -Dn=60 -Dkeys=50 -Dmaxnode=14 -Dsd=500 -Dops=4 -Dlong=1 -Ddel=25"
    echo "big     -Dn=40 -Dkeys=200 -Dmaxnode=8 -Dsd=1000 -Dops=40 -Dexact=1"
    echo "bulk    -Dn=60 -Dkeys=100 -Dmaxnode=8 -Dsd=300 -Dbulk=40"
    echo "idle    -Dn=150 -Dkeys=30 -Dmaxnode=8 -Dsd=100 -Dops=2 -Dempty=30 -Dnodel=20"
    echo "hot     -Dn=300 -Dkeys=1 -Dmaxnode=8 -Dsd=200 -Dops=1 -Dlive=1"
    echo "a6      -Dn=40 -Dkeys=200 -Dmaxnode=8 -Dsd=1000 -Dops=40 -Dexact=1 -Dlong=1 -Ddel=25"
}

drain() {
    # Batches with many deletes: splits and deletes in one transaction.
    echo "d-batch  -Dn=60 -Dkeys=200 -Dmaxnode=8 -Dsd=1000 -Dops=40 -Dexact=1 -Ddel=60"
    echo "d-a6     -Dn=60 -Dkeys=200 -Dmaxnode=8 -Dsd=1000 -Dops=40 -Dexact=1 -Dlong=1 -Ddel=60"
    echo "d-b14    -Dn=80 -Dkeys=600 -Dmaxnode=14 -Dsd=2000 -Dops=80 -Dexact=1 -Ddel=55"
    # UnlinkFuzz's shapes and defaults.
    echo "d-random -Dn=150 -Dkeys=60 -Dmaxnode=8 -Dsd=300 -Dops=6 -Ddel=40 -Dlive=1"
    echo "d-fifo   -Dn=150 -Dkeys=60 -Dmaxnode=8 -Dsd=300 -Dops=6 -Dshape=fifo"
    echo "d-fifo2  -Dn=200 -Dkeys=400 -Dmaxnode=8 -Dsd=1000 -Dops=30 -Dshape=fifo"
    echo "d-long3  -Dn=150 -Dkeys=60 -Dmaxnode=8 -Dsd=300 -Dops=6 -Ddel=40 -Dshape=long3"
    echo "d-long3b -Dn=100 -Dkeys=300 -Dmaxnode=8 -Dsd=1000 -Dops=40 -Ddel=50 -Dshape=long3"
    # Bulk loads in key order, deleted again; one hot key deleted and put.
    echo "d-bulk   -Dn=120 -Dkeys=100 -Dmaxnode=8 -Dsd=300 -Dbulk=40 -Ddel=70 -Dops=8"
    echo "d-hot    -Dn=200 -Dkeys=2 -Dmaxnode=8 -Dsd=200 -Dops=2 -Ddel=40"
    echo "d-30     -Dn=120 -Dkeys=800 -Dmaxnode=30 -Dsd=3000 -Dops=60 -Ddel=50"
}

reclaim() {
    # conformance.sh's reclaim set.
    echo "r-small -Dn=300 -Dkeys=30 -Dmaxnode=8 -Dsd=200 -Dops=4 -Dretain=1"
    echo "r-del   -Dn=500 -Dkeys=100 -Dmaxnode=8 -Dsd=500 -Dops=4 -Ddel=25 -Dnodel=5 -Dempty=5 -Dretain=1"
    echo "r-long  -Dn=500 -Dkeys=100 -Dmaxnode=14 -Dsd=500 -Dops=4 -Dlong=1 -Ddel=25 -Dretain=2"
    echo "r-big   -Dn=800 -Dkeys=200 -Dmaxnode=14 -Dsd=1000 -Dops=8 -Ddel=25 -Dretain=2"
    echo "r-idle  -Dn=400 -Dkeys=50 -Dmaxnode=8 -Dsd=300 -Dops=2 -Dempty=20 -Dnodel=10 -Dretain=1"
}

medium() {
    # conformance.sh's medium set.
    echo "m-mixed -Dn=500 -Dkeys=500 -Dmaxnode=8 -Dsd=2000 -Dops=4 -Ddel=20 -Dnodel=5 -Dempty=5"
    echo "m-long  -Dn=500 -Dkeys=3000 -Dmaxnode=30 -Dsd=5000 -Dops=8 -Dlong=1 -Ddel=20"
    echo "m-big   -Dn=120 -Dkeys=1000 -Dmaxnode=30 -Dsd=10000 -Dops=20 -Dbulk=60"
    # Draining, larger: node sizes 8, 30 and 62.
    echo "m-d8    -Dn=500 -Dkeys=2000 -Dmaxnode=8 -Dsd=5000 -Dops=60 -Dexact=1 -Ddel=55"
    echo "m-d30   -Dn=500 -Dkeys=5000 -Dmaxnode=30 -Dsd=10000 -Dops=120 -Dexact=1 -Ddel=55"
    echo "m-d62   -Dn=400 -Dkeys=8000 -Dmaxnode=62 -Dsd=20000 -Dops=200 -Dexact=1 -Ddel=55"
    echo "m-long3 -Dn=500 -Dkeys=2000 -Dmaxnode=14 -Dsd=5000 -Dops=60 -Ddel=50 -Dshape=long3"
    echo "m-fifo  -Dn=500 -Dkeys=4000 -Dmaxnode=30 -Dsd=5000 -Dops=100 -Dshape=fifo"
    echo "m-r-del -Dn=800 -Dkeys=300 -Dmaxnode=8 -Dsd=1000 -Dops=12 -Ddel=45 -Dretain=1"
}

large() {
    # conformance.sh's large set.
    echo "l-mixed -Dn=2000 -Dkeys=1000 -Dmaxnode=8 -Dsd=5000 -Dops=4 -Ddel=20 -Dnodel=5 -Dempty=5"
    echo "l-long  -Dn=2000 -Dkeys=3000 -Dmaxnode=30 -Dsd=10000 -Dops=8 -Dlong=1 -Ddel=20"
    echo "l-big62 -Dn=1000 -Dkeys=3000 -Dmaxnode=62 -Dsd=20000 -Dops=20 -Ddel=10 -Dbulk=60"
    echo "l-5000  -Dn=5000 -Dkeys=1000 -Dmaxnode=30 -Dsd=5000 -Dops=4 -Ddel=20 -Dnodel=5 -Dempty=5"
    echo "l-hot   -Dn=2000 -Dkeys=1 -Dmaxnode=8 -Dsd=200 -Dops=1"
    echo "l-few   -Dn=5000 -Dkeys=30 -Dmaxnode=8 -Dsd=500 -Dops=4 -Ddel=20"
}

one_trace() {
    dir=$1; name=$2; s=$3; props=$4
    t=$dir/$name-$s.trace
    $JAVA -ea $props -Dtree=1 -cp $CP bergdb.core.TraceExport $s $t > $dir/$name-$s.export.txt 2>&1 \
        || echo "TraceExport failed: $(tail -1 $dir/$name-$s.export.txt)" > $dir/$name-$s.tree.txt
    if [ -f $t ] && [ "$CHECK" = none ]; then
        grep -q '^DONE ' $t && echo "EXPORTED" > $dir/$name-$s.tree.txt
    elif [ -f $t ]; then
        "$CHECK" $t > $dir/$name-$s.tree.txt 2>&1
    fi
}

FAILED=0
run_set() {
    set_name=$1
    seeds=$2
    dir=build/traces/tree-$set_name$SUF
    mkdir -p $dir
    find $dir -type f -delete
    if [ -n "${ONLY:-}" ]; then
        $set_name | awk -v n="$ONLY" '$1 == n' > $dir/configs.txt
        [ -s $dir/configs.txt ] || { echo "TREECONF FAILED: no configuration $ONLY in set $set_name"; exit 2; }
    else
        $set_name > $dir/configs.txt
    fi
    running=0
    while read name props; do
        s=$FIRST
        while [ $s -lt $((FIRST + seeds)) ]; do
            one_trace $dir $name $s "$props" &
            running=$((running + 1))
            if [ $running -ge $PAR ]; then
                wait
                running=0
            fi
            s=$((s + 1))
        done
    done < $dir/configs.txt
    wait
    : > $dir/failed.txt
    while read name props; do
        s=$FIRST
        while [ $s -lt $((FIRST + seeds)) ]; do
            last=$(tail -1 $dir/$name-$s.tree.txt)
            echo "   $name-$s: $last"
            if ! { [ "$last" = "TREE OK" ] || { [ "$CHECK" = none ] && [ "$last" = EXPORTED ]; }; }; then
                FAILED=$((FAILED + 1))
                echo "$dir/$name-$s.trace" >> $dir/failed.txt
                echo "   FAILED $name-$s, set $set_name, seed $s: $last; trace java/$dir/$name-$s.trace;" \
                    "rerun from the repository's root: ONLY=$name sh java/stress/treeconf.sh $set_name 1 $s"
            fi
            s=$((s + 1))
        done
    done < $dir/configs.txt
    echo "Summed over the traces of tree-$set_name:"
    grep -h '^tree: ' $dir/*.tree.txt | sed -E 's/.*; ([0-9]+) transactions, ([0-9]+) operations \(([0-9]+) noops\), ([0-9]+) key nodes made, ([0-9]+) taken back, ([0-9]+) KN lines, ([0-9]+) GET lines, ([0-9]+) SCAN lines, ([0-9]+) touches.*/\1 \2 \3 \4 \5 \6 \7 \8 \9/' \
        | awk '{t+=$1; o+=$2; n+=$3; m+=$4; b+=$5; k+=$6; g+=$7; s+=$8; u+=$9} END {print "   " t+0 " transactions, " o+0 " operations (" n+0 " noops), " m+0 " key nodes made, " b+0 " taken back, " k+0 " KN lines, " g+0 " GET lines, " s+0 " SCAN lines, " u+0 " touches"}'
    grep -h '^bound: ' $dir/*.tree.txt | awk '{m+=$2; b+=$7} END {print "   " m+0 " key nodes marked, dirtyNodeBound " b+0 ", summed"}'
    grep -h '^run: ' $dir/*.tree.txt | awk '{r+=$2} END {print "   " r+0 " records of the model'"'"'s own run compared with Java'"'"'s"}'
    for k in "C-T1 change" "C-T2 klongs" "C-T3 noops" "C-T4 reads" "C-T5 touch" "C-T6 invariants" "C-T8 bound" "C-T9 run" "C-T7 form" "C-T7 model errors"; do
        grep -h "^$k:" $dir/*.tree.txt | awk -v k="$k" '{f+=$3; n++} END {if (n > 0) print "   " k ": " f+0 " failures"}'
    done
    grep -h '^reached: ' $dir/*.tree.txt | sed 's/^reached: //' | tr ',' '\n' \
        | awk 'NF==2 {s[$1]+=$2} END {for (n in s) print "   reached " n ": " s[n]}' | sort
    echo "   exporter errors: $(grep -c '^ERROR' $dir/*.trace | awk -F: '{s+=$2} END {print s+0}')"
}

START=$(date +%s)
case $SET in
    small) run_set small ${2:-10} ;;
    drain) run_set drain ${2:-10} ;;
    reclaim) run_set reclaim ${2:-3} ;;
    all) run_set small ${2:-10}; run_set drain ${2:-10}; run_set reclaim ${2:-3} ;;
    medium) run_set medium ${2:-3} ;;
    large) run_set large ${2:-1} ;;
    *) echo "Usage: treeconf.sh [small|drain|reclaim|all|medium|large] [seeds [first]]"; exit 2 ;;
esac
echo "Time: $(( $(date +%s) - START )) s"
if [ $FAILED -eq 0 ]; then
    echo "TREECONF OK"
else
    echo "TREECONF FAILED: $FAILED traces"
    exit 1
fi
