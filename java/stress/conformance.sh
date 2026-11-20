#!/bin/sh
# Level 2 conformance (bergdb 011-11): runs TraceExport on a set of
# configurations, and checks each trace with the Lean checker (lean/, lake exe
# tracecheck). Written 2026-10-15 for F1-008-11, WPs C3 and F1.
#
# Usage: [ONLY=NAME] java/stress/conformance.sh [small|medium|large|all|reclaim|crash|evict|drain] [seeds [first]]
#   small (default): the Lean tier on every transaction, in the target mode
#   (marking, Java's still-dirty test, the virtual root) and, for the first
#   three seeds of the first two configurations, in the unchanged model's mode
#   (--model). medium: larger runs, target mode only. large (2026-10-16, bergdb
#   item 001, WP C3): up to 5,000 transactions, node sizes 8 to 62, up to 3,000
#   keys, and runs with hundreds of top nodes. all: the three. reclaim
#   (2026-10-17, bergdb item 001, K3): Level 3, the small reclaim set of
#   reclaimtraces.sh, reclaim on, with the checker's reclaim checks (the touch,
#   the steps on the cut stream, CutOK at every cut, the probes after restarts
#   from the cut stream); a trace without a cut fails. Since bergdb 030-27 its traces
#   are of format 3 with STEP lines (TraceExport's tree=1 and steps=1), and the
#   checker's C-STEP checks each step of reclaim against the model of the steps
#   (030-25; since 030-34 also the values it writes back and that it writes nothing
#   else than them and its row) and each cut against its iteration's last step; a
#   trace without a STEP
#   line fails. crash (bergdb 030-31): the reclaim set's kind of runs, with run A
#   restarted after every K-th call and crashed right after every K-th step of reclaim
#   (TraceExport's restart and crash), RESTART and RESUME lines, and C-STEP's
#   STEP-resume: an iteration across a restart goes on from the row its last step
#   committed; a trace without a cut, a STEP line or a crash fails. evict (2026-10-18, bergdb
#   item 001, WP J4): Level 4, configurations of the small, medium and reclaim
#   sets with run E (TraceExport's rune: run A's workload with a forced eviction
#   schedule, or the capacity controller with a small budget, since J7), whose
#   stream must be run A's, and whose slots (SLOT lines) the checker's C-P
#   checks against the model's INV-SLOT; a trace without SLOT lines fails.
#   Since bergdb item 009, step 4c, run E also writes its handle state (HMEM,
#   HTABLE, HANDLE, HOBJ and HPTR lines, the objects' histories by their
#   hashes), which the checker's C-H checks against the model's invariants with
#   handles; a trace without HANDLE lines fails. Four of its configurations read between run E's transactions, and
#   three of them restart run E too (TraceExport's ereads and erestart).
#   Since bergdb 005-04 the small and evict sets each have a configuration
#   with A6's kind, a segment root that a transaction makes and splits in
#   place (a6, e-a6: two-segment keys, 40 KVs per transaction). Since 023-09
#   (fault 12's fix, 023-08, Q9) the segment leaf's klong is pointed to the
#   new root in place, so no node is adopted below its old parent: a trace of
#   them with such an adoption, or without the checker's count, fails (A6,
#   not only A6'). Until then a trace of them without one failed. Since
#   bergdb 024-09 (Frans, 2026-11-11, question 2) the rule holds for every
#   trace of every set: the gates require A6 everywhere.
#   drain (2026-11-11, bergdb 024-09, step A1): configurations that drain
#   trees (50 to 65 percent deletes, few keys), so that the delete path's
#   joins (merges) and root collapse are in the traces (until record format
#   8, bergdb 026-25: the upward unlink, root collapse and take-back of
#   bergdb 023-05); three of them with long=2, UnlinkFuzz's long keys, whose
#   small segment trees a transaction makes and empties. The reclaim set has
#   one such configuration (r-drain) and the evict set two (e-drain,
#   e-r-drain). A configuration whose name contains "drain" must join a node
#   in one of its seeds at least (TraceExport's last output line, the Dag's
#   counters): else its traces no longer reach the merges, and the run
#   fails. Every set's summary has the sum of those counters.
#   seeds: per configuration (default 10 small, 3 medium, 2 large, 5 reclaim, 3
#   evict, 3 drain). The checker computes
#   the model's own definitions, with fast versions proven equal to them
#   (lean/Check/Fast.lean, since bergdb item 001, WP C2).
#   first: the first seed (default 1): the seeds are first to first + seeds - 1, and a
#   trace's seed is in its name (NAME-SEED). The fixed seeds from 1 are the level scripts'
#   regression set; night.sh adds a run on new seeds each day, from the day's number times
#   1000 (bergdb 030-30). With a first other than 1 the traces go to
#   build/traces/SET-FIRST/, so that the fixed seeds' traces stay.
#
# ONLY=NAME runs only the configuration NAME of the set: with seeds 1 and first SEED, one
# trace again (bergdb 030-30). A failing trace gets a line FAILED with its seed and the
# command that runs it again, and its path in the set's failed.txt (night.sh keeps those
# traces).
#
# PAR=N runs N traces at once (default 4), each an export and its check.
#
# Needs java/build (java/build.sh) and the checker (cd lean && lake build).
# Traces and checker outputs go to java/build/traces/SET/. Prints one line per
# trace, then the failing checks summed over all traces, the time and memory of
# the runs, and CONFORMANCE OK or CONFORMANCE FAILED for the sets run. Set
# JAVA_HOME or PATH for the JDK.
#
# Kind: functional (bergdb 028-23): the result does not depend on the machine's speed or
# load.

cd "$(dirname "$0")/.."
echo "Kind: functional"
JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi
CP=build/bergdb.jar:build/stress
RAN=

# The time and memory of each run, where /usr/bin/time has -l and -o (macOS).
if /usr/bin/time -l -o /dev/null true 2> /dev/null; then
    timed() { o=$1; shift; /usr/bin/time -l -o "$o" "$@"; }
else
    timed() { shift; "$@"; }
fi
SET=${1:-small}
PAR=${PAR:-4}
# The first seed, and the suffix of the sets' directories (bergdb 030-30).
FIRST=${3:-1}
if [ "$FIRST" = 1 ]; then SUF=; else SUF=-$FIRST; fi
LEAN=../lean
CHECK=${CHECK:-$LEAN/.lake/build/bin/tracecheck}
[ -x "$CHECK" ] || { echo "CONFORMANCE FAILED: no checker; run lake build in lean/"; exit 1; }

small() {
    # name and TraceExport properties
    echo "mixed   -Dn=60 -Dkeys=20 -Dmaxnode=8 -Dsd=200 -Dops=4 -Ddel=25 -Dnodel=10 -Dempty=10 -Dprobe=1 -Dlive=1"
    echo "long    -Dn=60 -Dkeys=50 -Dmaxnode=14 -Dsd=500 -Dops=4 -Dlong=1 -Ddel=25 -Dprobe=10 -Dlive=1"
    echo "big     -Dn=40 -Dkeys=200 -Dmaxnode=8 -Dsd=1000 -Dops=40 -Dexact=1 -Dprobe=10"
    echo "bulk    -Dn=60 -Dkeys=100 -Dmaxnode=8 -Dsd=300 -Dbulk=40 -Dprobe=5"
    echo "idle    -Dn=150 -Dkeys=30 -Dmaxnode=8 -Dsd=100 -Dops=2 -Dempty=30 -Dnodel=20 -Dprobe=1"
    # Many top nodes (one hot key), the root queried at every time (bergdb item 001, L5).
    echo "hot     -Dn=300 -Dkeys=1 -Dmaxnode=8 -Dsd=200 -Dops=1 -Dprobe=30 -Dlive=1"
    # A6's kind: a segment root made and split in place in one transaction (bergdb 005-04).
    echo "a6      -Dn=40 -Dkeys=200 -Dmaxnode=8 -Dsd=1000 -Dops=40 -Dexact=1 -Dlong=1 -Ddel=25 -Dprobe=10"
}

medium() {
    echo "m-mixed -Dn=500 -Dkeys=500 -Dmaxnode=8 -Dsd=2000 -Dops=4 -Ddel=20 -Dnodel=5 -Dempty=5 -Dprobe=50"
    echo "m-long  -Dn=500 -Dkeys=3000 -Dmaxnode=30 -Dsd=5000 -Dops=8 -Dlong=1 -Ddel=20 -Dprobe=100"
    echo "m-big   -Dn=120 -Dkeys=1000 -Dmaxnode=30 -Dsd=10000 -Dops=20 -Dbulk=60 -Dprobe=30"
}

reclaim() {
    # The small reclaim set of reclaimtraces.sh (bergdb item 001, WP R2): retain is in
    # seconds of RestartInvariance's scaled clock; probes every ten transactions and
    # right after each cut.
    echo "r-small -Dn=300 -Dkeys=30 -Dmaxnode=8 -Dsd=200 -Dops=4 -Dretain=1 -Dprobe=10"
    echo "r-del   -Dn=500 -Dkeys=100 -Dmaxnode=8 -Dsd=500 -Dops=4 -Ddel=25 -Dnodel=5 -Dempty=5 -Dretain=1 -Dprobe=10"
    echo "r-long  -Dn=500 -Dkeys=100 -Dmaxnode=14 -Dsd=500 -Dops=4 -Dlong=1 -Ddel=25 -Dretain=2 -Dprobe=10"
    echo "r-big   -Dn=800 -Dkeys=200 -Dmaxnode=14 -Dsd=1000 -Dops=8 -Ddel=25 -Dretain=2 -Dprobe=10"
    echo "r-idle  -Dn=400 -Dkeys=50 -Dmaxnode=8 -Dsd=300 -Dops=2 -Dempty=20 -Dnodel=10 -Dretain=1 -Dprobe=10"
    # Trees drained and refilled; must take back a node (bergdb 024-09, step A1).
    echo "r-drain -Dn=400 -Dkeys=30 -Dmaxnode=8 -Dsd=200 -Dops=6 -Ddel=60 -Dretain=1 -Dprobe=10"
    # maintain() after every user transaction (bergdb 024-32): its steps, its empty records
    # with a take beyond the share, its fillers and its cuts.
    echo "r-maint -Dn=300 -Dkeys=30 -Dmaxnode=8 -Dsd=200 -Dops=4 -Ddel=25 -Dretain=1 -Dprobe=10 -Dmaint=1"
}

crash() {
    # Reclaim across restarts and crashes of run A (bergdb 030-31): larger values and more
    # keys than the reclaim set's, so that iterations take several steps and cross a
    # restart; no run B (probe), whose run has no crash.
    echo "c-small -Dn=300 -Dkeys=30 -Dmaxnode=8 -Dsd=200 -Dops=4 -Dretain=1 -Drestart=10 -Dcrash=2"
    echo "c-vals  -Dn=400 -Dkeys=200 -Dmaxnode=8 -Dsd=500 -Dops=6 -Ddel=20 -Dvalsize=200 -Dretain=1 -Drestart=5 -Dcrash=3"
    echo "c-long  -Dn=400 -Dkeys=150 -Dmaxnode=14 -Dsd=500 -Dops=6 -Dlong=1 -Ddel=25 -Dvalsize=150 -Dretain=2 -Drestart=7 -Dcrash=2"
    echo "c-del60 -Dn=300 -Dkeys=60 -Dmaxnode=8 -Dsd=200 -Dops=6 -Ddel=60 -Dvalsize=100 -Dretain=1 -Drestart=4 -Dcrash=2"
    echo "c-maint -Dn=200 -Dkeys=100 -Dmaxnode=8 -Dsd=300 -Dops=4 -Ddel=25 -Dvalsize=150 -Dretain=1 -Dmaint=2 -Drestart=6 -Dcrash=4"
}

evict() {
    # Run E with the random schedule (each slot to a detachable object with probability
    # 0.3, seeded by the trace's seed), every, values, and the capacity controller; SLOT
    # lines after every transaction (every fifth in e-m-mixed).
    echo "e-mixed   -Dn=60 -Dkeys=20 -Dmaxnode=8 -Dsd=200 -Dops=4 -Ddel=25 -Dnodel=10 -Dempty=10 -Dprobe=1 -Drune=random"
    echo "e-long    -Dn=60 -Dkeys=50 -Dmaxnode=14 -Dsd=500 -Dops=4 -Dlong=1 -Ddel=25 -Dprobe=10 -Drune=random"
    echo "e-every   -Dn=60 -Dkeys=50 -Dmaxnode=8 -Dsd=500 -Dops=4 -Ddel=25 -Dprobe=10 -Drune=every"
    echo "e-values  -Dn=60 -Dkeys=50 -Dmaxnode=8 -Dsd=500 -Dops=4 -Ddel=25 -Dprobe=10 -Drune=values"
    echo "e-hot     -Dn=300 -Dkeys=1 -Dmaxnode=8 -Dsd=200 -Dops=1 -Dprobe=30 -Drune=random"
    echo "e-m-mixed -Dn=500 -Dkeys=500 -Dmaxnode=8 -Dsd=2000 -Dops=4 -Ddel=20 -Dnodel=5 -Dempty=5 -Dprobe=50 -Drune=random -Dslotevery=5"
    echo "e-r-small -Dn=300 -Dkeys=30 -Dmaxnode=8 -Dsd=200 -Dops=4 -Dretain=1 -Dprobe=10 -Drune=random"
    echo "e-r-long  -Dn=500 -Dkeys=100 -Dmaxnode=14 -Dsd=500 -Dops=4 -Dlong=1 -Ddel=25 -Dretain=2 -Dprobe=10 -Drune=random"
    # The capacity controller (bergdb item 001, WP J7) with a budget of 30 kB.
    echo "e-budget  -Dn=300 -Dkeys=200 -Dmaxnode=8 -Dsd=500 -Dops=4 -Ddel=25 -Dprobe=10 -Drune=budget -Devictbudget=30000"
    echo "e-r-budget -Dn=300 -Dkeys=30 -Dmaxnode=8 -Dsd=200 -Dops=4 -Dretain=1 -Dprobe=10 -Drune=budget -Devictbudget=20000"
    # A6's kind with the random schedule (bergdb 005-04).
    echo "e-a6      -Dn=40 -Dkeys=200 -Dmaxnode=8 -Dsd=1000 -Dops=40 -Dexact=1 -Dlong=1 -Ddel=25 -Dprobe=10 -Drune=random"
    # Reads between run E's transactions, at random times, and restarts (bergdb item 009,
    # step 4c): versions read in handles, pointers that hold dead handles followed again, and
    # the startup's state, with Rule R from its section, for C-H.
    echo "e-reads   -Dn=60 -Dkeys=50 -Dmaxnode=14 -Dsd=500 -Dops=4 -Dlong=1 -Ddel=25 -Dprobe=10 -Drune=random -Dereads=20"
    echo "e-restart -Dn=100 -Dkeys=50 -Dmaxnode=8 -Dsd=300 -Dops=4 -Ddel=25 -Dprobe=10 -Drune=random -Dereads=20 -Derestart=10"
    echo "e-r-restart -Dn=300 -Dkeys=30 -Dmaxnode=8 -Dsd=200 -Dops=4 -Dretain=1 -Dprobe=10 -Drune=random -Dereads=20 -Derestart=25"
    echo "e-b-restart -Dn=300 -Dkeys=200 -Dmaxnode=8 -Dsd=500 -Dops=4 -Ddel=25 -Dprobe=10 -Drune=budget -Devictbudget=30000 -Dereads=20 -Derestart=50"
    # Trees drained and refilled, with reads and restarts, and with reclaim; each must take
    # back a node (bergdb 024-09, step A1).
    echo "e-drain   -Dn=200 -Dkeys=30 -Dmaxnode=8 -Dsd=300 -Dops=8 -Ddel=65 -Dprobe=10 -Drune=random -Dereads=20 -Derestart=10"
    echo "e-r-drain -Dn=300 -Dkeys=30 -Dmaxnode=8 -Dsd=200 -Dops=10 -Ddel=65 -Dretain=1 -Dprobe=10 -Drune=random -Dereads=20 -Derestart=25"
    # maintain() every third transaction, with eviction, reads and restarts (bergdb 024-32).
    echo "e-r-maint -Dn=300 -Dkeys=30 -Dmaxnode=8 -Dsd=200 -Dops=4 -Ddel=25 -Dretain=1 -Dprobe=10 -Dmaint=3 -Drune=random -Dereads=20 -Derestart=25"
}

drain() {
    # Trees drained and refilled (bergdb 023-05, P4's traces; 024-09, step A1): mostly
    # deletes on few keys. long=2 is UnlinkFuzz's long key shape, with which segment trees
    # come and go (until record format 8 a trace took back segment roots too).
    echo "drain      -Dn=300 -Dkeys=25 -Dmaxnode=8 -Dsd=200 -Dops=10 -Ddel=65 -Dprobe=10 -Dlive=1"
    echo "drainlong  -Dn=200 -Dkeys=60 -Dmaxnode=8 -Dsd=300 -Dops=20 -Dexact=1 -Ddel=60 -Dlong=1 -Dprobe=10"
    echo "drainbig   -Dn=100 -Dkeys=80 -Dmaxnode=8 -Dsd=1000 -Dops=40 -Dexact=1 -Ddel=60 -Dlong=2 -Dprobe=10"
    echo "drain14    -Dn=300 -Dkeys=200 -Dmaxnode=14 -Dsd=500 -Dops=30 -Dexact=1 -Ddel=60 -Dlong=2 -Dprobe=20"
    # Most of the keys in every transaction. Until record format 8 (bergdb 026-25) a
    # transaction made a segment root, split it in place and emptied it again, and a klong
    # left to a node taken back (fault 12 of bergdb 023-08, review C) failed here: the
    # writer's assertion on the pointer, or C-A's A-COPY.
    echo "drainroots -Dn=60 -Dkeys=90 -Dmaxnode=8 -Dsd=300 -Dops=120 -Dexact=1 -Ddel=50 -Dlong=2 -Dprobe=10"
}

large() {
    # l-hot and l-few have hundreds of top nodes (one hot key; 30 keys at node size 8).
    echo "l-mixed -Dn=2000 -Dkeys=1000 -Dmaxnode=8 -Dsd=5000 -Dops=4 -Ddel=20 -Dnodel=5 -Dempty=5 -Dprobe=200"
    echo "l-long  -Dn=2000 -Dkeys=3000 -Dmaxnode=30 -Dsd=10000 -Dops=8 -Dlong=1 -Ddel=20 -Dprobe=400"
    echo "l-big62 -Dn=1000 -Dkeys=3000 -Dmaxnode=62 -Dsd=20000 -Dops=20 -Ddel=10 -Dbulk=60 -Dprobe=200"
    echo "l-5000  -Dn=5000 -Dkeys=1000 -Dmaxnode=30 -Dsd=5000 -Dops=4 -Ddel=20 -Dnodel=5 -Dempty=5 -Dprobe=500"
    echo "l-hot   -Dn=2000 -Dkeys=1 -Dmaxnode=8 -Dsd=200 -Dops=1 -Dprobe=200"
    echo "l-few   -Dn=5000 -Dkeys=30 -Dmaxnode=8 -Dsd=500 -Dops=4 -Ddel=20 -Dprobe=500"
}

# One trace: the export and its check (and the unchanged model's mode for the first
# small traces).
one_trace() {
    set_name=$1; name=$2; s=$3; props=$4
    # The reclaim set: format 3 with STEP lines, for C-STEP (bergdb 030-27).
    if [ $set_name = reclaim ] || [ $set_name = crash ]; then props="$props -Dtree=1 -Dsteps=1"; fi
    dir=build/traces/$set_name$SUF
    t=$dir/$name-$s.trace
    timed $dir/$name-$s.export.time \
        $JAVA -ea $props -cp $CP bergdb.core.TraceExport $s $t > $dir/$name-$s.export.txt 2>&1 \
        || echo "TraceExport failed: $(tail -1 $dir/$name-$s.export.txt)" > $dir/$name-$s.check.txt
    if [ -f $t ]; then
        timed $dir/$name-$s.check.time "$CHECK" $t > $dir/$name-$s.check.txt 2>&1
        if [ $set_name = small ] && [ $s -le 3 ] && { [ $name = mixed ] || [ $name = long ]; }; then
            "$CHECK" $t --model > $dir/$name-$s.model.txt 2>&1
        fi
    fi
}

run_set() {
    set_name=$1
    seeds=$2
    dir=build/traces/$set_name$SUF
    RAN="$RAN $set_name"
    mkdir -p $dir
    find $dir -type f -delete
    if [ -n "${ONLY:-}" ]; then
        $set_name | awk -v n="$ONLY" '$1 == n' > $dir/configs.txt
        [ -s $dir/configs.txt ] || { echo "CONFORMANCE FAILED: no configuration $ONLY in set $set_name"; exit 2; }
    else
        $set_name > $dir/configs.txt
    fi
    # PAR traces at once, in batches.
    running=0
    while read name props; do
        s=$FIRST
        while [ $s -lt $((FIRST + seeds)) ]; do
            one_trace $set_name $name $s "$props" &
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
            echo "   $name-$s: $(tail -1 $dir/$name-$s.check.txt)"
            why=$(trace_failure $set_name $dir/$name-$s)
            if [ -n "$why" ]; then
                echo "$dir/$name-$s.trace" >> $dir/failed.txt
                echo "   FAILED $name-$s, set $set_name, seed $s: $why; trace java/$dir/$name-$s.trace;" \
                    "rerun from the repository's root: ONLY=$name sh java/stress/conformance.sh $set_name 1 $s"
            fi
            s=$((s + 1))
        done
    done < $dir/configs.txt
}

# Why the trace $2 (its path without .trace) of set $1 fails, by the checks of the end of
# this script; nothing if it passes (bergdb 030-30).
trace_failure() {
    if ! grep -q 'TRACECHECK OK' $2.check.txt 2> /dev/null; then
        echo "$(tail -1 $2.check.txt 2> /dev/null)"
    elif [ $1 = reclaim ] && ! grep -q '^CUT ' $2.trace; then
        echo "a reclaim trace without a cut"
    elif [ $1 = reclaim ] && ! grep -q '^STEP ' $2.trace; then
        echo "a reclaim trace without a STEP line"
    elif [ $1 = evict ] && ! grep -q '^SLOT ' $2.trace; then
        echo "an eviction trace without SLOT lines"
    elif [ $1 = evict ] && ! grep -q '^HANDLE ' $2.trace; then
        echo "an eviction trace without HANDLE lines"
    elif ! grep -q '^C-A adoptions below the old parent .*: 0 of' $2.check.txt; then
        echo "an adoption below the old parent (A6), or no count of them"
    fi
}

# The Dag's counters of the exports of set $1, summed (TraceExport's last output line, so
# each trace's runs A, B and E together): how far the set's traces reach the writer's
# decisions (PeWriter, bergdb 026-25; until record format 8 the delete path's upward unlink,
# root collapse and take-back, bergdb 024-06, section 4.4).
dag_counters() {
    cat build/traces/$1$SUF/*.export.txt | sed -nE 's/^Dag counters: transactions ([0-9]+), appends ([0-9]+), replaced ([0-9]+), compactions ([0-9]+), cuts ([0-9]+), joins ([0-9]+), collapses ([0-9]+), new roots ([0-9]+), dropped ([0-9]+)$/\1 \2 \3 \4 \5 \6 \7 \8 \9/p' \
        | awk '{n++; a+=$2; r+=$3; p+=$4; u+=$5; j+=$6; c+=$7; w+=$8; d+=$9; if ($6 > 0) nj++; if ($7 > 0) nc++}
            END {print "   Dag counters (the exports, each with its runs A, B and E): appends " a+0 ", replaced " r+0 ", compactions " p+0 ", cuts " u+0 ", joins " j+0 ", collapses " c+0 ", new roots " w+0 ", dropped " d+0 "; of " n+0 " traces " nj+0 " join a node, " nc+0 " collapse a root"}'
}

# The joins of the exports of configuration $2 of set $1, over its seeds.
joins() {
    cat build/traces/$1$SUF/$2-*.export.txt | sed -nE 's/^Dag counters: .*, joins ([0-9]+), .*/\1/p' \
        | awk '{s+=$1} END {print s+0}'
}

summary() {
    dir=build/traces/$1$SUF
    echo "Summed over the traces of $1, target mode: transactions failing, by check"
    for k in "C-A assumptions" "C-S steps" "diagnostics"; do
        grep -h "^$k" $dir/*.check.txt | sed -E 's/.*\((.*)\)/\1/' | tr ',' '\n' \
            | awk -v k="$k" 'NF==2 {s[$1]+=$2} END {for (n in s) print "   " k ": " n " " s[n]}'
    done
    echo "   C-A adoptions below the old parent (A6' allows them, A6 not): $(grep -h '^C-A adoptions below' $dir/*.check.txt | sed -E 's/.*: ([0-9]+) of .*/\1/' | awk '{s+=$1} END {print s+0}') transactions"
    echo "   C-V: $(grep -h '^C-V' $dir/*.check.txt | awk '{s+=$3} END {print s+0}') transactions with live differences, $(grep -h '^C-V' $dir/*.check.txt | awk '{s+=$7} END {print s+0}') LIVE lines"
    if [ $1 = reclaim ] || [ $1 = crash ]; then
        echo "   C-CUT: $(grep -h '^C-CUT cuts' $dir/*.check.txt | awk '{f+=$3; n+=$5} END {print f+0 " of " n+0}') CUT lines fail; traces without a cut: $(grep -L '^CUT ' $dir/*.trace | wc -l | tr -d ' ')"
        echo "   C-STEP: $(grep -h '^C-STEP' $dir/*.check.txt | sed -E 's/.*: ([0-9]+) of ([0-9]+) transactions fail.*; ([0-9]+) STEP lines, ([0-9]+) iterations \(([0-9]+) ended.*, ([0-9]+) old KVs.*, ([0-9]+) CUT lines.*/\1 \2 \3 \4 \5 \6 \7/' | awk '{f+=$1; t+=$2; s+=$3; i+=$4; e+=$5; o+=$6; c+=$7} END {print f+0 " of " t+0 " transactions fail; " s+0 " STEP lines, " i+0 " iterations (" e+0 " ended by a step with eod), " o+0 " old KVs met and checked put again with the value read, " c+0 " CUT lines with their iteration'"'"'s last step"}'); traces without a STEP line: $(grep -L '^STEP ' $dir/*.trace | wc -l | tr -d ' ')"
    fi
    if [ $1 = crash ]; then
        echo "   STEP-resume: $(grep -h '^C-STEP' $dir/*.check.txt | sed -nE 's/.*; ([0-9]+) restarts \(([0-9]+) crashes\), ([0-9]+) with an iteration in progress, ([0-9]+) iterations with.*/\1 \2 \3 \4/p' | awk '{r+=$1; c+=$2; i+=$3; s+=$4} END {print r+0 " restarts (" c+0 " crashes), " i+0 " with an iteration in progress, " s+0 " iterations with a step before a restart and the next after it"}')"
    fi
    if [ $1 = evict ]; then
        echo "   C-P: $(grep -h '^C-P slots' $dir/*.check.txt | sed -E 's/.*: ([0-9]+) of ([0-9]+) transactions fail; ([0-9]+) SLOT lines, ([0-9]+) checked.*/\1 \2 \3 \4/' | awk '{f+=$1; t+=$2; n+=$3; c+=$4} END {print f+0 " of " t+0 " transactions fail; " n+0 " SLOT lines, " c+0 " checked"}'); traces without SLOT lines: $(grep -L '^SLOT ' $dir/*.trace | wc -l | tr -d ' ')"
        echo "   C-H: $(grep -h '^C-H handles' $dir/*.check.txt | sed -E 's/.*: ([0-9]+) of ([0-9]+) transactions fail; ([0-9]+) states, ([0-9]+) handles, ([0-9]+) objects, ([0-9]+) histories compared, ([0-9]+) pointers, ([0-9]+) checked.*/\1 \2 \3 \4 \5 \6 \7 \8/' | awk '{f+=$1; t+=$2; n+=$3; h+=$4; o+=$5; x+=$6; p+=$7; c+=$8} END {print f+0 " of " t+0 " transactions fail; " n+0 " states, " h+0 " handles, " o+0 " objects, " x+0 " histories compared, " p+0 " pointers, " c+0 " checked by the record rule"}'); traces without HANDLE lines: $(grep -L '^HANDLE ' $dir/*.trace | wc -l | tr -d ' ')"
        echo "   C-H cases: $(grep -h '^C-H cases' $dir/*.check.txt | sed -E 's/.*: ([0-9]+) snapshots, ([0-9]+) of nodes.*; ([0-9]+) pointers to snapshots, ([0-9]+) with a reference.*; ([0-9]+) pointers checked written.*, ([0-9]+) with a vpos.*/\1 \2 \3 \4 \5 \6/' | awk '{a+=$1; b+=$2; c+=$3; d+=$4; e+=$5; f+=$6} END {print a+0 " snapshots (" b+0 " of nodes in the startup section after a restart), " c+0 " pointers to snapshots (" d+0 " with a reference older than the section'"'"'s), " e+0 " pointers written with their handle'"'"'s written position (" f+0 " with a vpos)"}')"
    fi
    echo "   C-L: $(grep -h '^C-L' $dir/*.check.txt | awk '{s+=$4} END {print s+0}') of $(grep -h '^C-L' $dir/*.check.txt | awk '{s+=$6} END {print s+0}') FIRST lines fail"
    echo "   C-R: $(grep -h '^C-R' $dir/*.check.txt | awk '{s+=$3} END {print s+0}') failed probes; kinds:"
    grep -h '^  PROBE' $dir/*.check.txt | sed -E 's/[0-9]+/N/g' | sort | uniq -c | sed 's/^/      /'
    echo "   exporter errors: $(grep -h '^exporter errors' $dir/*.check.txt | awk '{s+=$3} END {print s+0}')"
    echo "   traces: $(ls $dir/*.check.txt | wc -l | tr -d ' '), TRACECHECK OK: $(grep -l 'TRACECHECK OK' $dir/*.check.txt | wc -l | tr -d ' ')"
    for k in export check; do
        ls $dir/*.$k.time > /dev/null 2>&1 || continue
        echo "   time and memory, $k: $(awk '/ real /{s+=$1; if ($1>l) l=$1} /maximum resident set size/{if ($1>m) m=$1} END {printf "%.0f s in total, %.0f s at most, at most %.0f MB", s, l, m/1048576}' $dir/*.$k.time)"
    done
    dag_counters $1
    if ls $dir/*.model.txt > /dev/null 2>&1; then
        echo "Unchanged model's mode (--model), $(ls $dir/*.model.txt | wc -l | tr -d ' ') traces:"
        for k in "C-A assumptions" "C-S steps"; do
            grep -h "^$k" $dir/*.model.txt | sed -E 's/.*\((.*)\)/\1/' | tr ',' '\n' \
                | awk -v k="$k" 'NF==2 {s[$1]+=$2} END {for (n in s) print "   " k ": " n " " s[n]}'
        done
    fi
}

case $SET in
    small) run_set small ${2:-10}; summary small ;;
    medium) run_set medium ${2:-3}; summary medium ;;
    large) run_set large ${2:-2}; summary large ;;
    all) run_set small ${2:-10}; summary small; run_set medium ${2:-3}; summary medium
        run_set large ${2:-2}; summary large ;;
    reclaim) run_set reclaim ${2:-5}; summary reclaim ;;
    crash) run_set crash ${2:-3}; summary crash ;;
    evict) run_set evict ${2:-3}; summary evict ;;
    drain) run_set drain ${2:-3}; summary drain ;;
    *) echo "usage: $0 [small|medium|large|all|reclaim|crash|evict|drain] [seeds [first]]"; exit 2 ;;
esac

for set_name in $RAN; do
    if grep -L "TRACECHECK OK" build/traces/$set_name$SUF/*.check.txt 2>/dev/null | grep -q .; then
        echo "CONFORMANCE FAILED"
        exit 1
    fi
    if { [ $set_name = reclaim ] || [ $set_name = crash ]; } && grep -L '^CUT ' build/traces/$set_name$SUF/*.trace | grep -q .; then
        echo "CONFORMANCE FAILED: a reclaim trace without a cut"
        exit 1
    fi
    if { [ $set_name = reclaim ] || [ $set_name = crash ]; } && grep -L '^STEP ' build/traces/$set_name$SUF/*.trace | grep -q .; then
        echo "CONFORMANCE FAILED: a reclaim trace without a STEP line"
        exit 1
    fi
    if [ $set_name = crash ] && grep -L '^RESTART crash' build/traces/$set_name$SUF/*.trace | grep -q .; then
        echo "CONFORMANCE FAILED: a crash trace without a crash"
        exit 1
    fi
    if [ $set_name = evict ] && grep -L '^SLOT ' build/traces/$set_name$SUF/*.trace | grep -q .; then
        echo "CONFORMANCE FAILED: an eviction trace without SLOT lines"
        exit 1
    fi
    if [ $set_name = evict ] && grep -L '^HANDLE ' build/traces/$set_name$SUF/*.trace | grep -q .; then
        echo "CONFORMANCE FAILED: an eviction trace without HANDLE lines"
        exit 1
    fi
    for f in build/traces/$set_name$SUF/*.check.txt; do
        [ -f $f ] || continue
        if ! grep -q '^C-A adoptions below the old parent .*: 0 of' $f; then
            echo "CONFORMANCE FAILED: a trace with an adoption below the old parent (A6), or without the count ($f)"
            exit 1
        fi
    done
    # A draining configuration must reach the merges (bergdb 024-09, step A1; until record
    # format 8 the take-back, bergdb 026-25).
    for name in $(sed -n 's/^\([^ ]*drain[^ ]*\) .*/\1/p' build/traces/$set_name$SUF/configs.txt); do
        if [ "$(joins $set_name $name)" = 0 ]; then
            echo "CONFORMANCE FAILED: the draining configuration $name of set $set_name joins no node in its seeds: its traces do not reach the merges (the Dag counters in build/traces/$set_name$SUF/$name-*.export.txt)"
            exit 1
        fi
    done
done
echo "CONFORMANCE OK"
