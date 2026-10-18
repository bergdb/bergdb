#!/bin/sh
# Level 2 conformance (docs/level2-alignment.md): runs TraceExport on a set of
# configurations, and checks each trace with the Lean checker (lean/, lake exe
# tracecheck). Written 2026-10-15 for F1-008-11, WPs C3 and F1.
#
# Usage: java/stress/conformance.sh [small|medium|large|all|reclaim|evict] [seeds]
#   small (default): the Lean tier on every transaction, in the target mode
#   (marking, Java's still-dirty test, the virtual root) and, for the first
#   three seeds of the first two configurations, in the unchanged model's mode
#   (--model). medium: larger runs, target mode only. large (2026-10-16, bergdb
#   item 001, WP C3): up to 5,000 transactions, node sizes 8 to 62, up to 3,000
#   keys, and runs with hundreds of top nodes. all: the three. reclaim
#   (2026-10-17, bergdb item 001, K3): Level 3, the small reclaim set of
#   reclaimtraces.sh, reclaim on, with the checker's reclaim checks (the touch,
#   the steps on the cut stream, CutOK at every cut, the probes after restarts
#   from the cut stream); a trace without a cut fails. evict (2026-10-18, bergdb
#   item 001, WP J4): Level 4, configurations of the small, medium and reclaim
#   sets with run E (TraceExport's rune: run A's workload with a forced eviction
#   schedule), whose stream must be run A's, and whose slots (SLOT lines) the
#   checker's C-P checks against the model's INV-SLOT; a trace without SLOT lines
#   fails. seeds: per configuration (default 10 small, 3 medium, 2 large, 5
#   reclaim, 3 evict). The checker computes
#   the model's own definitions, with fast versions proven equal to them
#   (lean/Check/Fast.lean, since bergdb item 001, WP C2).
#
# PAR=N runs N traces at once (default 4), each an export and its check.
#
# Needs java/build (java/build.sh) and the checker (cd lean && lake build).
# Traces and checker outputs go to java/build/traces/SET/. Prints one line per
# trace, then the failing checks summed over all traces, the time and memory of
# the runs, and CONFORMANCE OK or CONFORMANCE FAILED for the sets run. Set
# JAVA_HOME or PATH for the JDK.

cd "$(dirname "$0")/.."
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
}

evict() {
    # Run E with the random schedule (each slot to a detachable object with probability
    # 0.3, seeded by the trace's seed), every and values; SLOT lines after every
    # transaction (every fifth in e-m-mixed).
    echo "e-mixed   -Dn=60 -Dkeys=20 -Dmaxnode=8 -Dsd=200 -Dops=4 -Ddel=25 -Dnodel=10 -Dempty=10 -Dprobe=1 -Drune=random"
    echo "e-long    -Dn=60 -Dkeys=50 -Dmaxnode=14 -Dsd=500 -Dops=4 -Dlong=1 -Ddel=25 -Dprobe=10 -Drune=random"
    echo "e-every   -Dn=60 -Dkeys=50 -Dmaxnode=8 -Dsd=500 -Dops=4 -Ddel=25 -Dprobe=10 -Drune=every"
    echo "e-values  -Dn=60 -Dkeys=50 -Dmaxnode=8 -Dsd=500 -Dops=4 -Ddel=25 -Dprobe=10 -Drune=values"
    echo "e-hot     -Dn=300 -Dkeys=1 -Dmaxnode=8 -Dsd=200 -Dops=1 -Dprobe=30 -Drune=random"
    echo "e-m-mixed -Dn=500 -Dkeys=500 -Dmaxnode=8 -Dsd=2000 -Dops=4 -Ddel=20 -Dnodel=5 -Dempty=5 -Dprobe=50 -Drune=random -Dslotevery=5"
    echo "e-r-small -Dn=300 -Dkeys=30 -Dmaxnode=8 -Dsd=200 -Dops=4 -Dretain=1 -Dprobe=10 -Drune=random"
    echo "e-r-long  -Dn=500 -Dkeys=100 -Dmaxnode=14 -Dsd=500 -Dops=4 -Dlong=1 -Ddel=25 -Dretain=2 -Dprobe=10 -Drune=random"
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
    dir=build/traces/$set_name
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
    dir=build/traces/$set_name
    RAN="$RAN $set_name"
    mkdir -p $dir
    find $dir -type f -delete
    $set_name > $dir/configs.txt
    # PAR traces at once, in batches.
    running=0
    while read name props; do
        s=1
        while [ $s -le $seeds ]; do
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
    while read name props; do
        s=1
        while [ $s -le $seeds ]; do
            echo "   $name-$s: $(tail -1 $dir/$name-$s.check.txt)"
            s=$((s + 1))
        done
    done < $dir/configs.txt
}

summary() {
    dir=build/traces/$1
    echo "Summed over the traces of $1, target mode: transactions failing, by check"
    for k in "C-A assumptions" "C-S steps" "diagnostics"; do
        grep -h "^$k" $dir/*.check.txt | sed -E 's/.*\((.*)\)/\1/' | tr ',' '\n' \
            | awk -v k="$k" 'NF==2 {s[$1]+=$2} END {for (n in s) print "   " k ": " n " " s[n]}'
    done
    echo "   C-V: $(grep -h '^C-V' $dir/*.check.txt | awk '{s+=$3} END {print s+0}') transactions with live differences, $(grep -h '^C-V' $dir/*.check.txt | awk '{s+=$7} END {print s+0}') LIVE lines"
    if [ $1 = reclaim ]; then
        echo "   C-CUT: $(grep -h '^C-CUT cuts' $dir/*.check.txt | awk '{f+=$3; n+=$5} END {print f+0 " of " n+0}') CUT lines fail; traces without a cut: $(grep -L '^CUT ' $dir/*.trace | wc -l | tr -d ' ')"
    fi
    if [ $1 = evict ]; then
        echo "   C-P: $(grep -h '^C-P slots' $dir/*.check.txt | sed -E 's/.*: ([0-9]+) of ([0-9]+) transactions fail; ([0-9]+) SLOT lines, ([0-9]+) checked.*/\1 \2 \3 \4/' | awk '{f+=$1; t+=$2; n+=$3; c+=$4} END {print f+0 " of " t+0 " transactions fail; " n+0 " SLOT lines, " c+0 " checked"}'); traces without SLOT lines: $(grep -L '^SLOT ' $dir/*.trace | wc -l | tr -d ' ')"
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
    evict) run_set evict ${2:-3}; summary evict ;;
    *) echo "usage: $0 [small|medium|large|all|reclaim|evict] [seeds]"; exit 2 ;;
esac

for set_name in $RAN; do
    if grep -L "TRACECHECK OK" build/traces/$set_name/*.check.txt 2>/dev/null | grep -q .; then
        echo "CONFORMANCE FAILED"
        exit 1
    fi
    if [ $set_name = reclaim ] && grep -L '^CUT ' build/traces/$set_name/*.trace | grep -q .; then
        echo "CONFORMANCE FAILED: a reclaim trace without a cut"
        exit 1
    fi
    if [ $set_name = evict ] && grep -L '^SLOT ' build/traces/$set_name/*.trace | grep -q .; then
        echo "CONFORMANCE FAILED: an eviction trace without SLOT lines"
        exit 1
    fi
done
echo "CONFORMANCE OK"
