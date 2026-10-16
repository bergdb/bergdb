#!/bin/sh
# Level 2 conformance (docs/level2-alignment.md): runs TraceExport on a set of
# configurations, and checks each trace with the Lean checker (lean/, lake exe
# tracecheck). Written 2026-10-15 for F1-008-11, WPs C3 and F1.
#
# Usage: java/stress/conformance.sh [small|medium|all] [seeds]
#   small (default): the Lean tier on every transaction, in the target mode
#   (marking, Java's still-dirty test, the virtual root) and, for the first
#   three seeds of the first two configurations, in the unchanged model's mode
#   (--model). medium: larger runs, target mode only. seeds: per configuration
#   (default 10 small, 3 medium). The checker uses the model's list-based
#   definitions as they are; its time grows fast with the number of versions,
#   which limits the sizes here (a node size of 62 with 40-key transactions
#   takes many minutes per trace).
#
# Needs java/build (java/build.sh) and the checker (cd lean && lake build).
# Traces and checker outputs go to java/build/traces/SET/. Prints one line per
# trace, then the failing checks summed over all traces, and CONFORMANCE OK or
# CONFORMANCE FAILED. Set JAVA_HOME or PATH for the JDK.

cd "$(dirname "$0")/.."
JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi
CP=build/bergdb.jar:build/stress
SET=${1:-small}
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
}

medium() {
    echo "m-mixed -Dn=500 -Dkeys=500 -Dmaxnode=8 -Dsd=2000 -Dops=4 -Ddel=20 -Dnodel=5 -Dempty=5 -Dprobe=50"
    echo "m-long  -Dn=500 -Dkeys=3000 -Dmaxnode=30 -Dsd=5000 -Dops=8 -Dlong=1 -Ddel=20 -Dprobe=100"
    echo "m-big   -Dn=120 -Dkeys=1000 -Dmaxnode=30 -Dsd=10000 -Dops=20 -Dbulk=60 -Dprobe=30"
}

run_set() {
    set_name=$1
    seeds=$2
    dir=build/traces/$set_name
    mkdir -p $dir
    find $dir -type f -delete
    $set_name > $dir/configs.txt
    while read name props; do
        s=1
        while [ $s -le $seeds ]; do
            t=$dir/$name-$s.trace
            $JAVA -ea $props -cp $CP bergdb.core.TraceExport $s $t > $dir/$name-$s.export.txt 2>&1 \
                || echo "TraceExport failed: $(tail -1 $dir/$name-$s.export.txt)" > $dir/$name-$s.check.txt
            if [ -f $t ]; then
                "$CHECK" $t > $dir/$name-$s.check.txt 2>&1
                if [ $set_name = small ] && [ $s -le 3 ] && { [ $name = mixed ] || [ $name = long ]; }; then
                    "$CHECK" $t --model > $dir/$name-$s.model.txt 2>&1
                fi
            fi
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
    echo "   C-R: $(grep -h '^C-R' $dir/*.check.txt | awk '{s+=$3} END {print s+0}') failed probes; kinds:"
    grep -h '^  PROBE' $dir/*.check.txt | sed -E 's/[0-9]+/N/g' | sort | uniq -c | sed 's/^/      /'
    echo "   exporter errors: $(grep -h '^exporter errors' $dir/*.check.txt | awk '{s+=$3} END {print s+0}')"
    echo "   traces: $(ls $dir/*.check.txt | wc -l | tr -d ' '), TRACECHECK OK: $(grep -l 'TRACECHECK OK' $dir/*.check.txt | wc -l | tr -d ' ')"
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
    all) run_set small ${2:-10}; summary small; run_set medium ${2:-3}; summary medium ;;
    *) echo "usage: $0 [small|medium|all] [seeds]"; exit 2 ;;
esac

if grep -L "TRACECHECK OK" build/traces/*/*.check.txt 2>/dev/null | grep -q .; then
    echo "CONFORMANCE FAILED"
    exit 1
fi
echo "CONFORMANCE OK"
