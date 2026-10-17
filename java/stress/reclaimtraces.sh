#!/bin/sh
# Traces of reclaim runs (bergdb item 001, WP R2): runs TraceExport with reclaim
# on (retain=S) on a set of configurations, and reports the exporter's own
# checks: no ERROR line (every touched node an index node of P, every stored
# position the start of a version, the physical cut at or below the decided
# one, Java's first available time the table's), no failing PROBE in run B
# (restarts every ten transactions and right after each cut, lookups from the
# first available time on, the streams the same from the cut), and at least one
# cut decided in each trace. The checker (lean/) reads these traces from R3 on.
#
# Usage: java/stress/reclaimtraces.sh [small|medium] [seeds]
#   small (default): the plan's 8.4, reclaim small; seeds per configuration,
#   default 5. medium: larger runs, default 2 seeds.
#
# PAR=N runs N exports at once (default 4). Needs java/build (java/build.sh).
# Traces and outputs go to java/build/traces/reclaim-SET/. Prints one line per
# trace, then RECLAIM TRACES OK or RECLAIM TRACES FAILED. Set JAVA_HOME or PATH
# for the JDK.

cd "$(dirname "$0")/.."
JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi
CP=build/bergdb.jar:build/stress
SET=${1:-small}
PAR=${PAR:-4}

small() {
    # name and TraceExport properties; retain is in seconds of the scaled clock
    echo "r-small -Dn=300 -Dkeys=30 -Dmaxnode=8 -Dsd=200 -Dops=4 -Dretain=1 -Dprobe=10"
    echo "r-del   -Dn=500 -Dkeys=100 -Dmaxnode=8 -Dsd=500 -Dops=4 -Ddel=25 -Dnodel=5 -Dempty=5 -Dretain=1 -Dprobe=10"
    echo "r-long  -Dn=500 -Dkeys=100 -Dmaxnode=14 -Dsd=500 -Dops=4 -Dlong=1 -Ddel=25 -Dretain=2 -Dprobe=10"
    echo "r-big   -Dn=800 -Dkeys=200 -Dmaxnode=14 -Dsd=1000 -Dops=8 -Ddel=25 -Dretain=2 -Dprobe=10"
    echo "r-idle  -Dn=400 -Dkeys=50 -Dmaxnode=8 -Dsd=300 -Dops=2 -Dempty=20 -Dnodel=10 -Dretain=1 -Dprobe=10"
}

medium() {
    echo "rm-mixed -Dn=2000 -Dkeys=500 -Dmaxnode=8 -Dsd=2000 -Dops=4 -Ddel=20 -Dnodel=5 -Dempty=5 -Dretain=2 -Dprobe=100"
    echo "rm-long  -Dn=3000 -Dkeys=3000 -Dmaxnode=30 -Dsd=5000 -Dops=8 -Dlong=1 -Ddel=20 -Dretain=2 -Dprobe=200"
    echo "rm-5000  -Dn=5000 -Dkeys=1000 -Dmaxnode=14 -Dsd=3000 -Dops=4 -Ddel=20 -Dretain=2 -Dprobe=500"
}

case $SET in
    small) SEEDS=${2:-5} ;;
    medium) SEEDS=${2:-2} ;;
    *) echo "Usage: reclaimtraces.sh [small|medium] [seeds]"; exit 2 ;;
esac

dir=build/traces/reclaim-$SET
mkdir -p $dir
rm -f $dir/*.trace $dir/*.export.txt
start=$(date +%s)

# One export.
one() {
    name=$1; s=$2; props=$3
    $JAVA -ea $props -cp $CP bergdb.core.TraceExport $s $dir/$name-$s.trace \
        > $dir/$name-$s.export.txt 2>&1 \
        || echo "TraceExport failed" >> $dir/$name-$s.export.txt
}

jobs=0
$SET | while read name props; do
    s=1
    while [ $s -le $SEEDS ]; do
        echo "$name $s $props"
        s=$((s + 1))
    done
done > $dir/runs.txt

while read name s props; do
    one $name $s "$props" &
    jobs=$((jobs + 1))
    if [ $jobs -ge $PAR ]; then
        wait
        jobs=0
    fi
done < $dir/runs.txt
wait

bad=0
while read name s props; do
    out=$dir/$name-$s.export.txt
    line=$(grep '^TraceExport seed=' $out | sed "s| $dir/.*||")
    errs=$(grep -c '^ERROR' $dir/$name-$s.trace 2> /dev/null)
    [ -z "$errs" ] && errs=1        # no trace
    fails=$(grep '^PROBE' $dir/$name-$s.trace 2> /dev/null | grep -c ' fail ')
    cuts=$(grep -c '^CUT ' $dir/$name-$s.trace 2> /dev/null)
    [ -z "$cuts" ] && cuts=0
    ok=ok
    if [ -z "$line" ] || [ "$errs" != 0 ] || [ "$fails" != 0 ] || [ "$cuts" = 0 ]; then
        ok=FAILED
        bad=$((bad + 1))
    fi
    echo "$name-$s $ok: ${line:-$(tail -1 $out)}"
done < $dir/runs.txt

echo "   traces: $(wc -l < $dir/runs.txt | tr -d ' '), failing: $bad, $(( $(date +%s) - start )) s"
if [ $bad = 0 ]; then
    echo "RECLAIM TRACES OK"
else
    echo "RECLAIM TRACES FAILED"
    exit 1
fi
