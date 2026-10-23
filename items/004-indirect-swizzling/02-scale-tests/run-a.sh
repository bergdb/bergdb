#!/bin/sh
# Part A of 004-02 (bergdb item 004): 004-01's IndirectionBench and IndexCensus, unchanged
# (compiled from ../01-report/), with heaps that fit a machine of 4 GB.
# Usage: sh run-a.sh OUTDIR BERGDB_JAR
# Environment: HEAP_BENCH (default 2g), HEAP_CENSUS (default 2600m), THREADS (the
# benchmark's reader threads, default "1 2 4"), CENSUS_THREADS (default 2), SIZES (default
# "20000 8000000"), CENSUS (0: no IndexCensus runs). Needs JAVA_HOME, or java and javac on
# the PATH. On Linux, a line after
# each JVM's output gives the steal time during it (/proc/stat). Writes DONE to OUTDIR/done.
set -e
OUT=$1
JAR=$2
HERE=$(cd "$(dirname "$0")" && pwd)
SRC=$HERE/../01-report
HB=${HEAP_BENCH:-2g}
HC=${HEAP_CENSUS:-2600m}
THREADS=${THREADS:-"1 2 4"}
CT=${CENSUS_THREADS:-2}
SIZES=${SIZES:-"20000 8000000"}
JAVA=${JAVA_HOME:+$JAVA_HOME/bin/}java
JAVAC=${JAVA_HOME:+$JAVA_HOME/bin/}javac
mkdir -p "$OUT/classes"
rm -f "$OUT/done"
"$JAVAC" -d "$OUT/classes" "$SRC/IndirectionBench.java"
"$JAVAC" -nowarn -cp "$JAR" -d "$OUT/classes" "$SRC/IndexCensus.java"

cpu() {
    if [ -r /proc/stat ]; then head -n 1 /proc/stat; else echo "cpu 0 0 0 0 0 0 0 0"; fi
}
steal() {   # the steal time between two cpu lines of /proc/stat
    echo "$1|$2" | awk -F'|' '{ split($1, a, " "); split($2, b, " "); t = 0;
        for (i = 2; i <= 9; i++) t += b[i] - a[i];
        printf "# steal %.2f%% of %d ticks; load %s\n", t ? 100 * (b[9] - a[9]) / t : 0, t, LOAD }' \
        LOAD="$(cut -d' ' -f1-3 /proc/loadavg 2>/dev/null)"
}
run() {     # run LOG JAVA-ARGUMENTS...
    log=$1
    shift
    c0=$(cpu)
    "$JAVA" "$@" >> "$log" 2>&1
    steal "$c0" "$(cpu)" >> "$log"
}

for t in $THREADS; do
    LOG="$OUT/bench-t$t.txt"
    "$JAVA" -version 2>&1 | head -n 1 > "$LOG"
    echo "# $(uname -sm), $(hostname), heap $HB, started $(date)" >> "$LOG"
    for n in $SIZES; do
        for v in direct lockstamp lock stamp handle handleacq handleclock hash chm; do
            run "$LOG" -Xms$HB -Xmx$HB -cp "$OUT/classes" IndirectionBench $v $n $t before
        done
        for layout in child parent scattered; do
            run "$LOG" -Xms$HB -Xmx$HB -cp "$OUT/classes" IndirectionBench handleacq $n $t $layout
        done
    done
done
[ "${CENSUS:-1}" = 1 ] && for kt in int4 pre16 rnd16; do
    LOG="$OUT/census-$kt.txt"
    echo "# $(uname -sm), $(hostname), heap $HC, threads $CT, started $(date)" > "$LOG"
    run "$LOG" -Xms$HC -Xmx$HC -Dkeys=1000000 -Dkeytype=$kt -Dvalsize=8 -Dthreads=$CT \
        -cp "$JAR:$OUT/classes" bergdb.core.IndexCensus
done
echo "finished $(date)" >> "$OUT/bench-t$(echo $THREADS | cut -d' ' -f1).txt"
echo DONE > "$OUT/done"
