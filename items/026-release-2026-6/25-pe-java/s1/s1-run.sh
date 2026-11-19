#!/bin/sh
# bergdb 026-25: the runner on s1, from 030-20's s1-run.sh. Runs the JVMs of a jobs file one
# after the other, each after a quiet check: no other JVM on the machine and a 1-minute load
# under 1.0 (it waits, 30 s a check, up to 20 minutes; then it stops with exit code 2).
#
# Usage: sh s1-run.sh JOBS OUT
#   JOBS: one JVM a line, "LABEL BUILD HEAP CLASS ARGS...": BUILD main or pe (the directory
#   beside this script), CLASS CCBench or Perf (Perf's argument the mode, the -D options after
#   it are given to the JVM). Lines starting with # are skipped. The check of the writer's
#   contract is off (-Dtranscheck=0); assertions off; G1.
#   OUT: the logs, one LABEL.txt a JVM (Perf: OUT/LABEL/), and log.txt.
# Environment: JAVA (default /opt/bergdb-bench/jdk-27/bin/java). A file STOP beside this
# script stops it before the next JVM.

set -u
P=$(cd "$(dirname "$0")" && pwd)
JOBS=$1
OUT=$2
JAVA=${JAVA:-/opt/bergdb-bench/jdk-27/bin/java}
mkdir -p "$OUT"
log() { echo "$(date '+%Y-%m-%d %H:%M:%S') $*" >> "$OUT/log.txt"; }

quiet() {
    i=0
    while [ $i -lt 40 ]; do
        if [ -e "$P/STOP" ]; then log "STOP file"; exit 3; fi
        others=$(ps -eo pid,comm | awk '$2 == "java" {print $1}' | wc -l)
        load=$(cut -d' ' -f1 /proc/loadavg)
        if [ "$others" -eq 0 ] && awk "BEGIN {exit !($load < 1.0)}"; then return 0; fi
        log "not quiet: $others JVMs, load $load"
        i=$((i + 1))
        sleep 30
    done
    log "not quiet for 20 minutes: stopped"
    exit 2
}

log "start $JOBS"
grep -v '^#' "$JOBS" | grep -v '^ *$' | while read -r label build heap cls rest; do
    [ -f "$OUT/$label.done" ] && continue
    set -- $rest
    cp=$P/$build/cc:$P/$build/stress:$P/$build/bergdb.jar
    quiet
    rm -rf "$P/data"
    mkdir -p "$P/data"
    log "run $label $build heap=$heap $cls $*"
    if [ "$cls" = Perf ]; then
        mode=$1; shift
        "$JAVA" -XX:+UseG1GC -da -Xms$heap -Xmx$heap -Dtranscheck=0 "$@" \
            -Dperf.scenario=$label -Dperf.out=$OUT/$label -Dperf.dir=$P/data/perf \
            -cp "$cp" bergdb.core.Perf "$mode" > "$OUT/$label.txt" 2>&1
    else
        "$JAVA" -XX:+UseG1GC -da -Xms$heap -Xmx$heap -Dtranscheck=0 "$@" \
            -Dcc.dir=$P/data/cc -cp "$cp" bergdb.core.CCBench > "$OUT/$label.txt" 2>&1
    fi
    rc=$?
    log "done $label rc=$rc"
    [ $rc -eq 0 ] && touch "$OUT/$label.done"
    rm -rf "$P/data"
    sleep 5
done
log "end $JOBS"
