#!/bin/sh
# bergdb 030-20: the runner of the commit check's cost on s1 (the Linux VPS of 007-05 and
# 005-48: 2 vCPUs, 3.8 GB). Written 2026-11-18. Runs the JVMs of a jobs file one after the
# other, each after a quiet check: no other JVM on the machine and a 1-minute load under 1.0
# (it waits, 30 s a check, up to 20 minutes; then it stops with exit code 2). Started with
# nohup by run-s1.sh beside it; needs the package that run-s1.sh copies (P below).
#
# Usage: sh s1-run.sh JOBS OUT
#   JOBS: one JVM a line, "LABEL TRANSCHECK HEAP CLASS ARGS...", TRANSCHECK 0 or 1; CLASS
#   CCBench, CCBenchTuned (CCBench with tuned/TransCheck.java's classes first on the class
#   path, P/tuned) or Perf (Perf's argument the mode, the -D options after it are given to the
#   JVM).
#   Lines starting with # are skipped. A line "jfr LABEL ..." records the JVM with JFR's
#   profile settings into OUT/LABEL.jfr.
#   OUT: the directory of the logs, one LABEL.txt a JVM, and log.txt.
# Environment: JAVA (default /opt/bergdb-bench/jdk-27/bin/java).

set -u
P=$(cd "$(dirname "$0")" && pwd)
JOBS=$1
OUT=$2
JAVA=${JAVA:-/opt/bergdb-bench/jdk-27/bin/java}
CP=$P/cc:$P/stress:$P/bergdb.jar
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
grep -v '^#' "$JOBS" | grep -v '^ *$' | while read -r first rest; do
    jfr=""
    if [ "$first" = jfr ]; then
        set -- $rest
        label=$1; shift
        jfr="-XX:StartFlightRecording=settings=profile,filename=$OUT/$label.jfr"
    else
        set -- $first $rest
        label=$1; shift
    fi
    tc=$1; heap=$2; cls=$3; shift 3
    [ -f "$OUT/$label.done" ] && continue
    cp=$CP
    if [ "$cls" = CCBenchTuned ]; then cp=$P/tuned:$CP; cls=CCBench; fi
    quiet
    rm -rf "$P/data"
    mkdir -p "$P/data"
    log "run $label transcheck=$tc heap=$heap $cls $*"
    if [ "$cls" = Perf ]; then
        mode=$1; shift
        "$JAVA" -XX:+UseG1GC -da -Xms$heap -Xmx$heap $jfr -Dtranscheck=$tc "$@" \
            -Dperf.scenario=$label -Dperf.out=$OUT/$label -Dperf.dir=$P/data/perf \
            -cp "$cp" bergdb.core.Perf "$mode" > "$OUT/$label.txt" 2>&1
    else
        "$JAVA" -XX:+UseG1GC -da -Xms$heap -Xmx$heap $jfr -Dtranscheck=$tc "$@" \
            -Dcc.dir=$P/data/cc -cp "$cp" bergdb.core.CCBench > "$OUT/$label.txt" 2>&1
    fi
    rc=$?
    log "done $label rc=$rc"
    [ $rc -eq 0 ] && touch "$OUT/$label.done"
    rm -rf "$P/data"
    sleep 5
done
log "end $JOBS"
