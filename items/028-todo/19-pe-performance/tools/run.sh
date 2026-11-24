#!/bin/sh
# bergdb 028-19: 026-25's perf2/f53-run.sh for this night. Runs the JVMs of a jobs file one after
# the other. QUIET=1 (timing): before each JVM, no other JVM on the machine and the CPU at least
# MINIDLE % idle over 2 s (default 85; the editor's idle JVM under ~/.vscode not counted); it waits, 10 s a check, up to 20 minutes, then stops with
# exit code 2. QUIET=0 (counts): no check, the JVM at nice 10.
#
# Usage: sh run.sh JOBS OUT
#   JOBS: one JVM a line, "LABEL BUILD HEAP Perf MODE ARGS...": BUILD a clone in $BUILDS, built.
#   OUT: one LABEL.txt a JVM, its result in OUT/LABEL/, its GC log LABEL.gc.log, and log.txt.
# Environment: BUILDS (default the directory above this one), JAVA (default
# /opt/homebrew/opt/openjdk/bin/java), DATA (the data directory's parent, default $OUT). A file
# STOP in OUT, or /Users/f/fl/bench/lead/2026-11-24/STOP, stops it before the next JVM.

set -u
JOBS=$1
OUT=$2
BUILDS=${BUILDS:-$(cd "$(dirname "$0")/.." && pwd)}
JAVA=${JAVA:-/opt/homebrew/opt/openjdk/bin/java}
QUIET=${QUIET:-1}
mkdir -p "$OUT"
P=${DATA:-$OUT}
log() { echo "$(date '+%Y-%m-%d %H:%M:%S') $*" >> "$OUT/log.txt"; }
stopped() { [ -e "$OUT/STOP" ] || [ -e /Users/f/fl/bench/lead/2026-11-24/STOP ]; }

quiet() {
    i=0
    while [ $i -lt 120 ]; do
        if stopped; then log "STOP file"; exit 3; fi
        others=$(ps -Ao comm | grep '/java$' | grep -vc '/\.vscode/')   # not the editor's idle JVM
        idle=$(top -l 2 -n 0 -s 2 | grep 'CPU usage' | tail -1 | sed 's/.*sys, *\([0-9.]*\)% idle.*/\1/')
        load=$(sysctl -n vm.loadavg | awk '{print $2}')
        if [ "$others" -eq 0 ] && awk "BEGIN {exit !($idle >= ${MINIDLE:-85})}"; then log "quiet: idle $idle %, load $load"; return 0; fi
        log "not quiet: $others JVMs, idle $idle %, load $load"
        i=$((i + 1))
        sleep 10
    done
    log "not quiet for 20 minutes: stopped"
    exit 2
}

log "start $JOBS QUIET=$QUIET"
grep -v '^#' "$JOBS" | grep -v '^ *$' | while read -r label build heap cls rest; do
    [ -f "$OUT/$label.done" ] && continue
    set -- $rest
    B=$BUILDS/$build/java/build
    cp=$B/stress:$B/bergdb.jar
    if [ "$QUIET" = 1 ]; then quiet; NICE=""; else
        if stopped; then log "STOP file"; exit 3; fi
        NICE="nice -n 10"
        log "counts: load $(sysctl -n vm.loadavg | awk '{print $2}')"
    fi
    rm -rf "$P/data"
    mkdir -p "$P/data"
    log "run $label $build heap=$heap $cls $*"
    mode=$1; shift
    $NICE "$JAVA" -XX:+UseG1GC -da -Xms$heap -Xmx$heap -Dtranscheck=0 \
        -Xlog:gc:file=$OUT/$label.gc.log:uptime "$@" \
        -Dperf.scenario=$label -Dperf.out=$OUT/$label -Dperf.dir=$P/data/perf \
        -cp "$cp" bergdb.core.Perf "$mode" > "$OUT/$label.txt" 2>&1
    rc=$?
    log "done $label rc=$rc"
    [ $rc -eq 0 ] && touch "$OUT/$label.done"
    rm -rf "$P/data"
    sleep 5
done
log "end $JOBS"
