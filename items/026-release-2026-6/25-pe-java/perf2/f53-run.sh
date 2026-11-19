#!/bin/sh
# bergdb 026-25, perf2: s1-run.sh for F53 (macOS). Runs the JVMs of a jobs file one after the
# other, each after a quiet check: no other JVM on the machine and the CPU at least MINIDLE %
# idle over 2 s (default 85) (it waits, 10 s a check, up to 20 minutes; then it stops with exit code 2); the idle
# figure and the load go to log.txt.
#
# Usage: sh f53-run.sh JOBS OUT
#   JOBS: one JVM a line, "LABEL BUILD HEAP CLASS ARGS...": BUILD main or pe (the clone
#   $BUILDS/BUILD, its java/ built and CCBench compiled into java/build/cc by run-s1.sh
#   copy), CLASS CCBench or Perf (Perf's argument the mode, the -D options after
#   it are given to the JVM). Lines starting with # are skipped. The check of the writer's
#   contract is off (-Dtranscheck=0); assertions off; G1.
#   OUT: the logs, one LABEL.txt a JVM (Perf: OUT/LABEL/), and log.txt.
# Environment: BUILDS (required), JAVA (default /opt/homebrew/opt/openjdk/bin/java), DATA (the
# data directory's parent, default $OUT). A file STOP in OUT, or /Users/f/fl/bench/2026-11-18/STOP,
# stops it before the next JVM.

set -u
JOBS=$1
OUT=$2
BUILDS=${BUILDS:?BUILDS: the directory of the clones main and pe}
JAVA=${JAVA:-/opt/homebrew/opt/openjdk/bin/java}
mkdir -p "$OUT"
P=${DATA:-$OUT}
log() { echo "$(date '+%Y-%m-%d %H:%M:%S') $*" >> "$OUT/log.txt"; }

quiet() {
    i=0
    while [ $i -lt 40 ]; do
        if [ -e "$OUT/STOP" ] || [ -e /Users/f/fl/bench/2026-11-18/STOP ]; then log "STOP file"; exit 3; fi
        others=$(ps -Ao comm | grep -c '/java$')
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

log "start $JOBS"
grep -v '^#' "$JOBS" | grep -v '^ *$' | while read -r label build heap cls rest; do
    [ -f "$OUT/$label.done" ] && continue
    set -- $rest
    B=$BUILDS/$build/java/build
    cp=$B/cc:$B/stress:$B/bergdb.jar
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
