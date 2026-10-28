#!/bin/sh
# minutes: 26
# bergdb 005-64, question 4: trickle and idle on F53, the wake-ups and energy of the process at
# the buffer times 20, 50 and 100 ms, for 006-10's quiet block. After 005-14's idle-run.sh.
# Written 2026-10-28 by Claude (Opus 5.5, Claude Code).
#
# One process at a time (tools/TrickleProbe.java, on the build's jar, the JDK's default flags as
# in 005-14): a database at the buffer time, RATE small transactions a second (no sync) for
# TRICKLE_S seconds, then idle; and a JVM with no database (idle only), for comparison. The
# kernel's counters of the process (procstat, 005-14's procstat.c: proc_pid_rusage: interrupt
# wake-ups, package idle wake-ups, CPU time, the energy the kernel attributes to it) are taken
# at the start and end of a window inside each phase: trickle, from SETTLE_T s after READY for
# WIN_T s; idle, from SETTLE_I s after IDLE for WIN_I s. Two rounds, in the order 20 50 100 jvm,
# then jvm 100 50 20; about 12 minutes a round. tools/trickle-table.py makes OUT/table.md, and
# its check (every row with every cell, each window inside its phase) OUT/check.txt.
#
# Quiet: the conductor has checked the machine. The script waits up to 15 minutes for other
# BergDB processes (as run-f53.sh), then exits 2. FORCE is not used (no performance.sh).
#
# Usage: sh trickle.sh            the runs
#        SMOKE=1 sh trickle.sh    a smoke test: one round, windows of 5 and 4 s, no wait; about
#                                 a minute
# Prepared by prepare.sh (TrickleProbe's class, procstat); compiles nothing.
# Environment: CLONE (default /Users/f/fl/bench/006-10/w3), BUILD (default main-bf9fc7f),
#   OUT (default /Users/f/fl/bench/006-10/night/out/64-trickle, -smoke for SMOKE=1; an OUT
#   with earlier results is renamed OUT-HHMMSS first, SMOKE=1 removes it), RATE (default 10),
#   VALSIZE (default 100), JAVA_HOME (default /opt/homebrew/opt/openjdk).
# Writes OUT/: log.txt; per process NAME (db-BT-rR or jvm-0-rR): NAME.log (the probe's output),
#   NAME.t0, NAME.t1 (procstat, the trickle window), NAME.i0, NAME.i1 (the idle window) and
#   NAME.time-t0 and so on (epoch seconds); table.md; check.txt.
# Exit code: 0 done and every row parsed; 1 a process failed or the check failed; 2 not quiet.

set -u
START=$(date +%s)
SMOKE=${SMOKE:-0}
T=$(cd "$(dirname "$0")" && pwd)
ITEM=$(dirname "$T")
CLONE=${CLONE:-/Users/f/fl/bench/006-10/w3}
BUILD=${BUILD:-main-bf9fc7f}
JAVA_HOME=${JAVA_HOME:-/opt/homebrew/opt/openjdk}
TOOLS=$CLONE/java/build/perf/005-64-tools
JAR=$CLONE/java/build/perf/builds/$BUILD/java/build/bergdb.jar
DATA=$CLONE/java/build/perf/data
RATE=${RATE:-10}
VALSIZE=${VALSIZE:-100}
if [ "$SMOKE" = 1 ]; then
    SETTLE_T=2; WIN_T=5; SETTLE_I=2; WIN_I=4; ROUNDS=1
    OUT=${OUT:-/Users/f/fl/bench/006-10/night/out/64-trickle-smoke}
    rm -rf "$OUT"
else
    SETTLE_T=10; WIN_T=120; SETTLE_I=15; WIN_I=60; ROUNDS=2
    OUT=${OUT:-/Users/f/fl/bench/006-10/night/out/64-trickle}
    [ -d "$OUT" ] && [ -n "$(ls -A "$OUT")" ] && mv "$OUT" "$OUT-$(date +%H%M%S)"
fi
TRICKLE_S=$((SETTLE_T + WIN_T + 5))     # 5 s after the window, so that it ends inside the phase

mkdir -p "$OUT" "$DATA"
log() { echo "$(date '+%H:%M:%S') $*" | tee -a "$OUT/log.txt"; }
[ -f "$JAR" ] || { log "no build $JAR"; exit 1; }
[ -f "$TOOLS/classes/TrickleProbe.class" ] && [ -x "$TOOLS/procstat" ] || { log "no tools in $TOOLS: sh prepare.sh"; exit 1; }

others() {
    ps -axo pid,command | grep -E 'level[1-4]\.sh|night\.sh|before-commit\.sh|performance\.sh|lake build|/lake |bergdb\.(dev|core)\.|bergdb\.jar' \
        | grep -v grep || true
}
if [ "$SMOKE" != 1 ]; then
    i=0
    while [ -n "$(others)" ]; do
        if [ $i -ge 15 ]; then
            log "not quiet after 15 minutes, stopped:"
            others | cut -c1-160 | tee -a "$OUT/log.txt"
            exit 2
        fi
        [ $i = 0 ] && { log "waiting for:"; others | cut -c1-160 | tee -a "$OUT/log.txt"; }
        sleep 60
        i=$((i + 1))
    done
fi

# wait_for PATTERN LOG SECONDS PID: waits until a line of LOG starts with PATTERN; 1 if the
# process ended or SECONDS passed first.
wait_for() {
    n=0
    while ! grep -q "^$1" "$2" 2>/dev/null; do
        kill -0 "$4" 2>/dev/null || return 1
        sleep 0.2
        n=$((n + 1))
        [ $n -gt $(($3 * 5)) ] && return 1
    done
    return 0
}

# snap NAME SUFFIX PID: one snapshot of the process's counters.
snap() {
    "$TOOLS/procstat" "$3" > "$OUT/$1.$2"
    date +%s > "$OUT/$1.time-$2"
}

# one MODE BT ROUND: one process.
one() {
    name=$1-$2-r$3
    l=$OUT/$name.log
    d=$DATA/005-64-trickle-$name
    rm -rf "$d"
    "$JAVA_HOME/bin/java" -cp "$JAR:$TOOLS/classes" TrickleProbe "$1" "$2" "$d" "$TRICKLE_S" "$RATE" "$VALSIZE" > "$l" 2>&1 &
    pid=$!
    if ! wait_for READY "$l" 60 $pid; then
        log "$name: no READY"; kill $pid 2>/dev/null; wait $pid 2>/dev/null; rm -rf "$d"; return 1
    fi
    if [ "$1" = db ]; then
        sleep "$SETTLE_T"
        snap "$name" t0 $pid
        sleep "$WIN_T"
        snap "$name" t1 $pid
    fi
    if ! wait_for IDLE "$l" $((TRICKLE_S + 60)) $pid; then
        log "$name: no IDLE"; kill $pid 2>/dev/null; wait $pid 2>/dev/null; rm -rf "$d"; return 1
    fi
    sleep "$SETTLE_I"
    snap "$name" i0 $pid
    sleep "$WIN_I"
    snap "$name" i1 $pid
    kill -TERM $pid
    wait $pid 2>/dev/null
    rm -rf "$d"
    grep -q '^IDLESTAT' "$l" || { log "$name: no IDLESTAT"; return 1; }
    log "$name done"
}

log "start: $BUILD, rate $RATE a second, values of $VALSIZE bytes, trickle window ${WIN_T}s, idle window ${WIN_I}s, $ROUNDS rounds"
rc=0
r=1
while [ $r -le $ROUNDS ]; do
    if [ $((r % 2)) = 1 ]; then confs="db:20 db:50 db:100 jvm:0"; else confs="jvm:0 db:100 db:50 db:20"; fi
    for c in $confs; do
        one "${c%%:*}" "${c#*:}" $r || rc=1
    done
    r=$((r + 1))
done

python3 -I "$ITEM/tools/trickle-table.py" "$OUT" > "$OUT/table.md" 2>&1
python3 -I "$ITEM/tools/trickle-table.py" --check "$OUT" > "$OUT/check.txt" 2>&1
crc=$?
log "$(tail -n 1 "$OUT/check.txt")"
if [ $rc != 0 ] || [ $crc != 0 ]; then
    log "FAILED: a process exit $rc, check exit $crc; see log.txt and check.txt"
    exit 1
fi
log "DONE in $(( ($(date +%s) - START) / 60 )) min: $OUT/table.md"
exit 0
