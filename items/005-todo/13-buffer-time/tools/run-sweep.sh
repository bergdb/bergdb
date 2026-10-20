#!/bin/sh
# 005-13: the buffer time sweep. Waits until the machine is quiet (no gate, night or
# performance run of another session, 90 % idle CPU), then the force probe, ROUNDS rounds of
# java/stress/performance-bufftime.suite with one run each (every buffer time in every round),
# and the force probe again. Copies the results to OUT (default: ../runs).
# Usage: tools/run-sweep.sh [ROUNDS] [FIRST]   (from a clone of the repo; JAVA_HOME as for performance.sh)
# FIRST is the number of the first round (default 1). QUIET=0: do not wait for a quiet machine;
# the runs are made with FORCE=1, and what else runs is logged.

ROUNDS=${1:-3}
FIRST=${2:-1}
QUIET=${QUIET:-1}
T=$(cd "$(dirname "$0")" && pwd)
ITEM=$(dirname "$T")
ROOT=$(cd "$ITEM/../../.." && pwd)
OUT=${OUT:-$ITEM/runs}
JAVA_HOME=${JAVA_HOME:-/opt/homebrew/opt/openjdk}
export JAVA_HOME
mkdir -p "$OUT"
log() { echo "$(date '+%H:%M:%S') $*" | tee -a "$OUT/sweep.log"; }

others() {
    ps -axo pid,command | grep -E 'level[1-4]\.sh|nightly\.sh|night\.sh|before-commit\.sh|performance\.sh|/lake |bergdb\.dev\.(Unit|F|Night)' \
        | grep -v grep | grep -v "$ROOT" || true
}
idle() { top -l 2 -n 0 -s 2 | grep "CPU usage" | tail -1 | sed -e 's/.* \([0-9.]*\)% idle.*/\1/'; }
wait_quiet() {
    if [ "$QUIET" = 0 ]; then
        log "not waiting (QUIET=0): $(idle) % idle; $(others | cut -c1-150 | tr '\n' ' ')"
        return
    fi
    while :; do
        o=$(others)
        i=$(idle)
        if [ -z "$o" ] && awk "BEGIN { exit !($i >= 90) }"; then
            log "quiet ($i % idle)"; return
        fi
        log "waiting: $i % idle; $(echo "$o" | head -2 | cut -c1-120 | tr '\n' ' ')"
        sleep 60
    done
}

probe() {
    wait_quiet
    d=$ROOT/java/build/perf/forceprobe
    rm -rf "$d"
    log "force probe $1"
    "$JAVA_HOME/bin/java" -cp "$ROOT/java/build/bergdb.jar:$T/classes" ForceProbe "$d" 200 > "$OUT/forceprobe-$1-quiet$QUIET.txt" 2>&1
    rm -rf "$d"
    cat "$OUT/forceprobe-$1-quiet$QUIET.txt" >> "$OUT/sweep.log"
}

log "sweep start, rounds $FIRST to $((FIRST + ROUNDS - 1)), QUIET=$QUIET, $(git -C "$ROOT" rev-parse --short HEAD)"
probe "$FIRST"
r=$FIRST
while [ $r -lt $((FIRST + ROUNDS)) ]; do
    wait_quiet
    log "round $r"
    (cd "$ROOT/java" && RUNS=1 FORCE=$([ "$QUIET" = 0 ] && echo 1 || echo 0) SUITE=stress/performance-bufftime.suite sh stress/performance.sh reference "round$r") \
        > "$OUT/round$r.txt" 2>&1
    rc=$?
    log "round $r exit $rc: $(tail -1 "$OUT/round$r.txt")"
    if grep -q 'machine is not quiet' "$OUT/round$r.txt"; then sleep 60; continue; fi
    [ $rc = 0 ] || exit 1
    s=$(sed -n 's/^PERFORMANCE RUN DONE: \(.*\) (summary.*/\1/p' "$OUT/round$r.txt")
    mkdir -p "$OUT/round$r"
    cp "$s/summary.txt" "$s/session.json" "$s/machine.txt" "$OUT/round$r/" 2>/dev/null
    (cd "$s" && find . -name 'write.result.json' -o -name 'write.stdout.txt' -o -name 'load-*.txt') | while read -r f; do
        mkdir -p "$OUT/round$r/$(dirname "$f")"; cp "$s/$f" "$OUT/round$r/$f"
    done
    r=$((r + 1))
done
probe "$r"
log "SWEEP DONE"
