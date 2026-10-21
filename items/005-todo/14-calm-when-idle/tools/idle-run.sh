#!/bin/sh
# 005-13, follow-up (2026-10-21): an idle JVM, and an idle database with buffer times
# 20, 50 and 100 ms, today's code (cur) and the prototype that sleeps when idle (proto).
# One process at a time: start, wait for READY, SETTLE s more, then the process counters
# (procstat) over MEASURE s, then SIGTERM (IdleProbe prints its threads' CPU). The
# reference processes REFS (pids of other programs of this user) are measured in the same
# windows, for comparison.
# Usage: idle-run.sh ROUNDS SETTLE MEASURE OUTDIR "CONFIGS" [REFS...]
#   CONFIGS: lines of "build mode bufferMs", build cur or proto.
# Expects, next to tools/, two built clones (java/build.sh): cur (the code measured) and
# proto (the same with idle-consumer.patch); IdleProbe compiled into tools/classes-cur and
# tools/classes-proto (javac -cp CLONE/java/build/bergdb.jar); procstat built (cc -O2).
# 005-14 ran: idle-run.sh 3 15 60 runs-busy "cur jvm 0 / cur db 20 / cur db 50 /
# cur db 100 / proto db 20" (one per line) 482 471 10131 2827, and 2 rounds to runs-quiet.
ROUNDS=$1; SETTLE=$2; MEASURE=$3; OUT=$4; CONFIGS=$5; shift 5; REFS="$*"
T=$(cd "$(dirname "$0")" && pwd)
D=$(dirname "$T")
JAVA=${JAVA:-/opt/homebrew/opt/openjdk/bin/java}
mkdir -p "$OUT"
r=1
while [ "$r" -le "$ROUNDS" ]; do
    echo "$CONFIGS" | while read -r build mode bt; do
        [ -n "$build" ] || continue
        name=$build-$mode-$bt-r$r
        log=$OUT/$name.log
        "$JAVA" -cp "$D/$build/java/build/bergdb.jar:$T/classes-$build" IdleProbe "$mode" "$bt" "$D/data-$name" "$SETTLE" > "$log" 2>&1 &
        pid=$!
        n=0
        while ! grep -q '^READY' "$log" 2>/dev/null; do
            sleep 0.2; n=$((n + 1)); [ $n -gt 300 ] && { echo "no READY: $name"; kill $pid; exit 1; }
        done
        sleep "$SETTLE"; sleep 1
        top -l 1 -n 5 -o cpu -stats pid,command,cpu 2>/dev/null | tail -6 > "$OUT/$name.top"
        "$T/procstat" $pid $REFS > "$OUT/$name.t0"
        date +%s > "$OUT/$name.time0"
        sleep "$MEASURE"
        "$T/procstat" $pid $REFS > "$OUT/$name.t1"
        date +%s > "$OUT/$name.time1"
        kill -TERM $pid; wait $pid 2>/dev/null
        rm -rf "$D/data-$name"
        echo "$(date +%H:%M:%S) $name done"
    done
    r=$((r + 1))
done
echo "IDLE RUN DONE"
