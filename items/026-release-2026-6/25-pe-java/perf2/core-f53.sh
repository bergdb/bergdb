#!/bin/sh
# bergdb 026-25, perf2: level 1's CORE (bergdb.dev.props.Core: get, get4t, getmany, set) on
# F53, main and PE alternating in ABBA order, ROUNDS rounds (default 3: 6 runs each). Written
# 2026-11-19. Before each run: the CPU at least MINIDLE % idle over 2 s (default 85; it waits),
# noted in the output with the load and the top processes (macOS's load average counts threads
# waiting for I/O and lags; Spotlight's indexing of new clones held it near 13 with 80 % idle).
# Each run is one JVM, as level1.sh runs it.
#
# Usage: sh core-f53.sh OUT     (OUT: one file a run, and log.txt)
# Environment: MAIN, PE (clones with java/build.sh run), JAVA_HOME, ROUNDS, MINIDLE.
# A file STOP in OUT, or /Users/f/fl/bench/2026-11-18/STOP, stops it before the next run.
set -u
OUT=$1
MAIN=${MAIN:?}; PE=${PE:?}
JAVA=${JAVA_HOME:-/opt/homebrew/opt/openjdk}/bin/java
ROUNDS=${ROUNDS:-3}; MINIDLE=${MINIDLE:-85}
mkdir -p "$OUT"
idle() { top -l 2 -n 0 -s 2 | grep 'CPU usage' | tail -1 | sed 's/.*sys, *\([0-9.]*\)% idle.*/\1/'; }
run() {  # LABEL BUILD
    while true; do
        I=$(idle)
        awk -v i="$I" -v m=$MINIDLE 'BEGIN { exit !(i >= m) }' && break
        sleep 5
    done
    if [ -e "$OUT/STOP" ] || [ -e /Users/f/fl/bench/2026-11-18/STOP ]; then exit 3; fi
    if [ $2 = main ]; then J=$MAIN/java; else J=$PE/java; fi
    { echo "# $(date '+%H:%M:%S') idle $I %, $(uptime)"; ps -Ao pcpu,comm -r | sed -n 2,4p | sed 's/^/# /'; } > "$OUT/$1.txt"
    (cd "$J" && "$JAVA" -cp build/bergdb.jar bergdb.dev.props.Core verbose) >> "$OUT/$1.txt" 2>&1
    echo "$(date '+%H:%M:%S') $1 $(grep -o 'CORE:[0-9.]* ([^)]*)' "$OUT/$1.txt")" >> "$OUT/log.txt"
}
i=1
while [ $i -le $ROUNDS ]; do
    run core-main-r${i}a main; run core-pe-r${i}b pe; run core-pe-r${i}c pe; run core-main-r${i}d main
    i=$((i + 1))
done
