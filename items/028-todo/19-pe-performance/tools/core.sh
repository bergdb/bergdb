#!/bin/sh
# bergdb 028-19: level 1's CORE (bergdb.dev.props.Core verbose: get, get4t, getmany, set), one
# JVM a run, as 026-25 perf2's core-f53.sh, for the builds given in the order given (ABBA by the
# caller), each after run.sh's quiet check. Usage: sh core.sh OUT LABEL...  (LABEL BUILD-x: the
# clone BUILD in the directory above tools/). A file STOP in OUT, or the lead's STOP file, stops it.
set -u
OUT=$1; shift
D=$(cd "$(dirname "$0")/.." && pwd)
JAVA=${JAVA:-/opt/homebrew/opt/openjdk/bin/java}
mkdir -p "$OUT"
log() { echo "$(date '+%Y-%m-%d %H:%M:%S') $*" >> "$OUT/log.txt"; }
quiet() {
    i=0
    while [ $i -lt 120 ]; do
        if [ -e "$OUT/STOP" ] || [ -e /Users/f/fl/bench/lead/2026-11-24/STOP ]; then log "STOP file"; exit 3; fi
        others=$(ps -Ao comm | grep '/java$' | grep -vc '/\.vscode/')
        idle=$(top -l 2 -n 0 -s 2 | grep 'CPU usage' | tail -1 | sed 's/.*sys, *\([0-9.]*\)% idle.*/\1/')
        load=$(sysctl -n vm.loadavg | awk '{print $2}')
        if [ "$others" -eq 0 ] && awk "BEGIN {exit !($idle >= ${MINIDLE:-85})}"; then log "quiet: idle $idle %, load $load"; return 0; fi
        log "not quiet: $others JVMs, idle $idle %, load $load"
        i=$((i + 1)); sleep 10
    done
    log "not quiet for 20 minutes: stopped"; exit 2
}
for lab in "$@"; do
    b=${lab%%-*}
    quiet
    (cd "$D/$b/java" && "$JAVA" -cp build/bergdb.jar bergdb.dev.props.Core verbose) > "$OUT/$lab.txt" 2>&1
    log "$lab $(grep -o 'CORE:[0-9.]* ([^)]*)' "$OUT/$lab.txt")"
done
