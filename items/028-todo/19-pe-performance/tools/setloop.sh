#!/bin/sh
# bergdb 028-19: SetLoop (026-25's perf2/setloop: the set test of Props CORE, N runs in one JVM)
# on jars in setloop/jars/, in the order given (ABBA by the caller), each JVM after the quiet
# check of run.sh (no other JVM but the editor's, the CPU at least MINIDLE % idle over 2 s).
# Usage: sh setloop.sh OUT N JAR...   (JAR: a name in setloop/jars without .jar; a label
# NAME-x runs jars/NAME.jar). A file STOP in OUT, or the lead's STOP file, stops it.
set -u
OUT=$1; N=$2; shift 2
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
    jar=${lab%%-*}
    quiet
    "$JAVA" -cp "$D/setloop/cls-main:$D/setloop/jars/$jar.jar" SetLoop "$N" > "$OUT/$lab.txt" 2>&1
    log "$lab $(tail -1 "$OUT/$lab.txt")"
done
