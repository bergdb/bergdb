#!/bin/sh
# Waits until F53 is quiet enough for a timed block of 004-02 (as 004-01's run-when-quiet):
# on AC power, not between 02:00 and 05:00 (java/night.sh starts at 02:10), no JVM, trace
# check, lake or gate other than the editor's, no other Claude session busy, and the
# 1-minute load below QUIETLOAD (default 1.5), for 10 checks in a row 30 s apart.
# Usage: sh quiet.sh [OWN_SESSION_ID]   (that Claude session's busy state is ignored; its id,
# not its pid, as the pid changes when the session restarts)
OWN=${1:-}
busy() {
    h=$(date +%H)
    [ "$h" -ge 2 ] && [ "$h" -lt 5 ] && return 0
    pmset -g batt | grep -q "AC Power" || return 0
    ps -Ao args | grep -E "tracecheck|bin/java|lake |level[0-9]\.sh|before-commit|night\.sh" \
        | grep -v -E "grep|vscode|Code Helper" | grep -q . && return 0
    for f in "$HOME"/.claude/sessions/*.json; do
        [ -f "$f" ] || continue
        [ -n "$OWN" ] && grep -q "\"sessionId\":\"$OWN\"" "$f" && continue
        grep -q '"status":"busy"' "$f" && return 0
    done
    l=$(sysctl -n vm.loadavg | awk '{print $2}')
    awk -v l="$l" -v q="${QUIETLOAD:-1.5}" 'BEGIN { exit !(l >= q) }'
}
n=0
while [ $n -lt 10 ]; do
    if busy; then n=0; else n=$((n + 1)); fi
    sleep 30
done
echo "quiet at $(date): $(uptime)"
