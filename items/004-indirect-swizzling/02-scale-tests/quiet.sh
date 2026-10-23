#!/bin/sh
# Waits until F53 is quiet enough for a timed block of 004-02 (as 004-01's run-when-quiet):
# on AC power; the block, MINUTES long, does not overlap 02:00 to 05:00 (java/night.sh
# starts at 02:10); no JVM, trace check, lake or gate other than the editor's; from 05:00
# to 22:00 no other Claude session busy (at night their tool calls are rare, and Frans's
# sessions may run unattended all evening, 2026-10-23); and the 1-minute load below
# QUIETLOAD (default 1.5); for 10 checks in a row 30 s apart. Then prints the time, the
# load and the other sessions' states.
# Usage: sh quiet.sh [OWN_SESSION_ID [MINUTES]]   (that Claude session's state is ignored;
# its id, not its pid, as the pid changes when the session restarts)
OWN=${1:-}
NEED=${2:-60}
sessions() {    # the other Claude sessions' states, as "busy idle ..."
    for f in "$HOME"/.claude/sessions/*.json; do
        [ -f "$f" ] || continue
        [ -n "$OWN" ] && grep -q "\"sessionId\":\"$OWN\"" "$f" && continue
        grep -o '"status":"[a-z]*"' "$f" | cut -d'"' -f4
    done | tr '\n' ' '
}
busy() {
    h=$(date +%H | sed 's/^0//')
    m=$(( h * 60 + $(date +%M | sed 's/^0//') ))
    if [ $m -lt 300 ] && [ $((m + NEED)) -gt 120 ]; then return 0; fi
    if [ $((m + NEED)) -gt 1560 ]; then return 0; fi
    pmset -g batt | grep -q "AC Power" || return 0
    ps -Ao args | grep -E "tracecheck|bin/java|lake |level[0-9]\.sh|before-commit|night\.sh" \
        | grep -v -E "grep|vscode|Code Helper" | grep -q . && return 0
    if [ "$h" -ge 5 ] && [ "$h" -lt 22 ]; then
        sessions | grep -q busy && return 0
    fi
    l=$(sysctl -n vm.loadavg | awk '{print $2}')
    awk -v l="$l" -v q="${QUIETLOAD:-1.5}" 'BEGIN { exit !(l >= q) }'
}
n=0
while [ $n -lt 10 ]; do
    if busy; then n=0; else n=$((n + 1)); fi
    sleep 30
done
echo "quiet at $(date): $(uptime | sed 's/.*load/load/'); other sessions: $(sessions)"
