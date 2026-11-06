#!/bin/sh
# 006-09's night conductor (bergdb items/006-2026-q4/09-unattended-27-28-october.md,
# section 5): runs the timed steps of the quiet block, independent of the Claude session
# that started it, so that a usage limit does not stop them. Written 2026-10-27.
#
# steps.txt, read again before each step: lines MINUTES|WHERE|SCRIPT|LABEL (WHERE is f53
# or s1; # starts a comment). A step runs only when SCRIPT.READY exists, and once (the
# conductor writes SCRIPT.DONE). A "# minutes: N" line in the script overrides MINUTES.
# f53 steps run one at a time, after a quiet check, and only if they end inside the window:
# window 1 from W1_START to W1_END, window 2 from night.sh's end (at the latest NIGHT_LATEST)
# to W2_END; night.sh has no fixed time since 2026-11-06 (bergdb 013-01, section 7: one
# window). s1 steps run one after another in the background from W1_START (they check s1
# themselves).
# Writes status.txt (one line, the state), conductor.log and out/LABEL.txt; one news entry
# when the block ends; at FALLBACK, a summary entry if the session has not written one
# (marker summary-written).

BASE=${BASE:-/Users/f/fl/bench/006-09/night}
REPO=/Users/f/fl/repos/bergdb
STEPS=$BASE/steps.txt
LOG=$BASE/conductor.log
ep() { date -j -f "%Y-%m-%d %H:%M" "$1" +%s; }
W1_START=${W1_START:-$(ep "2026-10-27 22:30")}
W1_END=${W1_END:-$(ep "2026-10-28 02:05")}
NIGHT_LATEST=${NIGHT_LATEST:-$(ep "2026-10-28 03:15")}
W2_END=${W2_END:-$(ep "2026-10-28 06:15")}
FALLBACK=${FALLBACK:-$(ep "2026-10-28 06:50")}
NEWS=${NEWS:-$REPO/tools/news.sh}
QUIET_CHECKS=${QUIET_CHECKS:-6}
QUIET_GAP=${QUIET_GAP:-30}
QUIET_MAX=${QUIET_MAX:-1800}

now() { date +%s; }
log() { echo "$(date '+%m-%d %H:%M:%S') $*" >> "$LOG"; }
status() { echo "$(date '+%m-%d %H:%M:%S') $*" > "$BASE/status.txt"; log "status: $*"; }
sleep_until() { while [ "$(now)" -lt "$1" ]; do sleep 20; done; }

# One quiet check: no JVM but the editor's, no build, gate, Lean or night.sh, no busy
# Claude session, and a 1-minute load below 2.
quiet_once() {
    j=$(ps -axo command | grep -E '[/]java |^java ' | grep -v -E 'redhat\.java|vscode|\.vscode' | wc -l)
    g=$(ps -axo command | grep -E '[l]ake |[b]efore-commit|[l]evel[1-4]\.sh|[j]ava/build\.sh|[n]ight\.sh|[g]ates\.sh' | wc -l)
    b=$(grep -l -E '"status" *: *"busy"' "$HOME"/.claude/sessions/*.json 2>/dev/null | wc -l)
    l=$(sysctl -n vm.loadavg | awk '{print $2}')
    [ "$j" -eq 0 ] && [ "$g" -eq 0 ] && [ "$b" -eq 0 ] && awk -v l="$l" 'BEGIN { exit !(l < 2.0) }'
}

# Waits for QUIET_CHECKS quiet checks in a row, at most QUIET_MAX seconds; returns 1 if not.
wait_quiet() {
    n=0; t0=$(now)
    while [ $n -lt "$QUIET_CHECKS" ]; do
        if quiet_once; then n=$((n + 1)); else n=0; fi
        [ $(( $(now) - t0 )) -lt "$QUIET_MAX" ] || return 1
        [ $n -lt "$QUIET_CHECKS" ] && sleep "$QUIET_GAP"
    done
    return 0
}

minutes_of() {     # $1 script, $2 the minutes of steps.txt
    m=$(grep -m1 -E '^# minutes: *[0-9]+' "$1" 2>/dev/null | sed -E 's/^# minutes: *([0-9]+).*/\1/')
    echo "${m:-$2}"
}

RESULTS=$BASE/results.txt

# Runs one step: $1 label, $2 script.
run_step() {
    out=$BASE/out/$1.txt
    log "start $1: $2"
    t0=$(now)
    sh "$2" > "$out" 2>&1
    rc=$?
    touch "$2.DONE"
    echo "$1 exit $rc, $(( ($(now) - t0) / 60 )) min, $out" >> "$RESULTS"
    log "end $1: exit $rc"
    return $rc
}

# The next f53 step that is READY, not DONE, and ends before $1 (an epoch); prints
# "LABEL|SCRIPT" or nothing.
next_f53() {
    grep -v -E '^\s*(#|$)' "$STEPS" 2>/dev/null | while IFS='|' read -r min where script label; do
        [ "$where" = f53 ] || continue
        [ -f "$script.READY" ] && [ ! -f "$script.DONE" ] || continue
        m=$(minutes_of "$script" "$min")
        if [ $(( $(now) + m * 60 )) -le "$1" ]; then echo "$label|$script"; break; fi
    done
}

run_window() {     # $1 the window's end
    while :; do
        s=$(next_f53 "$1")
        [ -n "$s" ] || break
        label=${s%%|*}; script=${s#*|}
        status "waiting for quiet before $label"
        if wait_quiet; then q=quiet; else q="NOT QUIET after ${QUIET_MAX}s"; fi
        # Check again that it still fits after the wait.
        s2=$(next_f53 "$1"); [ "$s2" = "$s" ] || continue
        status "running $label ($q)"
        echo "$label: $q" >> "$RESULTS"
        run_step "$label" "$script"
    done
}

run_s1() {
    grep -v -E '^\s*(#|$)' "$STEPS" 2>/dev/null | while IFS='|' read -r min where script label; do
        [ "$where" = s1 ] || continue
        [ -f "$script.READY" ] && [ ! -f "$script.DONE" ] || continue
        run_step "$label" "$script"
    done
}

: > "$RESULTS"
log "conductor started, pid $$; window 1 $(date -r "$W1_START" '+%H:%M')-$(date -r "$W1_END" '+%H:%M'), window 2 to $(date -r "$W2_END" '+%H:%M')"
status "waiting for window 1 at $(date -r "$W1_START" '+%m-%d %H:%M')"
sleep_until "$W1_START"

run_s1 &
S1PID=$!
run_window "$W1_END"

status "window 1 done; waiting for night.sh"
started=0
while [ "$(now)" -lt "$NIGHT_LATEST" ]; do
    if pgrep -f 'bergdb/java/night.sh' > /dev/null; then started=1
    elif [ $started = 1 ]; then break; fi
    sleep 30
done
while pgrep -f 'bergdb/java/night.sh' > /dev/null; do sleep 30; done
log "night.sh: started=$started, now over"

run_window "$W2_END"
wait $S1PID 2>/dev/null

nok=$(grep -c ' exit 0,' "$RESULTS"); nall=$(grep -c ' exit ' "$RESULTS")
left=$(grep -v -E '^\s*(#|$)' "$STEPS" 2>/dev/null | while IFS='|' read -r min where script label; do
    [ -f "$script.DONE" ] || echo "$label"; done | tr '\n' ' ' | sed 's/ *$//')
if [ "$nall" -gt 0 ] && [ "$nok" = "$nall" ] && [ -z "$left" ]; then st=OK
elif [ "$nok" != "$nall" ]; then st=FAILED
else st="needs a look"; fi
txt="Quiet block on F53 done: $nok of $nall timed steps exit 0${left:+; not run: $left}. Steps and outputs: $BASE/results.txt; the results go into 006-09 and the entries."
sh "$NEWS" "$st" "006-09 night conductor" "$txt"
status "block done: $nok of $nall steps exit 0${left:+; not run: $left}"

sleep_until "$FALLBACK"
if [ ! -f "$BASE/summary-written" ]; then
    sh "$NEWS" "needs a look" "006-09 session" "The session did not write its night summary by 06:50 (a usage limit, perhaps). The quiet block: $nok of $nall timed steps exit 0. See 006-09's progress section and $BASE/conductor.log."
    log "fallback summary written"
fi
status "ended"
log "conductor ended"
