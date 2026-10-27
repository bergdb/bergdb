# lib.sh: what soak.sh, props.sh and scalebench-c.sh share (bergdb 005-46's night steps for
# 006-09's quiet block, 2026-10-27). Sourced by absolute path, with STEP set; reads the step's
# "# minutes: N" header from $0, its deadline. SMOKE=1: tiny runs, outputs in $B/smoke.
# NEWS=1: an entry in news.md at the step's end (off by default: 006-09's conductor writes one
# for the block). Written 2026-10-27 by Claude (Opus 5.5, Claude Code).

NIGHT=/Users/f/fl/repos/bergdb/items/005-todo/46-stream-file-lock/night
REPO=/Users/f/fl/repos/bergdb
B=${B:-/Users/f/fl/bench/006-09/w1}
export JAVA_HOME=/opt/homebrew/opt/openjdk
JAVA=$JAVA_HOME/bin/java
T0=$(date +%s)
MINUTES=$(sed -n 's/^# minutes: *\([0-9][0-9]*\).*/\1/p' "$0" | head -n 1)
[ -n "$MINUTES" ] || { echo "$0: no '# minutes: N' line" >&2; exit 2; }
if [ "${SMOKE:-0}" = 1 ]; then
    MODE=" (SMOKE)"
    OUTROOT=$B/smoke
    export NEWS_FILE=$OUTROOT/news.md
    MINUTES=${LIMIT:-10}
    QCHECKS=1; QSLEEP=1; QMAX=0
else
    MODE=
    OUTROOT=$NIGHT/out
    QCHECKS=2; QSLEEP=15; QMAX=2       # the conductor waits for quiet before the step too
fi
OUT=$OUTROOT/$STEP
LOG=$OUTROOT/runs.txt
RAW=$B/raw$( [ -n "$MODE" ] && echo -smoke )/$STEP    # GC logs and the like, not for the item
DEADLINE=$((T0 + MINUTES * 60))
DONE=$RAW/.done-$$
mkdir -p "$OUT" "$RAW" || exit 1

log() { echo "$(date '+%F %T') $STEP: $*" >> "$LOG"; }
left() { echo $((DEADLINE - $(date +%s))); }      # seconds to the deadline
state() {
    echo "load $(sysctl -n vm.loadavg | awk '{print $2, $3, $4}'); $(pmset -g batt | head -n 1 | sed "s/.*'\(.*\)'.*/\1/");" \
        "sessions $(cat "$HOME"/.claude/sessions/*.json 2>/dev/null | grep -o '"status":"[a-z]*"' | cut -d'"' -f4 | sort | uniq -c | tr -s ' \n' ' ')"
}
others() {      # other JVMs, gates, Lean, trace checks, night.sh (as 004-02's quiet.sh)
    ps -Ao pid,args | grep -E "tracecheck|bin/java|lake |level[0-9]\.sh|before-commit|night\.sh" \
        | grep -v -E "grep|vscode|Code Helper"
}
quiet() {       # QCHECKS checks in a row, QSLEEP s apart, with none of others() and a 1-minute
    n=0         # load below 2.0; after QMAX minutes the step goes on in any case
    s=$(date +%s)
    while [ $n -lt $QCHECKS ]; do
        l=$(sysctl -n vm.loadavg | awk '{print $2}')
        if [ -z "$(others)" ] && awk -v l="$l" 'BEGIN { exit !(l < 2.0) }'; then n=$((n + 1)); else n=0; fi
        [ $n -ge $QCHECKS ] && break
        if [ $(( $(date +%s) - s )) -ge $((QMAX * 60)) ]; then
            log "  not quiet after $QMAX min, going on: $(state); others: $(others | cut -c1-160 | tr '\n' ';')"
            return
        fi
        sleep $QSLEEP
    done
    log "  quiet: $(state)"
}
need() {
    [ -e "$1" ] || { log "ABORTED: $1 missing (prep.sh makes it)"; echo "$STEP: missing $1" >&2; exit 1; }
}
jarinfo() {     # jarinfo CLONE: the clone's commit and its jar
    log "  $1's jar: commit $(git -C "$B/$1" rev-parse HEAD), sha256 $(shasum -a 256 "$B/$1/java/build/bergdb.jar" | cut -c1-16)"
}
watch() {       # watch PATTERN: caffeinate, and at the deadline pkill -f PATTERN (the step's JVMs)
    caffeinate -i -s &
    CAF=$!
    (
        while [ "$(date +%s)" -lt "$DEADLINE" ]; do
            [ -f "$DONE" ] && exit 0
            sleep 5
        done
        echo "$(date '+%F %T') $STEP: DEADLINE after $MINUTES min, its JVMs stopped" >> "$LOG"
        pkill -f "$1"
    ) &
    WD=$!
    trap 'touch "$DONE"; { kill $CAF; wait $CAF; } 2>/dev/null; wait $WD; rm -f "$DONE"' EXIT
}
finish() {      # finish STATUS TEXT: summary.txt, the end line, an entry in news.md
    python3 "$NIGHT/nightsum.py" "$OUTROOT" > "$OUTROOT/summary.txt" 2>&1
    log "end$MODE after $(( ($(date +%s) - T0) / 60 )) min: $1; $2"
    if [ "${NEWS:-0}" = 1 ]; then
        sh "$REPO/tools/news.sh" "$1" "005-46 night, $STEP" \
            "$2 For 005-46 and 009's target 2 (006-09's W1); items/005-todo/46-stream-file-lock/night/out/summary.txt" \
            >> "$LOG" 2>&1
    fi
}
