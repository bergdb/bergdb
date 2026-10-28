#!/bin/sh
# minutes: 30
# bergdb 005-65: ScaleBench from the OS's cache (C) at 4, 6 and 8 reader threads, 665 MB,
# ZGC, on three prebuilt builds in turns: bf19075 (005-50, the commit before 005-46), eaec93e
# (005-46 alone) and 4f7cd60 (006-09's HEAD: 005-46, 005-55, 005-57, 005-51), with the CPU of
# the eviction thread, of the readers and of the rest of the process in each threads phase
# (ScaleBench-065.diff). As 005-46's night/scalebench-c.sh (006-09's quiet block): 10M key24
# keys, the default startup distance (10 MB), one database loaded by the last build's jar
# with no get phases; then two rounds, each a run of each build, the order reversed in the
# second (ABC CBA): the phases warm and threads (4, 6, 8; 30 s each), then 8 sampled readers
# (20 s). About 17 minutes (the load 2.5, then 6 runs of about 2.4); a run that would start
# with less than 5 minutes left is skipped, and the step is stopped at 30. Uses only prebuilt
# jars and classes, from prep.sh. Written 2026-10-28 by Claude (Opus 5.5, Claude Code).
# Usage: sh threads.sh, from any directory. SMOKE=1: 20,000 keys, a startup distance of 100 KB
# and a budget of 0.5 MB (so that the eviction thread runs), phases of a second, outputs in $B/smoke (about a minute); it checks the parsed summary, not only the exit
# codes. B (default /Users/f/fl/bench/006-09/d2-009-builds) holds prep.sh's clones (one per
# build, named by the commit) and sb/. BUILDS (default "bf19075 eaec93e 4f7cd60", the first
# the reference) and ROUNDS (default 2) change the runs; the minutes line does not follow.
# Outputs: night/out/threads/ (NAME.txt, NAME.json, sb.sh's runs.txt), night/out/runs.txt
# (start, end, each run), night/out/summary.txt (sum.py); the GC logs in $B/raw/threads.
# Exit status: 0 if the load and all 6 runs ended with SCALEBENCH OK and the summary has
# every run's three thread phases with the eviction thread's CPU; 1 otherwise, 2 for a
# missing prerequisite.

STEP=threads
HERE=$(cd "$(dirname "$0")" && pwd)
B=${B:-/Users/f/fl/bench/006-09/d2-009-builds}
export JAVA_HOME=/opt/homebrew/opt/openjdk
JAVA=$JAVA_HOME/bin/java
T0=$(date +%s)
MINUTES=$(sed -n 's/^# minutes: *\([0-9][0-9]*\).*/\1/p' "$0" | head -n 1)
[ -n "$MINUTES" ] || { echo "$0: no '# minutes: N' line" >&2; exit 2; }
if [ "${SMOKE:-0}" = 1 ]; then
    MODE=" (SMOKE)"
    OUTROOT=$B/smoke
    MINUTES=${LIMIT:-5}
    QCHECKS=1; QSLEEP=1; QMAX=0
    KEYS=20000; KN=20k; LOADHEAP=1g; MINRUN=0; BUDGET=500000     # a budget that evicts
    EXTRA="-Dsb.sd=100000 -Dsb.window=0.2 -Dsb.threadsec=1 -Dsb.samplesec=1 -Dsb.warmmax=3"
else
    MODE=
    OUTROOT=$HERE/out
    QCHECKS=2; QSLEEP=15; QMAX=2        # the conductor waits for quiet before the step too
    KEYS=10000000; KN=10m; LOADHEAP=6g; MINRUN=300; BUDGET=665000000
    EXTRA=
fi
BUILDS=${BUILDS:-bf19075 eaec93e 4f7cd60}
ROUNDS=${ROUNDS:-2}
REVERSED=$(echo $BUILDS | tr ' ' '\n' | tail -r | tr '\n' ' ')
LAST=$(echo $BUILDS | awk '{print $NF}')
OUT=$OUTROOT/$STEP
LOG=$OUTROOT/runs.txt
RAW=$B/raw$( [ -n "$MODE" ] && echo -smoke )/$STEP
DEADLINE=$((T0 + MINUTES * 60))
DONE=$RAW/.done-$$
rm -rf "$OUT"
mkdir -p "$OUT" "$RAW" || exit 2

log() { echo "$(date '+%F %T') $STEP: $*" >> "$LOG"; }
left() { echo $((DEADLINE - $(date +%s))); }
state() {
    echo "load $(sysctl -n vm.loadavg | awk '{print $2, $3, $4}'); $(pmset -g batt | head -n 1 | sed "s/.*'\(.*\)'.*/\1/");" \
        "sessions $(cat "$HOME"/.claude/sessions/*.json 2>/dev/null | grep -o '"status":"[a-z]*"' | cut -d'"' -f4 | sort | uniq -c | tr -s ' \n' ' ')"
}
others() {      # other JVMs, gates, Lean, trace checks, night.sh (as 005-46's lib.sh)
    ps -Ao pid,args | grep -E "tracecheck|bin/java|lake |level[0-9]\.sh|before-commit|night\.sh" \
        | grep -v -E "grep|vscode|Code Helper"
}
quiet() {       # QCHECKS checks in a row, QSLEEP s apart; after QMAX minutes it goes on
    n=0
    s=$(date +%s)
    while [ $n -lt $QCHECKS ]; do
        l=$(sysctl -n vm.loadavg | awk '{print $2}')
        if [ -z "$(others)" ] && awk -v l="$l" 'BEGIN { exit !(l < 2.0) }'; then n=$((n + 1)); else n=0; fi
        [ $n -ge $QCHECKS ] && break
        if [ $(( $(date +%s) - s )) -ge $((QMAX * 60)) ]; then
            log "  NOT QUIET after $QMAX min, going on: $(state); others: $(others | cut -c1-160 | tr '\n' ';')"
            return
        fi
        sleep $QSLEEP
    done
    log "  quiet: $(state)"
}
need() {
    [ -e "$1" ] || { log "ABORTED: $1 missing (prep.sh makes it)"; echo "$STEP: missing $1" >&2; exit 2; }
}
jarinfo() {
    log "  $1's jar: commit $(git -C "$B/$1" rev-parse HEAD), sha256 $(shasum -a 256 "$B/$1/java/build/bergdb.jar" | cut -c1-16)"
}

SBSH=$HERE/../../../004-indirect-swizzling/02-scale-tests/sb.sh
for j in $BUILDS; do
    need "$B/$j/java/build/bergdb.jar"
    need "$B/sb/classes-$j/bergdb/core/ScaleBench.class"
done
need "$B/sb/pidio"
need "$SBSH"
need "$JAVA"
grep -q evictionCpuMs "$B/sb/src/ScaleBench.java" || { log "ABORTED: ScaleBench without ScaleBench-065.diff"; exit 2; }
DATA=$B/sbdata
PIDIO=$B/sb/pidio
THREADS=4,6,8
SAMPLED=8
. "$SBSH"       # sb_load and sb_get; they write OUT/NAME.txt, .json and .gc.log, and OUT/runs.txt

caffeinate -i -s &
CAF=$!
(
    while [ "$(date +%s)" -lt "$DEADLINE" ]; do
        [ -f "$DONE" ] && exit 0
        sleep 5
    done
    echo "$(date '+%F %T') $STEP: DEADLINE after $MINUTES min, its JVMs stopped" >> "$LOG"
    pkill -f "sb.out=$OUT/"
) &
WD=$!
trap 'touch "$DONE"; { kill $CAF; wait $CAF; } 2>/dev/null; wait $WD; rm -f "$DONE"' EXIT

log "start$MODE: $KN key24 keys, C at 665 MB, ZGC, threads $THREADS, builds $BUILDS, $ROUNDS rounds in turns; deadline in $MINUTES min;" \
    "$(sysctl -n machdep.cpu.brand_string), $(sysctl -n hw.perflevel0.physicalcpu) performance and $(sysctl -n hw.perflevel1.physicalcpu 2>/dev/null) efficiency cores"
for j in $BUILDS; do jarinfo $j; done
quiet
total=$((ROUNDS * $(echo $BUILDS | wc -w)))
bad=0
rm -rf "$DATA"
mkdir -p "$DATA"
CP=$B/sb/classes-$LAST:$B/$LAST/java/build/bergdb.jar
name=f53-l-$KN-$LAST
if (SBFLAGS="-XX:+UseG1GC $EXTRA"; sb_load $name key24 $KEYS $LOADHEAP 0 ""); then
    log "  $(grep -o 'load done.*' "$OUT/$name.txt" | cut -c1-160)"
else
    log "  FAILED: the load ($name.txt)"
    bad=$((total + 1))
fi
mv "$OUT/$name.gc.log" "$RAW/" 2>/dev/null
r=1
while [ $bad -le $total ] && [ $r -le $ROUNDS ]; do
    if [ $((r % 2)) = 1 ]; then order=$BUILDS; else order=$REVERSED; fi
    for j in $order; do
        name=f53-c-$KN-b665-zgc-$j-$r
        if [ "$(left)" -le $MINRUN ]; then
            log "  skipped $name: $(left) s to the deadline"
            bad=$((bad + 1))
            continue
        fi
        CP=$B/sb/classes-$j:$B/$j/java/build/bergdb.jar
        if (SBFLAGS="-XX:+UseZGC $EXTRA"; sb_get $name key24 $KEYS 2660m $BUDGET C warm,threads); then
            log "  $name: $(grep -o 'threads [0-9]*: [0-9]* gets a second.*max [0-9.]* us' "$OUT/$name.txt" \
                | sed 's/ gets a second;.*max / gets a second, max /' | tr '\n' ';')"
        else
            log "  FAILED: $name"
            bad=$((bad + 1))
        fi
        mv "$OUT/$name.gc.log" "$RAW/" 2>/dev/null
    done
    r=$((r + 1))
done
rm -rf "$DATA"
python3 "$HERE/sum.py" "$OUT" > "$OUTROOT/summary.txt" 2>&1
# The parsed result: every run's three thread phases with the eviction thread's CPU.
want=$((total * 3))
got=$(grep -c '^| f53-.* | [0-9][0-9.]* |$' "$OUTROOT/summary.txt" 2>/dev/null)
[ "$got" = "$want" ] || { log "  the summary has $got rows with the eviction thread's CPU, not $want"; bad=$((bad + 1)); }
if [ $bad = 0 ]; then st=OK; else st=FAILED; fi
log "end$MODE after $(( ($(date +%s) - T0) / 60 )) min: $st; $bad problems; $(grep '^Longest get' "$OUTROOT/summary.txt" | tr '\n' ' ' | cut -c1-400)"
echo "$STEP$MODE: $st, $bad problems; $OUTROOT/summary.txt"
[ $bad = 0 ]
