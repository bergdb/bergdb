#!/bin/sh
# minutes: 25
# bergdb 005-52's last point, for release 2026.2 (016-05; 005-52, Left to do and Plan for
# 2026.2): no get or commit may wait longer while the resident bytes converge to a lowered
# budget than with a fixed one. PauseProbe (java/stress), with its properties lower and
# lowerAt, on one jar of main: 1M keys of 100 bytes on disk, 4 readers, the phases tsize=1
# and tsize=1000, 60 s each. Six runs, in turns for each collector: (a) a fixed budget of
# 100 MB; (b) 400 MB, lowered to 100 MB 10 s into each phase; (a) again, for the spread
# between two runs of (a): ZGC a1 b a2, then G1 a1 b a2. About 17 minutes (a run about
# 2.5: the load and two phases); a run that would start with less than 4 minutes left is
# skipped, and a JVM still running at 24 minutes is killed. The conductor's step 52-lowered
# in night 1's window 2 (016-05, section 6).
# Created 2026-11-03 by Frans Lundberg.
# Uses only R (default /Users/f/fl/bench/016/005-52/run): bergdb.jar, stress/ (the compiled
# probe) and jar.txt, made by the plan's step 7; and JDK 27. It compiles nothing.
# Usage: sh lowered.sh, from any directory. SMOKE=1: 20,000 keys, phases of 3 s, budgets of
# 4 MB (a) and 8 MB lowered to 2 MB at 1 s (b), no skip, outputs in $R/smoke (about a
# minute); the same checks of the parsed summary.
# Outputs, outside the repository: $R/out (or $R/smoke): RUN.txt, RUN.gc.log, runs.txt, and
# summary.txt from sum52.py (beside this script).
# Exit status: 0 if every run printed PAUSE PROBE OK and the summary is complete (12 rows, a
# lowering in each of (b)'s 4 rows); 1 otherwise; 2 for a missing prerequisite.
# Written before PauseProbe has lower and lowerAt: smoke-test it (SMOKE=1) after the
# probe's commit, before its READY marker.

STEP=lowered
NIGHT=$(cd "$(dirname "$0")" && pwd)
R=${R:-/Users/f/fl/bench/016/005-52/run}
JAVA=/opt/homebrew/opt/openjdk/bin/java
T0=$(date +%s)
if [ "${SMOKE:-0}" = 1 ]; then
    MODE=" (SMOKE)"
    OUT=$R/smoke
    HEAP=512m; MINRUN=0; KILLAT=300
    COMMON="-Dkeys=20000 -Dseconds=3"
    PA="-Dbudget=4"
    PB="-Dbudget=8 -Dlower=2 -DlowerAt=1"
else
    MODE=
    OUT=$R/out
    HEAP=2g; MINRUN=240; KILLAT=1440
    COMMON="-Dkeys=1000000 -Dseconds=60"
    PA="-Dbudget=100"
    PB="-Dbudget=400 -Dlower=100 -DlowerAt=10"
fi
DB=$R/db
RUNS="zgc-a1 zgc-b zgc-a2 g1-a1 g1-b g1-a2"

for f in "$JAVA" "$R/bergdb.jar" "$R/stress/bergdb/core/PauseProbe.class" "$NIGHT/sum52.py"; do
    [ -e "$f" ] || { echo "$STEP$MODE: missing $f" >&2; exit 2; }
done
grep -q lowerAt "$R/stress/bergdb/core/PauseProbe.class" \
    || { echo "$STEP$MODE: PauseProbe without the properties lower and lowerAt" >&2; exit 2; }

rm -rf "$OUT"
mkdir -p "$OUT" || exit 2
left() { echo $((KILLAT - ($(date +%s) - T0))); }
log() { echo "$(date '+%F %T') $STEP: $*" >> "$OUT/runs.txt"; }

caffeinate -i -s &
CAF=$!
trap '{ kill $CAF; wait $CAF; } 2>/dev/null' EXIT

log "start$MODE: jar $(tr '\n' ' ' < "$R/jar.txt" 2>/dev/null | cut -c1-140); load" \
    "$(sysctl -n vm.loadavg | awk '{print $2, $3, $4}')"
bad=0
for run in $RUNS; do
    case $run in
        zgc-*) GC=-XX:+UseZGC ;;
        g1-*) GC=-XX:+UseG1GC ;;
    esac
    case $run in
        *-b) P=$PB ;;
        *) P=$PA ;;
    esac
    if [ "$(left)" -le $MINRUN ]; then
        log "  skipped $run: $(left) s left"
        bad=$((bad + 1))
        continue
    fi
    rm -rf "$DB"
    "$JAVA" -Xms$HEAP -Xmx$HEAP -XX:+AlwaysPreTouch $GC \
        -Xlog:gc*,safepoint:file="$OUT/$run.gc.log":uptime,level,tags \
        $COMMON -Dvalsize=100 -Dreaders=4 -Dtsize=1,1000 -Ddir="$DB" $P \
        -cp "$R/bergdb.jar:$R/stress" bergdb.core.PauseProbe > "$OUT/$run.txt" 2>&1 &
    pid=$!
    killed=0
    while kill -0 $pid 2>/dev/null; do
        if [ $killed = 0 ] && [ "$(left)" -le 0 ]; then
            kill $pid 2>/dev/null; sleep 5; kill -9 $pid 2>/dev/null
            killed=1
            log "  $run: killed at the deadline"
        fi
        sleep 2
    done
    wait $pid
    if grep -q "^PAUSE PROBE OK" "$OUT/$run.txt"; then
        log "  $run: OK, $(grep -c '^  lowered:' "$OUT/$run.txt") lowerings"
    else
        log "  FAILED: $run ($(tail -n 1 "$OUT/$run.txt" | cut -c1-200))"
        bad=$((bad + 1))
    fi
done
rm -rf "$DB"
if ! python3 "$NIGHT/sum52.py" "$OUT" > "$OUT/summary.txt" 2>&1; then
    log "  the summary is incomplete: $(tail -n 1 "$OUT/summary.txt" | cut -c1-200)"
    bad=$((bad + 1))
fi
if [ $bad = 0 ]; then st=OK; else st=FAILED; fi
log "end$MODE after $(( ($(date +%s) - T0) / 60 )) min: $st; $bad problems"
echo "$STEP$MODE: $st, $bad problems; $OUT/summary.txt"
[ $bad = 0 ]
