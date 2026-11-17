#!/bin/sh
# minutes: 45
# bergdb 005-52's first step (question 2), W6.4 of 006-09: the capacity controller's budget
# lowered by Eviction.setBudget while gets and commits run; the eviction thread's work and the
# longest waits of gets and commits until the resident bytes reach the new budget.
# BudgetBench.java, one JVM a run: a load of 10M key24 keys as ScaleBench's (budget 665 MB,
# which the load does not reach: it leaves the latest tree resident, about 16 bytes a key),
# then 2 readers (uniform gets) and a writer (200 commits a second of 10 puts): a warm-up
# until the resident bytes are steady; 60 s; the budget lowered to a fraction of the resident
# bytes, until they are at most that (at most 300 s); 60 s at the low budget; 30 s back at
# 665 MB. Three runs: ZGC to a fifth (its pauses well under a millisecond, so a wait is
# BergDB's own: 010-P1), G1 to a fifth (the default collector), ZGC to a half. About 7
# minutes a run (the load 2 to 4); a run that would start with less than 10 minutes left is
# skipped; a JVM still running at 44 minutes is killed.
# Written 2026-10-27 by Claude (Opus 5.5, Claude Code).
# Uses only the jar prebuilt from HEAD e747323 and the classes compiled from BudgetBench.java,
# both in /Users/f/fl/bench/006-09/w6/night (no build here).
# Usage: sh budget.sh, from any directory. SMOKE=1: 200,000 keys, phases of seconds, outputs
# in night/out/smoke/.
# Outputs: night/out/ (or night/out/smoke/): RUN.txt (the summary lines), RUN.csv (a sample
# every 100 ms), RUN.gc.log; runs.txt (start, end, verdicts).
# Exit status: 0 if every run ended with BUDGETBENCH OK.

NIGHT=/Users/f/fl/repos/bergdb/items/005-todo/52-cache-size-while-running/night
B=/Users/f/fl/bench/006-09/w6/night
JAVA=/opt/homebrew/opt/openjdk/bin/java
CP=$B/classes:$B/bergdb.jar
DATA=$B/bbdata

if [ -n "$SMOKE" ]; then
    OUT=$NIGHT/out/smoke
    PROPS="-Dbb.keys=200000 -Dbb.high=100000000 -Dbb.warmmax=3 -Dbb.base=2 -Dbb.convmax=10 -Dbb.after=2 -Dbb.raise=1"
    HEAP=1g; MINRUN=0; KILLAT=300
else
    OUT=$NIGHT/out
    PROPS="-Dbb.keys=10000000 -Dbb.high=665000000 -Dbb.warmmax=120 -Dbb.base=60 -Dbb.convmax=300 -Dbb.after=60 -Dbb.raise=30"
    HEAP=6g; MINRUN=600; KILLAT=2640
fi
mkdir -p "$OUT"
T0=$(date +%s)
left() { echo $((KILLAT - ($(date +%s) - T0))); }
log() { echo "$(date '+%Y-%m-%d %H:%M:%S') $*" | tee -a "$OUT/runs.txt"; }

for f in "$JAVA" "$B/bergdb.jar" "$B/classes/bergdb/core/BudgetBench.class"; do
    if [ ! -e "$f" ]; then log "budget: missing $f"; exit 2; fi
done

log "budget${SMOKE:+ (smoke)}: start; jar $(cat "$B/bergdb.jar.txt" 2>/dev/null | cut -c1-60)"
bad=0
for run in budget-zgc-f20 budget-g1-f20 budget-zgc-f50; do
    case $run in
        *-zgc-*) GCFLAG=-XX:+UseZGC ;;
        *-g1-*) GCFLAG=-XX:+UseG1GC ;;
    esac
    case $run in
        *-f20) FRAC=0.2 ;;
        *-f50) FRAC=0.5 ;;
    esac
    if [ "$(left)" -le $MINRUN ]; then
        log "  skipped $run: $(left) s left"
        bad=$((bad + 1))
        continue
    fi
    rm -rf "$DATA"
    "$JAVA" -Xms$HEAP -Xmx$HEAP $GCFLAG -Xlog:gc:file="$OUT/$run.gc.log" -cp "$CP" \
        -Dbb.dir="$DATA" -Dbb.out="$OUT/$run.csv" -Dbb.lowfrac=$FRAC $PROPS bergdb.core.BudgetBench \
        > "$OUT/$run.txt" 2>&1 &
    pid=$!
    # The deadline: a JVM still running when the step's time is up is killed.
    while kill -0 $pid 2>/dev/null; do
        if [ "$(left)" -le 0 ]; then
            kill $pid 2>/dev/null; sleep 5; kill -9 $pid 2>/dev/null
            log "  $run: killed at the deadline"
        fi
        sleep 2
    done
    wait $pid
    if grep -q "^BUDGETBENCH OK" "$OUT/$run.txt"; then
        log "  $run: $(grep '^converge:' "$OUT/$run.txt" | cut -c1-300)"
        log "  $run: $(grep -E '^(gets|commits), converge:' "$OUT/$run.txt" | sed 's/;.*//' | tr '\n' ' ')"
    else
        log "  FAILED: $run ($(tail -1 "$OUT/$run.txt" | cut -c1-200))"
        bad=$((bad + 1))
    fi
done
rm -rf "$DATA"
log "budget${SMOKE:+ (smoke)}: end, $bad of 3 runs failed or skipped"
[ $bad = 0 ]
