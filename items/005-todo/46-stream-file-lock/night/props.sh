#!/bin/sh
# minutes: 12
# bergdb 005-46, W1.4 of 006-09: Props (MEM, CORE, SS) on HEAD's prebuilt jar and on
# bf19075's (005-50, just before 005-46), in turns, four rounds (ABBA ABBA), as 009-03 ran it
# twice: no fewer reads a second. About 6 minutes (40 s a run); stopped at 12. Written
# 2026-10-27 by Claude (Opus 5.5, Claude Code); README.md beside it.
# Usage: sh props.sh, from any directory (SMOKE=1: Mem only, two rounds, outputs in
# /Users/f/fl/bench/006-09/w1/smoke). Needs prep.sh's clones head/ and bf19075/, built.
# Outputs: night/out/props/props-JAR-ROUND.txt; start and end in night/out/runs.txt.
# Exit status: 0 if every run printed its MEM (and, without SMOKE, CORE and SS).
STEP=props
. /Users/f/fl/repos/bergdb/items/005-todo/46-stream-file-lock/night/lib.sh

if [ -n "$MODE" ]; then
    CLASS=bergdb.dev.props.Mem; ROUNDS=2; WANT=1
else
    CLASS=bergdb.dev.props.Props; ROUNDS=4; WANT=3
fi
for j in head bf19075; do need "$B/$j/java/build/bergdb.jar"; done
need "$JAVA"
watch "$B/.*bergdb.jar $CLASS"
log "start$MODE: $CLASS, $ROUNDS rounds, bf19075 and HEAD in turns (ABBA); deadline in $MINUTES min"
jarinfo head
jarinfo bf19075
quiet
bad=0
r=1
while [ $r -le $ROUNDS ]; do
    if [ $((r % 2)) = 1 ]; then order="bf19075 head"; else order="head bf19075"; fi
    for j in $order; do
        f=$OUT/props-$j-$r.txt
        "$JAVA" -cp "$B/$j/java/build/bergdb.jar" $CLASS > "$f" 2>&1
        [ "$(grep -c -E '^(MEM|CORE|SS):' "$f")" -ge $WANT ] || bad=$((bad + 1))
        log "  $j, round $r: $(grep -E '^(MEM|CORE|SS):' "$f" | tr '\n' ' ')"
    done
    r=$((r + 1))
done
core() { cat "$OUT"/props-$1-*.txt 2>/dev/null | sed -n 's/^CORE:\([0-9.]*\).*/\1/p' | tr '\n' ' '; }
if [ $bad = 0 ]; then st="needs a look"; else st=FAILED; fi
finish "$st" "Props in turns, $((ROUNDS * 2)) runs, $bad failed; CORE (lower is faster): HEAD $(core head), bf19075 $(core bf19075)."
[ $bad = 0 ]
