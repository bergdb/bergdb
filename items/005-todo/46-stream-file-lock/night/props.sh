#!/bin/sh
# minutes: 12
# bergdb 005-46, W1.4 of 006-09: Props (MEM, CORE, SS) on HEAD's prebuilt jar and on
# bf19075's (005-50, just before 005-46), in turns, four rounds (ABBA ABBA), as 009-03 ran it
# twice: no fewer reads a second. About 6 minutes (40 s a run); stopped at 12. Written
# 2026-10-27 by Claude (Opus 5.5, Claude Code); README.md beside it.
# Usage: sh props.sh, from any directory (SMOKE=1: one round, about 80 s, outputs in
# $B/smoke). Needs prep.sh's clones in B (default /Users/f/fl/bench/006-09/w1), built: JARS
# names two of them, default "bf19075 head" (the reference first; another pair, such as two
# preserved builds before and after a change, by JARS="old new" with B set).
# Outputs: night/out/props/props-JAR-ROUND.txt; start and end in night/out/runs.txt.
# Exit status: 0 if every run printed MEM, CORE and SS, and summary.txt (nightsum.py) has
# every run's three values and a CORE mean for each jar. 2026-10-28: the CORE line follows a
# row of Core's progress dots, which the first version did not read (the step exited 1 in
# 006-09's block, its values in the files); SMOKE now runs Props itself and checks the parse.
STEP=props
. "$(dirname "$0")/lib.sh"

CLASS=bergdb.dev.props.Props; WANT=3
if [ -n "$MODE" ]; then ROUNDS=1; else ROUNDS=4; fi
JARS=${JARS:-bf19075 head}
J1=$(echo $JARS | awk '{print $1}'); J2=$(echo $JARS | awk '{print $2}')
rm -f "$OUT"/props-*.txt
for j in $J1 $J2; do need "$B/$j/java/build/bergdb.jar"; done
need "$JAVA"
watch "$B/.*bergdb.jar $CLASS"
log "start$MODE: $CLASS, $ROUNDS rounds, $J1 and $J2 in turns (ABBA); deadline in $MINUTES min"
jarinfo $J1
jarinfo $J2
quiet
bad=0
r=1
while [ $r -le $ROUNDS ]; do
    if [ $((r % 2)) = 1 ]; then order="$J1 $J2"; else order="$J2 $J1"; fi
    for j in $order; do
        f=$OUT/props-$j-$r.txt
        "$JAVA" -cp "$B/$j/java/build/bergdb.jar" $CLASS > "$f" 2>&1
        [ "$(grep -c -E '^\.*(MEM|CORE|SS):' "$f")" -ge $WANT ] || bad=$((bad + 1))
        log "  $j, round $r: $(grep -o -E '(MEM|CORE|SS):[0-9.]+' "$f" | tr '\n' ' ')"
    done
    r=$((r + 1))
done
core() { cat "$OUT"/props-$1-*.txt 2>/dev/null | sed -n 's/^\.*CORE:\([0-9.]*\).*/\1/p' | tr '\n' ' '; }
python3 "$NIGHT/nightsum.py" "$OUTROOT" > "$OUTROOT/summary.txt" 2>&1
# The parsed result, as the summary gives it: no value missing, a CORE mean for each jar.
sec=$(sed -n '/^# 2\. Props/,/^# 3\./p' "$OUTROOT/summary.txt")
if echo "$sec" | grep -q '?' || [ "$(echo "$sec" | grep -c 'CORE mean [0-9]')" != 2 ]; then
    log "  the summary lacks a parsed value: $(echo "$sec" | tr '\n' ' ' | cut -c1-300)"
    bad=$((bad + 1))
fi
if [ $bad = 0 ]; then st="needs a look"; else st=FAILED; fi
finish "$st" "Props in turns, $((ROUNDS * 2)) runs, $bad problems; CORE (lower is faster): $J2 $(core $J2), $J1 $(core $J1)."
echo "$STEP$MODE: $st, $bad problems; $OUTROOT/summary.txt"
[ $bad = 0 ]
