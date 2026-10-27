#!/bin/sh
# minutes: 115
# bergdb 005-46, W1.3 of 006-09: P4's soak under ZGC on HEAD's prebuilt jar, as 009-03 and
# 009-04 ran it (an 8 GB heap, a 1.6 GB budget, a writer of 200 commits and three readers of
# 5,000 reads a second, a retention of 300 s, 30 measured minutes, one restart): are reclaim's
# physical cuts still the slowest commits and reads (009-04, section 7.3)? About 47 minutes;
# the warm-up waits up to 60 minutes for its first cut and the measured phase can extend by
# 15, so at most about 106; stopped at 115. Written 2026-10-27 by Claude (Opus 5.5, Claude
# Code); README.md beside it.
# Usage: sh soak.sh, from any directory (SMOKE=1: a soak of seconds, outputs in
# /Users/f/fl/bench/006-09/w1/smoke). Needs prep.sh's clone head/, built.
# Outputs: night/out/soak/ (NAME-report.txt, NAME-summary.json, NAME-stdout.txt,
# NAME-source.txt, NAME-soak-sh.txt); the run directory with the GC log stays in the clone,
# java/build/soak/NAME; start and end in night/out/runs.txt. Exit status: the soak's (0: SOAK OK).
STEP=soak
. /Users/f/fl/repos/bergdb/items/005-todo/46-stream-file-lock/night/lib.sh

if [ -n "$MODE" ]; then
    NAME=smoke-46-zgc-$(date +%H%M%S)
    HEAP=1g; BUDGET=20000000
    PROPS="n=20000 rate=200 warmup=2 warmupmax=8 measure=6 restarts=1 mincuts=0 extend=5"
else
    NAME=p4-46-zgc-$(date +%m%d-%H%M)
    HEAP=8g; BUDGET=1600000000
    PROPS="rate=200 warmup=300 warmupmax=3600 measure=1800 restarts=1 mincuts=2 extend=900"
fi
RUN=$B/head/java/build/soak/$NAME
need "$B/head/java/build/bergdb.jar"
need "$B/head/java/build/stress/bergdb/core/Soak.class"
need "$B/head/java/build/stress/bergdb/core/TimedIo.class"
need "$JAVA"
watch "soak.out=$RUN"
log "start$MODE: $NAME, ZGC, heap $HEAP, budget $BUDGET bytes, $PROPS; deadline in $MINUTES min"
jarinfo head
quiet
(cd "$B/head" && HEAP=$HEAP GC=zgc JFLAGS="-Devictbudget=$BUDGET" sh java/stress/soak.sh "$NAME" $PROPS) \
    > "$OUT/$NAME-soak-sh.txt" 2>&1
rc=$?
for f in source.txt stdout.txt; do
    [ -f "$RUN/$f" ] && cp "$RUN/$f" "$OUT/$NAME-$f"
done
python3 "$NIGHT/soaksum.py" "$RUN" "$OUT/$NAME" > "$OUT/$NAME-report.txt" 2>&1
res=$(grep -E '^(SOAK OK|SOAK FAILED|FAILURE)' "$OUT/$NAME-soak-sh.txt" | cut -c1-200 | tr '\n' ' ')
cuts=$(grep -E '^  the cut at' "$OUT/$NAME-report.txt" | sed 's/^  the cut at //' | tr '\n' ' ')
if [ $rc = 0 ]; then st="needs a look"; else st=FAILED; fi
finish "$st" "P4's soak under ZGC on HEAD, exit $rc: ${res:-no result} The cuts: ${cuts:-none seen}. The GC log is in $RUN."
exit $rc
