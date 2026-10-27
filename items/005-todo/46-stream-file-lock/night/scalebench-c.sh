#!/bin/sh
# minutes: 65
# bergdb 005-46, W1.4 of 006-09: 009-03's ScaleBench block from the OS's cache (C), HEAD's
# prebuilt jar against bf19075's (005-50, just before 005-46), in turns: no fewer reads a
# second. As 009-03's f53-009.sh: 10M key24 keys, the default startup distance (10 MB, as
# 004-02 and 009-03), the phases warm, uniform, hot and threads (1, 2, 4, 8); C at 665 MB with
# G1 and with ZGC, and at 133 MB with G1; 004-02's sb.sh runs each JVM, ScaleBench with
# 009-03's port. One database, loaded by HEAD's jar with no get phases (both jars read it:
# both have 005-50's node size); then two rounds, each configuration once for each jar a
# round, the jars' order reversed in the second (ABBA). About 48 minutes (the load 3, then 12
# runs of 3.3 to 4.3); a run that would start with less than 6 minutes left is skipped, and
# the step is stopped at 65. Written 2026-10-27 by Claude (Opus 5.5, Claude Code); README.md.
# Usage: sh scalebench-c.sh, from any directory (SMOKE=1: 20,000 keys and short phases,
# outputs in /Users/f/fl/bench/006-09/w1/smoke). Needs prep.sh's clones and sb/.
# Outputs: night/out/scalebench-c/ (NAME.txt, NAME.json, sb.sh's runs.txt); the GC logs in
# /Users/f/fl/bench/006-09/w1/raw/scalebench-c; start and end in night/out/runs.txt.
# Exit status: 0 if the load and all 12 runs ended with SCALEBENCH OK.
STEP=scalebench-c
. /Users/f/fl/repos/bergdb/items/005-todo/46-stream-file-lock/night/lib.sh

if [ -n "$MODE" ]; then
    KEYS=20000; KN=20k; THREADS=1,2; SAMPLED=2; LOADHEAP=1g; MINRUN=0
    EXTRA="-Dsb.window=0.2 -Dsb.timedgets=2000 -Dsb.timedsec=1 -Dsb.threadsec=1 -Dsb.samplesec=1 -Dsb.warmmax=3"
else
    KEYS=10000000; KN=10m; THREADS=1,2,4,8; SAMPLED=4; LOADHEAP=6g; MINRUN=360
    EXTRA=
fi
SBSH=$B/head/items/004-indirect-swizzling/02-scale-tests/sb.sh
for j in head bf19075; do
    need "$B/$j/java/build/bergdb.jar"
    need "$B/sb/classes-$j/bergdb/core/ScaleBench.class"
done
need "$B/sb/pidio"
need "$SBSH"
need "$JAVA"
DATA=$B/sbdata
PIDIO=$B/sb/pidio
. "$SBSH"       # sb_load and sb_get; they write OUT/NAME.txt, .json and .gc.log, and OUT/runs.txt
watch "sb.out=$OUT/"
log "start$MODE: $KN key24 keys, C at 665 MB (G1, ZGC) and 133 MB (G1), 2 rounds in turns; deadline in $MINUTES min"
jarinfo head
jarinfo bf19075
quiet
bad=0
rm -rf "$DATA"
mkdir -p "$DATA"
CP=$B/sb/classes-head:$B/head/java/build/bergdb.jar
name=f53-l-$KN-head
if (SBFLAGS="-XX:+UseG1GC $EXTRA"; sb_load $name key24 $KEYS $LOADHEAP 0 ""); then
    log "  $(grep -o 'load done.*' "$OUT/$name.txt" | cut -c1-200)"
else
    log "  FAILED: the load ($name.txt)"
    bad=13
fi
mv "$OUT/$name.gc.log" "$RAW/" 2>/dev/null
r=1
while [ $bad -lt 13 ] && [ $r -le 2 ]; do
    if [ $r = 1 ]; then order="bf19075 head"; else order="head bf19075"; fi
    for cfg in b665-g1 b665-zgc b133-g1; do
        case $cfg in
            b665-g1) gc=-XX:+UseG1GC; heap=2660m; budget=665000000 ;;
            b665-zgc) gc=-XX:+UseZGC; heap=2660m; budget=665000000 ;;
            b133-g1) gc=-XX:+UseG1GC; heap=600m; budget=133000000 ;;
        esac
        for j in $order; do
            name=f53-c-$KN-$cfg-$j-$r
            if [ "$(left)" -le $MINRUN ]; then
                log "  skipped $name: $(left) s to the deadline"
                bad=$((bad + 1))
                continue
            fi
            CP=$B/sb/classes-$j:$B/$j/java/build/bergdb.jar
            if (SBFLAGS="$gc $EXTRA"; sb_get $name key24 $KEYS $heap $budget C warm,uniform,hot,threads); then
                log "  $name: uniform 1 thread $(sed -n 's/.*uniform, 1 thread: \([0-9]*\) gets a second.*/\1/p' "$OUT/$name.txt");" \
                    "threads $THREADS: $(sed -n 's/.*threads [0-9]*: \([0-9]*\) gets a second.*/\1/p' "$OUT/$name.txt" | tr '\n' ' ')"
            else
                log "  FAILED: $name"
                bad=$((bad + 1))
            fi
            mv "$OUT/$name.gc.log" "$RAW/" 2>/dev/null
        done
    done
    r=$((r + 1))
done
rm -rf "$DATA"
if [ $bad = 0 ]; then st="needs a look"; else st=FAILED; fi
python3 "$NIGHT/nightsum.py" "$OUTROOT" > "$OUTROOT/summary.txt" 2>&1
sum=$(grep -E '^(## |HEAD against)' "$OUTROOT/summary.txt" | sed 's/^## //; s/HEAD against bf19075, gets a second: /HEAD: /' | tr '\n' ' ' | cut -c1-400)
finish "$st" "ScaleBench C at $KN keys, HEAD against bf19075 in turns, $bad of 13 runs failed or skipped. $sum"
[ $bad = 0 ]
