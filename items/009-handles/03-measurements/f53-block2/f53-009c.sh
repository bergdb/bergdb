#!/bin/sh
# One more timed run of bergdb item 009, phase 5 (009-03): P4's soak under generational
# Shenandoah with a 12 GB heap (soak.sh's default; P4 has 8 GB), after the 8 GB run had two
# degenerated cycles (821 and 182 ms) with the heap nearly full. Usage: sh f53-009c.sh DIR WORKTREE
D=$1
W=$2
OUT=$D/out2
caffeinate -i -s &
CAF=$!
log() { echo "$(date '+%F %T') $*" >> "$OUT/runs.txt"; }
QUIETLOAD=2.0 sh "$D/quiet.sh" 32b68478-35b0-4112-9d94-6ddb9ecd9df2 60 >> "$OUT/runs.txt"
SHEN="-XX:+UseShenandoahGC -XX:ShenandoahGCMode=generational"
log "start soak p4-009-shen-12g"
if (cd "$W" && HEAP=12g GC=g1 JFLAGS="-XX:-UseG1GC $SHEN -Devictbudget=1600000000" sh java/stress/soak.sh \
        p4-009-shen-12g rate=200 warmup=300 warmupmax=3600 measure=1800 restarts=1 mincuts=2 extend=900) \
        >> "$OUT/runs.txt" 2>&1; then
    log "ok soak p4-009-shen-12g"
else
    log "FAILED soak p4-009-shen-12g"
fi
kill $CAF
log "F53 009 BLOCK 3 DONE"
