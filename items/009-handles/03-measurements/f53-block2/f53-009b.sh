#!/bin/sh
# F53's second timed block of bergdb item 009, phase 5 (009-03, section 8): ScaleBench
# under generational Shenandoah for 2026.1's jar and the branch's (M; C at 133 and 665 MB),
# as 004-04's run2.sh; then P4's soak with eviction on the branch under ZGC and Shenandoah,
# with 004-04's parameters (8 GB heap, a 1.6 GB budget, 30 measured minutes, one restart);
# 2026.1's soaks are 004-04's; and performance.sh's quick suite, 2026.1 against the branch
# (ab). Usage: sh f53-009b.sh DIR WORKTREE (DIR as f53-009.sh's;
# WORKTREE the branch's worktree, built: soak.sh copies its build).
D=$1
W=$2
OUT=$D/out2
export JAVA_HOME=/opt/homebrew/opt/openjdk
JAVA=$JAVA_HOME/bin/java
mkdir -p "$OUT"
caffeinate -i -s &
CAF=$!
log() { echo "$(date '+%F %T') $*" >> "$OUT/runs.txt"; }

QUIETLOAD=2.0 sh "$D/quiet.sh" 32b68478-35b0-4112-9d94-6ddb9ecd9df2 200 >> "$OUT/runs.txt"
log "block start, $(uptime | sed 's/.*load/load/')"

SHEN="-XX:+UseShenandoahGC -XX:ShenandoahGCMode=generational"
DATA=$D/sbdata
THREADS=1,2,4,8
SAMPLED=4
PIDIO=$D/pidio
. "$D/sb.sh"
P=warm,uniform,hot,threads
for j in 2026.1 009; do
    CP=$D/classes-$j:$D/jar-$j.jar
    mkdir -p "$DATA"
    ( SBFLAGS=$SHEN; sb_load f53-m-10m-shen-$j key24 10000000 6g 0 $P
      SBFLAGS=$SHEN; sb_get f53-c-10m-b133-shen-$j key24 10000000 600m 133000000 C $P
      SBFLAGS=$SHEN; sb_get f53-c-10m-b665-shen-$j key24 10000000 2660m 665000000 C $P ) \
        || log "scalebench shen $j FAILED"
    rm -rf "$DATA"
done

soak() {    # soak zgc|shen
    if [ $1 = zgc ]; then g=zgc; jf=-Devictbudget=1600000000
    else g=g1; jf="-XX:-UseG1GC $SHEN -Devictbudget=1600000000"; fi
    log "start soak p4-009-$1"
    if (cd "$W" && HEAP=8g GC=$g JFLAGS="$jf" sh java/stress/soak.sh p4-009-$1 rate=200 \
            warmup=300 warmupmax=3600 measure=1800 restarts=1 mincuts=2 extend=900) \
            >> "$OUT/runs.txt" 2>&1; then
        log "ok soak p4-009-$1"
    else
        log "FAILED soak p4-009-$1"
    fi
}
soak zgc
# performance.sh's quick suite, 2026.1's preserved build against the branch's working tree,
# in turns (ABBA); the 2026.1 build is java/build/perf/builds/2026.1 of the worktree.
log "start performance.sh ab quick"
(cd "$W" && SUITE=quick sh java/stress/performance.sh ab 2026.1 current) > "$OUT/perf-ab.txt" 2>&1
log "performance.sh ab quick: exit $? ($(tail -1 "$OUT/perf-ab.txt" | cut -c1-200))"
# As WP J10 (docs/level4-performance.md): again with eviction on and a budget larger than
# the data, 4 GB.
log "start performance.sh ab quick, budget 4 GB"
(cd "$W" && SUITE=quick JFLAGS=-Devictbudget=4000000000 sh java/stress/performance.sh ab 2026.1 current) \
    > "$OUT/perf-ab-4g.txt" 2>&1
log "performance.sh ab quick, budget 4 GB: exit $? ($(tail -1 "$OUT/perf-ab-4g.txt" | cut -c1-200))"
soak shen
kill $CAF
log "F53 009 BLOCK 2 DONE"
