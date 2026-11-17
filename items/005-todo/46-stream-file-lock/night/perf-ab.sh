#!/bin/sh
# minutes: 40
# bergdb 009-01's "done" item 7 (006-09's quiet block): performance.sh ab with the quick suite,
# release 2026.1 against HEAD (f9e295d), without a budget, in turns (ABBA), G1, an 8 GB heap:
# the run that 009-03 could not make on 2026-10-26, as the machine was not quiet (its run with
# a 4 GB budget had one unconfirmed alert). If this comparison alerts, a second ab run, and a
# compare of the first reference with both candidate sessions, confirm or dismiss it
# (performance.sh: "Run it twice before calling an alert a regression"). About 14 minutes, 28
# with the second run; stopped at 40. Written 2026-10-27 by Claude (Opus 5.5, Claude Code).
# Usage: sh perf-ab.sh, from any directory (SMOKE=1: perf-ab-smoke.suite, FORCE=1, outputs in
# /Users/f/fl/bench/006-09/w1/smoke). Needs prep.sh's clone head/ with the preserved builds
# java/build/perf/builds/2026.1 (a copy of the 009 worktree's, of the release commit 8e579c6)
# and head-4f7cd60 (performance.sh build), their harness compiled by the smoke test.
# Outputs: night/out/perf-ab/ (ab-1.txt, ab-2.txt, confirm.txt, the sessions' summaries); the
# sessions with their raw logs stay in the clone, java/build/perf/runs/. Exit status: 0 when
# the runs and the comparison are complete, alerts or not (they are in the outputs);
# otherwise performance.sh's.
STEP=perf-ab
. /Users/f/fl/repos/bergdb/items/005-todo/46-stream-file-lock/night/lib.sh

H=$B/head
REF=2026.1
CAND=head-4f7cd60
RUNS=$H/java/build/perf/runs
if [ -n "$MODE" ]; then
    export SUITE=$NIGHT/perf-ab-smoke.suite FORCE=1 COOLDOWN=1
else
    export SUITE=quick
fi
need "$H/java/build/perf/builds/$REF/java/build/bergdb.jar"
need "$H/java/build/perf/builds/$CAND/java/build/bergdb.jar"
need "$H/java/stress/performance.sh"
need "$JAVA"
watch "$H/java/build/perf/"
log "start$MODE: performance.sh ab $REF $CAND, suite $SUITE, G1, 8 GB heap, no budget; deadline in $MINUTES min"
jarinfo head
quiet

perf() { (cd "$H" && BUILD=$CAND sh java/stress/performance.sh "$@"); }
ab() {          # ab N: one ab run into OUT/ab-N.txt; three tries if not quiet, then FORCE=1
    t=1
    while :; do
        perf ab $REF $CAND > "$OUT/ab-$1.txt" 2>&1
        rc=$?
        grep -q "^performance.sh: the machine is not quiet" "$OUT/ab-$1.txt" || break
        if [ $t -ge 3 ]; then
            log "  ab $1: still not quiet, so FORCE=1 (the results are then not a reference)"
            FORCE=1 perf ab $REF $CAND > "$OUT/ab-$1.txt" 2>&1
            rc=$?
            break
        fi
        log "  ab $1: not quiet ($(grep -o '[0-9.]*% idle' "$OUT/ab-$1.txt" | head -n 1)), again in 60 s"
        t=$((t + 1))
        sleep 60
    done
    log "  ab $1: exit $rc; $(grep -E 'ALERT|Comparison exit' "$OUT/ab-$1.txt" | sed 's/  */ /g' | tr '\n' ';' | cut -c1-300)"
    return $rc
}
sid() { sed -n "s/^$1 session //p" "$OUT/ab-$2.txt" | head -n 1; }    # sid Reference|Candidate N

ab 1
rc=$?
n=1
if [ $rc = 1 ] || [ "${AB2:-0}" = 1 ]; then      # AB2=1: the second run in any case (a test)
    ab 2
    rc2=$?
    n=2
    perf compare "$RUNS/$(sid Reference 1)" "$RUNS/$(sid Candidate 1)" "$RUNS/$(sid Candidate 2)" \
        > "$OUT/confirm.txt" 2>&1
    log "  confirm: $(grep -E 'CONFIRMED|NOT REPEATED' "$OUT/confirm.txt" | sed 's/  */ /g' | tr '\n' ';' | cut -c1-300)"
    [ $rc2 -le 1 ] || rc=$rc2
fi
k=1
while [ $k -le $n ]; do
    for t in Reference Candidate; do
        s=$(sid $t $k)
        [ -n "$s" ] && perf summary "$RUNS/$s" > "$OUT/summary-$k-$t.txt" 2>&1
    done
    k=$((k + 1))
done
alerts=$(grep -c 'ALERT (' "$OUT/ab-1.txt")
conf=$(grep -c '^ *CONFIRMED' "$OUT/confirm.txt" 2>/dev/null)
if [ $rc -le 1 ]; then st="needs a look"; ec=0; else st=FAILED; ec=$rc; fi
finish "$st" "performance.sh ab, $SUITE suite, 2026.1 against HEAD: $n run(s), exit $rc; alerts in the first: $alerts${conf:+, confirmed by the second: $conf}. Sessions in $RUNS."
exit $ec
