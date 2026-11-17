#!/bin/sh
# minutes: 40
# bergdb 007-07, step 3 of 007-03 with D4:B: the quick performance suite on F53, main before
# 007-07 against the patched build, for a quiet block (013-01, section 7). Written 2026-10-28 by
# Claude (Opus 5.5, Claude Code).
#
# performance.sh ab REF CAND with SUITE=quick (performance-quick.suite: warm reads, updates with
# infinite and finite retention, restart), 3 runs of each build per scenario in ABBA order, run
# by run, so that a drift of the machine hits both; about 30 minutes. 007-03's step 3 asks for
# "the quick performance suite unchanged". FORCE=1: the conductor checks that the machine is
# quiet before the step, and performance.sh's own check (90 % idle CPU) refused a step that the
# conductor had found quiet (006-09; 013-01, section 9). The script uses only the two preserved
# builds made in the day, with the harness compiled in each (the smoke test did that); it
# compiles nothing.
#
# Usage: sh run-quick.sh           the runs
#        SMOKE=1 sh run-quick.sh   a smoke test of this script: the smoke suite, 1 run of each
#                                  build, no cooldown; about 2 minutes
# Environment:
#   CLONE       the clone whose java/stress/performance.sh runs and holds the builds (default
#               /Users/f/fl/bench/006-09/d2-007-07)
#   REF_BUILD   main before 007-07, a directory of CLONE/java/build/perf/builds/ (default below:
#               fb67f96, the base of 007-07's commits in CLONE)
#   CAND_BUILD  the patched build, the same (default below: b8ac8a1, 007-07's code commit)
#   OUT         the results (default out/quick beside this script, out/quick-smoke for SMOKE=1)
#   JAVA_HOME   default /opt/homebrew/opt/openjdk
# Writes OUT/: log.txt; ab.txt, performance.sh's output with the comparison of the candidate
# with the reference; summary-ref.txt and summary-cand.txt, the median, range and variation of
# each scenario. The sessions stay in CLONE/java/build/perf/runs/.
# Exit code: 0 the runs are done and compared (alerts, if any, are in ab.txt, to repeat in a
# matched run before calling them a regression); 1 a build is missing, a run failed, or the
# output is not complete.

set -u
SMOKE=${SMOKE:-0}
T=$(cd "$(dirname "$0")" && pwd)
CLONE=${CLONE:-/Users/f/fl/bench/006-09/d2-007-07}
REF_BUILD=${REF_BUILD:-main-cefb473}
CAND_BUILD=${CAND_BUILD:-d4b-f89846d}
JAVA_HOME=${JAVA_HOME:-/opt/homebrew/opt/openjdk}
FORCE=1
export JAVA_HOME FORCE
if [ "$SMOKE" = 1 ]; then
    SUITE=smoke; RUNS=1; COOLDOWN=0; OUT=${OUT:-$T/out/quick-smoke}; SCENARIOS=7
    export RUNS COOLDOWN
else
    SUITE=quick; OUT=${OUT:-$T/out/quick}; SCENARIOS=4
fi
export SUITE
BUILDS=$CLONE/java/build/perf/builds

mkdir -p "$OUT"
log() { echo "$(date '+%H:%M:%S') $*" | tee -a "$OUT/log.txt"; }
for b in "$REF_BUILD" "$CAND_BUILD"; do
    [ -f "$BUILDS/$b/java/build/bergdb.jar" ] && [ -f "$BUILDS/$b/identity.env" ] ||
        { log "no preserved build $BUILDS/$b"; exit 1; }
done

log "start: $REF_BUILD against $CAND_BUILD, SUITE=$SUITE, in $CLONE"
(cd "$CLONE/java" && sh stress/performance.sh ab "$REF_BUILD" "$CAND_BUILD") > "$OUT/ab.txt" 2>&1
rc=$?
log "performance.sh exit $rc: $(tail -n 1 "$OUT/ab.txt")"

# performance.sh exits 1 both for a failed run and for alerts; the comparison's last line says
# which (0: no alerts, 1: alerts, 3: incompatible, 4: failed or missing runs).
crc=$(sed -n 's/^Comparison exit code \([0-9]*\).*/\1/p' "$OUT/ab.txt")
if [ "$crc" != 0 ] && [ "$crc" != 1 ]; then
    log "the runs did not complete or were not compared (comparison exit code '${crc}'), see ab.txt"
    exit 1
fi

RUNSDIR=$CLONE/java/build/perf/runs
ok=1
for tag in ref cand; do
    if [ $tag = ref ]; then sid=$(sed -n 's/^Reference session //p' "$OUT/ab.txt")
    else sid=$(sed -n 's/^Candidate session //p' "$OUT/ab.txt"); fi
    s=$RUNSDIR/$sid
    if [ -z "$sid" ] || [ ! -d "$s" ]; then log "no session for $tag"; ok=0; continue; fi
    (cd "$CLONE/java" && BUILD=$REF_BUILD sh stress/performance.sh summary "$s") \
        > "$OUT/summary-$tag.txt" 2>&1
    # The summary has a header per scenario that ran: its name, then [mode, N runs, ...].
    n=$(grep -c -E '^[a-z][a-z0-9-]* +\[' "$OUT/summary-$tag.txt")
    if [ "$n" -lt "$SCENARIOS" ]; then
        log "summary-$tag.txt has $n scenarios, not $SCENARIOS"; ok=0
    fi
done
[ $ok = 1 ] || exit 1
log "DONE, comparison exit code $crc ($([ "$crc" = 0 ] && echo 'no alerts' || echo 'alerts, see ab.txt')): $OUT"
exit 0
