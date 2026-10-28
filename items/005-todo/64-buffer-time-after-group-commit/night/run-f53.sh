#!/bin/sh
# minutes: 90
# bergdb 005-64, the buffer time after group commit: the timed runs on F53, for 006-10's quiet
# block (questions 1 to 3). Written 2026-10-28 by Claude (Opus 5.5, Claude Code).
#
# One preserved build (default main-bf9fc7f, main's HEAD of 2026-10-28 before 007-07, in
# CLONE/java/build/perf/builds/), the buffer times 20, 50 and 100 ms in turns: ROUNDS rounds of
# rounds.sh (each: bufftime.suite through performance.sh reference with RUNS=1 and the CPU
# agent, then MixedProbe for each configuration of mixed.txt; the order of the buffer times
# rotated round by round). 005-13's force probe before and after. About 8 minutes a round (an
# estimate from the phases of 005-13's runs: some 5 minutes for the suite's 18 runs, 3 for the
# 9 probe runs), so ROUNDS=9 (three whole rotations) takes about 75 minutes; no round starts
# that would end more than BUDGET minutes after this script started (the mean round so far),
# so the step stays inside its 90 minutes. Then tools/table.py makes OUT/table.md,
# and its check (every scenario and configuration at each buffer time, every cell parsed)
# OUT/check.txt.
#
# Quiet: the conductor has checked the machine and sets FORCE=1, which goes to performance.sh
# (its own check, 90 % idle CPU, then only warns). Without FORCE=1, performance.sh's check
# applies. Beyond that, the script only waits up to 15 minutes for other BergDB processes
# (gates, level scripts, performance runs, Lean, BergDB JVMs), then exits 2.
#
# Usage: sh run-f53.sh           the runs
#        SMOKE=1 sh run-f53.sh   a smoke test: smoke.suite and smoke-mixed.txt, 2 rounds, no
#                                cooldown, no wait, FORCE=1, a short force probe; 2 minutes
# Prepared by prepare.sh (the harness in the build, the tools); compiles nothing.
# Environment:
#   CLONE     the clone with the build and performance.sh (default /Users/f/fl/bench/006-10/w3)
#   BUILD     the preserved build (default main-bf9fc7f)
#   ROUNDS    (default 9; 2 for SMOKE=1)      BUDGET  minutes for the rounds (default 84)
#   OUT       the results (default /Users/f/fl/bench/006-10/night/out/64-f53, -smoke for SMOKE=1);
#             an OUT with earlier results is renamed OUT-HHMMSS first (SMOKE=1: removed)
#   FORCE, COOLDOWN (default 5), HEAP (default 8g), JAVA_HOME (default /opt/homebrew/opt/openjdk)
# Writes OUT/: log.txt; forceprobe-before.txt, forceprobe-after.txt; rounds/ and mixed/
# (rounds.sh); table.md; check.txt. The sessions stay in CLONE/java/build/perf/runs/.
# Exit code: 0 done and every row parsed; 1 a run failed, something is missing, or the check
# failed; 2 not quiet.

set -u
START=$(date +%s)
SMOKE=${SMOKE:-0}
T=$(cd "$(dirname "$0")" && pwd)
ITEM=$(dirname "$T")
CLONE=${CLONE:-/Users/f/fl/bench/006-10/w3}
BUILD=${BUILD:-main-bf9fc7f}
JAVA_HOME=${JAVA_HOME:-/opt/homebrew/opt/openjdk}
TOOLS=$CLONE/java/build/perf/005-64-tools
FORCE=${FORCE:-0}
HEAP=${HEAP:-8g}
if [ "$SMOKE" = 1 ]; then
    SUITEF=$T/smoke.suite; MIXEDF=$T/smoke-mixed.txt; ROUNDS=${ROUNDS:-2}; PROBE=10
    OUT=${OUT:-/Users/f/fl/bench/006-10/night/out/64-f53-smoke}; COOLDOWN=0; FORCE=1; BUDGET=${BUDGET:-0}
    rm -rf "$OUT"
else
    SUITEF=$T/bufftime.suite; MIXEDF=$T/mixed.txt; ROUNDS=${ROUNDS:-9}; PROBE=200
    OUT=${OUT:-/Users/f/fl/bench/006-10/night/out/64-f53}; COOLDOWN=${COOLDOWN:-5}; BUDGET=${BUDGET:-84}
    [ -d "$OUT" ] && [ -n "$(ls -A "$OUT")" ] && mv "$OUT" "$OUT-$(date +%H%M%S)"
fi
DEADLINE=0
[ "$BUDGET" -gt 0 ] && DEADLINE=$((START + BUDGET * 60))
export JAVA_HOME FORCE COOLDOWN HEAP
JAR=$CLONE/java/build/perf/builds/$BUILD/java/build/bergdb.jar

mkdir -p "$OUT"
log() { echo "$(date '+%H:%M:%S') $*" | tee -a "$OUT/log.txt"; }
[ -f "$JAR" ] || { log "no build $JAR"; exit 1; }
[ -f "$TOOLS/classes/ForceProbe.class" ] || { log "no tools in $TOOLS: sh prepare.sh"; exit 1; }

# Other BergDB work: gates, level scripts, night runs, performance runs, Lean, and JVMs of
# BergDB (VS Code's Java language server is not one).
others() {
    ps -axo pid,command | grep -E 'level[1-4]\.sh|night\.sh|before-commit\.sh|performance\.sh|lake build|/lake |bergdb\.(dev|core)\.|bergdb\.jar' \
        | grep -v grep || true
}
if [ "$SMOKE" != 1 ]; then
    i=0
    while [ -n "$(others)" ]; do
        if [ $i -ge 15 ]; then
            log "not quiet after 15 minutes, stopped:"
            others | cut -c1-160 | tee -a "$OUT/log.txt"
            exit 2
        fi
        [ $i = 0 ] && { log "waiting for:"; others | cut -c1-160 | tee -a "$OUT/log.txt"; }
        sleep 60
        i=$((i + 1))
    done
fi

# 005-13's force probe: what one force of an append costs here, the floor of a sync.
probe() {
    log "force probe $1"
    "$JAVA_HOME/bin/java" -cp "$JAR:$TOOLS/classes" ForceProbe "$CLONE/java/build/perf/data/005-64-forceprobe" $PROBE \
        > "$OUT/forceprobe-$1.txt" 2>&1
    rm -rf "$CLONE/java/build/perf/data/005-64-forceprobe"
}

log "start: $BUILD in $CLONE, $(basename "$SUITEF") and $(basename "$MIXEDF"), ROUNDS=$ROUNDS, FORCE=$FORCE, budget ${BUDGET} min"
probe before
JAVADIR=$CLONE/java BUILD=$BUILD SUITEF=$SUITEF MIXEDF=$MIXEDF ROUNDS=$ROUNDS OUT=$OUT TOOLS=$TOOLS \
    DEADLINE=$DEADLINE sh "$T/rounds.sh"
rc=$?
probe after

python3 -I "$ITEM/tools/table.py" "$OUT" > "$OUT/table.md" 2>&1
python3 -I "$ITEM/tools/table.py" --check "$SUITEF" "$MIXEDF" "$OUT" > "$OUT/check.txt" 2>&1
crc=$?
log "$(tail -n 1 "$OUT/check.txt")"
[ $rc = 2 ] && exit 2
if [ $rc != 0 ] || [ $crc != 0 ]; then
    log "FAILED: rounds exit $rc, check exit $crc; see log.txt and check.txt"
    exit 1
fi
log "DONE in $(( ($(date +%s) - START) / 60 )) min: $OUT/table.md"
exit 0
