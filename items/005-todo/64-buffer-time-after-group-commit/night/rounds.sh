#!/bin/sh
# bergdb 005-64: the rounds of run-f53.sh and s1-runner.sh (one script for both machines).
# Written 2026-10-28 by Claude (Opus 5.5, Claude Code).
#
# Round r (1 to ROUNDS) runs, on one preserved build:
#   1. the suite SUITEF with performance.sh reference, RUNS=1, and the CPU agent (JFLAGS=
#      -javaagent:TOOLS/cpu64.jar, tools/CpuAgent.java); the three buffer times of each
#      scenario next to each other, in the order 20 50 100, then 50 100 20, then 100 20 50
#      (rotated round by round, so that a drift of the machine hits each buffer time alike);
#   2. MixedProbe (tools/) for each configuration of MIXEDF at the three buffer times, in the
#      same rotated order, one JVM each, with the flags of a Perf run (G1, -da, HEAP).
# No round starts unless it would end, at the mean length of the rounds so far, before
# DEADLINE (epoch seconds; 0: no deadline). It compiles nothing: the build's harness, the
# probe classes and the agent are made by prepare.sh.
#
# Environment (all set by the caller):
#   JAVADIR   the java/ directory whose stress/performance.sh runs (a clone, or s1's package)
#   BUILD     a preserved build in JAVADIR/build/perf/builds/
#   SUITEF, MIXEDF, ROUNDS, OUT, TOOLS (classes/ and cpu64.jar), HEAP, DEADLINE
#   COOLDOWN (seconds between runs, also between probe runs), FORCE, JAVA_HOME
# Writes OUT/: log.txt (appends); rounds/rN.txt (performance.sh's output), rounds/rN/SCENARIO/
# run1/ (write.result.json, write.stdout.txt, load-*.txt), rounds/rN-summary.txt;
# mixed/rN-CONFIG-bBT.txt (the probe's output).
# Exit code: 0 done; 1 a run failed or something is missing; 2 performance.sh found the
# machine not quiet.

set -u
: "${JAVADIR:?}" "${BUILD:?}" "${SUITEF:?}" "${MIXEDF:?}" "${ROUNDS:?}" "${OUT:?}" "${TOOLS:?}"
HEAP=${HEAP:-8g}
DEADLINE=${DEADLINE:-0}
COOLDOWN=${COOLDOWN:-5}
FORCE=${FORCE:-0}
export JAVA_HOME COOLDOWN FORCE HEAP
JAVA=$JAVA_HOME/bin/java
JAR=$JAVADIR/build/perf/builds/$BUILD/java/build/bergdb.jar
DATA=$JAVADIR/build/perf/data
mkdir -p "$OUT/rounds" "$OUT/mixed" "$DATA"
log() { echo "$(date '+%H:%M:%S') $*" | tee -a "$OUT/log.txt"; }

[ -f "$JAR" ] || { log "no build $JAR"; exit 1; }
[ -f "$TOOLS/cpu64.jar" ] && [ -f "$TOOLS/classes/MixedProbe.class" ] || { log "no tools in $TOOLS: prepare.sh"; exit 1; }

# order R: the buffer times of round R.
order() {
    case $(( ($1 - 1) % 3 )) in
        0) echo "20 50 100" ;;
        1) echo "50 100 20" ;;
        2) echo "100 20 50" ;;
    esac
}

# round_suite ORDER: SUITEF's scenario lines, each scenario's buffer times (the -bN suffix)
# in ORDER, the scenarios in the file's order.
round_suite() {
    awk -v order="$1" '
        BEGIN { n = split(order, o, " ") }
        /^[[:space:]]*(#|$)/ { next }
        {
            base = $1; sub(/-b[0-9]+$/, "", base)
            bt = $1; sub(/.*-b/, "", bt)
            if (!(base in seen)) { seen[base] = 1; groups[++g] = base }
            line[base, bt] = $0
        }
        END { for (i = 1; i <= g; i++) for (j = 1; j <= n; j++) if ((groups[i], o[j]) in line) print line[groups[i], o[j]] }
    ' "$SUITEF"
}

rc=0
t_first=$(date +%s)
r=1
while [ "$r" -le "$ROUNDS" ]; do
    now=$(date +%s)
    if [ "$r" -gt 1 ] && [ "$DEADLINE" -gt 0 ]; then
        mean=$(( (now - t_first) / (r - 1) ))
        if [ $(( now + mean )) -gt "$DEADLINE" ]; then
            log "round $r not started: it would end after the deadline (rounds of about $((mean / 60)) min)"
            break
        fi
    fi
    ord=$(order "$r")
    log "round $r of $ROUNDS, buffer times in the order $ord"

    # 1. The suite. The round's suite goes beside performance.sh's java/, so that the session
    # name stays short; removed after the round.
    rs=b64-r$r.suite
    round_suite "$ord" > "$JAVADIR/$rs"
    (cd "$JAVADIR" && RUNS=1 BUILD=$BUILD SUITE=$rs JFLAGS="-javaagent:$TOOLS/cpu64.jar" \
        sh stress/performance.sh reference "r$r") > "$OUT/rounds/r$r.txt" 2>&1
    prc=$?
    rm -f "$JAVADIR/$rs"
    grep -m1 'CPU idle before' "$OUT/rounds/r$r.txt" | sed 's/^/    /' | tee -a "$OUT/log.txt"
    if grep -q 'machine is not quiet.*stop other jobs' "$OUT/rounds/r$r.txt"; then
        log "performance.sh found the machine not quiet; stopped"
        exit 2
    fi
    s=$(sed -n 's/^PERFORMANCE RUN DONE: \(.*\) (summary.*/\1/p' "$OUT/rounds/r$r.txt")
    if [ $prc != 0 ] || [ -z "$s" ] || [ ! -d "$s" ]; then
        log "round $r: performance.sh failed (exit $prc), see rounds/r$r.txt; stopped"
        tail -n 5 "$OUT/rounds/r$r.txt" | tee -a "$OUT/log.txt"
        rc=1
        break
    fi
    mkdir -p "$OUT/rounds/r$r"
    cp "$s/session.json" "$s/machine.txt" "$OUT/rounds/r$r/" 2>/dev/null
    cp "$s/summary.txt" "$OUT/rounds/r$r-summary.txt" 2>/dev/null
    (cd "$s" && find . -name 'write.result.json' -o -name 'write.stdout.txt' -o -name 'load-*.txt') |
    while read -r f; do
        mkdir -p "$OUT/rounds/r$r/$(dirname "$f")"
        cp "$s/$f" "$OUT/rounds/r$r/$f"
    done

    # 2. The mixed writers.
    grep -v -E '^[[:space:]]*(#|$)' "$MIXEDF" | while read -r name st sr pt pr vs sec wu; do
        for bt in $ord; do
            o=$OUT/mixed/r$r-$name-b$bt.txt
            d=$DATA/005-64-mixed-r$r-$name-b$bt
            rm -rf "$d"
            "$JAVA" -XX:+UseG1GC -da "-Xms$HEAP" "-Xmx$HEAP" -cp "$JAR:$TOOLS/classes" \
                MixedProbe "$d" "$bt" "$st" "$sr" "$pt" "$pr" "$vs" "$sec" "$wu" > "$o" 2>&1
            prc=$?
            rm -rf "$d"
            if [ $prc != 0 ] || ! grep -q '^MIXED OK' "$o"; then
                log "round $r: MixedProbe $name at $bt ms failed (exit $prc), see mixed/$(basename "$o")"
                tail -n 5 "$o" | tee -a "$OUT/log.txt"
                exit 1      # Ends the pipeline's subshell; checked below.
            fi
            echo "    $name b$bt: $(sed -n 's/^MIXED //p' "$o" | tr ' ' '\n' | grep -E '^(sync_p50_ms|sync_commits_per_s|plain_puts_per_s|forces_per_s)=' | tr '\n' ' ')" |
                tee -a "$OUT/log.txt"
            if [ "$COOLDOWN" -gt 0 ]; then sleep "$COOLDOWN"; fi
        done
    done
    [ $? = 0 ] || { rc=1; break; }
    log "round $r done ($(( ($(date +%s) - now) / 60 )) min)"
    r=$((r + 1))
done
log "rounds done: $((r - 1)) of $ROUNDS, exit $rc"
exit $rc
