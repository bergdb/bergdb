#!/bin/sh
# minutes: 60
# bergdb 005-48, group commit: the timed runs on F53, for the quiet block of 006-09. Written
# 2026-10-27 by Claude (Opus 5.5, Claude Code).
#
# HEAD and the prototype in turns: performance.sh ab, ABBA order run by run, so that a drift of
# the machine hits both; group-commit.suite (005-13's scenarios at 20 ms), RUNS runs of each
# build per scenario; 005-13's force probe before and after. About 40 minutes with RUNS=10.
# Needs a quiet F53: no other JVM of BergDB, build, gate or Lean, and the Claude sessions idle.
# The script waits up to 15 minutes for other BergDB processes to end, then gives up (exit 2);
# performance.sh itself refuses to start under 90 % idle CPU. Uses only what "prepare" made:
# the two preserved builds with their harness compiled, and ForceProbe's class; it compiles
# nothing.
#
# Usage: sh run-f53.sh prepare   compiles ForceProbe and the harness ahead (done 2026-10-27)
#        sh run-f53.sh           the runs
#        SMOKE=1 sh run-f53.sh   a smoke test of this script: smoke.suite, 2 runs, no cooldown,
#                                no quiet check, a short force probe; about a minute
# Environment:
#   CLONE        the clone with the preserved builds (default /Users/f/fl/bench/006-09/gc48);
#                its java/stress/performance.sh runs them
#   HEAD_BUILD, PROTO_BUILD   directories of CLONE/java/build/perf/builds/, made by
#                performance.sh build (defaults below)
#   RUNS         runs of each build per scenario (default 10; even, for whole ABBA blocks)
#   OUT          the results (default out/f53 beside this script, out/f53-smoke for SMOKE=1)
#   JAVA_HOME    default /opt/homebrew/opt/openjdk
# Writes OUT/: log.txt; ab.txt, performance.sh's output; compare-with-ref.txt, its comparison
# (alerts are expected: the durable scenarios change); forceprobe-before.txt and -after.txt;
# summary-ref.txt (HEAD) and summary-cand.txt (the prototype); table.md (tools/table.py); ref/
# and cand/, each session's session.json, machine.txt and every run's write.result.json,
# write.stdout.txt and load-*.txt. The sessions stay in CLONE/java/build/perf/runs/.
# Exit code: 0 done; 1 a run failed, or something is missing; 2 not quiet.

set -u
SMOKE=${SMOKE:-0}
T=$(cd "$(dirname "$0")" && pwd)
ITEM=$(dirname "$T")
CLONE=${CLONE:-/Users/f/fl/bench/006-09/gc48}
HEAD_BUILD=${HEAD_BUILD:-head-e718347}
PROTO_BUILD=${PROTO_BUILD:-proto-e718347}
JAVA_HOME=${JAVA_HOME:-/opt/homebrew/opt/openjdk}
export JAVA_HOME
if [ "$SMOKE" = 1 ]; then
    SUITEF=$T/smoke.suite; RUNS=${RUNS:-2}; OUT=${OUT:-$T/out/f53-smoke}; PROBE=10
    COOLDOWN=0; FORCE=1; export COOLDOWN FORCE
else
    SUITEF=$T/group-commit.suite; RUNS=${RUNS:-10}; OUT=${OUT:-$T/out/f53}; PROBE=200
fi
BUILDS=$CLONE/java/build/perf/builds
HEADJAR=$BUILDS/$HEAD_BUILD/java/build/bergdb.jar
PC=$CLONE/java/build/perf/gc48-forceprobe     # ForceProbe's class, from prepare

if [ "${1:-}" = prepare ]; then
    rm -rf "$PC"
    mkdir -p "$PC/classes"
    "$JAVA_HOME/bin/javac" --release 17 -nowarn -cp "$HEADJAR" -d "$PC/classes" \
        "$ITEM/../13-buffer-time/tools/ForceProbe.java" || exit 1
    # The harness where performance.sh's prepare_target looks for it: harness- and the first
    # 12 hex digits of the SHA-256 of PerfUtil.java, Perf.java and PerfTool.java.
    S=$CLONE/java/stress
    H=harness-$(cd "$S" && cat PerfUtil.java Perf.java PerfTool.java | shasum -a 256 | cut -c1-12)
    for b in "$HEAD_BUILD" "$PROTO_BUILD"; do
        d=$BUILDS/$b
        [ -d "$d/$H" ] && continue
        mkdir -p "$d/$H.tmp"
        (cd "$S" && "$JAVA_HOME/bin/javac" --release 17 -Xlint:-options -encoding UTF-8 \
            -cp "$d/java/build/bergdb.jar" -d "$d/$H.tmp" PerfUtil.java Perf.java PerfTool.java) || exit 1
        mv "$d/$H.tmp" "$d/$H"
    done
    echo "prepared: $PC, $H in $HEAD_BUILD and $PROTO_BUILD"
    exit 0
fi

mkdir -p "$OUT"
log() { echo "$(date '+%H:%M:%S') $*" | tee -a "$OUT/log.txt"; }
for b in "$HEAD_BUILD" "$PROTO_BUILD"; do
    [ -f "$BUILDS/$b/java/build/bergdb.jar" ] || { log "no build $BUILDS/$b"; exit 1; }
done
[ -f "$PC/classes/ForceProbe.class" ] || { log "no ForceProbe class in $PC: sh run-f53.sh prepare"; exit 1; }

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
    "$JAVA_HOME/bin/java" -cp "$HEADJAR:$PC/classes" ForceProbe "$PC/data" $PROBE > "$OUT/forceprobe-$1.txt" 2>&1
    rm -rf "$PC/data"
}

# The suite goes beside performance.sh's java/, so that the session names stay short.
SUITE=gc48-$(basename "$SUITEF")
cp "$SUITEF" "$CLONE/java/$SUITE"

log "start: $HEAD_BUILD against $PROTO_BUILD, $(basename "$SUITEF"), RUNS=$RUNS, in $CLONE"
probe before
(cd "$CLONE/java" && RUNS=$RUNS SUITE=$SUITE sh stress/performance.sh ab "$HEAD_BUILD" "$PROTO_BUILD") \
    > "$OUT/ab.txt" 2>&1
rc=$?
log "performance.sh exit $rc: $(tail -n 1 "$OUT/ab.txt")"
probe after

if grep -q 'machine is not quiet.*stop other jobs' "$OUT/ab.txt"; then
    log "performance.sh found the machine not quiet"
    exit 2
fi
RUNSDIR=$CLONE/java/build/perf/runs
for tag in ref cand; do
    if [ $tag = ref ]; then sid=$(sed -n 's/^Reference session //p' "$OUT/ab.txt")
    else sid=$(sed -n 's/^Candidate session //p' "$OUT/ab.txt"); fi
    s=$RUNSDIR/$sid
    [ -n "$sid" ] && [ -d "$s" ] || { log "no session for $tag"; continue; }
    mkdir -p "$OUT/$tag"
    cp "$s/session.json" "$s/machine.txt" "$OUT/$tag/" 2>/dev/null
    [ -f "$s/compare-with-ref.txt" ] && cp "$s/compare-with-ref.txt" "$OUT/"
    (cd "$s" && find . -name 'write.result.json' -o -name 'write.stdout.txt' -o -name 'load-*.txt') |
    while read -r f; do
        mkdir -p "$OUT/$tag/$(dirname "$f")"
        cp "$s/$f" "$OUT/$tag/$f"
    done
    (cd "$CLONE/java" && BUILD=$HEAD_BUILD sh stress/performance.sh summary "$s") \
        > "$OUT/summary-$tag.txt" 2>&1
done
python3 -I "$ITEM/tools/table.py" "$OUT" > "$OUT/table.md" 2>&1
if grep -q '^FAILED' "$OUT/ab.txt" || [ ! -d "$OUT/cand" ]; then
    log "a run failed, see ab.txt"
    exit 1
fi
log "DONE: $OUT/table.md"
exit 0
