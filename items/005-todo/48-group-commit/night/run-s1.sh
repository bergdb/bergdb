#!/bin/sh
# minutes: 90
# bergdb 005-48, group commit: the timed runs on s1 (Hostup VPS: 2 vCPUs, 3.8 GB, a virtual
# disk; B056 in sk26), as run-f53.sh: HEAD and the prototype in turns (performance.sh ab,
# ABBA), group-commit.suite, RUNS runs of each build per scenario (default 6), a heap of 1 GB,
# the force probe before and after. About 40 minutes (an estimate: about 1.4 times F53's time
# a run). Written 2026-10-27 by Claude (Opus 5.5, Claude Code).
#
# "prepare" makes the package here, by day: performance.sh, the harness and both suites from
# CLONE; the two preserved builds' jars with the harness compiled, so that s1 needs no javac;
# ForceProbe's class; s1-runner.sh. The run does no build or other work here beyond ssh: it
# waits until s1 is idle (no JVM, a load under 1; up to 20 minutes, then exit 2), copies the
# package to s1:REMOTE (tar over ssh), starts s1-runner.sh there in the background (nohup: a dropped
# connection does not stop it), waits for it with one ssh a minute, and fetches its results.
# Other sessions time on s1 too (005-57's cold starts).
#
# Usage: sh run-s1.sh prepare    makes the package (done 2026-10-27)
#        sh run-s1.sh            copy, start, wait, fetch
#        sh run-s1.sh fetch      fetch only, when the wait was interrupted (the runner goes on)
#        SMOKE=1 sh run-s1.sh    a smoke test here, not on s1: the package in a local
#                                directory, smoke.suite, 2 runs, no checks; about a minute
# Environment: CLONE, HEAD_BUILD, PROTO_BUILD as for run-f53.sh; RUNS; HOST (default
#   root@s1); REMOTE (default /opt/bergdb-bench/005-48); S1JAVA (default
#   /opt/bergdb-bench/jdk-27); OUT (default out/s1 beside this script, out/s1-smoke for
#   SMOKE=1); JAVA_HOME here, for prepare (default /opt/homebrew/opt/openjdk).
# Writes OUT/: log.txt, and the runner's results (s1-runner.sh). The table, in the morning:
#   python3 -I ../tools/table.py OUT > OUT/table.md
# Exit code: the runner's (0 done, 1 a run failed, 2 another JVM ran or not quiet); 1 if the
# package is missing, the copy or the start failed, or the runner was not done after 4 hours;
# 2 if s1 was not idle.

set -u
SMOKE=${SMOKE:-0}
T=$(cd "$(dirname "$0")" && pwd)
ITEM=$(dirname "$T")
CLONE=${CLONE:-/Users/f/fl/bench/006-09/gc48}
HEAD_BUILD=${HEAD_BUILD:-head-e718347}
PROTO_BUILD=${PROTO_BUILD:-proto-e718347}
HOST=${HOST:-root@s1}
LJAVA=${JAVA_HOME:-/opt/homebrew/opt/openjdk}
P=$CLONE/java/build/perf/gc48-s1-package       # from prepare
if [ "$SMOKE" = 1 ]; then
    SUITE=gc48-smoke.suite; RUNS=${RUNS:-2}; OUT=${OUT:-$T/out/s1-smoke}; PROBE=10; POLL=5
    REMOTE=$CLONE/java/build/perf/gc48-s1-smoke; SMOKEARG=smoke
else
    SUITE=gc48-group-commit.suite; RUNS=${RUNS:-6}; OUT=${OUT:-$T/out/s1}; PROBE=200; POLL=60
    REMOTE=${REMOTE:-/opt/bergdb-bench/005-48}; SMOKEARG=
    case $REMOTE in
        /opt/bergdb-bench/?*) ;;
        *) echo "run-s1.sh: REMOTE must be under /opt/bergdb-bench/"; exit 1 ;;
    esac
fi
BUILDS=$CLONE/java/build/perf/builds

if [ "${1:-}" = prepare ]; then
    for b in "$HEAD_BUILD" "$PROTO_BUILD"; do
        [ -f "$BUILDS/$b/java/build/bergdb.jar" ] || { echo "no build $BUILDS/$b"; exit 1; }
    done
    rm -rf "$P"
    mkdir -p "$P/java/stress" "$P/java/bench" "$P/probe"
    for f in performance.sh PerfUtil.java Perf.java PerfTool.java; do
        cp "$CLONE/java/stress/$f" "$P/java/stress/" || exit 1
    done
    # The alert thresholds, if the clone has them (not in Git; PerfTool compares without).
    [ ! -f "$CLONE/java/bench/thresholds.json" ] || cp "$CLONE/java/bench/thresholds.json" "$P/java/bench/"
    cp "$T/group-commit.suite" "$P/java/gc48-group-commit.suite"
    cp "$T/smoke.suite" "$P/java/gc48-smoke.suite"
    cp "$T/s1-runner.sh" "$P/"
    # The harness where performance.sh's prepare_target looks for it: harness- and the first
    # 12 hex digits of the SHA-256 of PerfUtil.java, Perf.java and PerfTool.java.
    H=harness-$(cd "$P/java/stress" && cat PerfUtil.java Perf.java PerfTool.java | shasum -a 256 | cut -c1-12)
    for b in "$HEAD_BUILD" "$PROTO_BUILD"; do
        d=$P/java/build/perf/builds/$b
        mkdir -p "$d/java/build" "$d/$H"
        cp "$BUILDS/$b/identity.env" "$d/"
        cp "$BUILDS/$b/java/build/bergdb.jar" "$d/java/build/"
        (cd "$P/java/stress" && "$LJAVA/bin/javac" --release 17 -Xlint:-options -encoding UTF-8 \
            -cp "$d/java/build/bergdb.jar" -d "$d/$H" PerfUtil.java Perf.java PerfTool.java) || exit 1
    done
    "$LJAVA/bin/javac" --release 17 -nowarn -cp "$BUILDS/$HEAD_BUILD/java/build/bergdb.jar" -d "$P/probe" \
        "$ITEM/../13-buffer-time/tools/ForceProbe.java" || exit 1
    printf 'HEAD_BUILD=%s\nPROTO_BUILD=%s\nJAVA_HOME=%s\nHEAP=1g\n' "$HEAD_BUILD" "$PROTO_BUILD" \
        "${S1JAVA:-/opt/bergdb-bench/jdk-27}" > "$P/builds.env"
    echo "prepared: $P ($(du -sh "$P" | cut -f1))"
    exit 0
fi

mkdir -p "$OUT"
log() { echo "$(date '+%H:%M:%S') $*" | tee -a "$OUT/log.txt"; }
ssh1() { ssh -o BatchMode=yes -o ConnectTimeout=20 "$HOST" "$1"; }
# on CMD: runs CMD where the package is: on s1, or here for the smoke test.
on() {
    if [ "$SMOKE" = 1 ]; then sh -c "$1"; else ssh1 "$1"; fi
}

if [ "${1:-}" != fetch ]; then
    [ -f "$P/builds.env" ] || { log "no package in $P: sh run-s1.sh prepare"; exit 1; }
    grep -q "^HEAD_BUILD=$HEAD_BUILD\$" "$P/builds.env" && grep -q "^PROTO_BUILD=$PROTO_BUILD\$" "$P/builds.env" ||
        { log "the package in $P has other builds: sh run-s1.sh prepare"; exit 1; }
    if [ "$SMOKE" = 1 ]; then
        rm -rf "$REMOTE"
        cp -R "$P" "$REMOTE"
        sed -e "s|^JAVA_HOME=.*|JAVA_HOME=$LJAVA|" "$P/builds.env" > "$REMOTE/builds.env"
    else
        # s1 idle: no JVM, and a 1-minute load under 1 (2 vCPUs); up to 20 minutes.
        i=0
        while :; do
            st=$(ssh1 "ps -eo pid,args | grep '[j]ava' | cut -c1-150; echo LOAD \$(cut -d' ' -f1 /proc/loadavg)") ||
                { log "no ssh to $HOST"; exit 1; }
            load=$(echo "$st" | sed -n 's/^LOAD //p')
            jvms=$(echo "$st" | grep -v '^LOAD ')
            if [ -z "$jvms" ] && awk "BEGIN { exit !($load < 1.0) }"; then
                break
            fi
            if [ $i -ge 20 ]; then
                log "s1 not idle after 20 minutes (load $load), not started:"
                echo "$jvms" | tee -a "$OUT/log.txt"
                exit 2
            fi
            [ $i = 0 ] && { log "waiting for s1 (load $load):"; echo "$jvms" | tee -a "$OUT/log.txt"; }
            sleep 60
            i=$((i + 1))
        done
        S1J=$(sed -n 's/^JAVA_HOME=//p' "$P/builds.env")
        ssh1 "test -x $S1J/bin/java" || { log "no $S1J/bin/java on $HOST"; exit 1; }
        ssh1 "rm -rf $REMOTE && mkdir -p $REMOTE" &&
            (cd "$P" && tar cf - .) | ssh1 "cd $REMOTE && tar xf -" ||
            { log "the copy to $HOST failed"; exit 1; }
    fi
    log "start in $REMOTE ($([ "$SMOKE" = 1 ] && echo here || echo "$HOST")): $HEAD_BUILD against $PROTO_BUILD, $SUITE, RUNS=$RUNS"
    on "cd $REMOTE && nohup sh s1-runner.sh $SUITE $RUNS $PROBE $SMOKEARG > runner.txt 2>&1 < /dev/null &" ||
        { log "the start failed"; exit 1; }
    i=0
    while ! on "test -f $REMOTE/out/DONE"; do
        sleep $POLL
        i=$((i + 1))
        if [ $((i * POLL)) -gt 14400 ]; then
            log "the runner was not done after 4 hours; fetch later with: sh run-s1.sh fetch"
            exit 1
        fi
    done
fi

log "fetching the results"
if [ "$SMOKE" = 1 ]; then
    cp -R "$REMOTE/out/." "$OUT/"
else
    ssh1 "cd $REMOTE/out && tar cf - ." | (cd "$OUT" && tar xf -) || { log "the fetch failed"; exit 1; }
fi
rc=$(cat "$OUT/DONE" 2>/dev/null || echo 1)
log "runner exit $rc; the table: python3 -I $ITEM/tools/table.py $OUT"
exit "$rc"
