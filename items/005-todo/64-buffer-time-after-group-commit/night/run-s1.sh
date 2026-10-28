#!/bin/sh
# minutes: 60
# bergdb 005-64, the buffer time after group commit: the timed runs on s1 (Hostup VPS: 2 vCPUs,
# 3.8 GB, a virtual disk; B056 in sk26), for 006-10's quiet block, in the background from
# 22:30. The same rounds as run-f53.sh (rounds.sh: bufftime.suite through performance.sh, then
# MixedProbe, the buffer times 20, 50 and 100 ms rotated round by round), on the same build,
# with a heap of 2 GB; ROUNDS=6, and no round starts that would end more than BUDGET (55)
# minutes after the runner started (about 1.4 times F53's time a run, so some 11 minutes a
# round: 4 or 5 rounds). Written 2026-10-28 by Claude (Opus 5.5, Claude Code).
#
# prepare.sh makes the package by day (CLONE/java/build/perf/005-64-s1-package). The run does
# nothing heavy here, only ssh: it checks with ps that s1 is idle (no JVM, no performance run,
# a 1-minute load under 1; up to 15 minutes, then exit 2; other sessions time on s1 too),
# copies the package to s1:REMOTE (tar over ssh), starts night/s1-runner.sh there with nohup
# (a dropped connection does not stop it), waits for it with one ssh a minute, and fetches
# the summaries: log.txt, table.md, check.txt, the force probes, performance.sh's output and
# summary of each round, MixedProbe's output; not the runs' JSON and stdout (they stay on s1).
#
# Usage: sh run-s1.sh             copy, start, wait, fetch
#        sh run-s1.sh fetch       fetch only, when the wait was interrupted (the runner goes on)
#        sh run-s1.sh check       a dry check of s1, no timed run: ssh, ps, load, java, disk;
#                                 copies the package to REMOTE and tries it there (java,
#                                 the probe's usage, sh -n, the shims, table.py on nothing)
#        SMOKE=1 sh run-s1.sh     a smoke test here, not on s1: the package in a local
#                                 directory, smoke.suite and smoke-mixed.txt, one round, the
#                                 same fetch, and a check of what was fetched; 1 minute
# Environment: CLONE (default /Users/f/fl/bench/006-10/w3), BUILD (default main-bf9fc7f; must
#   be the package's), ROUNDS (default 6), BUDGET (default 55), HOST (default
#   root@s1), REMOTE (default /opt/bergdb-bench/005-64), OUT (default
#   /Users/f/fl/bench/006-10/night/out/64-s1, -smoke for SMOKE=1; an OUT with earlier results
#   is renamed OUT-HHMMSS first, SMOKE=1 removes it), FORCE (passed to the runner; the
#   conductor sets 1), JAVA_HOME here, for the smoke test (default /opt/homebrew/opt/openjdk).
# Exit code: the runner's (0 done and every row parsed, 1 a run failed or the check failed,
# 2 another JVM ran or not quiet); 1 if the package is missing, the copy, start or fetch
# failed, or the runner was not done after 3 hours; 2 if s1 was not idle.

set -u
SMOKE=${SMOKE:-0}
T=$(cd "$(dirname "$0")" && pwd)
CLONE=${CLONE:-/Users/f/fl/bench/006-10/w3}
BUILD=${BUILD:-main-bf9fc7f}
HOST=${HOST:-root@s1}
LJAVA=${JAVA_HOME:-/opt/homebrew/opt/openjdk}
FORCE=${FORCE:-0}
P=$CLONE/java/build/perf/005-64-s1-package
CMD=${1:-run}
if [ "$SMOKE" = 1 ]; then
    ROUNDS=${ROUNDS:-1}; BUDGET=0; PROBE=10; POLL=5; SMOKEARG=smoke
    REMOTE=$CLONE/java/build/perf/005-64-s1-smoke
    OUT=${OUT:-/Users/f/fl/bench/006-10/night/out/64-s1-smoke}
    [ "$CMD" = fetch ] || rm -rf "$OUT"
else
    ROUNDS=${ROUNDS:-6}; BUDGET=${BUDGET:-55}; PROBE=200; POLL=60; SMOKEARG=
    REMOTE=${REMOTE:-/opt/bergdb-bench/005-64}
    OUT=${OUT:-/Users/f/fl/bench/006-10/night/out/64-s1}
    case $REMOTE in
        /opt/bergdb-bench/?*) ;;
        *) echo "run-s1.sh: REMOTE must be under /opt/bergdb-bench/"; exit 1 ;;
    esac
    if [ "$CMD" = run ] && [ -d "$OUT" ] && [ -n "$(ls -A "$OUT")" ]; then
        mv "$OUT" "$OUT-$(date +%H%M%S)"
    fi
fi

mkdir -p "$OUT"
log() { echo "$(date '+%H:%M:%S') $*" | tee -a "$OUT/log-here.txt"; }
ssh1() { ssh -o BatchMode=yes -o ConnectTimeout=20 -o ServerAliveInterval=30 "$HOST" "$1"; }
# on CMD: runs CMD where the package is: on s1, or here for the smoke test.
on() {
    if [ "$SMOKE" = 1 ]; then sh -c "$1"; else ssh1 "$1"; fi
}

# s1's state: its JVMs and performance runs, and the 1-minute load.
s1state() {
    ssh1 "ps -eo pid,etime,args | grep -E '[j]ava|[p]erformance[.]sh|[r]unner[.]sh' | cut -c1-150; echo LOAD \$(cut -d' ' -f1 /proc/loadavg)"
}

copy() {
    ssh1 "rm -rf $REMOTE && mkdir -p $REMOTE" &&
        (cd "$P" && COPYFILE_DISABLE=1 tar --no-xattrs -cf - .) | ssh1 "cd $REMOTE && tar xf -"
}

check_package() {
    [ -f "$P/builds.env" ] || { log "no package in $P: sh prepare.sh"; exit 1; }
    grep -q "^BUILD=$BUILD\$" "$P/builds.env" || { log "the package in $P has another build: BUILD=$BUILD sh prepare.sh"; exit 1; }
}

if [ "$CMD" = check ]; then
    check_package
    log "dry check of $HOST, no timed run"
    st=$(s1state) || { log "no ssh to $HOST"; exit 1; }
    echo "$st" | tee -a "$OUT/log-here.txt"
    S1J=$(sed -n 's/^JAVA_HOME=//p' "$P/builds.env")
    ssh1 "$S1J/bin/java -version 2>&1 | head -1; python3 --version; df -h /opt | tail -n 1; free -m | head -n 2" |
        tee -a "$OUT/log-here.txt" || exit 1
    log "copying the package to $HOST:$REMOTE"
    copy || { log "the copy failed"; exit 1; }
    ssh1 "cd $REMOTE && . ./builds.env && for f in night/*.sh; do sh -n \$f || echo \"SYNTAX \$f\"; done;
          \$JAVA_HOME/bin/java -cp java/build/perf/builds/\$BUILD/java/build/bergdb.jar:tools/classes MixedProbe 2>&1 | head -n 1;
          ls java/build/perf/builds/\$BUILD/; mkdir -p /tmp/005-64-empty && python3 -I tools/table.py /tmp/005-64-empty | head -n 1;
          rmdir /tmp/005-64-empty" | tee -a "$OUT/log-here.txt"
    log "dry check done"
    exit 0
fi

if [ "$CMD" = run ]; then
    check_package
    if [ "$SMOKE" = 1 ]; then
        rm -rf "$REMOTE"
        cp -R "$P" "$REMOTE"
        sed -e "s|^JAVA_HOME=.*|JAVA_HOME=$LJAVA|" "$P/builds.env" > "$REMOTE/builds.env"
    else
        i=0
        while :; do
            st=$(s1state) || { log "no ssh to $HOST"; exit 1; }
            load=$(echo "$st" | sed -n 's/^LOAD //p')
            procs=$(echo "$st" | grep -v '^LOAD ')
            if [ -z "$procs" ] && awk "BEGIN { exit !($load < 1.0) }"; then
                break
            fi
            if [ $i -ge 15 ]; then
                log "s1 not idle after 15 minutes (load $load), not started:"
                echo "$procs" | tee -a "$OUT/log-here.txt"
                exit 2
            fi
            [ $i = 0 ] && { log "waiting for s1 (load $load):"; echo "$procs" | tee -a "$OUT/log-here.txt"; }
            sleep 60
            i=$((i + 1))
        done
        S1J=$(sed -n 's/^JAVA_HOME=//p' "$P/builds.env")
        ssh1 "test -x $S1J/bin/java" || { log "no $S1J/bin/java on $HOST"; exit 1; }
        copy || { log "the copy to $HOST failed"; exit 1; }
    fi
    log "start in $REMOTE ($([ "$SMOKE" = 1 ] && echo here || echo "$HOST")): $BUILD, ROUNDS=$ROUNDS, budget $BUDGET min, FORCE=$FORCE"
    on "cd $REMOTE && mkdir -p out && FORCE=$FORCE nohup sh night/s1-runner.sh $ROUNDS $BUDGET $PROBE $SMOKEARG > out/runner.txt 2>&1 < /dev/null &" ||
        { log "the start failed"; exit 1; }
    i=0
    while ! on "test -f $REMOTE/out/DONE"; do
        sleep $POLL
        i=$((i + 1))
        if [ $((i * POLL)) -gt 10800 ]; then
            log "the runner was not done after 3 hours; fetch later with: sh run-s1.sh fetch"
            exit 1
        fi
    done
fi

# The summaries, not the runs' JSON and stdout (rounds/rN/).
log "fetching the summaries"
SEL="cd $REMOTE/out && find . -type f ! -path './rounds/r*/*' | tar cf - -T -"
if [ "$SMOKE" = 1 ]; then
    sh -c "$SEL" | (cd "$OUT" && tar xf -) || { log "the fetch failed"; exit 1; }
else
    ssh1 "$SEL" | (cd "$OUT" && tar xf -) || { log "the fetch failed"; exit 1; }
fi
rc=$(cat "$OUT/DONE" 2>/dev/null || echo 1)
log "runner exit $rc; $(tail -n 1 "$OUT/check.txt" 2>/dev/null || echo 'no check.txt')"
if [ "$SMOKE" = 1 ]; then
    # The smoke test checks what was fetched: the check passed, the table is there, no JSON.
    grep -q '^CHECK OK' "$OUT/check.txt" 2>/dev/null || { log "SMOKE: the fetched check.txt is not CHECK OK"; exit 1; }
    [ -s "$OUT/table.md" ] || { log "SMOKE: no table.md fetched"; exit 1; }
    [ -z "$(find "$OUT" -name '*.json')" ] || { log "SMOKE: JSON was fetched"; exit 1; }
    log "SMOKE OK: $(grep -c '^ok' "$OUT/check.txt") rows parsed, table.md fetched, no JSON"
fi
exit "$rc"
