#!/bin/sh
# bergdb 005-48: the runner of run-s1.sh, in the package directory that run-s1.sh makes, on
# s1 (/opt/bergdb-bench/005-48), or on this machine for run-s1.sh's smoke test. Written
# 2026-10-27 by Claude (Opus 5.5, Claude Code).
# Usage: sh s1-runner.sh SUITE RUNS PROBECOUNT [smoke]
# The package: builds.env (HEAD_BUILD, PROTO_BUILD, JAVA_HOME, HEAP); java/stress/ with
# performance.sh and the harness; java/bench/thresholds.json; java/SUITE; the two builds in
# java/build/perf/builds/ (identity.env, the jar, the harness compiled); probe/ForceProbe.class.
# Writes out/: log.txt, ab.txt, compare-with-ref.txt, forceprobe-before.txt and -after.txt,
# summary-ref.txt and summary-cand.txt, ref/ and cand/ (as run-f53.sh), and at the end DONE
# with the exit code: 0 done, 1 a run failed, 2 another JVM ran or the machine was not quiet.
set -u
cd "$(dirname "$0")" || exit 1
D=$(pwd)
. ./builds.env
SUITE=$1
RUNS=$2
PROBE=$3
SMOKE=${4:-}
export JAVA_HOME
mkdir -p out bin
rm -f out/DONE
log() { echo "$(date '+%H:%M:%S') $*" | tee -a out/log.txt; }
done_with() { echo "$1" > out/DONE; exit "$1"; }

# Shims: s1's coreutils are uutils, whose tail and head do not take -N (performance.sh uses
# tail -1 and others); and shasum -a 256 from sha256sum, in case Perl's shasum is missing.
for t in tail head; do
    printf '#!/bin/sh\ncase "$1" in -[0-9]*) n=${1#-}; shift; exec /usr/bin/%s -n "$n" "$@" ;; esac\nexec /usr/bin/%s "$@"\n' \
        $t $t > bin/$t
done
if command -v sha256sum > /dev/null 2>&1; then
    printf '#!/bin/sh\n[ "$1" = -a ] && shift 2\nexec sha256sum "$@"\n' > bin/shasum
fi
chmod +x bin/*
PATH=$D/bin:$PATH
export PATH

log "runner on $(hostname): $HEAD_BUILD against $PROTO_BUILD, $SUITE, RUNS=$RUNS, HEAP=$HEAP"
[ -x "$JAVA_HOME/bin/java" ] || { log "no java at $JAVA_HOME"; done_with 1; }
if [ -z "$SMOKE" ]; then
    o=$(ps -eo pid,args | grep '[j]ava' || true)
    if [ -n "$o" ]; then
        log "another JVM runs, not started:"
        echo "$o" | cut -c1-160 | tee -a out/log.txt
        done_with 2
    fi
else
    COOLDOWN=0
    FORCE=1
    export COOLDOWN FORCE
fi

probe() {
    log "force probe $1"
    "$JAVA_HOME/bin/java" -cp "java/build/perf/builds/$HEAD_BUILD/java/build/bergdb.jar:probe" ForceProbe \
        "$D/probe-data" "$PROBE" > "out/forceprobe-$1.txt" 2>&1
    rm -rf "$D/probe-data"
}

probe before
(cd java && RUNS=$RUNS HEAP=$HEAP DISKMIN_GB=5 SUITE=$SUITE sh stress/performance.sh ab "$HEAD_BUILD" "$PROTO_BUILD") \
    > out/ab.txt 2>&1
rc=$?
log "performance.sh exit $rc: $(tail -n 1 out/ab.txt)"
probe after
grep -q 'machine is not quiet.*stop other jobs' out/ab.txt && { log "performance.sh found the machine not quiet"; done_with 2; }

for tag in ref cand; do
    if [ $tag = ref ]; then sid=$(sed -n 's/^Reference session //p' out/ab.txt)
    else sid=$(sed -n 's/^Candidate session //p' out/ab.txt); fi
    s=$D/java/build/perf/runs/$sid
    [ -n "$sid" ] && [ -d "$s" ] || { log "no session for $tag"; continue; }
    mkdir -p out/$tag
    cp "$s/session.json" "$s/machine.txt" out/$tag/ 2>/dev/null
    [ -f "$s/compare-with-ref.txt" ] && cp "$s/compare-with-ref.txt" out/
    (cd "$s" && find . -name 'write.result.json' -o -name 'write.stdout.txt' -o -name 'load-*.txt') |
    while read -r f; do
        mkdir -p "out/$tag/$(dirname "$f")"
        cp "$s/$f" "out/$tag/$f"
    done
    (cd java && BUILD=$HEAD_BUILD sh stress/performance.sh summary "$s") > out/summary-$tag.txt 2>&1
done
if grep -q '^FAILED' out/ab.txt; then
    log "a run failed, see ab.txt"
    done_with 1
fi
log "DONE"
done_with 0
