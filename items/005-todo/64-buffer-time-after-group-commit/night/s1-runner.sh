#!/bin/sh
# bergdb 005-64: the runner of run-s1.sh, in the package that prepare.sh makes, on s1
# (/opt/bergdb-bench/005-64/night/), or on this machine for run-s1.sh's smoke test. After
# 005-48's s1-runner.sh. Written 2026-10-28 by Claude (Opus 5.5, Claude Code).
#
# Usage: sh night/s1-runner.sh ROUNDS BUDGET_MIN PROBECOUNT [smoke]
# The package: builds.env (BUILD, JAVA_HOME, HEAP); java/stress/ with performance.sh and the
# harness sources; the build in java/build/perf/builds/BUILD (identity.env, the jar, the harness
# compiled); tools/ (classes/, cpu64.jar, table.py); night/ (rounds.sh, this script, the suites,
# the mixed configurations). It runs 005-13's force probe, rounds.sh (bufftime.suite and
# mixed.txt; smoke.suite and smoke-mixed.txt with smoke), the probe again, then table.py and its
# check. No round starts that would end more than BUDGET_MIN minutes after the start. FORCE
# from the environment goes to performance.sh (smoke: FORCE=1).
# Writes out/: runner.txt (from run-s1.sh), log.txt, forceprobe-before.txt and -after.txt,
# rounds/ and mixed/ (rounds.sh), table.md, check.txt, and at the end DONE with the exit code:
# 0 done and every row parsed, 1 a run failed or the check failed, 2 another JVM ran or the
# machine was not quiet.
set -u
cd "$(dirname "$0")/.." || exit 1
D=$(pwd)
. ./builds.env
ROUNDS=$1
BUDGET=$2
PROBE=$3
SMOKE=${4:-}
FORCE=${FORCE:-0}
START=$(date +%s)
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
if [ "$(uname -s)" != Darwin ]; then
    PATH=$D/bin:$PATH
    export PATH
fi

if [ -n "$SMOKE" ]; then
    SUITEF=$D/night/smoke.suite; MIXEDF=$D/night/smoke-mixed.txt; COOLDOWN=0; FORCE=1
else
    SUITEF=$D/night/bufftime.suite; MIXEDF=$D/night/mixed.txt; COOLDOWN=5
fi
export COOLDOWN FORCE
DISKMIN_GB=5
export DISKMIN_GB

log "runner on $(hostname): $BUILD, $(basename "$SUITEF"), ROUNDS=$ROUNDS, budget $BUDGET min, HEAP=$HEAP, FORCE=$FORCE"
[ -x "$JAVA_HOME/bin/java" ] || { log "no java at $JAVA_HOME"; done_with 1; }
if [ -z "$SMOKE" ]; then
    o=$(ps -eo pid,args | grep -E '[j]ava|[p]erformance\.sh' || true)
    if [ -n "$o" ]; then
        log "another JVM or performance run, not started:"
        echo "$o" | cut -c1-160 | tee -a out/log.txt
        done_with 2
    fi
fi

JAR=$D/java/build/perf/builds/$BUILD/java/build/bergdb.jar
probe() {
    log "force probe $1"
    "$JAVA_HOME/bin/java" -cp "$JAR:$D/tools/classes" ForceProbe "$D/probe-data" "$PROBE" > "out/forceprobe-$1.txt" 2>&1
    rm -rf "$D/probe-data"
}

probe before
DEADLINE=0
[ "$BUDGET" -gt 0 ] && DEADLINE=$((START + BUDGET * 60))
JAVADIR=$D/java BUILD=$BUILD SUITEF=$SUITEF MIXEDF=$MIXEDF ROUNDS=$ROUNDS OUT=$D/out TOOLS=$D/tools \
    HEAP=$HEAP DEADLINE=$DEADLINE sh night/rounds.sh
rc=$?
probe after

python3 -I tools/table.py out > out/table.md 2>&1
python3 -I tools/table.py --check "$SUITEF" "$MIXEDF" out > out/check.txt 2>&1
crc=$?
log "$(tail -n 1 out/check.txt)"
[ $rc = 2 ] && done_with 2
if [ $rc != 0 ] || [ $crc != 0 ]; then
    log "FAILED: rounds exit $rc, check exit $crc"
    done_with 1
fi
log "DONE in $(( ($(date +%s) - START) / 60 )) min"
done_with 0
