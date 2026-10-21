#!/bin/sh
# 005-09: the flaky test under load, as in 005-02: on each build, J JVMs (default 4) of
# Probe009 with N runs each (default 1000), all at once, beside B busy loops (default 4).
# TEST=F runs the f-test (Probe009's F).
# Builds: preserved builds of performance.sh build (java/build/perf/builds/LABEL).
# Usage: probe.sh OUTDIR BUILD... ; prints one line per JVM, and the totals per build.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../../.." && pwd)
PERF=${PERF:-$REPO/java/build/perf/builds}
JAVA_HOME=${JAVA_HOME:-/opt/homebrew/opt/openjdk}
J=${J:-4}; N=${N:-1000}; B=${B:-4}
OUT=$1; shift
mkdir -p "$OUT"
for b in "$@"; do
    mkdir -p "$OUT/classes-$b"
    "$JAVA_HOME/bin/javac" --release 8 -nowarn -Xlint:-options -d "$OUT/classes-$b" \
        -cp "$PERF/$b/java/build/bergdb.jar" "$HERE/Probe009.java"
done
busy=""
i=0; while [ $i -lt "$B" ]; do (while :; do :; done) & busy="$busy $!"; i=$((i + 1)); done
trap 'kill $busy 2>/dev/null' EXIT
echo "start $(date '+%Y-%m-%d %H:%M:%S'), J=$J N=$N B=$B TEST=${TEST:-unit}, load $(sysctl -n vm.loadavg)"
pids=""
for b in "$@"; do
    i=1; while [ $i -le "$J" ]; do
        "$JAVA_HOME/bin/java" -ea -cp "$PERF/$b/java/build/bergdb.jar:$OUT/classes-$b" Probe009 "$N" ${TEST:-} \
            > "$OUT/$b-$i.txt" 2>&1 &
        pids="$pids $!"; i=$((i + 1))
    done
done
for p in $pids; do wait $p || true; done
echo "end $(date '+%Y-%m-%d %H:%M:%S')"
for b in "$@"; do
    for f in "$OUT/$b"-*.txt; do echo "$(basename "$f"): $(grep '^PROBE' "$f")"; grep '^FAILURE' "$f" | sed 's/^/    /'; done
    awk '/^PROBE/ { r += $3; f += $5 } END { printf "TOTAL '"$b"': %d runs, %d failures\n", r, f }' "$OUT/$b"-*.txt
done
