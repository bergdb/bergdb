#!/bin/sh
# 005-09: Props (bergdb.dev.props.Props: MEM, CORE and SS; CORE's four times are Core's get,
# get4t, set and getmany) on preserved builds of java/stress/performance.sh
# ("performance.sh build LABEL"): pre-0509, the code before the fix, and fix-0509, with it.
# 005-08's run.sh, with its own runs/ and OUT; the commands probe and tool are 005-08's.
#
#   run.sh one BUILD LABEL                     one Props run
#   run.sh class BUILD LABEL CLASS [ARGS]      one run of another class (bergdb.dev.props.Core)
#   run.sh ab LABEL N BUILD1 BUILD2            N blocks of Props runs: B1, B2, B2, B1
#   run.sh abclass LABEL N BUILD1 BUILD2 CLASS [ARGS]   the same with another class
#
# A run is one fresh JVM with the flags in $JFLAGS (default none: no -ea, as Props was run
# in 2013 to 2017), started when the CPU is at least $IDLEMIN percent idle (default 90; at
# most $WAITMAX seconds of waiting, default 1800), ten seconds after the run before in a
# block. Its file runs/TIME-LABEL-BUILD.txt here holds the build, the machine state before
# it, the command and the output.
#
# Environment: PERF (the preserved builds, default java/build/perf/builds), OUT (default
# java/build/005-09), JAVA_HOME (default /opt/homebrew/opt/openjdk), JFLAGS.

set -e
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../../.." && pwd)
PERF=${PERF:-$REPO/java/build/perf/builds}
OUT=${OUT:-$REPO/java/build/005-09}
PROBE=$REPO/items/006-2026-q4/02-props-2017-vs-2026/Probe006.java
JAVA_HOME=${JAVA_HOME:-/opt/homebrew/opt/openjdk}
JAVA=$JAVA_HOME/bin/java
JAVAC=$JAVA_HOME/bin/javac
RUNS=$HERE/runs
IDLEMIN=${IDLEMIN:-90}
WAITMAX=${WAITMAX:-1800}

die() { echo "run.sh: $*" >&2; exit 1; }

jar_of() {
    j=$PERF/$1/java/build/bergdb.jar
    [ -f "$j" ] || die "no preserved build $1 (performance.sh build $1)"
    echo "$j"
}

idle() {
    top -l 2 -n 0 -s 2 | grep "CPU usage" | tail -1 | sed -e 's/.* \([0-9.]*\)% idle.*/\1/'
}

wait_quiet() {
    waited=0
    while :; do
        IDLE=$(idle)
        if awk "BEGIN { exit !($IDLE >= $IDLEMIN) }"; then
            return
        fi
        if [ "$waited" -ge "$WAITMAX" ]; then
            echo "WARNING: not quiet after ${waited} s (${IDLE}% idle); running anyway"
            return
        fi
        sleep 30
        waited=$((waited + 34))
    done
}

run_class() {
    build=$1; label=$2; class=$3; shift 3
    jar=$(jar_of "$build")
    mkdir -p "$RUNS"
    wait_quiet
    f=$RUNS/$(date +%Y%m%d-%H%M%S)-$label-$build.txt
    {
        echo "build: $build"
        grep -E '^(COMMIT|DIRTY|DIFFSHA|JARSHA)=' "$PERF/$build/identity.env"
        echo "label: $label"
        echo "class: $class $*"
        echo "flags: $JFLAGS"
        echo "start: $(date '+%Y-%m-%d %H:%M:%S %Z')"
        echo "idle: $IDLE"
        echo "load: $(sysctl -n vm.loadavg)"
        echo "----"
    } > "$f"
    t0=$(date +%s)
    # $JFLAGS is split into words on purpose.
    "$JAVA" $JFLAGS -cp "$jar:$OUT/probe-$build:$OUT/tools-$build" "$class" "$@" >> "$f" 2>&1 \
        || echo "EXIT CODE $?" >> "$f"
    t1=$(date +%s)
    {
        echo "----"
        echo "seconds: $((t1 - t0))"
    } >> "$f"
    echo "$(basename "$f"): $(grep -o -E '(MEM|CORE|SS|set|HISTO):[0-9.]+( \([^)]*\))?' "$f" | tr '\n' ' ')($((t1 - t0)) s, ${IDLE}% idle)"
}

# ab LABEL N B1 B2 CLASS [ARGS]: N blocks of B1, B2, B2, B1.
ab() {
    label=$1; n=$2; b1=$3; b2=$4; shift 4
    jar_of "$b1" > /dev/null; jar_of "$b2" > /dev/null
    i=1
    while [ "$i" -le "$n" ]; do
        run_class "$b1" "$label" "$@"; sleep 10
        run_class "$b2" "$label" "$@"; sleep 10
        run_class "$b2" "$label" "$@"; sleep 10
        run_class "$b1" "$label" "$@"; sleep 10
        i=$((i + 1))
    done
}

cmd=${1:-}
[ $# -gt 0 ] && shift
case "$cmd" in
    probe)
        for b in "$@"; do
            mkdir -p "$OUT/probe-$b"
            "$JAVAC" --release 8 -nowarn -Xlint:-options -d "$OUT/probe-$b" -cp "$(jar_of "$b")" \
                "$PROBE" || die "Probe006 for $b"
            echo "Probe006 compiled for $b"
        done;;
    one)
        [ $# -eq 2 ] || die "usage: run.sh one BUILD LABEL"
        run_class "$1" "$2" bergdb.dev.props.Props;;
    class)
        [ $# -ge 3 ] || die "usage: run.sh class BUILD LABEL CLASS [ARGS]"
        run_class "$@";;
    ab)
        [ $# -eq 4 ] || die "usage: run.sh ab LABEL N BUILD1 BUILD2"
        ab "$1" "$2" "$3" "$4" bergdb.dev.props.Props;;
    abclass)
        [ $# -ge 5 ] || die "usage: run.sh abclass LABEL N BUILD1 BUILD2 CLASS [ARGS]"
        ab "$@";;
    tool)
        [ $# -ge 3 ] || die "usage: run.sh tool BUILD LABEL FILE [ARGS]"
        b=$1; l=$2; src=$HERE/$3; shift 3
        [ -f "$src" ] || die "no $src"
        mkdir -p "$OUT/tools-$b"
        "$JAVAC" --release 8 -nowarn -Xlint:-options -d "$OUT/tools-$b" \
            -cp "$(jar_of "$b"):$OUT/probe-$b" "$src" || die "javac $src"
        pkg=$(sed -n 's/^package \([a-z.]*\);.*/\1./p' "$src")
        run_class "$b" "$l" "$pkg$(basename "$src" .java)" "$@";;
    *)
        sed -n '2,25p' "$0"; exit 2;;
esac
