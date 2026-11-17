#!/bin/sh
# 006-02: the 2013-2017 Props suite (bergdb.dev.props.Props: MEM, CORE and SS)
# on four versions of the code, on this machine and its installed JVM.
#
#   run.sh build [VERSION...]            builds the four versions (or the ones named)
#                                        into $OUT, with the same javac and flags, and
#                                        Probe006.java for each
#   run.sh one VERSION LABEL             one Props run
#   run.sh ab LABEL N VERSION1 VERSION2  N ABBA blocks: V1, V2, V2, V1
#   run.sh class VERSION LABEL CLASS [ARGS]   one run of another class, such as
#                                        Probe006 ss 20000000
#   run.sh probe VERSION...              recompiles Probe006.java for the versions named
#   run.sh maphash                       the 2026 build with maphash.patch, as version
#                                        2026-10-19-maphash (an experiment)
#   run.sh facts                         the machine and the JVM, into runs/machine.txt
#
# The versions (NAME: where, commit, directory of the Java project):
#
#   2015-12-28  F1-007's bergdb-git.bundle  358ad6b  bergdb/   Props run on cissi that day
#   2017-07-29  F1-007's bergdb-git.bundle  b64383a  bergdb/   Props run on cissi that day
#   2017-08-01  this repository             0257e0b  java/     the 2017 import (= 50786b2)
#   2026-10-19  this repository             0e7292d  java/     the 2026 code (HEAD)
#   orig-HASH   F1-007's bergdb-git.bundle  HASH     bergdb/   any original commit
#   repo-HASH   this repository             HASH     java/     any commit here
#
# A run is one fresh JVM with the flags in $JFLAGS (default none), as Props was run
# in 2013 to 2017 (no -ea). Its file runs/TIME-LABEL-VERSION.txt in this directory
# holds the machine state before it (idle CPU, load), the command and the output.
# Before each run the script waits until the CPU is at least $IDLEMIN percent idle
# (default 90), at most $WAITMAX seconds (default 1800), and records the idle value
# it started with.
#
# Environment: OUT (builds, default java/build/props-006-02, ignored by Git),
# JAVA_HOME (default /opt/homebrew/opt/openjdk), BUNDLE (the original Git history),
# JFLAGS.

set -e
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../../.." && pwd)
OUT=${OUT:-$REPO/java/build/props-006-02}
JAVA_HOME=${JAVA_HOME:-/opt/homebrew/opt/openjdk}
JAVA=$JAVA_HOME/bin/java
JAVAC=$JAVA_HOME/bin/javac
BUNDLE=${BUNDLE:-$HOME/fl/repos/f1/a/007-bergdb-261012/bergdb-git.bundle}
RUNS=$HERE/runs
IDLEMIN=${IDLEMIN:-90}
WAITMAX=${WAITMAX:-1800}
VERSIONS="2015-12-28 2017-07-29 2017-08-01 2026-10-19"

die() { echo "run.sh: $*" >&2; exit 1; }

# version NAME: sets SRC (a Git repository), COMMIT and PREFIX.
version() {
    case "$1" in
        2015-12-28) SRC=$OUT/orig-git; COMMIT=358ad6b; PREFIX=bergdb;;
        2017-07-29) SRC=$OUT/orig-git; COMMIT=b64383a; PREFIX=bergdb;;
        2017-08-01) SRC=$REPO; COMMIT=0257e0b; PREFIX=java;;
        2026-10-19) SRC=$REPO; COMMIT=0e7292d; PREFIX=java;;
        orig-*) SRC=$OUT/orig-git; COMMIT=${1#orig-}; PREFIX=bergdb;;
        repo-*) SRC=$REPO; COMMIT=${1#repo-}; PREFIX=java;;
        2026-10-19-maphash) SRC=$REPO; COMMIT=0e7292d; PREFIX=java;;   # run.sh maphash
        *) die "unknown version: $1 (one of: $VERSIONS)";;
    esac
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

build_one() {
    name=$1
    version "$name"
    dir=$OUT/$name
    case "$dir" in
        */props-006-02/*) ;;
        *) die "refusing to clean $dir";;
    esac
    if [ "$SRC" = "$OUT/orig-git" ] && [ ! -d "$SRC" ]; then
        git clone -q "$BUNDLE" "$SRC"
    fi
    rm -rf "$dir"
    mkdir -p "$dir/src" "$dir/classes" "$dir/probe"
    git -C "$SRC" archive "$COMMIT" "$PREFIX" | tar -x -C "$dir/src"
    j=$dir/src/$PREFIX
    if ! "$JAVAC" --release 8 -encoding UTF-8 -nowarn -Xlint:-options -d "$dir/classes" \
            -cp "$j/in/icu-for-bergdb.jar" \
            $(find "$j/src" "$j/src-dev" "$j/src-icu" -name '*.java') > "$dir/javac.log" 2>&1; then
        cat "$dir/javac.log"
        die "javac failed for $name"
    fi
    # Non-Java resources, as in java/build.sh.
    for d in src src-dev; do
        (cd "$j/$d" && find . -type f ! -name '*.java' ! -name '*.html') |
            while read f; do
                mkdir -p "$dir/classes/$(dirname "$f")"
                cp "$j/$d/$f" "$dir/classes/$f"
            done
    done
    [ -f "$dir/classes/bergdb/dev/props/Props.class" ] || die "build of $name failed"
    git -C "$SRC" rev-parse "$COMMIT" > "$dir/commit"
    (cd "$dir/classes" && find . -type f -name '*.class' | LC_ALL=C sort |
        xargs shasum -a 256 | shasum -a 256 | cut -d' ' -f1) > "$dir/classes.sha256"
    if "$JAVAC" --release 8 -nowarn -Xlint:-options -d "$dir/probe" -cp "$dir/classes" \
            "$HERE/Probe006.java" > "$dir/probe.log" 2>&1; then
        probe="Probe006 built"
    else
        probe="Probe006 does not compile (see $dir/probe.log)"
    fi
    echo "Built $name: $(cat "$dir/commit"), classes $(cat "$dir/classes.sha256"); $probe"
}

run_class() {
    name=$1; label=$2; class=$3; shift 3
    dir=$OUT/$name
    [ -f "$dir/commit" ] || die "no build of $name; run.sh build first"
    mkdir -p "$RUNS"
    wait_quiet
    f=$RUNS/$(date +%Y%m%d-%H%M%S)-$label-$name.txt
    {
        echo "version: $name"
        echo "commit: $(cat "$dir/commit")"
        echo "classes: $(cat "$dir/classes.sha256")"
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
    "$JAVA" $JFLAGS -cp "$dir/classes:$dir/probe:$(ls "$dir"/src/*/in/icu-for-bergdb.jar)" \
        "$class" "$@" >> "$f" 2>&1 || echo "EXIT CODE $?" >> "$f"
    t1=$(date +%s)
    {
        echo "----"
        echo "seconds: $((t1 - t0))"
    } >> "$f"
    echo "$(basename "$f"): $(grep -o -E '(MEM|CORE|SS|set):[0-9.]+( \([^)]*\))?' "$f" | tr '\n' ' ')($((t1 - t0)) s, ${IDLE}% idle)"
}

run_one() {
    name=$1; label=$2
    run_class "$name" "$label" bergdb.dev.props.Props
}

# ab LABEL N V1 V2: N blocks of V1, V2, V2, V1.
ab() {
    label=$1; n=$2; v1=$3; v2=$4
    version "$v1"; version "$v2"
    i=1
    while [ "$i" -le "$n" ]; do
        run_one "$v1" "$label"; sleep 10
        run_one "$v2" "$label"; sleep 10
        run_one "$v2" "$label"; sleep 10
        run_one "$v1" "$label"; sleep 10
        i=$((i + 1))
    done
}

facts() {
    mkdir -p "$RUNS"
    {
        echo "date: $(date '+%Y-%m-%d %H:%M:%S %Z')"
        echo "host: $(hostname -s)"
        echo "model: $(sysctl -n hw.model)"
        echo "cpu: $(sysctl -n machdep.cpu.brand_string), $(sysctl -n hw.ncpu) cores ($(sysctl -n hw.perflevel0.physicalcpu) performance, $(sysctl -n hw.perflevel1.physicalcpu) efficiency)"
        echo "memory: $(($(sysctl -n hw.memsize) / 1073741824)) GB"
        echo "os: $(sw_vers -productName) $(sw_vers -productVersion) ($(sw_vers -buildVersion))"
        echo "power: $(pmset -g batt | head -1)"
        echo "java: $JAVA"
        "$JAVA" -version 2>&1 | sed -e 's/^/  /'
        echo "default flags:"
        "$JAVA" -XX:+PrintCommandLineFlags -version 2>&1 | head -1 | sed -e 's/^/  /'
        "$JAVA" -XX:+PrintFlagsFinal -version 2>/dev/null |
            grep -E ' (UseCompactObjectHeaders|UseCompressedOops|UseG1GC|UseParallelGC|MaxHeapSize|ParallelGCThreads) ' |
            sed -e 's/^ */  /'
        echo "builds:"
        for v in $VERSIONS; do
            [ -f "$OUT/$v/commit" ] && echo "  $v: $(cat "$OUT/$v/commit"), classes $(cat "$OUT/$v/classes.sha256")"
        done
    } > "$RUNS/machine.txt"
    cat "$RUNS/machine.txt"
}

cmd=${1:-}
[ $# -gt 0 ] && shift
case "$cmd" in
    build)
        if [ $# -gt 0 ]; then
            for v in "$@"; do
                build_one "$v"
            done
        else
            for v in $VERSIONS; do
                build_one "$v"
            done
            facts
        fi;;
    one)
        [ $# -eq 2 ] || die "usage: run.sh one VERSION LABEL"
        run_one "$1" "$2";;
    ab)
        [ $# -eq 4 ] || die "usage: run.sh ab LABEL N VERSION1 VERSION2"
        ab "$1" "$2" "$3" "$4";;
    class)
        [ $# -ge 3 ] || die "usage: run.sh class VERSION LABEL CLASS [ARGS]"
        v=$1; l=$2; c=$3; shift 3
        run_class "$v" "$l" "$c" "$@";;
    maphash)
        # The experiment of section 4 of the report: the 2026 build with maphash.patch
        # (Cache3.mapIndex), as version 2026-10-19-maphash.
        src=$OUT/2026-10-19
        dir=$OUT/2026-10-19-maphash
        [ -f "$src/commit" ] || die "no build of 2026-10-19"
        rm -rf "$dir"
        cp -R "$src" "$dir"
        patch -s -p1 -d "$dir/src" < "$HERE/maphash.patch"
        "$JAVAC" --release 8 -encoding UTF-8 -nowarn -Xlint:-options -d "$dir/classes" \
            -cp "$dir/classes" "$dir/src/java/src/bergdb/core/Cache3.java" || die "javac"
        echo "$(cat "$src/commit") with maphash.patch" > "$dir/commit"
        (cd "$dir/classes" && find . -type f -name '*.class' | LC_ALL=C sort |
            xargs shasum -a 256 | shasum -a 256 | cut -d' ' -f1) > "$dir/classes.sha256"
        echo "Built 2026-10-19-maphash: $(cat "$dir/commit"), classes $(cat "$dir/classes.sha256")";;
    probe)
        # Recompiles Probe006.java for the versions named, without rebuilding them.
        for v in "$@"; do
            "$JAVAC" --release 8 -nowarn -Xlint:-options -d "$OUT/$v/probe" \
                -cp "$OUT/$v/classes" "$HERE/Probe006.java" || die "Probe006 for $v"
            echo "Probe006 compiled for $v"
        done;;
    facts)
        facts;;
    *)
        sed -n '2,30p' "$0"; exit 2;;
esac
