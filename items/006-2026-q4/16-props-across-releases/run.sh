#!/bin/sh
# bergdb 006-16: Props (MEM, CORE, SS) across BergDB's history, from the oldest code
# in Git (2013-06-06) to the 2026.4 candidate, on this machine with its installed JDK.
# After 006-02's run.sh; the builds and the raw output are in the work directory $W.
#
#   run.sh build [NAME...]       builds the versions (all, or the ones named) into $W/builds
#   run.sh list                  the versions: name, kind, commit, which Props
#   run.sh one NAME LABEL [WHAT] one run, a fresh JVM: WHAT is all (Props: MEM, CORE,
#                                SS; the default), mem or ss
#   run.sh memss LABEL [NAME...] MEM and SS of each version, two JVMs each, no quiet
#                                check (they do not depend on time)
#   run.sh rounds LABEL N [NAME...]  N rounds of a Props run of each version, the order
#                                forward in odd rounds and backward in even ones; each
#                                run only on a quiet machine (quiet_ok below)
#   run.sh quiet                 prints the quiet check once
#   run.sh facts                 the machine and the JVM, into $RUNS/machine.txt
#
# Versions (NAME: kind, commit, Props):
#
#   2013.1      orig  9ffbdf9  release-2013.1.130606, KissDB, the first release (p16)
#   2013-07-05  orig  550ce4e  the code of CORE's baseline, cissi 2013-07-05 (p16)
#   2013.3      orig  466a18f  release-2013.3-3 (p16)
#   2014.1      orig  7e29e8e  release-2014.1-3, the last node stream (p16)
#   2015.1      orig  f51fc8d  release-2015.1-1, the KV stream (kv2), the first Props
#   2015.4      orig  9384bce  release-2015.4-2, the last public release
#   2015-12-28  orig  bc11dbf  "Typical output (2015-12-28)" (006-02)
#   2017-07-29  orig  dbf131a  the last Props run on cissi (006-02)
#   2017-08-01  repo  195cf88  the 2017 import (006-02)
#   2026-10-19  repo  11ea2f6  006-02's 2026 code
#   2026.1      jar   a42947c  releases/2026.1/bergdb-2026.1.jar, as released
#   2026.2      jar   95bde62  releases/2026.2/bergdb-2026.2.jar
#   2026.3      jar   929fa33  releases/2026.3/bergdb-2026.3.jar
#   2026.4c     cand  f3af680  the 2026.4 candidate: main at the start of 006-16, built
#                              by its own java/build.sh (build/bergdb.jar)
#
# orig: F1-007's bergdb-git.bundle (cloned into $W/orig-git); repo: this repository.
# Both compiled as 006-02 did: one javac call, --release 8, from git archive.
# Props: "own" is the version's bergdb.dev.props.Props; "p16" is P16.java.in, made for
# the API of the time (run.sh p16_make), for the code before 2015 that has no Props.
#
# A run is a fresh JVM with $JFLAGS (default none), no -ea, as Props was run in 2013 to
# 2017. Its file $RUNS/TIME-LABEL-NAME[-WHAT].txt holds the version, the commit, a hash
# of the classes, the machine state before the run, the output and the time.
#
# Environment: W (work directory, default this script's), JAVA_HOME (default
# /opt/homebrew/opt/openjdk), REPO (default ~/fl/repos/bergdb), BUNDLE, JFLAGS,
# LOADMAX (default 1.5), QUIETN (quiet checks in a row before a block, default 4),
# DEADLINE (HHMM, default 1300: no timed run starts at or after it).

set -e
W=${W:-$(cd "$(dirname "$0")" && pwd)}
REPO=${REPO:-$HOME/fl/repos/bergdb}
BUNDLE=${BUNDLE:-$HOME/fl/repos/f1/a/007-bergdb-261012/bergdb-git.bundle}
JAVA_HOME=${JAVA_HOME:-/opt/homebrew/opt/openjdk}
JAVA=$JAVA_HOME/bin/java
JAVAC=$JAVA_HOME/bin/javac
OUT=$W/builds
RUNS=$W/runs
LOADMAX=${LOADMAX:-1.5}
QUIETN=${QUIETN:-4}
MARKER=$W/QUIET-BLOCK
VERSIONS="2013.1 2013-07-05 2013.3 2014.1 2015.1 2015.4 2015-12-28 2017-07-29 2017-08-01 2026-10-19 2026.1 2026.2 2026.3 2026.4c"

die() { echo "run.sh: $*" >&2; exit 1; }

# version NAME: sets KIND, COMMIT, PREFIX and P16 (empty: own Props; else
# "PKG KEYS PUT SYNC RUNM" for p16_make).
version() {
    P16=
    case "$1" in
        2013.1)     KIND=orig; COMMIT=9ffbdf9; PREFIX=KissDB
                    P16="kissdb kissdb.core.Keys set sync0 runMethod";;
        2013-07-05) KIND=orig; COMMIT=550ce4e; PREFIX=bergdb
                    P16="bergdb bergdb.core.Keys set sync0 runMethod";;
        2013.3)     KIND=orig; COMMIT=466a18f; PREFIX=bergdb
                    P16="bergdb bergdb.dag.Keys put sync0 runMethod";;
        2014.1)     KIND=orig; COMMIT=7e29e8e; PREFIX=bergdb
                    P16="bergdb bergdb.dag.Keys put syncL runOneMethod";;
        2015.1)     KIND=orig; COMMIT=f51fc8d; PREFIX=bergdb;;
        2015.4)     KIND=orig; COMMIT=9384bce; PREFIX=bergdb;;
        2015-12-28) KIND=orig; COMMIT=bc11dbf; PREFIX=bergdb;;
        2017-07-29) KIND=orig; COMMIT=dbf131a; PREFIX=bergdb;;
        2017-08-01) KIND=repo; COMMIT=195cf88; PREFIX=java;;
        2026-10-19) KIND=repo; COMMIT=11ea2f6; PREFIX=java;;
        2026.1)     KIND=jar; COMMIT=a42947c; PREFIX=releases/2026.1/bergdb-2026.1.jar;;
        2026.2)     KIND=jar; COMMIT=95bde62; PREFIX=releases/2026.2/bergdb-2026.2.jar;;
        2026.3)     KIND=jar; COMMIT=929fa33; PREFIX=releases/2026.3/bergdb-2026.3.jar;;
        2026.4c)    KIND=cand; COMMIT=f3af680; PREFIX=java;;
        *) die "unknown version: $1 (one of: $VERSIONS)";;
    esac
}

hash_dir() {
    (cd "$1" && find . -type f -name '*.class' | LC_ALL=C sort |
        xargs shasum -a 256 | shasum -a 256 | cut -d' ' -f1)
}

# p16_make DIR: P16.java.in for the API of the version (P16 set by version), compiled
# against DIR/classes into DIR/p16.
p16_make() {
    dir=$1
    set -- $P16
    pkg=$1; keys=$2; put=$3; sync=$4; runm=$5
    case "$sync" in
        sync0) syncline="db.sync();";;
        syncL) syncline="db.sync($pkg.core.SyncLevel.ORDINARY);";;
    esac
    mkdir -p "$dir/p16src/p16" "$dir/p16"
    sed -e "s/@P@/$pkg/g" -e "s/@KEYS@/$keys/g" -e "s/@PUT@/$put/g" \
        -e "s/@SYNC@/$syncline/g" -e "s/@RUNM@/$runm/g" \
        "$W/P16.java.in" > "$dir/p16src/p16/P16.java"
    "$JAVAC" --release 8 -nowarn -Xlint:-options -d "$dir/p16" -cp "$dir/classes" \
        "$dir/p16src/p16/P16.java" > "$dir/p16.log" 2>&1 || { cat "$dir/p16.log"; die "P16 for $dir"; }
}

build_one() {
    name=$1
    version "$name"
    dir=$OUT/$name
    case "$dir" in
        */006-16/builds/*) ;;
        *) die "refusing to clean $dir";;
    esac
    rm -rf "$dir"
    mkdir -p "$dir"
    case "$KIND" in
        orig|repo)
            if [ "$KIND" = orig ]; then
                src=$W/orig-git
                [ -d "$src" ] || git clone -q "$BUNDLE" "$src"
            else
                src=$REPO
            fi
            mkdir -p "$dir/src" "$dir/classes"
            git -C "$src" archive "$COMMIT" "$PREFIX" | tar -x -C "$dir/src"
            j=$dir/src/$PREFIX
            icu=
            [ -f "$j/in/icu-for-bergdb.jar" ] && icu=$j/in/icu-for-bergdb.jar
            # src-icu only with its jar: 2013.1 (KissDB) has no ICU jar in Git, and
            # nothing of src or src-dev needs src-icu.
            dirs=
            for d in src src-dev src-icu; do
                [ "$d" = src-icu ] && [ -z "$icu" ] && continue
                [ -d "$j/$d" ] && dirs="$dirs $j/$d"
            done
            if ! "$JAVAC" --release 8 -encoding UTF-8 -nowarn -Xlint:-options -d "$dir/classes" \
                    -cp "${icu:-$dir/classes}" $(find $dirs -name '*.java') > "$dir/javac.log" 2>&1; then
                tail -30 "$dir/javac.log"
                die "javac failed for $name"
            fi
            for d in src src-dev; do
                [ -d "$j/$d" ] || continue
                (cd "$j/$d" && find . -type f ! -name '*.java' ! -name '*.html') |
                    while read f; do
                        mkdir -p "$dir/classes/$(dirname "$f")"
                        cp "$j/$d/$f" "$dir/classes/$f"
                    done
            done
            git -C "$src" rev-parse "$COMMIT" > "$dir/commit"
            hash_dir "$dir/classes" > "$dir/classes.sha256"
            cp=$dir/classes
            [ -n "$icu" ] && cp=$cp:$icu
            if [ -n "$P16" ]; then
                p16_make "$dir"
                cp=$cp:$dir/p16
                echo "p16 ($P16)" > "$dir/props"
            else
                echo "own" > "$dir/props"
            fi
            echo "$cp" > "$dir/cp";;
        jar)
            jar=$REPO/$PREFIX
            (cd "$(dirname "$jar")" && grep " $(basename "$jar")\$" SHA256SUMS | shasum -a 256 -c -) \
                > "$dir/sha.log" 2>&1 || { cat "$dir/sha.log"; die "SHA256SUMS for $jar"; }
            cp "$jar" "$dir/"
            git -C "$REPO" rev-parse "$COMMIT" > "$dir/commit"
            shasum -a 256 "$dir/$(basename "$jar")" | cut -d' ' -f1 > "$dir/classes.sha256"
            echo "own" > "$dir/props"
            echo "$dir/$(basename "$jar")" > "$dir/cp";;
        cand)
            mkdir -p "$dir/src"
            git -C "$REPO" archive "$COMMIT" java | tar -x -C "$dir/src"
            (cd "$dir/src/java" && JAVAC=$JAVAC JAR=$JAVA_HOME/bin/jar JAVA=$JAVA \
                JDEPS=$JAVA_HOME/bin/jdeps ./build.sh) > "$dir/build.log" 2>&1 ||
                { tail -30 "$dir/build.log"; die "build.sh failed for $name"; }
            git -C "$REPO" rev-parse "$COMMIT" > "$dir/commit"
            shasum -a 256 "$dir/src/java/build/bergdb.jar" | cut -d' ' -f1 > "$dir/classes.sha256"
            echo "own" > "$dir/props"
            echo "$dir/src/java/build/bergdb.jar" > "$dir/cp";;
    esac
    echo "Built $name: $(cat "$dir/commit"), $(cat "$dir/classes.sha256"), Props $(cat "$dir/props")"
}

# The main class for WHAT (all, mem, ss) of a version; sets CLASS and ARGS.
main_class() {
    name=$1; what=$2
    version "$name"
    ARGS=
    if [ -n "$P16" ]; then
        CLASS=p16.P16; ARGS=$what
        return
    fi
    case "$what" in
        all) CLASS=bergdb.dev.props.Props;;
        ss)  CLASS=bergdb.dev.props.SS;;
        mem) case "$name" in
                 2015.1|2015.4) CLASS=bergdb.dev.props.MEM;;   # renamed Mem on 2015-08-18
                 *) CLASS=bergdb.dev.props.Mem;;
             esac;;
    esac
}

other_jvms() {
    # Every java process but the editor's language server (VS Code, redhat.java).
    ps -Ao pid=,command= | grep -E '/java( |$)|bin/java ' | grep -v -E 'redhat\.java|grep' |
        awk '{print $1}' | tr '\n' ' '
}

markers() {
    ls /Users/f/fl/bench/*/QUIET-BLOCK /Users/f/fl/bench/coord/*/QUIET-BLOCK 2>/dev/null |
        grep -v "^$MARKER\$" | tr '\n' ' '
}

runners() {
    ps -Ao command= | grep -E 'before-commit\.sh|night\.sh|performance\.sh|perf\.sh|level[0-9]\.sh|quiet\.sh|lake (build|env)' |
        grep -v grep | cut -c1-60 | tr '\n' ';'
}

load1() { sysctl -n vm.loadavg | awk '{print $2}'; }

busy_sessions() {
    grep -l '"status":"busy"' "$HOME"/.claude/sessions/*.json 2>/dev/null | wc -l | tr -d ' '
}

# quiet_ok: 0 if the machine is quiet for a timed run; sets QUIET (a description).
quiet_ok() {
    l=$(load1)
    j=$(other_jvms)
    m=$(markers)
    r=$(runners)
    if lockf -t 0 /Users/f/fl/bench/006-15/gate.lock true 2>/dev/null; then g=free; else g=held; fi
    QUIET="load1=$l jvms=[${j% }] markers=[${m% }] runners=[$r] gate=$g busy-sessions=$(busy_sessions)"
    awk "BEGIN { exit !($l < $LOADMAX) }" && [ -z "$j" ] && [ -z "$m" ] && [ -z "$r" ] && [ "$g" = free ]
}

# past_deadline: 0 when the time (HHMM) is at or after $DEADLINE (default 1300).
past_deadline() {
    [ "$(date +%H%M)" -ge "${DEADLINE:-1300}" ]
}

# wait_quiet N: until quiet_ok holds at N checks in a row, 10 s apart (30 s when N > 2);
# returns 1 when the deadline passes first.
wait_quiet() {
    need=$1
    gap=10
    [ "$need" -gt 2 ] && gap=30
    ok=0
    WAITED=0
    while :; do
        if past_deadline; then
            return 1
        fi
        if quiet_ok; then
            ok=$((ok + 1))
            [ "$ok" -ge "$need" ] && return
        else
            ok=0
        fi
        sleep $gap
        WAITED=$((WAITED + gap))
    done
}

run_one() {
    name=$1; label=$2; what=${3:-all}; timed=${4:-no}
    dir=$OUT/$name
    [ -f "$dir/cp" ] || die "no build of $name; run.sh build $name first"
    main_class "$name" "$what"
    mkdir -p "$RUNS"
    if [ "$timed" = yes ]; then
        if ! wait_quiet 2; then
            echo "deadline ${DEADLINE:-1300} passed before a quiet window: $name not run"
            return 1
        fi
    else
        WAITED=0
        quiet_ok || true
    fi
    suffix=
    [ "$what" != all ] && suffix=-$what
    f=$RUNS/$(date +%Y%m%d-%H%M%S)-$label-$name$suffix.txt
    {
        echo "version: $name"
        echo "commit: $(cat "$dir/commit")"
        echo "classes: $(cat "$dir/classes.sha256")"
        echo "props: $(cat "$dir/props")"
        echo "label: $label"
        echo "class: $CLASS $ARGS"
        echo "flags: $JFLAGS"
        echo "start: $(date '+%Y-%m-%d %H:%M:%S %Z')"
        echo "timed: $timed (waited ${WAITED} s for quiet)"
        echo "quiet: $QUIET"
        echo "----"
    } > "$f"
    t0=$(date +%s)
    # $JFLAGS and $ARGS are split into words on purpose.
    "$JAVA" $JFLAGS -cp "$(cat "$dir/cp")" $CLASS $ARGS >> "$f" 2>&1 || echo "EXIT CODE $?" >> "$f"
    t1=$(date +%s)
    {
        echo "----"
        echo "seconds: $((t1 - t0))"
        echo "load after: $(sysctl -n vm.loadavg)"
    } >> "$f"
    echo "$(basename "$f"): $(grep -o -E '(MEM|CORE|SS):[0-9.]+( \([^)]*\))?' "$f" | tr '\n' ' ')($((t1 - t0)) s, $QUIET)"
}

rounds() {
    label=$1; n=$2; shift 2
    list=${*:-$VERSIONS}
    rev=
    for v in $list; do version "$v"; rev="$v $rev"; done
    echo "006-16 Props block, label $label, $n rounds, started $(date '+%Y-%m-%d %H:%M'); no builds, gates or other timing while this file exists" > "$MARKER"
    trap 'rm -f "$MARKER"' EXIT
    trap 'rm -f "$MARKER"; exit 1' INT TERM
    echo "block $label: waiting for $QUIETN quiet checks, $(date '+%H:%M:%S')"
    if ! wait_quiet "$QUIETN"; then
        echo "block $label: deadline ${DEADLINE:-1300} passed, no quiet window; nothing run"
        rm -f "$MARKER"
        return 1
    fi
    echo "block $label: quiet after ${WAITED} s, $(date '+%H:%M:%S')"
    i=1
    while [ "$i" -le "$n" ]; do
        if [ $((i % 2)) -eq 1 ]; then order=$list; else order=$rev; fi
        echo "round $i: $order"
        for v in $order; do
            if ! run_one "$v" "$label" all yes; then
                echo "block $label: stopped in round $i, $(date '+%H:%M:%S')"
                rm -f "$MARKER"
                return 1
            fi
            sleep 10
        done
        i=$((i + 1))
    done
    echo "block $label: done, $(date '+%H:%M:%S')"
    rm -f "$MARKER"
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
            [ -f "$OUT/$v/commit" ] && echo "  $v: $(cat "$OUT/$v/commit"), $(cat "$OUT/$v/classes.sha256"), Props $(cat "$OUT/$v/props")"
        done
    } > "$RUNS/machine.txt"
    cat "$RUNS/machine.txt"
}

cmd=${1:-}
[ $# -gt 0 ] && shift
case "$cmd" in
    build)
        for v in ${*:-$VERSIONS}; do
            build_one "$v"
        done;;
    list)
        for v in $VERSIONS; do
            version "$v"
            echo "$v $KIND $COMMIT ${P16:+p16 ($P16)}"
        done;;
    one)
        [ $# -ge 2 ] || die "usage: run.sh one NAME LABEL [WHAT]"
        run_one "$1" "$2" "${3:-all}" no;;
    memss)
        [ $# -ge 1 ] || die "usage: run.sh memss LABEL [NAME...]"
        label=$1; shift
        for v in ${*:-$VERSIONS}; do
            run_one "$v" "$label" mem no
            run_one "$v" "$label" ss no
        done;;
    rounds)
        [ $# -ge 2 ] || die "usage: run.sh rounds LABEL N [NAME...]"
        rounds "$@";;
    quiet)
        if quiet_ok; then echo "quiet: $QUIET"; else echo "not quiet: $QUIET"; fi;;
    facts)
        facts;;
    *)
        sed -n '2,45p' "$0"; exit 2;;
esac
