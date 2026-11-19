#!/bin/sh
# The performance runner of Level 3 (bergdb 011-06, task 3), written 2026-10-14.
# Repeatable workloads on a FileStream, with a short smoke mode and a full reference mode, and a
# comparison of a candidate with an explicitly chosen reference. It is a performance check
# alongside the correctness gates (level1.sh to level3.sh), not one of them. Do not run
# anything else on the machine while it runs; results of concurrent benchmark jobs are
# not a reference.
#
# Usage: java/stress/performance.sh COMMAND ...
#
#   smoke                      One small scenario of each kind (performance-smoke.suite), one or
#                              two runs: the plumbing and the correctness checks, a few minutes.
#   quick [LABEL]              The simple baseline (performance-quick.suite): warm reads, updates with
#                              infinite and finite retention, restart; 3 runs each, about 15 minutes.
#                              Enough to see that a later level did not wreck performance.
#   reference [LABEL]          The principal suite (performance.suite): every scenario, the runs
#                              it names (3; 5 for warm reads). SUITE=grid for the rest of the
#                              grid (performance-grid.suite). Prints a summary at the end.
#   build LABEL                A preserved build: a copy of the sources in java/build/perf/builds/LABEL
#                              and its jar. Never replaced. Make one of the reference source
#                              before changing production code, to compare against it later.
#   ab REFBUILD CANDBUILD      Runs the suite alternately on two preserved builds (ABBA order, on
#                              this machine), then compares. REFBUILD and CANDBUILD name
#                              directories of "build" (or the keyword "current": a snapshot of the
#                              working tree). Run it twice before calling an alert a regression.
#   compare REF CAND [CAND2]   Compare sessions (directories). A reference may be a tracked one in
#                              java/bench/reference/. Refuses incompatible workloads or environments.
#   summary SESSION [--md]     Median, range, variation and run count of every scenario.
#   calibrate SESSION SESSION...  Propose alert thresholds from the repeatability of sessions of
#                              the same build (see PerfTool); with OUT=FILE writes the proposal.
#   promote SESSION NAME       Copies the compact results of a session to java/bench/reference/NAME
#                              for committing. Never replaces an existing reference.
#   list                       Builds and sessions.
#
# Environment:
#   JAVA_HOME     The JDK (java, javac, jar); the JDK on the PATH otherwise.
#   RUNS=N        Runs per scenario, instead of the suite's.   ONLY=REGEX  Only these scenarios.
#   GC=g1|zgc|parallel  The collector (default g1). A separate configuration: results of
#                 different collectors are not compared.      HEAP=8g  -Xms and -Xmx (default 8g).
#   BUILD=DIR     Use a preserved build (reference, smoke); default: a snapshot of the working tree.
#   OSCACHE=warm|cold  warm (default): the OS file cache is not touched, and a restart reads
#                 files that were just written. cold: `purge` before the restart (needs root:
#                 sudo -n purge); the run stops if it cannot.
#   SUITE=principal|grid|smoke|quick|release|FILE  The scenarios (default principal; smoke sets
#                 smoke; release: 1M and 10M keys, timing.sh's, bergdb 028-23).
#   FORCE=1       Run although the machine is not quiet (under 90% idle CPU); the results are then
#                 not a reference.    DISKMIN_GB=N  Free disk space needed (default 30).
#   KEEPDATA=1    Keep the data directories (java/build/perf/data/, deleted after each run otherwise).
#   COOLDOWN=S    Seconds between runs (default 5).        THRESHOLDS=FILE  (default java/bench/thresholds.json)
#   JFLAGS="..."  Extra JVM flags for every run, recorded with the others (jvm.flags): for
#                 example -Devictbudget=N, the capacity controller's budget in bytes (bergdb
#                 item 001, WP J10; Perf's databases are built with noEvict(), so without it
#                 nothing is evicted). Sessions with other flags are not compared.
#
# Every run is a separate JVM (java/stress/Perf.java) with fixed flags (G1, a fixed heap,
# assertions off, unified GC and safepoint logging to the run directory). Each result records
# the source (commit, diff, manifest, jar), the harness, the JVM and machine, and the
# effective workload parameters. Sessions are in java/build/perf/runs/COMMIT-TIME-SUITE-GC-HEAP/
# (ignored by Git); raw logs, histograms and GC logs stay there. A correctness failure stops
# everything at once.
#
# Kind: timing (bergdb 028-23): the figures are the result; it checks that the machine is
# quiet itself. timing.sh runs its ab with the release suite.

cd "$(dirname "$0")/.." || exit 1
echo "Kind: timing"
JAVADIR=$(pwd)
ROOT=$(cd .. && pwd)
PERF=$JAVADIR/build/perf
DATA=$PERF/data

if [ -n "${JAVA_HOME:-}" ]; then
    JAVA=$JAVA_HOME/bin/java; JAVAC=$JAVA_HOME/bin/javac; JAR=$JAVA_HOME/bin/jar
else
    JAVA=${JAVA:-java}; JAVAC=${JAVAC:-javac}; JAR=${JAR:-jar}
fi
export JAVAC JAR

GC=${GC:-g1}
HEAP=${HEAP:-8g}
RUNS=${RUNS:-}
ONLY=${ONLY:-}
OSCACHE=${OSCACHE:-warm}
COOLDOWN=${COOLDOWN:-5}
FORCE=${FORCE:-0}
KEEPDATA=${KEEPDATA:-0}
THRESHOLDS=${THRESHOLDS:-$JAVADIR/bench/thresholds.json}
SRCPATHS="java/src java/src-dev java/stress java/build.sh java/in"
HARNESS_FILES="PerfUtil.java Perf.java PerfTool.java"

die() { echo "performance.sh: $*" >&2; exit 1; }

case $GC in
    g1) GCFLAGS="-XX:+UseG1GC" ;;
    zgc) GCFLAGS="-XX:+UseZGC" ;;
    parallel) GCFLAGS="-XX:+UseParallelGC" ;;
    *) die "GC must be g1, zgc or parallel" ;;
esac
# Assertions off (the gates run with them on); the heap is fixed (-Xms = -Xmx, set per run), not pretouched, so
# that the resident set size shows what the program uses.
JVMFLAGS="$GCFLAGS -da${JFLAGS:+ $JFLAGS}"

sha256() { shasum -a 256 | cut -d' ' -f1; }

# ---- Source identity ----

# Sets COMMIT, BRANCH, DIRTY, DIFFSHA, MANIFEST for the working tree.
identity() {
    COMMIT=$(git -C "$ROOT" rev-parse HEAD 2>/dev/null || echo unknown)
    BRANCH=$(git -C "$ROOT" rev-parse --abbrev-ref HEAD 2>/dev/null || echo unknown)
    status=$(git -C "$ROOT" status --porcelain -- $SRCPATHS 2>/dev/null)
    if [ -n "$status" ]; then
        DIRTY=true
        DIFFSHA=$({
            git -C "$ROOT" diff HEAD -- $SRCPATHS
            git -C "$ROOT" ls-files --others --exclude-standard -- $SRCPATHS | LC_ALL=C sort | while read -r f; do
                echo "untracked $f"; shasum -a 256 "$ROOT/$f"
            done
        } | sha256)
    else
        DIRTY=false
        DIFFSHA=none
    fi
    MANIFEST=$(cd "$ROOT" && find $SRCPATHS -type f ! -name .DS_Store | LC_ALL=C sort | while read -r f; do
        shasum -a 256 "$f"
    done | sha256)
}

# ---- Preserved builds ----

# build_snapshot LABEL: copies the sources of the working tree and builds them.
build_snapshot() {
    label=$1
    dest=$PERF/builds/$label
    [ -e "$dest" ] && die "build $label exists: a preserved build is never replaced (choose another label)"
    identity
    mkdir -p "$dest/java" || die "cannot create $dest"
    (cd "$JAVADIR" && rsync -a --exclude .DS_Store src src-dev in stress build.sh "$dest/java/") \
        || die "cannot copy the sources"
    echo "Building $label from $COMMIT (dirty: $DIRTY) in $dest"
    (cd "$dest/java" && ./build.sh) > "$dest/build.log" 2>&1 || { tail -20 "$dest/build.log"; die "build failed (log: $dest/build.log)"; }
    jarsha=$(shasum -a 256 "$dest/java/build/bergdb.jar" | cut -d' ' -f1)
    {
        echo "COMMIT=$COMMIT"
        echo "BRANCH=$BRANCH"
        echo "DIRTY=$DIRTY"
        echo "DIFFSHA=$DIFFSHA"
        echo "MANIFEST=$MANIFEST"
        echo "JARSHA=$jarsha"
        echo "BUILDLABEL=$label"
        echo "BUILTAT=$(date '+%Y-%m-%dT%H:%M:%S%z')"
    } > "$dest/identity.env"
    "$JAVAC" -version > "$dest/javac-version.txt" 2>&1
    echo "Built $dest"
}

# The directory of the build named by $1: "current" snapshots the working tree (once per manifest).
resolve_build() {
    case $1 in
        current)
            identity
            label=current-$(echo "$COMMIT" | cut -c1-8)-$(echo "$MANIFEST" | cut -c1-8)
            [ -d "$PERF/builds/$label" ] || build_snapshot "$label" >&2
            echo "$PERF/builds/$label" ;;
        /*) echo "$1" ;;
        *) if [ -d "$PERF/builds/$1" ]; then echo "$PERF/builds/$1"; else echo "$1"; fi ;;
    esac
}

# prepare_target TAG BUILDDIR: loads the identity of the build and compiles the harness against its
# jar; sets TAG_CP, TAG_BUILD, TAG_ID (variables read by target()).
prepare_target() {
    tag=$1; bdir=$2
    [ -f "$bdir/identity.env" ] || die "$bdir is not a preserved build (no identity.env)"
    [ -f "$bdir/java/build/bergdb.jar" ] || die "$bdir has no jar"
    bjar=$bdir/java/build/bergdb.jar
    hsha=$(cat $(for f in $HARNESS_FILES; do echo "$JAVADIR/stress/$f"; done) | sha256)
    hclasses=$bdir/harness-$(echo "$hsha" | cut -c1-12)
    if [ ! -d "$hclasses" ]; then
        mkdir -p "$hclasses.tmp"
        "$JAVAC" --release 17 -Xlint:-options -encoding UTF-8 -cp "$bjar" -d "$hclasses.tmp" \
            $(for f in $HARNESS_FILES; do echo "$JAVADIR/stress/$f"; done) || die "the harness does not compile against $bjar"
        mv "$hclasses.tmp" "$hclasses"
    fi
    eval "${tag}_CP=\"$bjar:$hclasses\""
    eval "${tag}_BUILD=\"$bdir\""
    eval "${tag}_HSHA=\"$hsha\""
}

tool() { "$JAVA" -cp "$CP" bergdb.core.PerfTool "$@"; }

# ---- Machine ----

machine_facts() {
    if [ "$(uname -s)" = Darwin ]; then
        echo "machine.model=$(sysctl -n hw.model)"
        echo "machine.cpu=$(sysctl -n machdep.cpu.brand_string)"
        echo "machine.cores=$(sysctl -n hw.ncpu)"
        echo "machine.memBytes=$(sysctl -n hw.memsize)"
        echo "machine.osBuild=$(sw_vers -productVersion) $(sw_vers -buildVersion)"
        echo "machine.power=$(pmset -g batt 2>/dev/null | head -1 | tr -d "'" )"
        echo "machine.thermal=$(pmset -g therm 2>/dev/null | grep -i -m1 -E 'warning|cpu_' | tr -s ' ')"
    else
        echo "machine.model=$(cat /sys/devices/virtual/dmi/id/product_name 2>/dev/null || echo unknown)"
        echo "machine.cpu=$(grep -m1 'model name' /proc/cpuinfo 2>/dev/null | cut -d: -f2 | sed 's/^ //')"
        echo "machine.cores=$(nproc)"
        echo "machine.memBytes=$(($(grep MemTotal /proc/meminfo | tr -s ' ' | cut -d' ' -f2) * 1024))"
        echo "machine.osBuild=$(uname -sr)"
        echo "machine.power=unknown"
        echo "machine.thermal=unknown"
    fi
    echo "machine.kernel=$(uname -sr)"
    echo "machine.host=$(hostname -s)"
    mkdir -p "$DATA"
    mp=$(df -P "$DATA" | tail -1 | awk '{print $NF}')
    echo "machine.dataVolume=$mp"
    echo "machine.fsType=$(mount | grep " on $mp " | head -1 | sed -e 's/.*(\([^,)]*\).*/\1/')"
}

# Refuses to start when other work uses the machine, or the disk is nearly full.
quiet_check() {
    mkdir -p "$DATA"
    freekb=$(df -Pk "$DATA" | tail -1 | awk '{print $4}')
    if [ "$freekb" -lt $((${DISKMIN_GB:-30} * 1000000)) ]; then
        die "less than ${DISKMIN_GB:-30} GB free where the data directories are (DISKMIN_GB to change): $(df -h "$DATA" | tail -1)"
    fi
    if [ "$(uname -s)" = Darwin ]; then
        idle=$(top -l 2 -n 0 -s 2 | grep "CPU usage" | tail -1 | sed -e 's/.* \([0-9.]*\)% idle.*/\1/')
    else
        idle=$(vmstat 1 2 | tail -1 | awk '{print $15}')
    fi
    echo "CPU idle before the runs: ${idle}%"
    if [ -n "$idle" ] && awk "BEGIN { exit !($idle < 90) }"; then
        if [ "$FORCE" = 1 ] || [ "$MODE_SMOKE" = 1 ]; then
            echo "WARNING: the machine is not quiet (${idle}% idle); results are not a reference."
        else
            die "the machine is not quiet (${idle}% idle): stop other jobs, or FORCE=1 (the results are then not a reference)"
        fi
    fi
}

# ---- Sessions ----

# new_session TAG SUITEFILE SUITENAME LABEL: creates the session directory of a target.
new_session() {
    tag=$1; suitefile=$2; suitename=$3; label=$4
    eval "bdir=\$${tag}_BUILD; hsha=\$${tag}_HSHA; cp=\$${tag}_CP"
    # shellcheck disable=SC1090
    . "$bdir/identity.env"
    stamp=$(date '+%Y%m%dT%H%M%S')
    short=$(echo "$COMMIT" | cut -c1-8)
    [ "$DIRTY" = true ] && short=$short-d$(echo "$DIFFSHA" | cut -c1-6)
    sid=$short-$stamp-$suitename-$GC-$HEAP
    [ -n "$label" ] && sid=$sid-$label
    sdir=$PERF/runs/$sid
    [ -e "$sdir" ] && die "session $sdir exists"
    mkdir -p "$sdir"
    traceversion=$(grep -m1 'TRACE_VERSION =' "$JAVADIR/stress/Perf.java" | sed -e 's/[^0-9]*\([0-9]*\).*/\1/')
    CP=$cp
    machine_facts > "$sdir/machine.txt"
    set -- "id=$sid" "createdAt=$(date '+%Y-%m-%dT%H:%M:%S%z')" "label=$label" \
        "command=$0 $COMMANDLINE" "suite.name=$suitename" "suite.file=$(basename "$suitefile")" \
        "suite.sha256=$(sha256 < "$suitefile")" "runsOverride=${RUNS:-none}" "only=${ONLY:-all}" \
        "source.commit=$COMMIT" "source.branch=$BRANCH" "source.dirty=$DIRTY" "source.diffSha256=$DIFFSHA" \
        "source.manifestSha256=$MANIFEST" "source.jarSha256=$JARSHA" "source.buildLabel=$BUILDLABEL" \
        "source.builtAt=$BUILTAT" "source.buildDir=$bdir" \
        "harness.sha256=$hsha" "harness.traceVersion=$traceversion" \
        "jvm.java=$JAVA" "jvm.flags=$JVMFLAGS -Xms$HEAP -Xmx$HEAP" "jvm.gc=$GC" "jvm.heap=$HEAP" \
        "jvm.version=$("$JAVA" -version 2>&1 | tr '\n' ';')" \
        "osCache=$OSCACHE" "cooldownSec=$COOLDOWN"
    while IFS= read -r fact; do set -- "$@" "$fact"; done < "$sdir/machine.txt"
    tool session "$sdir/session.json" "$@" || die "cannot write the session description"
    cp "$suitefile" "$sdir/suite.txt"
    eval "${tag}_SDIR=\"$sdir\""
    eval "${tag}_SID=\"$sid\""
}

# target TAG: selects the build and session of the reference ("R") or the candidate ("C").
target() {
    eval "CP=\$${1}_CP; SDIR=\$${1}_SDIR; SID=\$${1}_SID; HSHA=\$${1}_HSHA"
}

# ---- Running ----

# jvm MODE [extra options]: one JVM of Perf in the current run directory; stops everything on a failure.
jvm() {
    mode=$1; shift
    log=$rundir/$mode.stdout.txt
    # shellcheck disable=SC2086
    "$JAVA" $JVMFLAGS "-Xms$RUNHEAP" "-Xmx$RUNHEAP" "-Xlog:gc*,safepoint:file=$rundir/$mode.gc.log:uptime,level,tags" \
        $DOPTS "$@" "-Dperf.scenario=$name" "-Dperf.out=$rundir" "-Dperf.dir=$datadir" \
        "-Dperf.source=$SID" "-Dperf.oscache=$OSSTATE" \
        -cp "$CP" bergdb.core.Perf "$mode" > "$log" 2>&1
    rc=$?
    if [ $rc -ne 0 ] || ! grep -q '^PERF OK' "$log"; then
        echo "FAILED: $name run $k ($mode): exit code $rc. Last lines of $log:" >&2
        tail -25 "$log" >&2
        echo "A correctness or storage failure fails the whole run; the data is in $datadir" >&2
        exit 1
    fi
    tool finish "$rundir" "$mode" || die "cannot read the GC log of $log"
}

# run_one NAME MODE K PROPS
run_one() {
    name=$1; mode=$2; k=$3; props=$4
    rundir=$SDIR/$name/run$k
    mkdir -p "$rundir"
    datadir=$DATA/$SID/$name-run$k
    mkdir -p "$DATA/$SID"
    DOPTS=""
    RUNHEAP=$HEAP
    for p in $props; do
        case $p in
            jvm.heap=*) RUNHEAP=${p#jvm.heap=} ;;
            *) DOPTS="$DOPTS -Dperf.$p" ;;
        esac
    done
    uptime > "$rundir/load-before.txt"
    OSSTATE=$OSCACHE
    case $mode in
        restart)
            jvm write -Dperf.keep=1
            if [ "$OSCACHE" = cold ]; then
                if sudo -n purge 2>/dev/null || purge 2>/dev/null; then OSSTATE=cold; else die "OSCACHE=cold: purge failed (needs root: sudo -n purge)"; fi
            fi
            jvm restart ;;
        read|write) jvm "$mode" ;;
        *) die "unknown mode $mode in the suite" ;;
    esac
    uptime > "$rundir/load-after.txt"
    echo "  $name run $k: $(grep -h -E '^(WRITE|READ get_latest:|STARTUP|MIXED)' "$rundir"/*.stdout.txt | head -3 | tr '\n' '|' | cut -c1-200)"
    [ "$KEEPDATA" = 1 ] || rm -rf "$datadir"
}

# Scenario lines of a suite file: name mode runs [props...]
scenarios() {
    grep -v '^[[:space:]]*#' "$1" | grep -v '^[[:space:]]*$' | while read -r name mode runs props; do
        if [ -n "$ONLY" ] && ! echo "$name" | grep -Eq "$ONLY"; then continue; fi
        echo "$name $mode ${RUNS:-$runs} $props"
    done
}

# run_suite SUITEFILE: all runs on the current target.
run_suite() {
    scenarios "$1" | while read -r name mode runs props; do
        echo "$name ($mode, $runs runs)"
        k=1
        while [ "$k" -le "$runs" ]; do
            run_one "$name" "$mode" "$k" "$props"
            [ "$COOLDOWN" -gt 0 ] && sleep "$COOLDOWN"
            k=$((k + 1))
        done
    done
}

# run_ab SUITEFILE: ABBA order, per scenario, run by run, so drift of the machine hits both.
run_ab() {
    scenarios "$1" | while read -r name mode runs props; do
        echo "$name ($mode, $runs runs, alternating)"
        k=1
        while [ "$k" -le "$runs" ]; do
            if [ $((k % 2)) = 1 ]; then order="R C"; else order="C R"; fi
            for t in $order; do
                target $t
                echo " [$t]"
                run_one "$name" "$mode" "$k" "$props"
                [ "$COOLDOWN" -gt 0 ] && sleep "$COOLDOWN"
            done
            k=$((k + 1))
        done
    done
}

# check_scenarios SUITEFILE: stops if ONLY matches nothing.
check_scenarios() {
    n=$(scenarios "$1" | wc -l)
    [ "$n" -gt 0 ] || die "no scenario of $1 matches ONLY='$ONLY'"
    echo "$n scenarios from $(basename "$1")"
}

suite_file() {
    case ${SUITE:-principal} in
        principal) echo "$JAVADIR/stress/performance.suite" ;;
        grid) echo "$JAVADIR/stress/performance-grid.suite" ;;
        smoke) echo "$JAVADIR/stress/performance-smoke.suite" ;;
        quick) echo "$JAVADIR/stress/performance-quick.suite" ;;
        release) echo "$JAVADIR/stress/performance-release.suite" ;;
        *) [ -f "$SUITE" ] && echo "$SUITE" || die "unknown SUITE $SUITE" ;;
    esac
}

# ---- Commands ----
# The commands are in one function, so that the shell has read the whole script before it runs
# anything: editing this file during a long run does not disturb the run.

start_caffeinate() {
    if command -v caffeinate > /dev/null 2>&1; then
        caffeinate -i -w $$ &
    fi
}

main() {
COMMANDLINE="$*"
MODE_SMOKE=0
[ $# -ge 1 ] || { sed -n '2,/^$/p' "$0" | sed -e 's/^# \{0,1\}//'; exit 2; }
cmd=$1; shift

case $cmd in
    build)
        [ $# = 1 ] || die "usage: performance.sh build LABEL"
        build_snapshot "$1" ;;

    smoke)
        MODE_SMOKE=1
        SUITE=smoke
        b=$(resolve_build "${BUILD:-current}")
        prepare_target R "$b"
        sf=$(suite_file)
        check_scenarios "$sf"
        quiet_check
        start_caffeinate
        new_session R "$sf" smoke "${1:-}"
        target R
        echo "Session $SID"
        run_suite "$sf" || exit 1
        rm -rf "$DATA/$SID"
        tool summary "$SDIR"; rc=$?
        [ $rc = 0 ] || die "smoke: a run failed"
        echo "Comparing the session with itself (checks the comparison, expects no alerts)"
        tool compare "$SDIR" "$SDIR" > "$SDIR/self-compare.txt"; rc=$?
        tail -3 "$SDIR/self-compare.txt"
        [ $rc = 0 ] || die "smoke: the self-comparison reported something (exit $rc), see $SDIR/self-compare.txt"
        echo "PERFORMANCE SMOKE OK ($SDIR)" ;;

    reference|quick)
        [ "$cmd" = quick ] && SUITE=quick
        b=$(resolve_build "${BUILD:-current}")
        prepare_target R "$b"
        sf=$(suite_file)
        check_scenarios "$sf"
        quiet_check
        start_caffeinate
        new_session R "$sf" "${SUITE:-principal}" "${1:-}"
        target R
        echo "Session $SID, source ${R_BUILD}"
        run_suite "$sf" || exit 1
        rm -rf "$DATA/$SID"
        tool summary "$SDIR" | tee "$SDIR/summary.txt"
        tool summary "$SDIR" --md > "$SDIR/summary.md"
        echo "PERFORMANCE RUN DONE: $SDIR (summary.txt, summary.md)" ;;

    ab)
        [ $# = 2 ] || die "usage: performance.sh ab REFBUILD CANDBUILD"
        rb=$(resolve_build "$1"); cb=$(resolve_build "$2")
        prepare_target R "$rb"; prepare_target C "$cb"
        sf=$(suite_file)
        [ "$R_HSHA" = "$C_HSHA" ] || die "the harness differs"
        check_scenarios "$sf"
        quiet_check
        start_caffeinate
        new_session R "$sf" "${SUITE:-principal}" "ref"
        new_session C "$sf" "${SUITE:-principal}" "cand"
        echo "Reference session $R_SID"
        echo "Candidate session $C_SID"
        run_ab "$sf" || exit 1
        rm -rf "$DATA/$R_SID" "$DATA/$C_SID"
        CP=$R_CP
        tool compare "$R_SDIR" "$C_SDIR" --thresholds "$THRESHOLDS" > "$C_SDIR/compare-with-ref.txt"
        rc=$?
        cat "$C_SDIR/compare-with-ref.txt"
        echo "Comparison exit code $rc (0: no alerts, 1: alerts to repeat in a matched run, 3: incompatible, 4: failed or missing runs)"
        exit $rc ;;

    compare)
        [ $# -ge 2 ] || die "usage: performance.sh compare REF CAND [CAND2]"
        b=$(resolve_build "${BUILD:-current}")
        prepare_target R "$b"
        CP=$R_CP
        tool compare "$@" --thresholds "$THRESHOLDS" ;;

    summary)
        b=$(resolve_build "${BUILD:-current}")
        prepare_target R "$b"
        CP=$R_CP
        tool summary "$@" ;;

    calibrate)
        b=$(resolve_build "${BUILD:-current}")
        prepare_target R "$b"
        CP=$R_CP
        if [ -n "${OUT:-}" ]; then tool calibrate "$@" --out "$OUT"; else tool calibrate "$@"; fi ;;

    promote)
        [ $# = 2 ] || die "usage: performance.sh promote SESSION NAME"
        src=$1; name=$2
        [ -f "$src/session.json" ] || die "$src is not a session"
        dest=$JAVADIR/bench/reference/$name
        [ -e "$dest" ] && die "$dest exists: a reference is never replaced silently (use a new version name)"
        mkdir -p "$dest"
        cp "$src/session.json" "$src/suite.txt" "$src/machine.txt" "$dest/"
        (cd "$src" && find . -name '*.result.json' -o -name 'summary.*') | while read -r f; do
            mkdir -p "$dest/$(dirname "$f")"
            cp "$src/$f" "$dest/$f"
        done
        echo "Promoted $src to $dest (compact results only; raw logs stay in $src). Commit it with the report."
        ;;

    list)
        echo "Builds:"; ls -1 "$PERF/builds" 2>/dev/null | sed -e 's/^/  /'
        echo "Sessions:"; ls -1 "$PERF/runs" 2>/dev/null | sed -e 's/^/  /'
        echo "Tracked references:"; ls -1 "$JAVADIR/bench/reference" 2>/dev/null | sed -e 's/^/  /' ;;

    *) die "unknown command $cmd" ;;
esac
}

main "$@"
exit $?
