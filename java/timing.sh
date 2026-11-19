#!/bin/sh
# The timing run (bergdb 028-23): the tests whose number is the result, the speed of this
# tree against the last release's. Frans, 2026-11-19, 10:39: "Functional testing in
# before-commit.sh, night.sh, week.sh. Timing in timing.sh, only this script requires a
# quite machine." Run it before every release, on a commit near it, as week.sh (minor
# changes after are acceptable), and when a change may cost speed. Not a gate: a slower
# figure is an alert to look at, not a fault.
#
# Kind: timing. The only script that needs a quiet machine: it checks the CPU itself, as
# performance.sh does, and refuses to start when the machine is busy (less than MINIDLE %
# idle over 2 s, default 90), or waits for it (WAIT); it checks again before each run of
# CORE and of the pause probe, and stops the step if the machine stays busy. Nothing else
# heavy may run beside it: no night.sh, week.sh or level script, no build, no other
# session's tests. FORCE=1 runs it anyway, for a trial of the script: its report then says
# "not a measurement" on every figure.
#
# Usage: java/timing.sh [STEP...]     STEP: core, pauses, perf; all three without one
#        java/timing.sh prepare       only the two builds (no load check; see s1 below)
#   About 2 hours on F53 (an estimate of 2026-11-19, not yet measured): core 10 minutes,
#   pauses 10, perf about 100 (1M keys about 60, 10M about 40).
#
# The candidate is this tree, built with build.sh (its commit, and whether java/ has
# changes, are in the report); the reference is the last release (REFTAG, default the
# highest tag release-*), cloned from this repository into build/timing/ref.noindex/REFTAG/ and
# built there once, kept for the next run. The steps, in this order:
#   core    level1.sh's CORE (bergdb.dev.props.Core: get, get4t, getmany and set, as times
#           against cissi's of July 2013, smaller is faster), one JVM a run, the candidate
#           and the reference in ABBA order, ROUNDS rounds (default 2: 4 runs each); the
#           median of each build and their ratio. An alert when the candidate's CORE is
#           more than CORE_ALERT times the reference's (default 1.10).
#   pauses  the pause probe (stress/PauseProbe.java, bergdb 009; P1 of 010: no
#           stop-the-world) with ZGC, -Xmx2g, 1M keys, a cache budget of 20 MB, phases of
#           PAUSE_SECONDS (default 30) s, each build's own probe, ABBA, 2 runs each: the
#           longest get and commit of the phases. An alert when the candidate's is over
#           PAUSE_GUIDE_MS (default 50, F53's guide; 100 on s1: a guide of Frans,
#           2026-11-06, not a limit).
#   perf    stress/performance.sh ab with SUITE=release (performance-release.suite: 1M and
#           10M keys), the reference's preserved build (made with the reference's own
#           performance.sh build) against "current", this tree; its comparison's alerts
#           (exit code 1) are alerts here. Its sessions stay in build/perf/runs/.
# The report is build/timing/RUN/report.txt (RUN the date and time): the commit, the JDK,
# the CPU's idle share at the start, each step's figures and result, and TIMING OK (no
# alert), TIMING ALERTS: STEPS (a figure to look at), TIMING FAILED: STEPS (a run that
# failed or crashed: a correctness failure), or TIMING REFUSED (busy). Each run's output
# is in RUN/. Then a tools/news.sh entry: OK, "needs a look" (alerts, refused) or FAILED.
#
# Environment: JAVA_HOME (the JDK; the PATH's otherwise), MINIDLE, WAIT (minutes to wait
# for a quiet machine at the start, default 0: refuse at once), RUNWAIT (minutes to wait
# before each run, default 15), FORCE, REFTAG, ROUNDS, CORE_ALERT, PAUSE_SECONDS,
# PAUSE_GUIDE_MS, CAND and REF (directories that hold a bergdb.jar and its stress/ classes,
# made before: no build of that side), and performance.sh's (HEAP, ONLY, RUNS, ...).
#
# On s1 (a Linux VPS with 2 vCPUs and 3.8 GB, used for timing in 026-25 and 030-20; its
# ssh destination is not in this repository): s1 has a Java runtime; the builds are made
# here and copied, as 030-20 did. Here: `sh java/timing.sh prepare` prints the two
# directories (build/timing/RUN/cand and the reference's java/build); copy them and this
# script to s1 (tar over ssh), then there:
#     CAND=DIR REF=DIR PAUSE_GUIDE_MS=100 sh timing.sh core pauses
# The perf step needs a JDK and this repository; on s1 with a JDK and a clone, run it with
# HEAP=2900m ONLY='^(read|w|r)-' (the 10M scenarios need about 8 GB).

cd "$(dirname "$0")" || exit 1
JAVADIR=$(pwd)
if [ -n "${JAVA_HOME:-}" ]; then JAVA=$JAVA_HOME/bin/java; else JAVA=${JAVA:-java}; fi
MINIDLE=${MINIDLE:-90}
WAIT=${WAIT:-0}
RUNWAIT=${RUNWAIT:-15}
FORCE=${FORCE:-0}
ROUNDS=${ROUNDS:-2}
CORE_ALERT=${CORE_ALERT:-1.10}
PAUSE_SECONDS=${PAUSE_SECONDS:-30}
PAUSE_GUIDE_MS=${PAUSE_GUIDE_MS:-50}
echo "Kind: timing"

STEPS="$*"
[ -n "$STEPS" ] || STEPS="core pauses perf"
for s in $STEPS; do
    case $s in core|pauses|perf|prepare) ;; *) echo "timing.sh: unknown step $s"; exit 2 ;; esac
done

RUN=$JAVADIR/build/timing/$(date +%Y-%m-%d-%H%M)
REPORT=$RUN/report.txt
mkdir -p "$RUN" || exit 1
if [ "$FORCE" = 1 ]; then NOTE=" (FORCE=1: not a measurement)"; else NOTE=""; fi

# The CPU's idle percentage over 2 s.
idle() {
    if [ "$(uname -s)" = Darwin ]; then
        top -l 2 -n 0 -s 2 | grep "CPU usage" | tail -1 | sed -e 's/.* \([0-9.]*\)% idle.*/\1/'
    else
        vmstat 2 2 | tail -1 | awk '{print $15}'
    fi
}

# quiet_within MINUTES: 0 once the CPU is at least MINIDLE % idle, checked every 30 s up to
# MINUTES; 1 if it never was. Sets IDLE. With FORCE=1 always 0.
quiet_within() {
    end=$(( $(date +%s) + $1 * 60 ))
    while true; do
        IDLE=$(idle)
        [ "$FORCE" = 1 ] && return 0
        [ -n "$IDLE" ] && awk -v i="$IDLE" -v m="$MINIDLE" 'BEGIN { exit !(i >= m) }' && return 0
        [ "$(date +%s)" -lt $end ] || return 1
        sleep 30
    done
}

ALERTS=""
FAILED=""
INTERRUPTED=""

finish() {
    echo >> "$REPORT"
    if [ -n "$FAILED" ]; then
        line="TIMING FAILED:$FAILED"; st=FAILED
    elif [ -n "$ALERTS$INTERRUPTED" ]; then
        line="TIMING ALERTS:$ALERTS${INTERRUPTED:+ (busy, stopped:$INTERRUPTED)}"; st="needs a look"
    else
        line="TIMING OK"; st=OK
    fi
    echo "$line$NOTE" >> "$REPORT"
    cat "$REPORT"
    news "$st" "$line$NOTE"
    [ -z "$FAILED" ]
}

# news STATUS TEXT: one line in news.md (AGENTS.md, "News"), unless FORCE=1 (a trial).
news() {
    [ "$FORCE" = 1 ] && return 0
    [ -f "$JAVADIR/../tools/news.sh" ] || return 0
    sh "$JAVADIR/../tools/news.sh" "$1" timing.sh \
        "$2 on $(git -C "$JAVADIR" log -1 --format=%h) against $REFTAG. Report: java/build/timing/$(basename "$RUN")/report.txt" \
        || echo "timing.sh: news.sh failed"
}

REFTAG=${REFTAG:-$(git -C "$JAVADIR" tag -l 'release-*' | sort -V | tail -1)}
{
    echo "Timing run $(basename "$RUN") on $(hostname -s)$NOTE"
    echo "Kind: timing"
    echo "Commit: $(git -C "$JAVADIR" log -1 --format='%h %ad %s' --date=format:'%Y-%m-%d %H:%M' 2>/dev/null)"
    if [ -n "$(git -C "$JAVADIR" status --porcelain -- . 2>/dev/null)" ]; then
        echo "java/ has changes that are not committed: the candidate is the working tree"
    fi
    echo "Reference: $REFTAG"
    echo "JDK: $("$JAVA" -version 2>&1 | head -1)"
} > "$REPORT"

if [ "$STEPS" != prepare ]; then
    if ! quiet_within "$WAIT"; then
        echo "CPU ${IDLE}% idle, under $MINIDLE %" >> "$REPORT"
        echo "TIMING REFUSED: the machine is busy (${IDLE}% idle, at least $MINIDLE needed);" \
            "stop other work, or WAIT=MINUTES" | tee -a "$REPORT"
        [ "$WAIT" -gt 0 ] && news "needs a look" "TIMING REFUSED: busy for $WAIT minutes"
        exit 2
    fi
    echo "CPU ${IDLE}% idle at the start" >> "$REPORT"
fi

# ---- The two builds ----

# The candidate: this tree's jar and stress classes, copied, so that a build meanwhile
# changes nothing of the runs.
if [ -z "${CAND:-}" ]; then
    ./build.sh > "$RUN/build.txt" 2>&1 || { echo "TIMING FAILED: build (log: $RUN/build.txt)"; exit 1; }
    CAND=$RUN/cand
    mkdir -p "$CAND" && cp build/bergdb.jar "$CAND/" && cp -R build/stress "$CAND/stress" || exit 1
fi
# The reference: the release's tag, cloned and built once.
# In a directory named .noindex, which Spotlight leaves alone (its indexing of a new clone
# held F53's load near 13 in 026-25, section 7).
REFREPO=$JAVADIR/build/timing/ref.noindex/$REFTAG
if [ -z "${REF:-}" ]; then
    if [ ! -f "$REFREPO/java/build/bergdb.jar" ]; then
        rm -rf "$REFREPO"
        git clone -q --branch "$REFTAG" "$JAVADIR/.." "$REFREPO" 2> "$RUN/ref-clone.txt" \
            || { echo "TIMING FAILED: clone of $REFTAG (log: $RUN/ref-clone.txt)"; exit 1; }
        (cd "$REFREPO/java" && ./build.sh) > "$RUN/ref-build.txt" 2>&1 \
            || { echo "TIMING FAILED: build of $REFTAG (log: $RUN/ref-build.txt)"; exit 1; }
    fi
    REF=$REFREPO/java/build
fi
echo "Candidate: $CAND; reference: $REF" >> "$REPORT"
if [ "$STEPS" = prepare ]; then
    echo "Candidate: $CAND"
    echo "Reference: $REF"
    exit 0
fi

# median: the median of the numbers on standard input, one a line.
median() {
    sort -n | awk '{ v[NR] = $1 } END { if (NR == 0) exit 1
        if (NR % 2) print v[(NR + 1) / 2]; else printf "%.3f\n", (v[NR / 2] + v[NR / 2 + 1]) / 2 }'
}

# ---- core ----
core() {
    echo "core: CORE, $ROUNDS ABBA rounds" >> "$REPORT"
    : > "$RUN/core-cand.txt"; : > "$RUN/core-ref.txt"
    i=1
    while [ $i -le "$ROUNDS" ]; do
        for side in cand ref ref cand; do
            if ! quiet_within "$RUNWAIT"; then
                INTERRUPTED="$INTERRUPTED core"
                echo "  stopped: the machine busy for $RUNWAIT minutes (${IDLE}% idle)" >> "$REPORT"
                return
            fi
            if [ $side = cand ]; then D=$CAND; else D=$REF; fi
            out=$RUN/core-$side-$i-$(date +%H%M%S).txt
            echo "# idle ${IDLE}%, $(uptime)" > "$out"
            "$JAVA" -cp "$D/bergdb.jar" bergdb.dev.props.Core >> "$out" 2>&1
            c=$(grep -o 'CORE:[0-9.]* ([^)]*)' "$out" | tail -1)
            if [ -z "$c" ]; then
                FAILED="$FAILED core"
                echo "  $side: no CORE line (log: $out)" >> "$REPORT"
                return
            fi
            echo "  $side round $i: $c (idle ${IDLE}%)" >> "$REPORT"
            echo "$c" | sed 's/CORE:\([0-9.]*\).*/\1/' >> "$RUN/core-$side.txt"
        done
        i=$((i + 1))
    done
    mc=$(median < "$RUN/core-cand.txt"); mr=$(median < "$RUN/core-ref.txt")
    ratio=$(awk -v c="$mc" -v r="$mr" 'BEGIN { printf "%.3f", c / r }')
    echo "  CORE median: candidate $mc, reference $mr, ratio $ratio (smaller is faster;" \
        "alert above $CORE_ALERT)$NOTE" >> "$REPORT"
    if awk -v x="$ratio" -v a="$CORE_ALERT" 'BEGIN { exit !(x > a) }'; then
        ALERTS="$ALERTS core"
    fi
}

# ---- pauses ----
# pausemax FILE: the longest get or commit of the probe's phases, in ms.
pausemax() {
    awk '/^phase/ { p = 1 } p && /^  (gets|commits) / {
            s = $0; sub(/.* max /, "", s); sub(/ ms.*/, "", s); if (s + 0 > m) m = s + 0 }
        END { printf "%.1f\n", m }' "$1"
}
pauses() {
    echo "pauses: PauseProbe, ZGC, phases of $PAUSE_SECONDS s, ABBA" >> "$REPORT"
    : > "$RUN/pauses-cand.txt"; : > "$RUN/pauses-ref.txt"
    for side in cand ref ref cand; do
        if ! quiet_within "$RUNWAIT"; then
            INTERRUPTED="$INTERRUPTED pauses"
            echo "  stopped: the machine busy for $RUNWAIT minutes (${IDLE}% idle)" >> "$REPORT"
            return
        fi
        if [ $side = cand ]; then D=$CAND; else D=$REF; fi
        out=$RUN/pauses-$side-$(date +%H%M%S).txt
        echo "# idle ${IDLE}%, $(uptime)" > "$out"
        "$JAVA" -XX:+UseZGC -Xmx2g -Dseconds="$PAUSE_SECONDS" -Ddir="$RUN/pauseprobe" \
            -cp "$D/bergdb.jar:$D/stress" bergdb.core.PauseProbe >> "$out" 2>&1
        rm -rf "$RUN/pauseprobe"
        if ! grep -q '^PAUSE PROBE OK' "$out"; then
            FAILED="$FAILED pauses"
            echo "  $side: PAUSE PROBE not OK (log: $out)" >> "$REPORT"
            return
        fi
        m=$(pausemax "$out")
        echo "  $side: longest get or commit $m ms (idle ${IDLE}%)" >> "$REPORT"
        echo "$m" >> "$RUN/pauses-$side.txt"
    done
    mc=$(sort -n "$RUN/pauses-cand.txt" | tail -1); mr=$(sort -n "$RUN/pauses-ref.txt" | tail -1)
    echo "  longest: candidate $mc ms, reference $mr ms (guide $PAUSE_GUIDE_MS ms)$NOTE" >> "$REPORT"
    if awk -v x="$mc" -v g="$PAUSE_GUIDE_MS" 'BEGIN { exit !(x > g) }'; then
        ALERTS="$ALERTS pauses"
    fi
}

# ---- perf ----
perf() {
    echo "perf: performance.sh ab, SUITE=release, $REFTAG against current" >> "$REPORT"
    if [ ! -d "$REFREPO/.git" ]; then
        git clone -q --branch "$REFTAG" "$JAVADIR/.." "$REFREPO" 2> "$RUN/ref-clone.txt" || {
            FAILED="$FAILED perf"
            echo "  the clone of $REFTAG failed (log: $RUN/ref-clone.txt)" >> "$REPORT"
            return
        }
    fi
    if [ ! -f "$REFREPO/java/build/perf/builds/ref/identity.env" ]; then
        (cd "$REFREPO" && sh java/stress/performance.sh build ref) > "$RUN/perf-ref-build.txt" 2>&1 || {
            FAILED="$FAILED perf"
            echo "  the reference's preserved build failed (log: $RUN/perf-ref-build.txt)" >> "$REPORT"
            return
        }
    fi
    if [ "$FORCE" = 1 ]; then PF=1; else PF=0; fi
    SUITE=release FORCE=$PF sh stress/performance.sh ab "$REFREPO/java/build/perf/builds/ref" current \
        > "$RUN/perf.txt" 2>&1
    rc=$?
    echo "  $(grep '^Comparison exit code' "$RUN/perf.txt" | cut -c1-60) (log: $RUN/perf.txt)$NOTE" \
        >> "$REPORT"
    case $rc in
        0) ;;
        1) ALERTS="$ALERTS perf" ;;
        *) if grep -q 'not quiet' "$RUN/perf.txt"; then INTERRUPTED="$INTERRUPTED perf"
           else FAILED="$FAILED perf"; fi ;;
    esac
}

for s in $STEPS; do
    $s
done
finish
