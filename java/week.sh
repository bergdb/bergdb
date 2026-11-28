#!/bin/sh
# The week run (bergdb 028-23, 028-27): the deepest functional testing, on demand, and
# before every release, on a commit near it, not necessarily the one that ships; a minor
# change after it is acceptable (Frans decided, 2026-11-19). Not a gate; read its report
# when it ends. Started by hand, or by the lead (013-04) as a step of its
# plan, from the main tree, with the Android SDK set (see Android below):
#     ANDROID_SDK=/path/to/android/sdk nohup caffeinate -i sh java/week.sh >/dev/null 2>&1 &
#
# Kind: functional, as night.sh: no step's result depends on the machine's speed or load;
# the time limits inside are hang guards. It may run while someone works on the machine,
# and at a low priority with nice -n 10; not with taskpolicy -b on macOS, which throttles
# CPU and disk hard (night.sh's header: several times longer) and so would take the large
# reclaim run past large.sh's 12-hour JVM limit.
# Timing is timing.sh's, which also runs before every release.
#
# A distinct set of tests (Frans decided, 2026-11-19; bergdb 028-27): this script does not
# run night.sh, and night.sh, week.sh and timing.sh are disjoint sets of tests: no step of
# one runs in another, except before-commit.sh, which night.sh and this script run first,
# to fail quickly. Where a harness runs in night.sh too (kill-restart, fuzz, unlinkfuzz,
# harness-soak), this script runs it with other seeds, sizes or durations; 028-27 lists
# each pair and what differs.
#
# Usage: java/week.sh          the week run, about 6 hours on F53 (5.5 to 6.7, an
#                              estimate of 2026-11-26, bergdb 028-64): its longest lane,
#                              the large reclaim run, up to 5.5 hours alone
#        java/week.sh short    a trial of the script: its steps small (13 minutes on
#                              2026-11-26)
#        DRY=1 java/week.sh [short]
#                              prints the steps in order with their commands, runs
#                              nothing (no clone, no report)
#
# It clones HEAD of this repository into build/week/RUN/repo (RUN is the date and time;
# lean/.lake and lean/contractcheck/.lake are copied in) and runs there before-commit, then
# three lanes at once (bergdb 028-64): large-reclaim and conformance-large, each in a
# clone of its own (build/week/RUN/repo-NAME, so that no build of one deletes the jar or
# classes under another's JVMs), beside the other steps, which run one after another in
# RUN/repo. Each step goes on after a failure except the first's (the clones, the steps'
# runner, the report, the interrupt and the news entry are stress/runlib.sh's, which
# night.sh shares). The lanes' times: large-reclaim 5.5 to 6.6 hours with seed 20782's
# order, which wrote the most bytes of those 028-63 measured; the two others 4 to 5 hours
# each (028-64 has the figures, what was measured and what estimated).
#   1. before-commit: before-commit.sh, the unit and f-tests and the demos (about 2
#      minutes). If it fails, the run stops: the rest would test broken code.
#   Then the two steps beside the others, in their own clones:
#   2. large-reclaim: stress/large.sh full, 10 million keys and a long history with
#      reclaim, old reads, bounded kept bytes, clean restarts and a child JVM killed
#      during writes; the day's seed (028-43). Its time depends on the seed's key order
#      (028-63): 79 minutes with seed 20778's local order (028-43), 5.5 hours with seed
#      20782's (2026-11-26, alone on F53), whose order wrote the most bytes of those that
#      028-63 measured; few seeds give an order as local as 20778's. This workload is
#      only here, disjoint from night.sh's smaller reclaim tests and timing.sh. A failing
#      run's data and build stay in RUN/large-reclaim-failure/ when this script removes
#      its temporary clone.
#   3. conformance-large: the Lean checker built (lake build in lean/), then
#      stress/conformance.sh large, 12 traces of 1,000 to 5,000 transactions at node sizes
#      8 to 62, on the day's seeds: 2 a configuration, from the day's number times 1000
#      plus 700 (Frans, 2026-11-20; night.sh runs the medium set, and its day steps the
#      other sets from times 1000). Each trace's seed is in its name and its log line; a
#      failing trace has a FAILED line with the command that makes it again from its seed,
#      and is kept with its outputs in build/week/RUN/traces/; 4 to 4.7 hours (2026-11-20
#      and 25), most of it its longest trace (a check of 3.9 hours on 2026-11-25).
#   And one after another, in RUN/repo:
#   4. apps-quick, apps-soak-cc, apps-kill-cc: stress/apps.sh, the user applications of
#      024-26, 026-13, 026-26, 031-08 (parts A and B) and 031-02 (its header), built against the
#      clone's own release jar: quick (about 15 minutes), soak and kill rounds with the
#      day's number as N, new seeds each day (about 105 and 95 minutes; 031-08's and
#      031-02's apps added about 65 and 65, and 9 to quick, on 2026-11-28, partly
#      estimated). Soak and kill with CC (below).
#   5. kill-restart-week, kill-restart-cc: stress/kill-restart.sh, its self-check and 1,000
#      kills on each of three seeds (the day's number times 10, plus 1 to 3; night.sh's
#      seed is the date, YYYYMMDD), the third with CC; about 80 minutes. Stops at the
#      first failure, which keeps its database until the next seed starts.
#   6. fuzz-week: stress/fuzz.sh for 60 minutes, seeds from the day's number times 1000
#      plus 100 (night's 12 turns take those from plus 0).
#   7. unlinkfuzz-week: stress/unlinkfuzz.sh with only the day's block of seeds, from the
#      day's number times 1000 plus 500 (night.sh runs the fixed block and the day's from
#      plus 0); about 2.5 minutes.
#   8. harness-soak-week, harness-soak-cc: stress/harness-soak.sh, ten rounds (night.sh:
#      two), seeds from the day's number times 1000 plus 100 (night.sh's from the date
#      times 1000): rounds 0 to 6, then rounds 7 to 9 with CC (-f 7 -r 3); about 20
#      minutes.
#   9. apptraces-week: stress/apptraces.sh week, the user apps' workloads against the
#      model (bergdb 030-31): the apps larger than night.sh's apptraces step, DeleteHeavy
#      at node sizes 8 to 62 and WorstCase too, with seeds from the day's number (night.sh:
#      fixed seeds, small); about 15 minutes.
#  10. android: stress/android.sh, the unit tests and the demos on an Android emulator;
#      about 3 minutes.
# The steps' times are those of 2026-11-19 to 25, when all ran one after another; since
# 2026-11-26 (bergdb 028-64) the steps are the same, with the same seeds and sizes, and
# the lanes slow each other somewhat.
# With "short": before-commit; beside the others, large-reclaim quick and conformance small
# with 1 seed in place of large; apps quick with CC (so that the trial takes the apps' path
# of CC), kill-restart 10 kills on two seeds, the second with CC, fuzz 1 minute, unlinkfuzz
# the day's block, harness-soak rounds 0 and 1, round 1 with CC, android.
#
# The aim for the whole run is about 10 hours on F53, at most 12 (Frans, 2026-11-26); no
# guard of the whole run enforces it (Frans decided, 2026-11-26): a step without a guard of
# its own that hangs holds the run without a report, as before 028-64. An interrupt (INT,
# TERM) of this script kills the steps' processes too, the background steps' with the
# others (runlib.sh's run_stop); the run's directory stays.
#
# CC (bergdb 030-30): the steps whose names end in -cc run with Java's commit-time check
# of the writer's contract on (TransCheck; bergdb 030-09, section 3; 030-20) at every
# commit of every JVM they start, their children too, through the environment variable
# BERGDB_TRANSCHECK (with_cc below): the apps' soak and kill rounds, the third seed of
# kill-restart and three of the harness soak's ten rounds; each harness runs without CC
# as well. Measured on 2026-11-20, CC adds about 4 minutes to the full run, and checks
# about 4.4 million commits (030-30). Each JVM appends its summary to
# build/cc/NAME.txt at its exit, and a failure at once; a failure fails the step with the
# line CC FAILED and the check's message, and a step whose JVMs wrote no summary fails too.
# The step's line in the report gives the commits checked by the JVMs that ended normally
# (a JVM killed with SIGKILL writes no summary).
#
# It writes build/week/RUN/report.txt (the commit, the JDK, whether the Android SDK is set,
# the lanes, each step's last line, result and time, the two steps of the
# other lanes last, and WEEK OK or WEEK FAILED with the run's minutes, less than the sum of
# the steps'), each step's output in STEP.txt, and the scripts' *.txt logs in logs/; then
# deletes the clones and their databases, and adds a tools/news.sh entry. Exits with
# status 1 if a step failed.
#
# Android: the android step needs the Android SDK (bergdb 006-18-03, section 3, says how to
# install it) through the environment, which this script passes on to stress/android.sh:
# ANDROID_SDK, the SDK's directory (or ANDROID_HOME); ANDROID_USER_HOME, whose avd/ holds
# the AVD (default user/ beside the SDK); ANDROID_AVD, API and PORT (android.sh's header).
# The Android tests are part of the week run (Frans decided, 2026-11-19): without the SDK
# the step fails, and the run is WEEK FAILED.
#
# Set JAVA_HOME or PATH for the JDK; the build needs javac too, and the Lean steps elan.

cd "$(dirname "$0")" || exit 1
echo "Kind: functional"
# JAVA, DAY, run_start, step, step_bg, step_wait, run_stop and run_finish
# (bergdb 028-27, 028-64).
. ./stress/runlib.sh

SHORT=0
case "${1:-}" in
    "") ;;
    short) SHORT=1 ;;
    *) echo "Usage: java/week.sh [short]"; exit 2 ;;
esac

SDK=${ANDROID_SDK:-${ANDROID_HOME:-}}
if [ -n "$SDK" ]; then
    SDKLINE="Android SDK: $SDK"
else
    SDKLINE="Android SDK: not set (ANDROID_SDK, ANDROID_HOME): the android step fails"
    echo "week.sh: ANDROID_SDK (or ANDROID_HOME) is not set: the android step will fail" \
        "(the header says how to start it)"
fi

if [ $SHORT = 1 ]; then
    run_start week "Week run" ", short" "$SDKLINE
Lanes: large-reclaim-quick and conformance-small beside the other steps, each in its own clone"
else
    run_start week "Week run" "" "$SDKLINE
Lanes: large-reclaim and conformance-large beside the other steps, each in its own clone"
fi
# An interrupt kills the steps' processes too, the background steps' with the others
# (runlib.sh's run_stop; bergdb 028-64).
[ "$DRY" = 1 ] || trap run_stop INT TERM

# kill_seeds KILLS SEED...: kill-restart.sh with each seed in turn, KILLS kills each; stops
# at the first failure, whose database stays in build/kill-restart/ (the next run would
# delete it).
kill_seeds() {
    kills=$1; shift
    for seed in "$@"; do
        sh stress/kill-restart.sh $kills $seed || return 1
    done
}

# with_cc NAME COMMAND...: the command with Java's commit-time check of the writer's
# contract on (CC; bergdb 030-09, section 3; 030-30) in every JVM that it starts, their
# children too: the environment variable BERGDB_TRANSCHECK names the file build/cc/NAME.txt,
# to which each JVM appends its summary line at its exit (a JVM killed with SIGKILL leaves
# none) and its first failure at once. Prints the command's output, then CC FAILED with the
# first failure, which fails the step whatever the command returned, or the command's last
# line with the commits that the JVMs that ended normally checked.
with_cc() {
    name=$1; shift
    mkdir -p build/cc
    f=$(pwd)/build/cc/$name.txt
    rm -f $f build/cc/$name.out
    # In a subshell: the variable reaches the command's JVMs, and no later step.
    (export BERGDB_TRANSCHECK=$f; "$@") > build/cc/$name.out 2>&1
    st=$?
    cat build/cc/$name.out
    if grep -q '^TRANSCHECK FAILURE: \|^TRANSCHECK: .*; first failure: ' $f 2> /dev/null; then
        echo "CC FAILED: Java's commit-time check of the writer's contract failed in" \
            "$(grep -c '^TRANSCHECK FAILURE: ' $f) JVMs; the first: $(grep -m 1 '^TRANSCHECK FAILURE: ' $f \
            | cut -c 21-400) (log: java/build/cc/$name.txt)"
        return 1
    fi
    sum=$(awk '/^TRANSCHECK: / {n++; t += $2} END {print t + 0 " commits checked in " n + 0 " JVMs"}' $f 2> /dev/null)
    case "$sum" in
        *" in 0 JVMs") echo "CC FAILED: no JVM wrote its summary to java/build/cc/$name.txt: the check was not on"; return 1 ;;
    esac
    echo "$(tail -1 build/cc/$name.out); CC: $sum that ended normally, no failure"
    return $st
}

# conformance SET [SEEDS [FIRST]]: the jar and the Lean checker built first, as the level scripts
# do for theirs (in its own clone, no other step builds them there), then stress/conformance.sh.
conformance() {
    ./build.sh > /dev/null || { echo "CONFORMANCE FAILED: build"; return 1; }
    (cd ../lean && lake build) > build/lake-week.txt 2>&1 \
        || { echo "CONFORMANCE FAILED: lake build (log: java/build/lake-week.txt)"; return 1; }
    sh stress/conformance.sh "$@"; st=$?
    # A run from a first seed (the day's): its failing traces kept (runlib.sh's keep_traces).
    [ -n "$3" ] && keep_traces $1-$3
    return $st
}

# Preserve the large database and its exact build on failure, before run_finish removes
# the temporary clone. Passing logs are collected by run_finish as for the other steps.
large_reclaim() {
    sh stress/large.sh "$@"
    large_status=$?
    if [ "$large_status" -ne 0 ] && [ -d build/large ]; then
        mkdir -p "$RUN/large-reclaim-failure" || return 1
        for large_result in build/large/*; do
            [ -d "$large_result" ] || continue
            mv "$large_result" "$RUN/large-reclaim-failure/" || return 1
        done
        echo "LARGE RECLAIM FAILED: data and build kept in $RUN/large-reclaim-failure/"
    fi
    return "$large_status"
}

if ! step before-commit sh before-commit.sh; then
    echo "(the other steps not run: before-commit.sh failed)" >> $REPORT
    run_finish
    exit 1
fi
# The two longest steps beside the others, each in a clone of its own (runlib.sh's step_bg;
# bergdb 028-64); the steps whose names end in -cc run with CC on (with_cc; bergdb 030-30).
if [ $SHORT = 0 ]; then
    step_bg large-reclaim large_reclaim full $DAY
    step_bg conformance-large conformance large 2 $((DAY * 1000 + 700))
    step apps-quick sh stress/apps.sh quick
    step apps-soak-cc with_cc apps-soak sh stress/apps.sh soak $DAY
    step apps-kill-cc with_cc apps-kill sh stress/apps.sh kill $DAY
    step kill-restart-week kill_seeds 1000 $((DAY * 10 + 1)) $((DAY * 10 + 2))
    step kill-restart-cc with_cc kill-restart kill_seeds 1000 $((DAY * 10 + 3))
    step fuzz-week sh stress/fuzz.sh 60 $((DAY * 1000 + 100))
    step unlinkfuzz-week sh stress/unlinkfuzz.sh $((DAY * 1000 + 500)) day
    step harness-soak-week sh stress/harness-soak.sh -r 7 -b $((DAY * 1000 + 100)) \
        -o build/harness-soak-week
    step harness-soak-cc with_cc harness-soak sh stress/harness-soak.sh -f 7 -r 3 \
        -b $((DAY * 1000 + 100)) -o build/harness-soak-cc
    step apptraces-week sh stress/apptraces.sh week
else
    step_bg large-reclaim-quick large_reclaim quick $DAY
    step_bg conformance-small conformance small 1
    step apps-quick-cc with_cc apps-quick sh stress/apps.sh quick
    step kill-restart-week kill_seeds 10 $((DAY * 10 + 1))
    step kill-restart-cc with_cc kill-restart kill_seeds 10 $((DAY * 10 + 2))
    step fuzz-week sh stress/fuzz.sh 1 $((DAY * 1000 + 100))
    step unlinkfuzz-week sh stress/unlinkfuzz.sh $((DAY * 1000 + 500)) day
    step harness-soak-week sh stress/harness-soak.sh -r 1 -b $((DAY * 1000 + 100)) \
        -o build/harness-soak-week
    step harness-soak-cc with_cc harness-soak sh stress/harness-soak.sh -f 1 -r 1 \
        -b $((DAY * 1000 + 100)) -o build/harness-soak-cc
fi
step android sh stress/android.sh
# The lanes' lines last, in the order in which they started.
step_wait

run_finish
