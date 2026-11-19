#!/bin/sh
# The week run (bergdb 028-23, 028-27): the deepest functional testing, on demand, and
# before every release, on a commit near it, not necessarily the one that ships; a minor
# change after it is acceptable (Frans decided, 2026-11-19). Not a gate; read its report
# when it ends. Started by hand, or by the day's coordinator (013-02) as a step of its
# plan, from the main tree, with the Android SDK set (see Android below):
#     ANDROID_SDK=/path/to/android/sdk nohup caffeinate -i sh java/week.sh >/dev/null 2>&1 &
#
# Kind: functional, as night.sh: no step's result depends on the machine's speed or load;
# the time limits inside are hang guards. It may run while someone works on the machine,
# and at a low priority (nice -n 10, or taskpolicy -b on macOS; night.sh's header says
# more). Timing is timing.sh's, which also runs before every release.
#
# A distinct set of tests (Frans decided, 2026-11-19; bergdb 028-27): this script does not
# run night.sh, and night.sh, week.sh and timing.sh are disjoint sets of tests: no step of
# one runs in another, except before-commit.sh, which night.sh and this script run first,
# to fail quickly. Where a harness runs in night.sh too (kill-restart, fuzz, unlinkfuzz,
# harness-soak), this script runs it with other seeds, sizes or durations; 028-27 lists
# each pair and what differs.
#
# Usage: java/week.sh          the week run, about 9 hours on F53 (an estimate of
#                              2026-11-19 from the steps' times below)
#        java/week.sh short    a trial of the script: its steps small (13 minutes on
#                              F53 at a load of 13 to 22, 2026-11-19)
#        DRY=1 java/week.sh [short]
#                              prints the steps in order with their commands, runs
#                              nothing (no clone, no report)
#
# It clones HEAD of this repository into build/week/RUN/repo (RUN is the date and time;
# lean/.lake and lean/contractcheck/.lake are copied in) and runs there, one after another,
# going on after a failure except the first's (the clone, the steps' runner, the report and
# the news entry are stress/runlib.sh's, which night.sh shares):
#   1. before-commit: before-commit.sh, the unit and f-tests and the demos (about 2
#      minutes). If it fails, the run stops: the rest would test broken code.
#   2. apps-quick, apps-soak, apps-kill: stress/apps.sh, the user applications of 024-26
#      and 026-13 (its header), built against the clone's own release jar: quick (about
#      6 minutes), soak and kill rounds with the day's number as N, new seeds each day
#      (about 40 and 30 minutes).
#   3. kill-restart-week: stress/kill-restart.sh, its self-check and 1,000 kills on each of
#      three seeds (the day's number times 10, plus 1 to 3; night.sh's seed is the date,
#      YYYYMMDD); about 80 minutes. Stops at the first failure, which keeps its database.
#   4. fuzz-week: stress/fuzz.sh for 60 minutes, seeds from the day's number times 1000
#      plus 100 (night's 12 turns take those from plus 0).
#   5. unlinkfuzz-week: stress/unlinkfuzz.sh with only the day's block of seeds, from the
#      day's number times 1000 plus 500 (night.sh runs the fixed block and the day's from
#      plus 0); about 2.5 minutes.
#   6. harness-soak-week: stress/harness-soak.sh -r 10 (night.sh: -r 2), seeds from the
#      day's number times 1000 plus 100 (night.sh's from the date times 1000); about 20
#      minutes.
#   7. conformance-large: the Lean checker built (lake build in lean/), then
#      stress/conformance.sh large, 12 traces of 1,000 to 5,000 transactions at node sizes
#      8 to 62 (night.sh runs the medium set); about 5 hours.
#   8. android: stress/android.sh, the unit tests and the demos on an Android emulator;
#      about 3 minutes.
# With "short": before-commit, apps quick, kill-restart 10 kills on two seeds, fuzz 1
# minute, unlinkfuzz the day's block, harness-soak -r 1, conformance small with 1 seed in
# place of large, android.
#
# It writes build/week/RUN/report.txt (the commit, the JDK, whether the Android SDK is set,
# each step's last line, result and time, and WEEK OK or WEEK FAILED), each step's output
# in STEP.txt, and the scripts' *.txt logs in logs/; then deletes the clone and its
# databases, and adds a tools/news.sh entry. Exits with status 1 if a step failed.
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
# JAVA, DAY, run_start, step and run_finish (bergdb 028-27).
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
    run_start week "Week run" ", short" "$SDKLINE"
else
    run_start week "Week run" "" "$SDKLINE"
fi

# kill_seeds KILLS SEED...: kill-restart.sh with each seed in turn, KILLS kills each; stops
# at the first failure, whose database stays in build/kill-restart/ (the next run would
# delete it).
kill_seeds() {
    kills=$1; shift
    for seed in "$@"; do
        sh stress/kill-restart.sh $kills $seed || return 1
    done
}

# conformance SET SEEDS...: the jar and the Lean checker built first, as the level scripts
# do for theirs (no step before it builds the checker), then stress/conformance.sh.
conformance() {
    ./build.sh > /dev/null || { echo "CONFORMANCE FAILED: build"; return 1; }
    (cd ../lean && lake build) > build/lake-week.txt 2>&1 \
        || { echo "CONFORMANCE FAILED: lake build (log: java/build/lake-week.txt)"; return 1; }
    sh stress/conformance.sh "$@"
}

if ! step before-commit sh before-commit.sh; then
    echo "(the other steps not run: before-commit.sh failed)" >> $REPORT
    run_finish
    exit 1
fi
if [ $SHORT = 0 ]; then
    step apps-quick sh stress/apps.sh quick
    step apps-soak sh stress/apps.sh soak $DAY
    step apps-kill sh stress/apps.sh kill $DAY
    step kill-restart-week kill_seeds 1000 $((DAY * 10 + 1)) $((DAY * 10 + 2)) $((DAY * 10 + 3))
    step fuzz-week sh stress/fuzz.sh 60 $((DAY * 1000 + 100))
    step unlinkfuzz-week sh stress/unlinkfuzz.sh $((DAY * 1000 + 500)) day
    step harness-soak-week sh stress/harness-soak.sh -r 10 -b $((DAY * 1000 + 100)) \
        -o build/harness-soak-week
    step conformance-large conformance large
else
    step apps-quick sh stress/apps.sh quick
    step kill-restart-week kill_seeds 10 $((DAY * 10 + 1)) $((DAY * 10 + 2))
    step fuzz-week sh stress/fuzz.sh 1 $((DAY * 1000 + 100))
    step unlinkfuzz-week sh stress/unlinkfuzz.sh $((DAY * 1000 + 500)) day
    step harness-soak-week sh stress/harness-soak.sh -r 1 -b $((DAY * 1000 + 100)) \
        -o build/harness-soak-week
    step conformance-small conformance small 1
fi
step android sh stress/android.sh

run_finish
