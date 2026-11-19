#!/bin/sh
# The night run (since 2026-10-20, bergdb 006-03): the checks that
# before-commit.sh leaves out, on a clean copy of the committed code. Not a
# gate; read its report when it ends. No fixed time (since 2026-11-06,
# bergdb 013-02, section 2): it is started by hand, or by the day's
# coordinator session (013-02) when the machine has room for it, from the
# main tree:
#     nohup caffeinate -i sh java/night.sh >/dev/null 2>&1 &
# caffeinate -i keeps the Mac awake.
#
# Kind: functional (bergdb 028-23): no step's result depends on the machine's speed or
# load; the time limits inside are hang guards, generous for a loaded machine, and a
# number of time that a step prints (level1.sh's CORE) is information, never a pass or a
# fail. So it may run while someone works on the machine, beside other work, and at a
# low priority: `nice -n 10 sh java/night.sh`, or on macOS `taskpolicy -b sh
# java/night.sh` (a background process: CPU and disk throttled hard, the run takes
# several times longer). Timing has its own script, timing.sh, the only one that needs a
# quiet machine. The three functional scripts: before-commit.sh before each commit, this
# one about once a day while there is development, week.sh on demand and before every
# release. This one, week.sh and timing.sh are disjoint sets of tests (Frans decided,
# 2026-11-19; bergdb 028-27): no step of one runs in another, except before-commit.sh,
# which this one and week.sh run first; where a harness runs here and in week.sh, week.sh
# runs it with other seeds and sizes (028-27 lists them).
#
# Usage: java/night.sh          the night run, about 2.5 hours on F53 (100 minutes
#                               before bergdb 030-13, which adds about 30 to 35)
#        java/night.sh tests [-c classPattern] [-m methodPattern] [-v | -vv | -d | -s]
#                               only the night tests, here, about 4.5 minutes
#        DRY=1 java/night.sh    prints the steps in order with their commands, runs
#                               nothing (no clone, no report)
# The large conformance set, once "night.sh large", is week.sh's since 2026-11-19 (bergdb
# 028-27), and week.sh no longer runs this script's steps.
#
# The night tests (bergdb.dev.Night, the Nano test group "night") are the
# long-running tests of 2013 to 2015, with assertions on (-ea); with "tests",
# the options go to the test runner (-c and -m are regular expressions for
# the test class and method names; see bergdb.dev.NanotestForBergDB), the
# output is printed and kept in build/test/night.txt.
#
# The night run clones HEAD of this repository into build/night/RUN/repo (RUN
# is the date and time; lean/.lake and lean/contractcheck/.lake are copied in, so
# that lake builds only what changed) and runs there, one after another, going
# on after a failure (the clone, the steps' runner, the report and the news entry are
# stress/runlib.sh's, which week.sh shares):
#   1. before-commit.sh: the unit and f-tests.
#   2. stress/core-build.sh unit f: the Core Layer built alone, with an empty
#      class path, a program that calls Db with only it, and its unit and
#      f-tests on it; about a minute (bergdb 006-08, 005-56; 010-01, P12).
#  2b. stress/transcheck.sh: the unit and f-tests with Java's own check of
#      the writer's contract on (TransCheck); about a minute (bergdb 030-09).
#   3. stress/level1.sh to level4.sh, full: the random stress programs at
#      scale (RestartStress, CrashTest, RestartInvariance, ReclaimStress,
#      EvictionInvariance, LargerThanMemory, ...), conformance with the Lean
#      model (the small, drain, reclaim and evict sets), the writer's contract
#      and the bridge on the small and drain sets (level2.sh, bergdb 030-13),
#      and level1.sh's MEM and SS limits.
#   4. stress/count-gates.sh: count gates of aims 2 and 3 of release 2026.5
#      at 1M keys (the largest record, the reachable key nodes against a
#      twin's, the stream kept under reclaim, back to empty after a fill and
#      its deletes); about 3 minutes (bergdb 024-30).
#   5. stress/lean-tests.sh: the Lean model's test programs, sistest,
#      phystest and reclaimtest, at small sizes; about 4.5 minutes (bergdb
#      021-03).
#   6. The night tests.
#   7. stress/harness-soak.sh -r 2: two rounds of the Pub layer's randomized
#      harnesses (IndexHarness, IndexJobsHarness, PrimaryHarness, the object
#      codec's and the Data Objects' properties) with other seeds and larger
#      sizes than the night tests' runs; about 4 minutes (bergdb 020-17).
#   8. stress/fuzz.sh 12: FormatFuzzer's six areas, the readers of bytes that
#      2026.4 added, each against its spec, for 12 minutes, with new seeds
#      each day (bergdb 020-16).
#   9. stress/unlinkfuzz.sh: UnlinkFuzz, the fuzzer of the Dag's delete path
#      (the upward unlink and the take-back of bergdb 023-05), on its fixed
#      list of configurations, each with a fixed block of seeds and a block
#      of new seeds each day; about 5 minutes (bergdb 024-09, step A1).
#  10. stress/kill-restart.sh 1000: the Pub layer's kill-and-restart harness,
#      its self-check and 1,000 kills of a child JVM with SIGKILL, each start
#      checked against the journal of the children before; about 26 minutes
#      (bergdb 020-15).
#  11. stress/conformance.sh medium: 9 traces of 120 to 500 transactions.
#  11b. stress/contractconf.sh medium: the medium tree set (treeconf.sh medium,
#      27 traces of 120 to 800 transactions, node sizes 8 to 62, written with
#      no tree check, which would take over an hour), then the writer's
#      contract (lean/contract/check.sh) and the bridge
#      (lean/contract/bridge-check.sh) on its traces, four at a time (bergdb
#      030-13); 32 minutes on F53 under a heavy load (2026-11-17), most of it
#      the bridge's six traces of m-d30 and m-d62.
#      level2.sh's step 8b checks both on the small and drain sets.
# It writes build/night/RUN/report.txt (the commit, the JDK, each step's last
# line, result and time, and NIGHT OK or NIGHT FAILED), each step's output in
# STEP.txt, and the scripts' *.txt logs in logs/; then deletes the clone and
# its databases. Exits with status 1 if a step failed. Set JAVA_HOME or PATH
# for the JDK; the build needs javac too, and the Lean steps elan.

cd "$(dirname "$0")" || exit 1
echo "Kind: functional"
# JAVA, DAY, run_start, step and run_finish (bergdb 028-27).
. ./stress/runlib.sh

if [ "$1" = tests ]; then
    shift
    LOG=build/test/night.txt
    ./build.sh > /dev/null || { echo "NIGHT FAILED: build"; exit 1; }
    mkdir -p build/test
    $JAVA -ea -cp build/bergdb.jar bergdb.dev.Night "$@" 2>&1 | tee $LOG
    grep -q '^SUCCESS' $LOG || { echo "NIGHT FAILED (log: java/$LOG)"; exit 1; }
    exit 0
fi

if [ -n "${1:-}" ]; then
    echo "Usage: java/night.sh [tests [OPTIONS]] (\"large\" and \"week\" are week.sh's since bergdb 028-27)"
    exit 2
fi

run_start night "Night run"

# The night tests in the clone (its night.sh may be older than this one).
night_tests() {
    ./build.sh > /dev/null || { echo "NIGHT TESTS FAILED: build"; return 1; }
    mkdir -p build/test
    $JAVA -ea -cp build/bergdb.jar bergdb.dev.Night 2>&1 | tee build/test/night.txt
    grep -q '^SUCCESS' build/test/night.txt
}

step before-commit sh before-commit.sh
step core-build sh stress/core-build.sh unit f
step transcheck sh stress/transcheck.sh
step level1 sh stress/level1.sh
step level2 sh stress/level2.sh
step level3 sh stress/level3.sh
step level4 sh stress/level4.sh
# Count gates of aims 2 and 3 at 1M keys (bergdb 024-30).
step count-gates sh stress/count-gates.sh
step lean-tests sh stress/lean-tests.sh
# The tree model's small cases (bergdb 024-12): lake exe treetest, on one core.
step tree-tests sh stress/tree-tests.sh
step night-tests night_tests
step harness-soak sh stress/harness-soak.sh -r 2
step fuzz sh stress/fuzz.sh 12
step unlinkfuzz sh stress/unlinkfuzz.sh
step kill-restart sh stress/kill-restart.sh 1000
step conformance-medium sh stress/conformance.sh medium
# The writer's contract and the bridge on the medium tree set (bergdb 030-13).
step contract-medium sh stress/contractconf.sh medium

run_finish
