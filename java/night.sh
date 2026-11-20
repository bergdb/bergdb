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
#                               before bergdb 030-13, which adds about 30 to 35;
#                               030-30's two steps on the day's seeds about 13 more)
#        java/night.sh tests [-c classPattern] [-m methodPattern] [-v | -vv | -d | -s]
#                               only the night tests, here, about 4.5 minutes
#        java/night.sh day      only steps 12 and 12b, the sets on the day's seeds, in a
#                               clone as the night run (about 15 minutes); with DAY=N in
#                               the environment, the seeds of day N again (bergdb 030-30)
#        DRY=1 java/night.sh [day]
#                               prints the steps in order with their commands, runs
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
#  11c. lean/pecmp/check.sh medium: the tested writer against the proved writer
#      (pecmp, bergdb 030-28) on the medium set's traces of step 11b, as level2.sh's
#      step 8c on the small, drain and reclaim sets; its own tests first, on level2.sh's
#      small and drain traces. About 1.5 minutes on F53 (added 2026-11-20).
#  12. conformance-day: new seeds each day (bergdb 030-30). Every set of traces above
#      (conformance.sh, treeconf.sh and contractconf.sh, in the level scripts and steps 11
#      to 11c) numbers its seeds from 1: the same traces every night, a regression set.
#      This step runs conformance.sh's sets on the day's seeds, from the day's number
#      times 1000 (CONFSETS_DAY below): small and drain 10 seeds a configuration, reclaim
#      4, evict and medium 3; 211 traces.
#  12b. contract-day: the tree sets on the day's seeds (TREESETS_DAY): contractconf.sh
#      with TREE=1 (the tree check, the writer's contract, the bridge) on small and drain,
#      10 seeds a configuration, and reclaim, 3; then pecmp on them; 195 traces.
#      Both steps 13 minutes on F53 at a load of 20 to 37 (2026-11-20). Each trace's seed
#      is in its name and on its line in the step's log (NAME-SEED: ...), and the step's
#      line in the report gives the seeds. A failing trace has a line FAILED in the log
#      with its seed and the command that makes it again from its seed, and the trace
#      with its outputs is kept in build/night/RUN/traces/ (runlib.sh's keep_traces).
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

DAYONLY=0
case "${1:-}" in
    "") ;;
    day) DAYONLY=1 ;;
    *) echo "Usage: java/night.sh [tests [OPTIONS] | day] (\"large\" and \"week\" are week.sh's since bergdb 028-27)"
       exit 2 ;;
esac

# The night tests in the clone (its night.sh may be older than this one).
night_tests() {
    ./build.sh > /dev/null || { echo "NIGHT TESTS FAILED: build"; return 1; }
    mkdir -p build/test
    $JAVA -ea -cp build/bergdb.jar bergdb.dev.Night 2>&1 | tee build/test/night.txt
    grep -q '^SUCCESS' build/test/night.txt
}

# pecmp on the medium set's traces, which contract-medium wrote; its own tests need the
# small and drain sets' traces of level2.sh's step 8 (bergdb 030-28).
pecmp_medium() {
    (cd ../lean/pecmp && lake build) > build/pecmp-medium-lake.txt 2>&1 \
        || { echo "PECMP FAILED: lake build in lean/pecmp (log: build/pecmp-medium-lake.txt)"; return 1; }
    sh ../lean/pecmp/check.sh medium
}

# The day's seeds (bergdb 030-30): from the day's number times 1000; each set with its
# seeds a configuration.
DSEED=$((DAY * 1000))
CONFSETS_DAY="small:10 drain:10 reclaim:4 evict:3 medium:3"
TREESETS_DAY="small:10 drain:10 reclaim:3"

# conformance_day FIRST SET:SEEDS...: conformance.sh on each set from the seed FIRST; the
# failing traces kept (runlib.sh's keep_traces).
conformance_day() {
    first=$1; shift
    ./build.sh > /dev/null || { echo "CONFORMANCE DAY FAILED: build"; return 1; }
    (cd ../lean && lake build) > build/lake-day.txt 2>&1 \
        || { echo "CONFORMANCE DAY FAILED: lake build (log: build/lake-day.txt)"; return 1; }
    bad=; max=0; n=0
    for x in "$@"; do
        set_name=${x%:*}; seeds=${x#*:}
        [ $seeds -gt $max ] && max=$seeds
        echo "== conformance.sh $set_name $seeds $first: seeds $first to $((first + seeds - 1))"
        sh stress/conformance.sh $set_name $seeds $first || bad="$bad $set_name"
        keep_traces $set_name-$first
        n=$((n + $(ls build/traces/$set_name-$first/*.check.txt 2> /dev/null | wc -l)))
    done
    line="$n traces, seeds $first to $((first + max - 1)) ($*)"
    if [ -n "$bad" ]; then
        echo "CONFORMANCE DAY FAILED:$bad; $line; the FAILED lines in the log"
        return 1
    fi
    echo "CONFORMANCE DAY OK: $line"
}

# contract_day FIRST SET:SEEDS...: contractconf.sh with the tree check (TREE=1) on each set
# from the seed FIRST, then pecmp on their traces; the failing traces kept.
contract_day() {
    first=$1; shift
    ./build.sh > /dev/null || { echo "CONTRACT DAY FAILED: build"; return 1; }
    (cd ../lean/pecmp && lake build) > build/pecmp-day-lake.txt 2>&1 \
        || { echo "CONTRACT DAY FAILED: lake build in lean/pecmp (log: build/pecmp-day-lake.txt)"; return 1; }
    # The fixed seeds' traces that the checkers' own tests take (bridge-faults.sh, pecmp's
    # --cap-h and --top-fault), from level2.sh's step 8; written here when level2.sh did
    # not run (night.sh day).
    if ! ls build/traces/tree-small/mixed-1.trace build/traces/tree-drain/d-30-2.trace \
            build/traces/tree-reclaim/r-del-1.trace > /dev/null 2>&1; then
        echo "== the fixed traces for the checkers' own tests: TREECHECK=none treeconf.sh small 1, drain 2, reclaim 1"
        TREECHECK=none sh stress/treeconf.sh small 1 | tail -1
        TREECHECK=none sh stress/treeconf.sh drain 2 | tail -1
        TREECHECK=none sh stress/treeconf.sh reclaim 1 | tail -1
    fi
    bad=; max=0; n=0; dirs=
    for x in "$@"; do
        set_name=${x%:*}; seeds=${x#*:}
        [ $seeds -gt $max ] && max=$seeds
        echo "== TREE=1 contractconf.sh $set_name $seeds $first: seeds $first to $((first + seeds - 1))"
        TREE=1 sh stress/contractconf.sh $set_name $seeds $first || bad="$bad $set_name"
        dirs="$dirs $set_name-$first"
        n=$((n + $(ls build/traces/tree-$set_name-$first/*.trace 2> /dev/null | wc -l)))
    done
    echo "== lean/pecmp/check.sh$dirs"
    if ! sh ../lean/pecmp/check.sh $dirs; then
        bad="$bad pecmp"
        for d in $dirs; do
            grep '\.trace: ' build/traces/tree-$d/pecmp.txt 2> /dev/null | grep -v ' 0 differ$' \
                | sed 's/: .*//' | while read t; do
                name=$(basename $t .trace); seed=${name##*-}; name=${name%-*}
                echo "build/traces/$t" >> build/traces/tree-$d/failed.txt
                echo "   FAILED $name-$seed, seed $seed: pecmp; trace java/build/traces/$t; rerun from the" \
                    "repository's root: ONLY=$name TREECHECK=none sh java/stress/treeconf.sh ${d%-*} 1 $seed;" \
                    "lean/pecmp/.lake/build/bin/pecmp java/build/traces/tree-${d%-*}-$seed/$name-$seed.trace"
            done
        done
    fi
    for d in $dirs; do keep_traces tree-$d; done
    line="$n traces, seeds $first to $((first + max - 1)) ($*)"
    if [ -n "$bad" ]; then
        echo "CONTRACT DAY FAILED:$bad; $line; the FAILED lines in the log"
        return 1
    fi
    echo "CONTRACT DAY OK: $line"
}

if [ $DAYONLY = 1 ]; then
    run_start night "Night run" ", the day's seeds only (night.sh day)"
else
    run_start night "Night run"
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
    # The tested writer against the proved writer on the medium set's traces (bergdb 030-28).
    step pecmp-medium pecmp_medium
fi
# The sets of traces on the day's seeds (bergdb 030-30).
step conformance-day conformance_day $DSEED $CONFSETS_DAY
step contract-day contract_day $DSEED $TREESETS_DAY

run_finish
