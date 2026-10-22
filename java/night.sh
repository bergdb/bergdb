#!/bin/sh
# The night run (since 2026-10-20, bergdb 006-03): the checks that
# before-commit.sh leaves out, on a clean copy of the committed code. Not a
# gate; read its report in the morning. launchd starts it at 02:10
# (~/Library/LaunchAgents/local.bergdb.nightly.plist, with ProcessType
# Interactive: without it launchd throttles the job and timing tests fail).
#
# Usage: java/night.sh          the night run, about 50 minutes on F53
#        java/night.sh large    the same and the large conformance set,
#                               about 6 hours; by hand
#        java/night.sh tests [-c classPattern] [-m methodPattern] [-v | -vv | -d | -s]
#                               only the night tests, here, about 4.5 minutes
#
# The night tests (bergdb.dev.Night, the Nano test group "night") are the
# long-running tests of 2013 to 2015, with assertions on (-ea); with "tests",
# the options go to the test runner (-c and -m are regular expressions for
# the test class and method names; see bergdb.dev.NanotestForBergDB), the
# output is printed and kept in build/test/night.txt.
#
# The night run clones HEAD of this repository into build/night/RUN/repo (RUN
# is the date and time; lean/.lake is copied in, so that lake builds only what
# changed) and runs there, one after another, going on after a failure:
#   1. before-commit.sh: the unit and f-tests.
#   2. stress/level1.sh to level4.sh, full: the random stress programs at
#      scale (RestartStress, CrashTest, RestartInvariance, ReclaimStress,
#      EvictionInvariance, LargerThanMemory, ...), conformance with the Lean
#      model (the small, reclaim and evict sets), and level1.sh's MEM and SS
#      limits.
#   3. The night tests.
#   4. stress/conformance.sh medium: 9 traces of 120 to 500 transactions.
#   5. With "large": stress/conformance.sh large, 12 traces of 1,000 to 5,000
#      transactions at node sizes 8 to 62; about 5 hours, most of it the two
#      l-big62 traces.
# It writes build/night/RUN/report.txt (the commit, the JDK, each step's last
# line, result and time, and NIGHT OK or NIGHT FAILED), each step's output in
# STEP.txt, and the scripts' *.txt logs in logs/; then deletes the clone and
# its databases. Exits with status 1 if a step failed. Set JAVA_HOME or PATH
# for the JDK; the build needs javac too, and the Lean steps elan.

cd "$(dirname "$0")" || exit 1

JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi

if [ "$1" = tests ]; then
    shift
    LOG=build/test/night.txt
    ./build.sh > /dev/null || { echo "NIGHT FAILED: build"; exit 1; }
    mkdir -p build/test
    $JAVA -ea -cp build/bergdb.jar bergdb.dev.Night "$@" 2>&1 | tee $LOG
    grep -q '^SUCCESS' $LOG || { echo "NIGHT FAILED (log: java/$LOG)"; exit 1; }
    exit 0
fi

LARGE=0
if [ "$1" = large ]; then LARGE=1; fi

REPO=$(git rev-parse --show-toplevel) || { echo "NIGHT FAILED: not in git"; exit 1; }
RUN=$(pwd)/build/night/$(date +%Y-%m-%d-%H%M)
SRC=$RUN/repo
REPORT=$RUN/report.txt
START=$(date +%s)

mkdir -p $RUN || exit 1
git clone -q "$REPO" $SRC || { echo "NIGHT FAILED: clone" | tee $REPORT; exit 1; }
if [ -d "$REPO/lean/.lake" ]; then
    cp -R "$REPO/lean/.lake" $SRC/lean/ 2>/dev/null
fi
{
    echo "Night run $(basename $RUN) on $(hostname -s)"
    echo "Commit: $(git -C $SRC log -1 --format='%h %ad %s' --date=format:'%Y-%m-%d %H:%M')"
    echo "JDK: $($JAVA -version 2>&1 | head -1)"
    echo
} > $REPORT

FAILED=""

# step NAME COMMAND...: runs the command in the clone's java/, output in NAME.txt.
step() {
    name=$1; shift
    s=$(date +%s)
    (cd $SRC/java && "$@") > $RUN/$name.txt 2>&1
    status=$?
    t=$(( $(date +%s) - s ))
    if [ $status = 0 ]; then result=ok; else result=FAILED; FAILED="$FAILED $name"; fi
    printf '%-18s %-6s %5d s   %s\n' $name $result $t "$(tail -1 $RUN/$name.txt)" >> $REPORT
}

# The night tests in the clone (its night.sh may be older than this one).
night_tests() {
    ./build.sh > /dev/null || { echo "NIGHT TESTS FAILED: build"; return 1; }
    mkdir -p build/test
    $JAVA -ea -cp build/bergdb.jar bergdb.dev.Night 2>&1 | tee build/test/night.txt
    grep -q '^SUCCESS' build/test/night.txt
}

step before-commit sh before-commit.sh
step level1 sh stress/level1.sh
step level2 sh stress/level2.sh
step level3 sh stress/level3.sh
step level4 sh stress/level4.sh
step night-tests night_tests
step conformance-medium sh stress/conformance.sh medium
if [ $LARGE = 1 ]; then
    step conformance-large sh stress/conformance.sh large
fi

# The logs, without the databases and traces; then the clone.
(cd $SRC/java/build && find . -name '*.txt' -size -20000k | while read f; do
    mkdir -p "$RUN/logs/$(dirname "$f")"
    cp "$f" "$RUN/logs/$f"
done)
rm -rf $SRC

echo >> $REPORT
if [ -z "$FAILED" ]; then
    echo "NIGHT OK ($(( ($(date +%s) - START) / 60 )) minutes)" >> $REPORT
else
    echo "NIGHT FAILED:$FAILED ($(( ($(date +%s) - START) / 60 )) minutes)" >> $REPORT
fi
cat $REPORT
[ -z "$FAILED" ]
