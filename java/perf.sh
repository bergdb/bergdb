#!/bin/sh
# The perf-tests (bergdb.dev.Perf, the Nano test group "perf"): the 2013 to
# 2017 micro benchmarks. Run without -ea, since assertions slow the code
# down. Other work on the machine disturbs the times; for the reference
# performance runs, see stress/performance.sh.
#
# Usage: java/perf.sh [-c classPattern] [-m methodPattern] [-v | -vv | -d | -s]
#   The options go to the test runner; -c and -m are regular expressions
#   for the test class and method names. See bergdb.dev.NanotestForBergDB.
#
# Builds with build.sh, then runs the tests. Prints their output and keeps a
# copy in build/test/perf.txt. Exits with status 1 unless the tests print
# SUCCESS. Set JAVA_HOME or PATH for the JDK; the build needs javac too.

cd "$(dirname "$0")"

JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi

LOG=build/test/perf.txt

./build.sh > /dev/null || { echo "PERF FAILED: build"; exit 1; }
mkdir -p build/test
$JAVA -cp build/bergdb.jar bergdb.dev.Perf "$@" 2>&1 | tee $LOG
grep -q '^SUCCESS' $LOG || { echo "PERF FAILED (log: java/$LOG)"; exit 1; }
