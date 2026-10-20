#!/bin/sh
# The night tests (bergdb.dev.Night, the Nano test group "night"), with
# assertions on (-ea): long-running tests of 2013 to 2015 that no level
# script runs, about 4.5 minutes. Not a gate. stress/night.sh runs the
# same tests with the output in a log only and prints NIGHT OK.
#
# Usage: java/night.sh [-c classPattern] [-m methodPattern] [-v | -vv | -d | -s]
#   The options go to the test runner; -c and -m are regular expressions
#   for the test class and method names. See bergdb.dev.NanotestForBergDB.
#
# Builds with build.sh, then runs the tests. Prints their output and keeps a
# copy in build/test/night.txt. Exits with status 1 unless the tests print
# SUCCESS. Set JAVA_HOME or PATH for the JDK; the build needs javac too.

cd "$(dirname "$0")"

JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi

LOG=build/test/night.txt

./build.sh > /dev/null || { echo "NIGHT FAILED: build"; exit 1; }
mkdir -p build/test
$JAVA -ea -cp build/bergdb.jar bergdb.dev.Night "$@" 2>&1 | tee $LOG
grep -q '^SUCCESS' $LOG || { echo "NIGHT FAILED (log: java/$LOG)"; exit 1; }
