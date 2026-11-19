#!/bin/sh
# The f-tests (bergdb.dev.F, the Nano test group "f"), with assertions on
# (-ea): functional tests with a larger scope than the unit tests, each
# within about 10 seconds. Run them before every commit (before-commit.sh
# runs them, with the unit tests); level3.sh runs them too.
#
# Usage: java/f.sh [-c classPattern] [-m methodPattern] [-v | -vv | -d | -s]
#   The options go to the test runner; -c and -m are regular expressions
#   for the test class and method names. See bergdb.dev.NanotestForBergDB.
#
# Builds with build.sh, then runs the tests. Prints their output and keeps a
# copy in build/test/f.txt. Exits with status 1 unless the tests print
# SUCCESS. Set JAVA_HOME or PATH for the JDK; the build needs javac too.
#
# Kind: functional (bergdb 028-23): the result does not depend on the machine's speed or
# load; the tests' time limits are hang guards, generous for a loaded machine.

cd "$(dirname "$0")"
echo "Kind: functional"

JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi

LOG=build/test/f.txt

./build.sh > /dev/null || { echo "F FAILED: build"; exit 1; }
mkdir -p build/test
$JAVA -ea -cp build/bergdb.jar bergdb.dev.F "$@" 2>&1 | tee $LOG
grep -q '^SUCCESS' $LOG || { echo "F FAILED (log: java/$LOG)"; exit 1; }
