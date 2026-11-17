#!/bin/sh
# The unit tests (bergdb.dev.Unit, the Nano test group "unit"), with
# assertions on (-ea) and Java's own check of the writer's contract
# (TransCheck, the system property transcheck=1; bergdb 030-09). Each test
# should be fast, normally max 100 ms. Run
# them before every commit (before-commit.sh runs them, with the f-tests);
# level1.sh to level4.sh run them too.
#
# Usage: java/unit.sh [-c classPattern] [-m methodPattern] [-v | -vv | -d | -s]
#   The options go to the test runner; -c and -m are regular expressions
#   for the test class and method names. See bergdb.dev.NanotestForBergDB.
#
# Builds with build.sh, then runs the tests. Prints their output and keeps a
# copy in build/test/unit.txt. Exits with status 1 unless the tests print
# SUCCESS. Set JAVA_HOME or PATH for the JDK; the build needs javac too.

cd "$(dirname "$0")"

JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi

LOG=build/test/unit.txt

./build.sh > /dev/null || { echo "UNIT FAILED: build"; exit 1; }
mkdir -p build/test
$JAVA -ea -Dtranscheck=1 -cp build/bergdb.jar bergdb.dev.Unit "$@" 2>&1 | tee $LOG
grep -q '^SUCCESS' $LOG || { echo "UNIT FAILED (log: java/$LOG)"; exit 1; }
