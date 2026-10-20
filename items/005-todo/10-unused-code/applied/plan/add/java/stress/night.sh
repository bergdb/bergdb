#!/bin/sh
# The night tests (bergdb.dev.Night, the test group "night"): long-running
# tests of BergDB from 2013 to 2015 that no level script runs. Not a gate;
# run it now and then, and after larger changes (bergdb 005-10, D3).
#
# Usage: java/stress/night.sh
#   about 4.5 minutes on 10 cores (F53, 2026-10-19).
#
# Builds with ../java/build.sh, then runs the night tests, in
# src-dev/bergdb/test/night/:
#   * BryanIssueNight: the bug that Bryan reported in 2015-11, on disk and
#     with more iterations than BryanIssue (an f-test) and BryanRepro
#     (level2.sh).
#   * CcDbNightTest: up to a million cards in a database; lookup speed and
#     disk size.
#   * Issue150420: a restart issue of 2015-04-20 (ISSUE-150420-1), on a
#     small copy of the data that showed it (Issue150420-data.txt).
#   * PayTest: 1.2 million accounts, all there after a restart (bug-130925).
# Prints NIGHT OK when they pass. Logs go to build/night/. Set JAVA_HOME or
# PATH for the JDK; the build needs javac too.

cd "$(dirname "$0")/.."

JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi

LOG=build/night

./build.sh > /dev/null || { echo "NIGHT FAILED: build"; exit 1; }
# Removes old logs, files only (see build.sh about Finder).
mkdir -p $LOG
find $LOG -type f -delete

$JAVA -ea -cp build/bergdb.jar bergdb.dev.Night > $LOG/night.txt 2>&1
if ! grep -q '^SUCCESS' $LOG/night.txt; then
    echo "NIGHT FAILED: the night tests (log: $LOG/night.txt)"
    exit 1
fi
grep '^SUCCESS' $LOG/night.txt
echo "NIGHT OK"
