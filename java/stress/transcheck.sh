#!/bin/sh
# Java's own check of the writer's contract (bergdb 030-09, section 3;
# src/bergdb/core/TransCheck.java) in the unit tests and the f-tests: both run
# side by side, each in its own JVM with assertions on (-ea) and the system
# property transcheck=1, as before-commit.sh runs them. before-commit.sh turns
# the check on in the unit tests only: in the f-tests it adds about 7 s
# (50 s to 57 s on F53, 2026-11-17), more than a commit gate may grow
# (bergdb 030-09). night.sh runs this script.
#
# Usage: java/stress/transcheck.sh
#   About a minute. Builds with build.sh. Logs go to build/transcheck/. Prints
#   each test group's result and the check's summary (TRANSCHECK: transactions,
#   nodes visited, ...), then TRANSCHECK OK, or TRANSCHECK FAILED unless both
#   groups print SUCCESS and the check found no failure. Set JAVA_HOME or PATH
#   for the JDK; the build needs javac too.
#
# Kind: functional (bergdb 028-23): the result does not depend on the machine's speed or
# load; the tests' time limits are hang guards, generous for a loaded machine.

cd "$(dirname "$0")/.."
echo "Kind: functional"

JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi

LOG=build/transcheck
START=$(date +%s)
./build.sh > /dev/null || { echo "TRANSCHECK FAILED: build"; exit 1; }
mkdir -p $LOG
rm -f $LOG/unit.txt $LOG/f.txt

$JAVA -ea -Dtranscheck=1 -cp build/bergdb.jar bergdb.dev.Unit > $LOG/unit.txt 2>&1 &
$JAVA -ea -Dtranscheck=1 -cp build/bergdb.jar bergdb.dev.F > $LOG/f.txt 2>&1 &
wait

FAILED=0
for group in unit f; do
    echo "$group: $(grep -E '^SUCCESS|^FAILURE' $LOG/$group.txt)"
    echo "   $(grep '^TRANSCHECK' $LOG/$group.txt)"
    grep -q '^SUCCESS' $LOG/$group.txt || FAILED=1
    grep -q '^TRANSCHECK: .*; no failure$' $LOG/$group.txt || FAILED=1
done
echo "Time: $(( $(date +%s) - START )) s"
if [ $FAILED -eq 0 ]; then
    echo "TRANSCHECK OK"
else
    echo "TRANSCHECK FAILED (logs: java/$LOG)"
    exit 1
fi
