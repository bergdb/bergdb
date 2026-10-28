#!/bin/sh
# The check before a commit: the only one required (since 2026-10-20). It must
# print BEFORE COMMIT OK before a change to java/ is committed. The level scripts
# (stress/level1.sh to level4.sh), night.sh and perf.sh are not commit gates.
#
# Usage: java/before-commit.sh
#   About 2 minutes on F53 (10 cores, 2026-10-20).
#
# Builds with build.sh, checks the package dependencies with deps.py (each
# package in src uses only what its package.html lists, bergdb 005-56; under a
# second), then runs at the same time, each in its own JVM with assertions on
# (-ea):
#   * the unit tests (bergdb.dev.Unit, the Nano test group "unit"), about 10 s;
#   * the f-tests (bergdb.dev.F, the Nano test group "f"), about 2 minutes.
# Logs go to build/before-commit/. Exits with status 1 unless deps.py passes
# and both print SUCCESS. Set JAVA_HOME or PATH for the JDK; the build needs
# javac too; deps.py needs python3.

cd "$(dirname "$0")"

JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi

LOG=build/before-commit
START=$(date +%s)

fail() {
    echo "BEFORE COMMIT FAILED: $1 (log: java/$2)"
    exit 1
}

./build.sh > /dev/null || { echo "BEFORE COMMIT FAILED: build"; exit 1; }
mkdir -p $LOG
rm -f $LOG/unit.txt $LOG/f.txt $LOG/deps.txt

if ! python3 -I deps.py > $LOG/deps.txt 2>&1; then
    grep -E 'NOT ALLOWED|BAD LIST|Error' $LOG/deps.txt
    fail "package dependencies: a use that its package's package.html does not list, or a list not in the form \"Depends on: a, b, c.\"; change the code or the list" $LOG/deps.txt
fi
echo "Deps: $(tail -1 $LOG/deps.txt)"

$JAVA -ea -cp build/bergdb.jar bergdb.dev.Unit > $LOG/unit.txt 2>&1 &
$JAVA -ea -cp build/bergdb.jar bergdb.dev.F > $LOG/f.txt 2>&1 &
wait

grep -q '^SUCCESS' $LOG/unit.txt || fail "unit tests" $LOG/unit.txt
echo "Unit: $(grep '^SUCCESS' $LOG/unit.txt)"
grep -q '^SUCCESS' $LOG/f.txt || fail "f-tests" $LOG/f.txt
echo "F:    $(grep '^SUCCESS' $LOG/f.txt)"
echo "BEFORE COMMIT OK ($(( $(date +%s) - START )) s)"
