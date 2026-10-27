#!/bin/sh
# Runs LeakFinder (bergdb 005-55) on the unit and f-tests of a built java/ directory, both at
# once, with finalization disabled: after each test, the databases it left running.
# Usage: leaks.sh JAVA OUT [GROUP...]; JAVA is a java/ directory after build.sh, OUT a
# directory for leaks-GROUP.txt (default groups: unit f). The f-tests take about 2 minutes.
set -e
JAVA=$(cd "$1" && pwd)
OUT=$2
shift 2
SETS=${*:-unit f}
HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)
CLASSES=$(mktemp -d)
javac --release 17 -cp "$JAVA/build/bergdb.jar" -d "$CLASSES" "$HERE/LeakFinder.java"
cd "$JAVA"
for g in $SETS; do
    java -ea --finalization=disabled -cp "$CLASSES:build/bergdb.jar" bergdb.dev.LeakFinder $g \
        > "$OUT/leaks-$g.txt" 2>&1 &
done
wait
for g in $SETS; do
    echo "$g: $(grep -h '^SUCCESS\|^FAILURE' "$OUT/leaks-$g.txt") $(grep -h '^LEAKED TOTAL' "$OUT/leaks-$g.txt")"
done
rm -rf "$CLASSES"
