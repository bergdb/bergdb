#!/bin/sh
# 005-10: the checks of a patched clone: build, unit and f-tests, the four
# level gates, lake build. Usage: gates.sh <clone> <log dir>
R=$1
L=$2
mkdir -p "$L"
cd "$R/java" || exit 1
./build.sh > "$L/build.txt" 2>&1 || { echo "BUILD FAILED"; exit 1; }
java -ea -cp build/bergdb.jar bergdb.dev.Unit > "$L/unit.txt" 2>&1
echo "unit: $(tail -1 "$L/unit.txt")"
java -ea -cp build/bergdb.jar bergdb.dev.F > "$L/f.txt" 2>&1
echo "f: $(tail -1 "$L/f.txt")"
for n in 1 2 3 4; do
    start=$(date +%s)
    sh stress/level$n.sh > "$L/level$n.txt" 2>&1
    echo "level$n: $(tail -1 "$L/level$n.txt") ($(( $(date +%s) - start )) s)"
done
(cd "$R/lean" && lake build > "$L/lake.txt" 2>&1; echo "lake: $(tail -1 "$L/lake.txt")")
