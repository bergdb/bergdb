#!/bin/sh
# Runs the probes of bergdb 005-55 against a built jar, with finalization on and off.
# Usage: run.sh JAR OUT; JAR is java/build/bergdb.jar of the code to probe, OUT a directory.
# FinalizeProbe takes seconds; SuiteThreads runs the unit and f-tests, about 5 minutes.
set -e
JAR=$1
OUT=$2
HERE=$(cd "$(dirname "$0")" && pwd)
CLASSES=$(mktemp -d)
mkdir -p "$OUT"
javac --release 17 -cp "$JAR" -d "$CLASSES" "$HERE/FinalizeProbe.java" "$HERE/SuiteThreads.java"
for k in mem file evict; do
    java -cp "$JAR:$CLASSES" FinalizeProbe $k > "$OUT/probe-$k.txt" 2>&1
    java --finalization=disabled -cp "$JAR:$CLASSES" FinalizeProbe $k \
        > "$OUT/probe-$k-disabled.txt" 2>&1
done
for s in Unit F; do
    java -ea -cp "$JAR:$CLASSES" SuiteThreads bergdb.dev.$s > "$OUT/suite-$s.txt" 2>&1
    java -ea --finalization=disabled -cp "$JAR:$CLASSES" SuiteThreads bergdb.dev.$s \
        > "$OUT/suite-$s-disabled.txt" 2>&1
done
rm -rf "$CLASSES"
