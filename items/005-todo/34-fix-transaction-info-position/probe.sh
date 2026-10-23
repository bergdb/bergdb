#!/bin/sh
# bergdb 005-34: compiles TposProbe against a build and runs it with zero values and with
# random values (seed 1).
# Usage: probe.sh JAR WORK_DIR
#   JAR: java/build/bergdb.jar of the build to probe; WORK_DIR: a scratch directory.
set -e
JAR=$1
WORK=$2
HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$WORK"
javac --release 8 -Xlint:-options -cp "$JAR" -d "$WORK" "$HERE/TposProbe.java"
for v in zeros 1; do
    echo "== values: $v"
    java -ea -Xmx1g -cp "$JAR:$WORK" bergdb.core.TposProbe $v
done
