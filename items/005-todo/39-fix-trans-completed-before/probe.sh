#!/bin/sh
# bergdb 005-39: compiles CompletedBeforeProbe against a build and runs it.
# Usage: probe.sh JAR WORK_DIR
#   JAR: java/build/bergdb.jar of the build to probe; WORK_DIR: a scratch directory.
set -e
JAR=$1
WORK=$2
HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$WORK"
javac -cp "$JAR" -d "$WORK" "$HERE/CompletedBeforeProbe.java"
java -ea -Xmx1g -cp "$WORK:$JAR" bergdb.core.CompletedBeforeProbe
