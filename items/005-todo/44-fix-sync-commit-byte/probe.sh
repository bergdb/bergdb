#!/bin/sh
# bergdb 005-44: compiles SyncCommitByteProbe against a build and runs it.
# Usage: probe.sh JAR WORK_DIR [runs]
#   JAR: java/build/bergdb.jar of the build to probe; WORK_DIR: a scratch directory.
set -e
JAR=$1
WORK=$2
HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$WORK"
javac --release 8 -Xlint:-options -cp "$JAR" -d "$WORK" "$HERE/SyncCommitByteProbe.java"
java -ea -cp "$WORK:$JAR" SyncCommitByteProbe ${3:-5}
