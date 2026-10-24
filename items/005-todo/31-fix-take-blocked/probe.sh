#!/bin/sh
# bergdb 005-31's first step: BoundProbe at the four node sizes, outputs bound-m*.txt here.
# Usage: probe.sh JAR WORK_DIR   (JAR: java/build/bergdb.jar of the build; WORK_DIR: scratch)
set -e
JAR=$1
WORK=$2
HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$WORK"
javac --release 8 -Xlint:-options -nowarn -cp "$JAR" -d "$WORK" "$HERE/BoundProbe.java"
for m in 30 8 14 62; do
    java -ea -Dm=$m -cp "$WORK:$JAR" bergdb.core.BoundProbe > "$HERE/bound-m$m.txt" 2>&1
done
