#!/bin/sh
# Compiles StopCloseProbe against java/build/bergdb.jar of this tree and runs one probe.
# Usage (from anywhere): items/005-todo/35-fix-stop-and-close/tools/run.sh PROBE DIR
# Build first with java/build.sh. DIR must not exist; the probes stop and exit write there.

set -e
cd "$(dirname "$0")/../../../.."
OUT=java/build/stopcloseprobe
mkdir -p $OUT
javac --release 8 -Xlint:-options -nowarn -cp java/build/bergdb.jar -d $OUT \
    items/005-todo/35-fix-stop-and-close/tools/StopCloseProbe.java
exec java -ea -cp java/build/bergdb.jar:$OUT bergdb.core.StopCloseProbe "$@"
