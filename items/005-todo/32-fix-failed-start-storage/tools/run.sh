#!/bin/sh
# Compiles FailedStartProbe against java/build/bergdb.jar of this tree and runs one case.
# Usage (from anywhere): items/005-todo/32-fix-failed-start-storage/tools/run.sh CASE [args]
# Build first with java/build.sh. JAVA_OPTS replaces the JVM options (default -ea). See
# FailedStartProbe.java for the cases.

set -e
cd "$(dirname "$0")/../../../.."
OUT=java/build/probe-005-32
mkdir -p $OUT
javac --release 8 -Xlint:-options -nowarn -cp java/build/bergdb.jar -d $OUT \
    items/005-todo/32-fix-failed-start-storage/tools/FailedStartProbe.java
exec java ${JAVA_OPTS:--ea} -cp java/build/bergdb.jar:$OUT bergdb.core.FailedStartProbe "$@"
