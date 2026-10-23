#!/bin/sh
# Compiles CreationCrashProbe against java/build/bergdb.jar of this tree and runs one case.
# Usage (from anywhere): items/005-todo/33-crashed-creation/tools/run.sh CASE [args]
# Build first with java/build.sh. See CreationCrashProbe.java for the cases.

set -e
cd "$(dirname "$0")/../../../.."
OUT=java/build/probe-005-33
mkdir -p $OUT
javac --release 8 -Xlint:-options -nowarn -cp java/build/bergdb.jar -d $OUT \
    items/005-todo/33-crashed-creation/tools/CreationCrashProbe.java
exec java -ea -cp java/build/bergdb.jar:$OUT bergdb.core.CreationCrashProbe "$@"
