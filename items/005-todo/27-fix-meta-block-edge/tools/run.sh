#!/bin/sh
# Compiles FileBoundaryProbe against java/build/bergdb.jar of this tree and runs it.
# Usage (from anywhere): items/005-todo/27-fix-meta-block-edge/tools/run.sh DIR
# Build first with java/build.sh. DIR must not exist; the probe writes about 2.5 MB there.

set -e
cd "$(dirname "$0")/../../../.."
OUT=java/build/fileboundaryprobe
mkdir -p $OUT
javac --release 8 -Xlint:-options -nowarn -cp java/build/bergdb.jar -d $OUT \
    items/005-todo/27-fix-meta-block-edge/tools/FileBoundaryProbe.java
exec java -ea -cp java/build/bergdb.jar:$OUT bergdb.core.FileBoundaryProbe "$@"
