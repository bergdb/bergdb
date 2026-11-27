#!/bin/sh
# 028-72: Java's count (Dag.dirtyNodeBound) on the worst tree for a transaction within L1
# to L5, made in memory (ActionRoomProbe), and on trees that PE built (RealTreeProbe).
# Functional, not timing: counts only, about a minute in all, one JVM at a time, under 4 GB
# of heap, no database on disk.
# Usage, from anywhere: sh items/028-todo/72-action-room-lean-count/run.sh
# Needs java/build/bergdb.jar (java/build.sh). Classes go to $W/cls (W: a scratch directory,
# by default $TMPDIR/c28-72); the output to out/ beside this script.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../.." && pwd)
JAR=$ROOT/java/build/bergdb.jar
W=${W:-${TMPDIR:-/tmp}/c28-72}
mkdir -p "$W/cls" "$HERE/out"
javac -d "$W/cls" -cp "$JAR" "$HERE/ActionRoomProbe.java" "$HERE/RealTreeProbe.java"
CP="$W/cls:$JAR"
run() {
    name=$1; shift
    nice -n 10 java -Xss1g -Xmx4g -cp "$CP" "$@" > "$HERE/out/$name.txt" 2>&1
    echo "$name: $(tail -1 "$HERE/out/$name.txt")"
}
run full bergdb.core.ActionRoomProbe
run fill-7 bergdb.core.ActionRoomProbe 7 8:61
run fill-6 bergdb.core.ActionRoomProbe 6 8:61
run fill-4 bergdb.core.ActionRoomProbe 4 8:61 14:38
run heights bergdb.core.ActionRoomProbe 8:48 8:38 14:30
run real -ea bergdb.dag.RealTreeProbe
