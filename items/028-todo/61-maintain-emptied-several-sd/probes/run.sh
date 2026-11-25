#!/bin/sh
# bergdb 028-61: RetainChurnRows (031-02's RetainChurn with reclaim's table printed) against
# the jar of a tree. Kind: functional (the app's checks); not a commit gate.
#
# Usage, from the repository's root of the tree whose java/build/bergdb.jar is used (build
# it with java/build.sh first):
#   sh PROBES/run.sh WORKDIR SEED [ROUNDS] [JAVA OPTIONS...]
# PROBES is this directory (it may be in another tree). WORKDIR holds the classes and the
# database (removed after the run).
set -e
W=${1:?usage: run.sh WORKDIR SEED [ROUNDS] [JAVA OPTIONS...]}
SEED=${2:?seed}
ROUNDS=${3:-1}
shift 2; [ $# -gt 0 ] && shift
HERE=$(cd "$(dirname "$0")" && pwd)
JAR=$(pwd)/java/build/bergdb.jar
[ -f "$JAR" ] || { echo "no $JAR: run java/build.sh first"; exit 1; }
if [ -n "$JAVA_HOME" ]; then JAVA=${JAVA:-$JAVA_HOME/bin/java}; JAVAC=${JAVAC:-$JAVA_HOME/bin/javac}; fi
JAVA=${JAVA:-java}; JAVAC=${JAVAC:-javac}
mkdir -p "$W/classes"
$JAVAC -nowarn -d "$W/classes" -cp "$JAR" "$HERE"/RowsShow.java "$HERE"/RetainChurnRows.java
rm -rf "$W/db"
$JAVA -ea -Xmx2g "$@" -cp "$W/classes:$JAR" RetainChurnRows "$W/db" "$SEED" "$ROUNDS"
rm -rf "$W/db"
