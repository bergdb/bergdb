#!/bin/sh
# The apps of bergdb 031-02, against the release jar of this tree (java/build.sh makes it).
# Kind: functional: each app exits non-zero on a wrong result; its time limits only guard
# against a hang. Not a commit gate.
#
# Usage, from the repository's root:
#   sh items/031-release-2026-7/02-app-hunt/apps/run.sh WORKDIR [quick]
# WORKDIR holds the classes and the databases (about 1 GB at most); quick runs each app
# small (a few minutes), else the sizes of the item's runs (about 30 minutes each, several
# at once). JAVA and JAVAC, or JAVA_HOME, choose the JDK.
set -e
W=${1:?usage: run.sh WORKDIR [quick]}
MODE=${2:-full}
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
JAR=$ROOT/java/build/bergdb-release.jar
if [ -n "$JAVA_HOME" ]; then JAVA=${JAVA:-$JAVA_HOME/bin/java}; JAVAC=${JAVAC:-$JAVA_HOME/bin/javac}; fi
JAVA=${JAVA:-java}; JAVAC=${JAVAC:-javac}
[ -f "$JAR" ] || { echo "no $JAR: run java/build.sh first"; exit 1; }
mkdir -p "$W/classes" "$W/db"
$JAVAC -nowarn -d "$W/classes" -cp "$JAR" "$HERE"/*.java
J="$JAVA -ea -Xmx3g -XX:+UseZGC -XX:+ExitOnOutOfMemoryError -cp $JAR:$W/classes"
run() { name=$1; shift; rm -rf "$W/db/$name"; echo "== $name: $*"; "$@"; rm -rf "$W/db/$name"; }
if [ "$MODE" = quick ]; then
    run e1 $J -DnoiseSleep=8 StmBank "$W/db/e1" 1 30 6 2000
    run e2 $J CoreTransform "$W/db/e2" 1 1600
    run e3 $J RetainChurn "$W/db/e3" 2 2
    run e4 $J KillWriter parent "$W/db/e4" 1 10
    run e5 $J ReplaceLimits "$W/db/e5" 2 600
    run e6 $J IndexQuery "$W/db/e6" 1 6
    run e7 $J TreeShaper "$W/db/e7" 1 25 4
    run e8 $J StmWindow "$W/db/e8" 1 40
    run e9 $J StmBins 1 3
else
    run e1 $J -DnoiseSleep=30 StmBank "$W/db/e1" 11 600 8 3000
    run e1 $J -DnoiseSleep=1 -DnoiseSpace=250000 -Dretain=3 StmBank "$W/db/e1" 21 900 12 400
    run e2 $J CoreTransform "$W/db/e2" 5 5000
    run e3 $J RetainChurn "$W/db/e3" 2 6
    run e4 $J KillWriter parent "$W/db/e4" 5 300
    run e5 $J ReplaceLimits "$W/db/e5" 3 3000
    run e6 $J IndexQuery "$W/db/e6" 4 30
    run e7 $J TreeShaper "$W/db/e7" 7 150 4
    run e8 $J StmWindow "$W/db/e8" 8 400
    run e9 $J StmBins 9 40
fi
echo "APPS 031-02 OK"
