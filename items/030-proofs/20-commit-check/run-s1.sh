#!/bin/sh
# bergdb 030-20: the commit check's cost on s1. Written 2026-11-18. Run from F53, in this
# directory, after java/build.sh in the clone (CLONE, default ../../.. from here).
#
#   sh run-s1.sh copy            compiles CCBench against the clone's jar, copies the package
#                                (bergdb.jar, build/stress, CCBench's classes, s1-run.sh, the
#                                jobs files) to s1:REMOTE
#   sh run-s1.sh start JOBS...   starts s1-run.sh on s1 in the background (nohup), for each
#                                jobs file in turn
#   sh run-s1.sh fetch           copies s1:REMOTE/out to OUT
#   sh run-s1.sh clean           deletes REMOTE on s1 (the data directories are deleted
#                                after each JVM)
#
# Environment: HOST (the ssh destination of s1; required), REMOTE (default
# /opt/bergdb-bench/030-20), OUT (default /Users/f/fl/bench/2026-11-18/cc/s1-out),
# JAVA_HOME (default /opt/homebrew/opt/openjdk).

set -eu
T=$(cd "$(dirname "$0")" && pwd)
CLONE=${CLONE:-$(cd "$T/../../.." && pwd)}
HOST=${HOST:?HOST: the ssh destination of s1}
REMOTE=${REMOTE:-/opt/bergdb-bench/030-20}
OUT=${OUT:-/Users/f/fl/bench/2026-11-18/cc/s1-out}
JH=${JAVA_HOME:-/opt/homebrew/opt/openjdk}

case ${1:-} in
copy)
    J=$CLONE/java
    rm -rf "$J/build/cc"
    mkdir -p "$J/build/cc"
    "$JH/bin/javac" --release 17 -Xlint:-options -encoding UTF-8 -cp "$J/build/stress:$J/build/bergdb.jar" \
        -d "$J/build/cc" "$T/CCBench.java"
    rm -rf "$J/build/tuned"
    mkdir -p "$J/build/tuned"
    "$JH/bin/javac" --release 17 -Xlint:-options -encoding UTF-8 -cp "$J/build/bergdb.jar" \
        -d "$J/build/tuned" "$T/tuned/TransCheck.java"
    ssh "$HOST" "mkdir -p $REMOTE"
    COPYFILE_DISABLE=1 tar --no-xattrs -C "$J/build" -cf - bergdb.jar stress cc tuned | ssh "$HOST" "tar -C $REMOTE -xf -"
    COPYFILE_DISABLE=1 tar --no-xattrs -C "$T" -cf - s1-run.sh jobs-1m.txt jobs-perf.txt jobs-jfr.txt jobs-10m.txt jobs-tuned.txt jobs-durable.txt | ssh "$HOST" "tar -C $REMOTE -xf -"
    ;;
start)
    shift
    cmd=""
    for j in "$@"; do cmd="$cmd sh s1-run.sh $REMOTE/$j $REMOTE/out;"; done
    ssh "$HOST" "cd $REMOTE && nohup sh -c '$cmd' > $REMOTE/nohup.log 2>&1 < /dev/null &" < /dev/null
    ;;
fetch)
    mkdir -p "$OUT"
    ssh "$HOST" "tar -C $REMOTE -cf - out" | tar -C "$OUT" --strip-components=1 -xf -
    ;;
clean)
    ssh "$HOST" "rm -rf $REMOTE"
    ;;
*)
    echo "usage: sh run-s1.sh copy|start JOBS|fetch|clean"; exit 1 ;;
esac
