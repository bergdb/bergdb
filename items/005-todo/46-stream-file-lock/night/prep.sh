#!/bin/sh
# Makes what run.sh needs, before the quiet block, not in it (bergdb 005-46's night runs,
# 006-09's W1.3 and W1.4): in B (default /Users/f/fl/bench/006-09/w1) the clones head/ (at
# COMMIT, default the main tree's HEAD) and bf19075/ (005-50, just before 005-46), each built
# with java/build.sh; ScaleBench (004-02) with 009-03's port (ScaleBench-009.diff) and
# java/stress/PerfUtil.java, compiled against each jar (sb/classes-head, sb/classes-bf19075);
# and 004-02's pidio. About 2 minutes. Written 2026-10-27 by Claude (Opus 5.5, Claude Code).
# Usage: sh prep.sh [COMMIT]   (an existing head/ or bf19075/ in B is made again)
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../../../.." && pwd)
B=${B:-/Users/f/fl/bench/006-09/w1}
COMMIT=${1:-$(git -C "$REPO" rev-parse HEAD)}
export JAVA_HOME=/opt/homebrew/opt/openjdk
export PATH=$JAVA_HOME/bin:$PATH
mkdir -p "$B"
for j in head bf19075; do
    rm -rf "${B:?}/$j"
    git clone -q "$REPO" "$B/$j"
    if [ $j = head ]; then c=$COMMIT; else c=bf19075; fi
    git -C "$B/$j" checkout -q "$c"
    (cd "$B/$j/java" && nice sh build.sh > /dev/null)
    echo "$j: $(git -C "$B/$j" log --oneline -1 | cut -c1-80); jar sha256 $(shasum -a 256 "$B/$j/java/build/bergdb.jar" | cut -c1-16)"
done
S=$B/head/items/004-indirect-swizzling/02-scale-tests
rm -rf "${B:?}/sb"
mkdir -p "$B/sb/src"
cp "$S/ScaleBench.java" "$B/head/java/stress/PerfUtil.java" "$B/sb/src/"
(cd "$B/sb/src" && patch -s -p0 ScaleBench.java < "$B/head/items/009-handles/03-measurements/ScaleBench-009.diff")
for j in head bf19075; do
    mkdir -p "$B/sb/classes-$j"
    nice javac --release 17 -Xlint:-options -nowarn -cp "$B/$j/java/build/bergdb.jar" -d "$B/sb/classes-$j" \
        "$B/sb/src/ScaleBench.java" "$B/sb/src/PerfUtil.java"
done
cc -O2 -o "$B/sb/pidio" "$S/pidio.c"
echo "PREP OK: $B"
