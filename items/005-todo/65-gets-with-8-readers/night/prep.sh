#!/bin/sh
# Makes what threads.sh needs, before the quiet block, not in it (bergdb 005-65). In B
# (default /Users/f/fl/bench/006-09/d2-009-builds): a clone for each commit of BUILDS (default
# "c1f1f15 1165c90 f9e295d": 005-50, the commit before 005-46; 005-46 alone; 006-09's HEAD,
# with 005-55, 005-57 and 005-51 after it), named by the commit, built with java/build.sh;
# ScaleBench (004-02) with 009-03's port (ScaleBench-009.diff) and this entry's
# ScaleBench-065.diff (the CPU of the eviction thread, the readers and the rest of the process
# in each threads phase), with java/stress/PerfUtil.java, compiled against each jar
# (sb/classes-COMMIT); and 004-02's pidio. About 3 minutes. As 005-46's
# night/prep.sh. Written 2026-10-28 by Claude (Opus 5.5, Claude Code).
# Usage: [BUILDS="c1 c2 ..."] sh prep.sh   (an existing clone in B is made again)
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../../../.." && pwd)
B=${B:-/Users/f/fl/bench/006-09/d2-009-builds}
BUILDS=${BUILDS:-bf19075 1165c90 f9e295d}
export JAVA_HOME=/opt/homebrew/opt/openjdk
export PATH=$JAVA_HOME/bin:$PATH
mkdir -p "$B"
for j in $BUILDS; do
    rm -rf "${B:?}/$j"
    git clone -q "$REPO" "$B/$j"
    git -C "$B/$j" checkout -q "$j"
    (cd "$B/$j/java" && nice sh build.sh > /dev/null)
    echo "$j: $(git -C "$B/$j" log --oneline -1 | cut -c1-80); jar sha256 $(shasum -a 256 "$B/$j/java/build/bergdb.jar" | cut -c1-16)"
done
S=$REPO/items/004-indirect-swizzling/02-scale-tests
rm -rf "${B:?}/sb"
mkdir -p "$B/sb/src"
cp "$S/ScaleBench.java" "$REPO/java/stress/PerfUtil.java" "$B/sb/src/"
(cd "$B/sb/src" && patch -s -p0 ScaleBench.java < "$REPO/items/009-handles/03-measurements/ScaleBench-009.diff" \
    && patch -s -p0 ScaleBench.java < "$HERE/ScaleBench-065.diff")
# Since 005-56 (8752cf0) SyncLevel is in bergdb.pub.util, and ScaleBench, in bergdb.core, names it
# without an import: a jar that has it there gets a copy with the import, on the package line so
# that the line numbers stay (2026-10-29, for the rerun with 005-65's fix).
mkdir -p "$B/sb/src-pub"
sed 's/^package bergdb\.core;$/package bergdb.core; import bergdb.pub.util.SyncLevel;/' \
    "$B/sb/src/ScaleBench.java" > "$B/sb/src-pub/ScaleBench.java"
for j in $BUILDS; do
    s=src
    if unzip -l "$B/$j/java/build/bergdb.jar" bergdb/pub/util/SyncLevel.class > /dev/null 2>&1; then s=src-pub; fi
    mkdir -p "$B/sb/classes-$j"
    nice javac --release 17 -Xlint:-options -nowarn -cp "$B/$j/java/build/bergdb.jar" -d "$B/sb/classes-$j" \
        "$B/sb/$s/ScaleBench.java" "$B/sb/src/PerfUtil.java"
done
cc -O2 -o "$B/sb/pidio" "$S/pidio.c"
echo "PREP OK: $B"
