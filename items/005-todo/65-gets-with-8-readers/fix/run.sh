#!/bin/sh
# bergdb 005-65's fix, untimed: the count of the entries into Eviction.evictorLock with 8 reader
# threads (EntriesProbe; 1M keys of 100 bytes on disk, from the OS's cache, a budget of 20 MB,
# ZGC), the code before the fix against the fix, in turns (base, fix, fix, base); and the race tests
# (RaceLoop) on the fix and on broken versions of it (mkvariant.py). Neither needs a quiet
# machine. Prints the results, about 5 minutes. Written 2026-10-29 by Claude (Opus 5.5, Claude
# Code).
# Usage: sh run.sh BASE   BASE: the commit before the fix, whose Eviction.java the count's base
#   is. CLASSES (default java/build/classes of this repository, made by java/build.sh): a build
#   with the fix. W (default /Users/f/fl/bench/006-10/e65-run): the work directory, made again.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../../../.." && pwd)
BASE=${1:?usage: sh run.sh BASE}
C=${CLASSES:-$REPO/java/build/classes}
W=${W:-/Users/f/fl/bench/006-10/e65-run}
E=$C/../../src/bergdb/core/Eviction.java
[ -f "$E" ] || E=$REPO/java/src/bergdb/core/Eviction.java
export JAVA_HOME=/opt/homebrew/opt/openjdk
export PATH=$JAVA_HOME/bin:$PATH
rm -rf "${W:?}"
mkdir -p "$W/probe"
git -C "$REPO" show "$BASE:java/src/bergdb/core/Eviction.java" > "$W/base.java"
variant() {     # NAME SOURCE: W/classes-NAME, the build's classes with that Eviction.java
    mkdir -p "$W/src-$1/bergdb/core"
    cp "$2" "$W/src-$1/bergdb/core/Eviction.java"
    cp -R "$C" "$W/classes-$1"
    javac --release 17 -nowarn -Xlint:-options -cp "$C" -d "$W/classes-$1" "$W/src-$1/bergdb/core/Eviction.java"
}
python3 -I "$HERE/mkcount.py" "$W/base.java" "$W/count-base.java"
python3 -I "$HERE/mkcount.py" "$E" "$W/count-fix.java"
variant count-base "$W/count-base.java"
variant count-fix "$W/count-fix.java"
for v in norecheck lateclear oldinterrupt; do
    python3 -I "$HERE/mkvariant.py" $v "$E" "$W/$v.java"
    variant $v "$W/$v.java"
done
javac --release 17 -nowarn -Xlint:-options -cp "$W/classes-count-fix" -d "$W/probe" \
    "$HERE/EntriesProbe.java" "$HERE/RaceLoop.java"
echo "run.sh: base $BASE ($(git -C "$REPO" log -1 --format=%h "$BASE")), the fix's classes $C; $(date '+%F %T'), load $(sysctl -n vm.loadavg)"
P="-XX:+UseZGC -Xms2g -Xmx2g -Ddir=$W/db -Dkeys=1000000 -Dbudget=20 -Dthreads=8 -Dsec=10"
nice java -cp "$W/probe:$W/classes-count-base" $P bergdb.core.EntriesProbe load
for v in base fix fix base; do
    echo "count, $v:"
    nice java -cp "$W/probe:$W/classes-count-$v" $P bergdb.core.EntriesProbe gets
done
rm -rf "${W:?}/db"
echo "race tests, the fix:"
nice java -ea -cp "$W/probe:$C" bergdb.core.RaceLoop 100
nice java -ea -cp "$W/probe:$C" bergdb.core.RaceLoop 20 f
for v in norecheck oldinterrupt; do
    echo "race tests, $v:"
    nice java -ea -cp "$W/probe:$W/classes-$v" bergdb.core.RaceLoop 10
done
echo "race tests, lateclear:"
nice java -ea -cp "$W/probe:$W/classes-lateclear" bergdb.core.RaceLoop 20 f
