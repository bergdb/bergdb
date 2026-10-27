#!/bin/sh
# bergdb 005-48: the stream's bytes, HEAD against the prototype (P2). Written 2026-10-27 by
# Claude (Opus 5.5, Claude Code), after 005-50's run.sh.
# Usage: sh digest.sh BUILDS OUT
#   BUILDS has the preserved builds of performance.sh, HEAD_BUILD (default head-e718347) and
#   PROTO_BUILD (default proto-e718347), each with java/build/bergdb.jar and java/build/stress.
# Writes OUT/: digest-{head,proto}.txt (StreamDigest all: 12 configurations, modes plain,
# reads and restarts) and their comparison digest-compare.txt; syncdigest-{head,proto}.txt
# (SyncDigest all, mode syncs, which checks itself against plain) and their comparisons,
# syncdigest-compare.txt (whole lines) and syncdigest-compare-cut.txt (without firstPos and
# sha256all, which follow the physical cut's timing). StreamDigest's class is HEAD's, for
# both jars. Each JVM with -ea. About 5 minutes on F53.
set -u
B=$1
OUT=$2
T=$(cd "$(dirname "$0")" && pwd)
J=${JAVA_HOME:-/opt/homebrew/opt/openjdk}/bin
HB=$B/${HEAD_BUILD:-head-e718347}
PB=$B/${PROTO_BUILD:-proto-e718347}
STRESS=$HB/java/build/stress
mkdir -p "$OUT/classes"
"$J/javac" --release 17 -nowarn -cp "$HB/java/build/bergdb.jar:$STRESS" -d "$OUT/classes" \
    "$T/SyncDigest.java" || exit 1
for v in head proto; do
    if [ $v = head ]; then CP=$HB; else CP=$PB; fi
    CP=$CP/java/build/bergdb.jar:$STRESS:$OUT/classes
    "$J/java" -ea -Xmx4g -cp "$CP" bergdb.core.StreamDigest all > "$OUT/digest-$v.txt" 2>&1
    "$J/java" -ea -Xmx4g -cp "$CP" bergdb.core.SyncDigest all > "$OUT/syncdigest-$v.txt" 2>&1
done
CP=$HB/java/build/bergdb.jar:$STRESS
cd "$OUT" || exit 1
"$J/java" -cp "$CP" bergdb.core.StreamDigest compare digest-head.txt digest-proto.txt > digest-compare.txt 2>&1
"$J/java" -cp "$CP" bergdb.core.StreamDigest compare syncdigest-head.txt syncdigest-proto.txt \
    > syncdigest-compare.txt 2>&1
for v in head proto; do
    sed -e 's/ firstPos=[0-9]*//' -e 's/ sha256all=[0-9a-f]*//' syncdigest-$v.txt > syncdigest-$v-cut.txt
done
"$J/java" -cp "$CP" bergdb.core.StreamDigest compare syncdigest-head-cut.txt syncdigest-proto-cut.txt \
    > syncdigest-compare-cut.txt 2>&1
rm -f syncdigest-head-cut.txt syncdigest-proto-cut.txt
rm -rf classes
tail -n 1 digest-head.txt digest-proto.txt syncdigest-head.txt syncdigest-proto.txt
tail -n 1 digest-compare.txt syncdigest-compare.txt syncdigest-compare-cut.txt
