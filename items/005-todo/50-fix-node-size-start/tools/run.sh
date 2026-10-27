#!/bin/sh
# bergdb 005-50: the probes, on the code before the fix (head) and with it (proto).
# Usage: sh run.sh SCRATCH, where SCRATCH has
#   jars/head.jar    java/build.sh's jar of the commit before the fix;
#   jars/proto.jar   the jar with the fix;
#   jars/rel.jar     releases/2026.1/bergdb-2026.1.jar;
#   stress-proto/    java/build/stress with the fix (StreamDigest with metamask).
# Writes SCRATCH/runs/: restart-*.txt (005-38's RestartNodeSize), mixed-*.txt
# (MixedNodeSize, -ea in the -ea files), cross.txt (cross.sh) and digest-*.txt (StreamDigest
# all, with metamask=44:2 in the -mask files, and the two comparisons). About 4 minutes on F53.
set -u
S=$1
T=$(cd "$(dirname "$0")" && pwd)
R=$T/../../38-writes-at-scale/node-size/RestartNodeSize.java
mkdir -p "$S/runs"
for v in head proto; do
    rm -rf "$S/cls-$v"
    mkdir -p "$S/cls-$v"
    javac --release 17 -nowarn -cp "$S/jars/$v.jar" -d "$S/cls-$v" "$R" "$T/MixedNodeSize.java" || exit 1
    java -Xmx1g -cp "$S/cls-$v:$S/jars/$v.jar" bergdb.core.RestartNodeSize > "$S/runs/restart-$v.txt" 2>&1
    java -Xmx2g -cp "$S/cls-$v:$S/jars/$v.jar" bergdb.core.MixedNodeSize > "$S/runs/mixed-$v.txt" 2>&1
    java -ea -Xmx2g -cp "$S/cls-$v:$S/jars/$v.jar" bergdb.core.MixedNodeSize > "$S/runs/mixed-$v-ea.txt" 2>&1
done
sh "$T/cross.sh" "$S" > "$S/runs/cross.txt" 2>&1
D="java -Xmx4g -cp"
for v in head proto; do
    $D "$S/jars/$v.jar:$S/stress-proto" bergdb.core.StreamDigest all > "$S/runs/digest-$v.txt" 2>&1
    $D "$S/jars/$v.jar:$S/stress-proto" -Dmetamask=44:2 bergdb.core.StreamDigest all > "$S/runs/digest-$v-mask.txt" 2>&1
done
cd "$S" || exit 1
$D jars/proto.jar:stress-proto bergdb.core.StreamDigest compare \
    runs/digest-head.txt runs/digest-proto.txt > runs/digest-compare.txt 2>&1
$D jars/proto.jar:stress-proto bergdb.core.StreamDigest compare \
    runs/digest-head-mask.txt runs/digest-proto-mask.txt > runs/digest-compare-mask.txt 2>&1
tail -1 runs/digest-compare.txt runs/digest-compare-mask.txt
