#!/bin/sh
# Runs the probes of bergdb 005-46 against a built jar.
# Usage: run.sh JAR STRESS WORK OUT
#   JAR: java/build/bergdb.jar and STRESS: java/build/stress of the code to probe (the pause
#   probe is in stress/); WORK: a scratch directory on the disk to probe; OUT: a directory
#   for the outputs. About 8 minutes; the probes force the disk often, so run it when no
#   timing runs on the machine.
set -e
JAR=$1
STRESS=$2
WORK=$3
OUT=$4
HERE=$(cd "$(dirname "$0")" && pwd)
CLASSES=$(mktemp -d)
mkdir -p "$WORK" "$OUT"
javac --release 17 -Xlint:-options -cp "$JAR:$STRESS" -d "$CLASSES" \
    "$HERE/StreamWaitProbe.java" "$HERE/ReadPathProbe.java" "$HERE/SlowForceProbe.java" \
    "$HERE/InterruptCutProbe.java" "$HERE/InterruptProbe.java"
CP="$JAR:$STRESS:$CLASSES"
sw() { java -cp "$CP" StreamWaitProbe "$@"; }
rp() { java -cp "$CP" ReadPathProbe "$@"; }
{
    sw append "$WORK/a1" 10 4096 20
    sw append "$WORK/a2" 10 2500000 0
    sw append "$WORK/a3" 10 4096 20 300 10
    sw append "$WORK/a4" 10 1000000 50 0 1 200
    sw salsa "$WORK/s1" 10 4096 20 300 10
    sw cut "$WORK/c1" 300
    sw cut "$WORK/c2" 300 100
    sw interrupt "$WORK/i1"
} > "$OUT/stream-wait.txt" 2>&1
{
    rp force "$WORK/f1" 10 4096
    rp force "$WORK/f2" 10 2500000
    rp cut "$WORK/f3" 10 20
    rp interrupt "$WORK/f4"
    rp scale "$WORK/f5" 256 2
} > "$OUT/read-path.txt" 2>&1
{
    echo "== a write buffer of 100,000 bytes, no syncs"
    java -ea -Dnosync=true -cp "$CP" bergdb.core.InterruptCutProbe 100000
    echo "== a write buffer of 10,000,000 bytes"
    java -ea -cp "$CP" bergdb.core.InterruptCutProbe 10000000
    echo "== a write buffer of 10,000,000 bytes, no interrupts"
    java -ea -Dnointerrupt=true -cp "$CP" bergdb.core.InterruptCutProbe 10000000
} > "$OUT/interrupt-db.txt" 2>&1
java -ea -cp "$CP" bergdb.core.InterruptProbe > "$OUT/interrupt-calls.txt" 2>&1
for d in 0 1000; do
    java -XX:+UseZGC -Xms2g -Xmx2g -Dforcedelay=$d -Devery=100 -Dkeys=1000000 -Dbudget=20 \
        -Dreaders=2 -Dseconds=20 -Dtsize=1,1000 -Ddir="$WORK/pp" -cp "$CP" \
        bergdb.core.SlowForceProbe > "$OUT/slow-force-$d.txt" 2>&1
done
rm -rf "$CLASSES" "$WORK/pp"
echo "005-46 PROBES DONE"
