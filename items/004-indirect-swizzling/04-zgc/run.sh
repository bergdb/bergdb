#!/bin/sh
# The runs of 004-04 on F53: today's code with G1 and with ZGC (generational, JDK 27), in
# blocks; each block first waits for a quiet machine (004-02's quiet.sh, every Claude session
# counted, this one too). caffeinate keeps the Mac awake while the script runs.
# Usage: sh run.sh WORKDIR BLOCK...   (blocks: sb soak-g1 soak-zgc)
# WORKDIR holds bergdb/ (a clone at the measured commit, built with java/build.sh), sb/classes
# (ScaleBench and PerfUtil compiled against its jar) and sb/pidio. The databases go to
# WORKDIR/sb/data; the outputs to WORKDIR/sb/out (ScaleBench, the .time files of javatime.sh,
# runs.txt) and WORKDIR/bergdb/java/build/soak/NAME (Soak).
set -e
W=$1
shift
HERE=$(cd "$(dirname "$0")" && pwd)
SB=$HERE/../02-scale-tests
export REALJAVA=/opt/homebrew/opt/openjdk/bin/java
export TIMEDIR=$W/sb/out
JAVA=$HERE/javatime.sh
JAR=$W/bergdb/java/build/bergdb.jar
CP=$W/sb/classes:$JAR
DATA=$W/sb/data
OUT=$W/sb/out
PIDIO=$W/sb/pidio
THREADS=1,2,4,8
SAMPLED=4
. "$SB/sb.sh"
export QUIETLOAD=${QUIETLOAD:-2.0}
mkdir -p "$OUT" "$DATA"
caffeinate -i -s -w $$ &
P=warm,uniform,hot,threads
G1=-XX:+UseG1GC
Z=-XX:+UseZGC
# The blocks' lengths in minutes, generous, so that none overlaps 02:00 to 05:00 (quiet.sh).
minutes() {
    case $1 in
    sb) echo 50 ;; *) echo 90 ;;
    esac
}
for block in "$@"; do
    sh "$SB/quiet.sh" "" "$(minutes $block)" >> "$OUT/runs.txt"
    echo "$(date '+%F %T') block $block, $(uptime)" >> "$OUT/runs.txt"
    case $block in
    sb)
        # 004-02's 10M runs: M (the load, then the gets in the same JVM), and C with the
        # budgets where G1 ran full collections (133 MB: 49 of them; 665 MB: 12).
        SBFLAGS=$G1; sb_load f53-m-10m-g1 key24 10000000 6g 0 $P
        SBFLAGS=$Z; sb_load f53-m-10m-zgc key24 10000000 6g 0 $P
        SBFLAGS=$G1; sb_get f53-c-10m-b133-g1 key24 10000000 600m 133000000 C $P
        SBFLAGS=$Z; sb_get f53-c-10m-b133-zgc key24 10000000 600m 133000000 C $P
        SBFLAGS=$Z; sb_get f53-c-10m-b133-zgc-1200m key24 10000000 1200m 133000000 C $P
        SBFLAGS=$G1; sb_get f53-c-10m-b665-g1 key24 10000000 2660m 665000000 C $P
        SBFLAGS=$Z; sb_get f53-c-10m-b665-zgc key24 10000000 2660m 665000000 C $P
        SBFLAGS=
        ;;
    soak-g1|soak-zgc)
        # P4 (docs/level4-evidence.md): P2's soak with an 8 GB heap and a budget of 1.6 GB,
        # here with 30 measured minutes and one restart instead of two hours and three.
        gc=${block#soak-}
        echo "$(date '+%F %T') start soak p4z-$gc" >> "$OUT/runs.txt"
        if (cd "$W/bergdb" && unset JAVA_HOME && JAVA=$JAVA HEAP=8g GC=$gc \
            JFLAGS=-Devictbudget=1600000000 sh java/stress/soak.sh p4z-$gc rate=200 \
            warmup=300 warmupmax=3600 measure=1800 restarts=1 mincuts=2 extend=900) \
            >> "$OUT/runs.txt" 2>&1; then
            echo "$(date '+%F %T') ok soak p4z-$gc" >> "$OUT/runs.txt"
        else
            echo "$(date '+%F %T') FAILED soak p4z-$gc" >> "$OUT/runs.txt"
            exit 1
        fi
        ;;
    *)
        echo "unknown block $block"
        exit 2
        ;;
    esac
    echo "$(date '+%F %T') block $block done" >> "$OUT/runs.txt"
done
