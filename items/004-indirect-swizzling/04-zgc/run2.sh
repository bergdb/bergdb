#!/bin/sh
# 004-04's further runs on F53, after run.sh: the M runs again (the first ZGC one overlapped
# this session's work), Shenandoah in its generational mode (concurrent like ZGC, but with
# compressed references), and G1 with a pause goal of 10 ms. Each block waits for a quiet
# machine as in run.sh, and is skipped if it could not end before DEADLINE.
# Usage: sh run2.sh WORKDIR DEADLINE BLOCK...   (DEADLINE: seconds since 1970; blocks: sb-x
# soak-shen). WORKDIR as for run.sh.
set -e
W=$1
DEADLINE=$2
shift 2
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
# Shenandoah: generational if this JDK has it, else the single-generation mode; soak.sh only
# knows g1 and zgc, so its runs turn G1 off again in JFLAGS (checked here too).
SHEN="-XX:+UseShenandoahGC -XX:ShenandoahGCMode=generational"
if ! "$REALJAVA" -XX:+UseG1GC -XX:-UseG1GC $SHEN -version > /dev/null 2>&1; then
    SHEN=-XX:+UseShenandoahGC
    "$REALJAVA" -XX:+UseG1GC -XX:-UseG1GC $SHEN -version > /dev/null 2>&1 || SHEN=
fi
echo "$(date '+%F %T') run2: Shenandoah flags: ${SHEN:-none}" >> "$OUT/runs.txt"
minutes() {
    case $1 in
    sb-x) echo 40 ;; *) echo 70 ;;
    esac
}
# quiet_by MINUTES: quiet.sh's wait; fails if a block of MINUTES could not end before DEADLINE.
quiet_by() {
    sh "$SB/quiet.sh" "" "$1" >> "$OUT/runs.txt" &
    q=$!
    while kill -0 $q 2>/dev/null; do
        if [ $(( $(date +%s) + $1 * 60 )) -gt "$DEADLINE" ]; then
            kill $q 2>/dev/null || true
            return 1
        fi
        sleep 30
    done
    return 0
}
for block in "$@"; do
    if ! quiet_by "$(minutes $block)"; then
        echo "$(date '+%F %T') skipped $block: no quiet window that ends before the deadline" >> "$OUT/runs.txt"
        continue
    fi
    echo "$(date '+%F %T') block $block, $(uptime)" >> "$OUT/runs.txt"
    case $block in
    sb-x)
        SBFLAGS=$G1; sb_load f53-m-10m-g1-r2 key24 10000000 6g 0 $P
        SBFLAGS=$Z; sb_load f53-m-10m-zgc-r2 key24 10000000 6g 0 $P
        if [ -n "$SHEN" ]; then
            SBFLAGS=$SHEN; sb_load f53-m-10m-shen key24 10000000 6g 0 $P
            SBFLAGS=$SHEN; sb_get f53-c-10m-b133-shen key24 10000000 600m 133000000 C $P
            SBFLAGS=$SHEN; sb_get f53-c-10m-b665-shen key24 10000000 2660m 665000000 C $P
        fi
        SBFLAGS="$G1 -XX:MaxGCPauseMillis=10"
        sb_get f53-c-10m-b665-g1p10 key24 10000000 2660m 665000000 C $P
        SBFLAGS=
        ;;
    soak-shen)
        if [ -z "$SHEN" ]; then
            echo "$(date '+%F %T') skipped soak-shen: no Shenandoah" >> "$OUT/runs.txt"
            continue
        fi
        echo "$(date '+%F %T') start soak p4z-shen" >> "$OUT/runs.txt"
        if (cd "$W/bergdb" && unset JAVA_HOME && JAVA=$JAVA HEAP=8g GC=g1 \
            JFLAGS="-XX:-UseG1GC $SHEN -Devictbudget=1600000000" sh java/stress/soak.sh \
            p4z-shen rate=200 warmup=300 warmupmax=3600 measure=1800 restarts=1 mincuts=2 \
            extend=900) >> "$OUT/runs.txt" 2>&1; then
            echo "$(date '+%F %T') ok soak p4z-shen" >> "$OUT/runs.txt"
        else
            echo "$(date '+%F %T') FAILED soak p4z-shen" >> "$OUT/runs.txt"
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
