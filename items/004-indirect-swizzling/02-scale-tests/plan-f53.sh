#!/bin/sh
# The runs of 004-02 on F53, in blocks, as fixed in 02-scale-tests.md (section 3.5). Each
# block first waits for a quiet machine (quiet.sh); caffeinate keeps the Mac awake (on AC,
# with the lid open) while the script runs.
# Usage: sh plan-f53.sh WORKDIR OWN_SESSION_ID BLOCK...   (blocks: a b b64 c m 50m 30m 100m rnd rep)
# WORKDIR holds bergdb/ (a clone at the measured commit, built with java/build.sh), sb/classes
# (ScaleBench, PerfUtil, DiskBaseline), sb/pidio; the databases go to WORKDIR/sb/data and the
# outputs to WORKDIR/sb/out.
set -e
W=$1
OWN=$2
shift 2
export JAVA_HOME=/opt/homebrew/opt/openjdk
JAVA=$JAVA_HOME/bin/java
JAR=$W/bergdb/java/build/bergdb.jar
CP=$JAR:$W/sb/classes
DATA=$W/sb/data
OUT=$W/sb/out/d
PIDIO=$W/sb/pidio
THREADS=1,2,4,8
SAMPLED=4
HERE=$(cd "$(dirname "$0")" && pwd)
. "$HERE/sb.sh"
# While Frans works, the 1-minute load stays near 1.5 to 1.9 with little CPU in use; 2.0
# still keeps out other jobs (2026-10-23 14:10: nothing ran from 10:58 to 13:30 at 1.5).
export QUIETLOAD=${QUIETLOAD:-2.0}
mkdir -p "$OUT" "$DATA"
caffeinate -i -s -w $$ &
P=warm,uniform,hot,threads
# The blocks' lengths in minutes, generous, so that none overlaps 02:00 to 05:00 (quiet.sh).
minutes() {
    case $1 in
    a) echo 50 ;; b) echo 25 ;; b64) echo 40 ;; c) echo 10 ;; m) echo 60 ;; 50m|30m) echo 40 ;;
    100m) echo 120 ;; rnd) echo 40 ;; rep) echo 15 ;; *) echo 60 ;;
    esac
}
for block in "$@"; do
    sh "$HERE/quiet.sh" "$OWN" "$(minutes $block)" >> "$OUT/runs.txt"
    echo "$(date '+%F %T') block $block, $(uptime)" >> "$OUT/runs.txt"
    case $block in
    a)
        HEAP_BENCH=2g HEAP_CENSUS=2600m THREADS="1 2 4" sh "$HERE/run-a.sh" "$W/sb/out/a" "$JAR"
        ;;
    b)
        sh "$HERE/run-b.sh" "$W/sb/out/b"
        ;;
    b64)
        SIZES=64000000 THREADS=1 HEAP_BENCH=16g CENSUS=0 sh "$HERE/run-a.sh" "$W/sb/out/b64" "$JAR"
        ;;
    c)
        "$JAVA" -cp "$W/sb/classes" DiskBaseline "$DATA/disk.bin" 40 15 > "$W/sb/out/c.txt" 2>&1
        rm -f "$DATA/disk.bin"
        ;;
    m)
        sb_load f53-m-key24-100k key24 100000 512m 0 $P,variants,census
        rm -rf "$DATA/key24-100000"
        sb_load f53-m-key24-1m key24 1000000 1g 0 $P,variants,census
        sb_load f53-m-key24-10m key24 10000000 6g 0 $P,variants,census
        sb_get f53-c-key24-1m-b66 key24 1000000 512m 66000000 C $P
        sb_get f53-c-key24-10m-b665 key24 10000000 2660m 665000000 C $P
        sb_get f53-c-key24-10m-b133 key24 10000000 600m 133000000 C $P
        ;;
    50m)
        # 50M keys need a 20 GB heap; with less than 75 percent of the memory free, 30M.
        free=$(memory_pressure | awk '/free percentage/ { sub("%", "", $5); print $5 }')
        echo "$(date '+%F %T') memory free: $free percent" >> "$OUT/runs.txt"
        if [ "${free:-0}" -ge 75 ]; then
            sb_load f53-m-key24-50m key24 50000000 20g 0 $P,variants,census
            rm -rf "$DATA/key24-50000000"
        else
            sb_load f53-m-key24-30m key24 30000000 12g 0 $P,variants,census
            rm -rf "$DATA/key24-30000000"
        fi
        ;;
    30m)
        sb_load f53-m-key24-30m key24 30000000 12g 0 $P,variants,census
        rm -rf "$DATA/key24-30000000"
        ;;
    100m)
        # Loaded with a budget that holds the latest index (about 5.4 GB), so that the writer
        # seldom loads (s1's 10M load with 600 MB took an hour); 4 GB if memory is short.
        free=$(memory_pressure | awk '/free percentage/ { sub("%", "", $5); print $5 }')
        echo "$(date '+%F %T') memory free: $free percent" >> "$OUT/runs.txt"
        if [ "${free:-0}" -ge 75 ]; then
            sb_load f53-l-key24-100m key24 100000000 20g 8000000000 ""
        else
            sb_load f53-l-key24-100m key24 100000000 12g 4000000000 ""
        fi
        sb_get f53-c-key24-100m-b1330 key24 100000000 5300m 1330000000 C $P
        sb_get f53-c-key24-100m-b2660 key24 100000000 10600m 2660000000 C $P
        ;;
    rnd)
        sb_load f53-m-rnd24-1m rnd24 1000000 3g 0 $P,variants,census
        sb_load f53-m-rnd24-10m rnd24 10000000 14g 0 $P,variants,census
        sb_get f53-c-rnd24-10m-b437 rnd24 10000000 1750m 437000000 C $P
        ;;
    rep)
        sb_get f53-c-key24-10m-b133-r2 key24 10000000 600m 133000000 C $P
        ;;
    *)
        echo "unknown block $block"
        exit 2
        ;;
    esac
    echo "$(date '+%F %T') block $block done" >> "$OUT/runs.txt"
done
