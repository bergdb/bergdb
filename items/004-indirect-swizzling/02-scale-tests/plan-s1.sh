#!/bin/sh
# The runs of 004-02 on s1, in blocks, as fixed in 02-scale-tests.md (section 3.5).
# Usage: sh plan-s1.sh BLOCK...   (blocks: b c m 1m 10m 30m rep)
# Expects /opt/bergdb-bench as set up for 004-02: jdk-27/, bergdb.jar, classes/ (ScaleBench,
# PerfUtil, DiskBaseline), item/02-scale-tests/ (these scripts and IndirectionBench.java).
set -e
B=/opt/bergdb-bench
export JAVA_HOME=$B/jdk-27
JAVA=$JAVA_HOME/bin/java
CP=$B/bergdb.jar:$B/classes
DATA=$B/data
OUT=$B/out/d
THREADS=1,2,4
SAMPLED=2
DISK=sda
HERE=$(cd "$(dirname "$0")" && pwd)
. "$HERE/sb.sh"
mkdir -p "$OUT" "$DATA"
P=warm,uniform,hot,threads
for block in "$@"; do
    echo "$(date '+%F %T') block $block, load $(cut -d' ' -f1-3 /proc/loadavg)" >> "$OUT/runs.txt"
    case $block in
    b)
        sh "$HERE/run-b.sh" "$B/out/b"
        ;;
    c)
        "$JAVA" -cp "$B/classes" DiskBaseline "$DATA/disk.bin" 8 15 > "$B/out/c.txt" 2>&1
        rm -f "$DATA/disk.bin"
        ;;
    m)
        sb_load s1-m-key24-100k key24 100000 512m 0 $P,variants,census
        sb_load s1-m-key24-3m key24 3000000 2600m 0 $P,variants,census
        rm -rf "$DATA/key24-100000" "$DATA/key24-3000000"
        sb_load s1-m-key24-1m key24 1000000 1g 0 $P,variants,census
        ;;
    1m)
        sb_get s1-c-key24-1m-b66 key24 1000000 512m 66000000 C $P
        sb_get s1-d-key24-1m-b66 key24 1000000 512m 66000000 D $P
        ;;
    10m)
        sb_load s1-l-key24-10m key24 10000000 2500m 600000000 ""
        sb_get s1-d-key24-10m-b133 key24 10000000 600m 133000000 D $P
        sb_get s1-d-key24-10m-b600 key24 10000000 2400m 600000000 D $P
        ;;
    30m)
        sb_load s1-l-key24-30m key24 30000000 2500m 600000000 ""
        sb_get s1-d-key24-30m-b200 key24 30000000 800m 200000000 D $P
        sb_get s1-d-key24-30m-b600 key24 30000000 2400m 600000000 D $P
        ;;
    rep)
        sb_get s1-c-key24-1m-b66-r2 key24 1000000 512m 66000000 C $P
        sb_get s1-d-key24-10m-b133-r2 key24 10000000 600m 133000000 D $P
        ;;
    *)
        echo "unknown block $block"
        exit 2
        ;;
    esac
    echo "$(date '+%F %T') block $block done" >> "$OUT/runs.txt"
done
