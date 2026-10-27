#!/bin/sh
# 009-03's ScaleBench from the device (D) on s1 after 005-46 (009-03, section 9), as s1-009.sh
# ran it for section 6: the 10M key24 load with a budget of 600 MB on HEAD's jar (4f7cd60),
# then D at 133 MB with its cold start (caches dropped, a cgroup of the heap and 300 MB),
# HEAD, bf19075 (005-50, the commit before 005-46) and 2026.1 in turns, G1 and then ZGC, on
# the same database. 004-02's ScaleBench with 009-03's port and its sb.sh; one source,
# compiled against each jar. Written 2026-10-27 by Claude (Opus 5.5, Claude Code).
# Usage: sh s1-46.sh. Expects /opt/bergdb-bench/009-46/: jar-head.jar, jar-bf19075.jar,
# jar-2026.1.jar, classes-*/ and sb.sh; the JDK in /opt/bergdb-bench/jdk-27.
B=/opt/bergdb-bench
R=$B/009-46
export JAVA_HOME=$B/jdk-27
JAVA=$JAVA_HOME/bin/java
DATA=$R/data
OUT=$R/out
THREADS=1,2,4
SAMPLED=2
DISK=sda
. "$R/sb.sh"
mkdir -p "$OUT" "$DATA"
P=warm,uniform,hot,threads
echo "$(date '+%F %T') start, load $(cut -d' ' -f1-3 /proc/loadavg)" >> "$OUT/runs.txt"
CP=$R/jar-head.jar:$R/classes-head
SBFLAGS=
if (sb_load s1-l-key24-10m-head key24 10000000 2500m 600000000 ""); then
    for gc in G1 Z; do
        if [ $gc = Z ]; then SBFLAGS=-XX:+UseZGC; else SBFLAGS=; fi
        for j in head bf19075 2026.1; do
            CP=$R/jar-$j.jar:$R/classes-$j
            (sb_get s1-d-key24-10m-b133-$j-$gc key24 10000000 600m 133000000 D $P) \
                || echo "$(date '+%F %T') FAILED s1-d-key24-10m-b133-$j-$gc, going on" >> "$OUT/runs.txt"
        done
    done
fi
rm -rf "$DATA"
echo "$(date '+%F %T') S1 009-46 DONE" >> "$OUT/runs.txt"
