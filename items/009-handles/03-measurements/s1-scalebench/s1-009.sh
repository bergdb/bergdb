#!/bin/sh
# The s1 runs of bergdb item 009 (009-03), with 004-02's ScaleBench (ported, 009-03) and its
# sb.sh: the 10M load with a budget of 600 MB on the branch's jar; then from the device (D)
# at 133 MB with its cold start, the branch's jar and 2026.1's in turns, G1 and then ZGC.
# Usage: sh s1-009.sh. Expects /opt/bergdb-bench/009/sb/: jar-009.jar, jar-2026.1.jar,
# classes-009/ and classes-2026.1/ (ScaleBench and PerfUtil compiled against each), sb.sh;
# the JDK in /opt/bergdb-bench/jdk-27.
B=/opt/bergdb-bench
R=$B/009/sb
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
CP=$R/jar-009.jar:$R/classes-009
SBFLAGS=
sb_load s1-l-key24-10m-009 key24 10000000 2500m 600000000 ""
for gc in G1 Z; do
    if [ $gc = Z ]; then SBFLAGS=-XX:+UseZGC; else SBFLAGS=; fi
    CP=$R/jar-009.jar:$R/classes-009
    sb_get s1-d-key24-10m-b133-009-$gc key24 10000000 600m 133000000 D $P
    CP=$R/jar-2026.1.jar:$R/classes-2026.1
    sb_get s1-d-key24-10m-b133-2026.1-$gc key24 10000000 600m 133000000 D $P
done
rm -rf "$DATA"
echo "$(date '+%F %T') S1 009 DONE" >> "$OUT/runs.txt"
