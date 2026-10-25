#!/bin/sh
# The F53 timed block of bergdb item 009, phase 5 (009-03): 2026.1's jar and the branch's,
# in turns, once 004-02's quiet.sh finds the machine quiet: Props twice each; the pause
# probe (1M keys, 4 readers, a 100 MB budget) with G1, ZGC and generational Shenandoah;
# and 2026.1's ScaleBench block (releases/2026.1, baseline/tools/f53.sh: 10M key24 keys,
# M with G1 and ZGC, C at 665 MB with both and at 133 MB with G1) for each jar.
# Usage: sh f53-009.sh DIR (holding jar-2026.1.jar, jar-009.jar, classes-2026.1/ and
# classes-009/ (ScaleBench and PerfUtil compiled against each), pp/ (PauseProbe), sb.sh,
# quiet.sh, pidio). caffeinate runs beside it, not with -w (008's hang).
D=$1
OUT=$D/out
export JAVA_HOME=/opt/homebrew/opt/openjdk
JAVA=$JAVA_HOME/bin/java
mkdir -p "$OUT"
caffeinate -i -s &
CAF=$!
log() { echo "$(date '+%F %T') $*" >> "$OUT/runs.txt"; }

QUIETLOAD=2.0 sh "$D/quiet.sh" 32b68478-35b0-4112-9d94-6ddb9ecd9df2 110 >> "$OUT/runs.txt"
log "block start, $(uptime | sed 's/.*load/load/')"

for i in 1 2; do
    for j in 2026.1 009; do
        $JAVA -cp "$D/jar-$j.jar" bergdb.dev.props.Props > "$OUT/props-$j-$i.txt" 2>&1
        log "props $j $i: $(grep -E '^(MEM|CORE|SS):' "$OUT/props-$j-$i.txt" | tr '\n' ' ')"
    done
done

for gc in G1 Z Shen; do
    case $gc in
        Shen) flags="-XX:+UseShenandoahGC -XX:ShenandoahGCMode=generational";;
        *) flags="-XX:+Use${gc}GC";;
    esac
    for j in 2026.1 009; do
        name=pp-$j-$gc-b100
        rm -rf "$D/ppdb"
        $JAVA $flags -Xmx1200m -Xms1200m -XX:+AlwaysPreTouch \
            -Xlog:gc*,safepoint:file=$OUT/$name-gc.log:uptime,level,tags \
            -Dkeys=1000000 -Dbudget=100 -Dreaders=4 -Dseconds=60 -Dtsize=1,1000 -Ddir=$D/ppdb \
            -cp "$D/jar-$j.jar:$D/pp" bergdb.core.PauseProbe > "$OUT/$name.txt" 2>&1
        log "$name: $(tail -1 "$OUT/$name.txt")"
    done
done
rm -rf "$D/ppdb"

DATA=$D/sbdata
THREADS=1,2,4,8
SAMPLED=4
PIDIO=$D/pidio
. "$D/sb.sh"
P=warm,uniform,hot,threads
G1=-XX:+UseG1GC
Z=-XX:+UseZGC
for j in 2026.1 009; do
    CP=$D/classes-$j:$D/jar-$j.jar
    mkdir -p "$DATA"
    ( SBFLAGS=$G1; sb_load f53-m-10m-g1-$j key24 10000000 6g 0 $P
      SBFLAGS=$Z; sb_load f53-m-10m-zgc-$j key24 10000000 6g 0 $P
      SBFLAGS=$G1; sb_get f53-c-10m-b665-g1-$j key24 10000000 2660m 665000000 C $P
      SBFLAGS=$Z; sb_get f53-c-10m-b665-zgc-$j key24 10000000 2660m 665000000 C $P
      SBFLAGS=$G1; sb_get f53-c-10m-b133-g1-$j key24 10000000 600m 133000000 C $P ) \
        || log "scalebench $j FAILED"
    rm -rf "$DATA"
done
kill $CAF
log "F53 009 DONE"
