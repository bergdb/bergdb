#!/bin/sh
# 024-14: one probe run. job.sh OUTDIR SET NAME args...   SET: main | p5 | m8 | m9 | dense
# main: main + split counters (bmain); the others: the thresholds build b1 with -Dbergdb.thr.
T=/Users/f/fl/bench/2026-11-11/thr
O=$1; S=$2; N=$3; shift 3
case $S in
main)  CP=$T/probe/c-bmain:$T/bmain/bergdb.jar; P="" ;;
p5)    CP=$T/probe/c-b1:$T/b1/bergdb.jar; P="" ;;
m8)    CP=$T/probe/c-b1:$T/b1/bergdb.jar; P="-Dbergdb.thr=8,17,17" ;;
m9)    CP=$T/probe/c-b1:$T/b1/bergdb.jar; P="-Dbergdb.thr=9,18,19" ;;
dense) CP=$T/probe/c-b1:$T/b1/bergdb.jar; P="-Dbergdb.thr=10,20,20" ;;
esac
mkdir -p $O
F=$O/$N-$S.txt
DD=$T/data/$(basename $O)-$N-$S
{ echo "== $N $S $(date '+%H:%M:%S') $*"; uptime; } > $F
${HEAP:+} java ${HEAP:--Xmx3g} -XX:+UseG1GC $P -cp $CP bergdb.core.THR "$@" dir=$DD >> $F 2>&1
echo "rc=$? $(date '+%H:%M:%S')" >> $F
uptime >> $F
rm -rf $DD $DD-twin
