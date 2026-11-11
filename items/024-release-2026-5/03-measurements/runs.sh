#!/bin/sh
# PF1's runs (bergdb 024-03), 2026-11-11. runs.sh SCALE (1m | 10m | 100m)
B=/Users/f/fl/bench/2026-11-11/pf1
cd $B || exit 1
S=$1
case $S in
1m)   N=1000000;   MD=100000; RP=5000;  G=1000000; MD3=100000 ;;
10m)  N=10000000;  MD=300000; RP=10000; G=1000000; MD3=50000 ;;
100m) N=100000000; MD=300000; RP=20000; G=1000000; MD3=0 ;;
esac
OUT=$B/out/$S
mkdir -p $OUT
step() {   # name ver cmd args...
    name=$1; shift
    { echo "== $name $(date '+%H:%M:%S')"; uptime; ps -Ao pcpu,comm -r | sed -n 2,4p; } >> $OUT/env.txt
    echo "$(date '+%H:%M:%S') start $name" >> $OUT/steps.txt
    ./pf1.sh "$@" > $OUT/$name.txt 2>&1
    rc=$?
    echo "$(date '+%H:%M:%S') end $name rc=$rc" >> $OUT/steps.txt
    [ $rc = 0 ] || echo "FAILED $name" >> $OUT/steps.txt
}
D=$B/data
if [ "$S" != 100m ]; then
step mem3 3 mem n=$N
step mem4 4 mem n=$N
fi
# (1) puts, gets, scans, sizes: 2026.3 and 2026.4
if [ "$S" != 100m ]; then
step fill3 3 fill dir=$D/d3-$S n=$N gets=$G
step cold3 3 cold dir=$D/d3-$S n=$N
fi
step fill4 4 fill dir=$D/d4-$S n=$N gets=$G
step cold4 4 cold dir=$D/d4-$S n=$N
# (2) mass delete of 90 %, drive; (4) a cold start after it
step massdel4 4 massdel dir=$D/d4-$S n=$N frac=0.9 maxdrive=$MD report=$RP
step start4 4 start dir=$D/d4-$S
# keys in time order on what is left: a FIFO (CL7's last touch, 021-25)
step log4 4 log dir=$D/d4-$S n=$N frac=0.9 maxdrive=$MD report=$RP
rm -rf $D/d4-$S
# its twin: the remaining 10 % put fresh, the same drive
step twinfill4 4 fill dir=$D/t4-$S n=$N frac=0.9 gets=$G
step twindrive4 4 drive dir=$D/t4-$S n=$N frac=0.9 maxdrive=$MD report=$RP
rm -rf $D/t4-$S
# (3) scattered deletes: all but every 30th key; its twin
step spfill4 4 fill dir=$D/s4-$S n=$N reads=0
step sparse4 4 sparse dir=$D/s4-$S n=$N keep=30 maxdrive=$MD report=$RP
rm -rf $D/s4-$S
step sptwinfill4 4 fill dir=$D/st4-$S n=$N keep=30 gets=$G
step sptwindrive4 4 drive dir=$D/st4-$S n=$N keep=30 frac=0 maxdrive=$MD report=$RP
rm -rf $D/st4-$S
# (2) on 2026.3, for the scan after a mass delete (020-30)
if [ "$MD3" != 0 ]; then
step massdel3 3 massdel dir=$D/d3-$S n=$N frac=0.9 maxdrive=$MD3 report=$RP
step start3 3 start dir=$D/d3-$S
step log3 3 log dir=$D/d3-$S n=$N frac=0.9 maxdrive=$MD3 report=$RP
fi
rm -rf $D/d3-$S
echo "$(date '+%H:%M:%S') ALL DONE $S" >> $OUT/steps.txt
