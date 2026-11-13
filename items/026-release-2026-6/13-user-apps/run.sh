#!/bin/sh
# Builds and runs the 026-13 applications against bergdb-release.jar (beside this script).
# Usage: run.sh quick   (about 4 minutes: each app once, small)
#        run.sh soak N  (round N of the long runs, new seeds per N, about 15 minutes, one slot)
#        run.sh kill N  (round N of the kill runs: KillEmpty and Buffers kill, about 15 minutes)
#        run.sh b1 N    (the B1 runs of soak N only, about 6 minutes)
# Each line of output that starts with FAIL (after a time or not), and an uncaught exception, is a
# wrong result; the script exits 1 then.
# B1 BackToEmpty (026-05), B2 Transform (026-06), B3 Buffers (026-07), B4 KeyLimits (026-02),
# B5 KillEmpty (SIGKILL, 026-05 and 026-06), A5 Readers and A6 IndexChurn (024-26's apps 5 and 6);
# GivenBack (026-06: a refused transaction's time) and Huge (026-07: transactions over the buffer);
# OldNodeSize (026-08: a database of node size 62 made before is refused, nothing written), when
# old-dbs/b2-node62 exists. Node size 30 only since 026-08: the apps' NODESIZE argument must be 30.
# C2 SlowDrive (U13-4) is a reproduction, not in a mode: java -cp bergdb-release.jar:out SlowDrive 1000000 5 10 [maintain].
# Each run compiles into its own out-MODE-N and writes in data/MODE-N, so that runs side by side share nothing.
cd "$(dirname "$0")"
JAR=bergdb-release.jar
mode=${1:-quick}
round=${2:-1}
OUT=out-$mode-$round
rm -rf $OUT
D=data/$mode-$round
mkdir -p $OUT $D results
javac -cp $JAR -d $OUT common/Common.java b1-back-to-empty/*.java b2-transform/*.java b3-buffers/*.java \
    b4-keys/*.java b5-kill/*.java a5-readers/*.java a6-index-churn/*.java c1-node-size/*.java c2-slow-drive/*.java || exit 1
CP=$JAR:$OUT
J="java -ea -Xmx2g -XX:+ExitOnOutOfMemoryError -cp $CP"
LOG=results/$mode-$round-$(date +%H%M).log
fail=0
r() { echo "== $*" >> $LOG; $J "$@" 2>&1 | grep -v "^..:..:..   drive" >> $LOG; tail -1 $LOG; grep -qE "^FAIL|^..:..:.. FAIL|Exception in thread" $LOG && fail=1; }

b=$((round * 100))
if [ "$mode" = quick ]; then
    [ -d old-dbs/b2-node62 ] && r OldNodeSize old-dbs/b2-node62
    r BackToEmpty 1 30 20000 3 $D/b1 8000
    r Transform 1 20 $D/b2 30
    r Buffers many 1 60 30 $D/b3
    r KeyLimits 1 5000 $D/b4
    r GivenBack $D/gb 50
    $J -Xmx3g Huge $D/huge 4 >> $LOG 2>&1; tail -1 $LOG; grep -qE "^FAIL|^..:..:.. FAIL|Exception in thread" $LOG && fail=1
    r KillEmpty parent 1 $D/b5 12 6 2500
    r Buffers kill 1 $D/b3k 6 8
    r IndexChurn 1 2000 $D/a6 1000
elif [ "$mode" = soak ] || [ "$mode" = b1 ]; then
    for s in 1 2 3 4; do
        for sd in 200000 400000 1000000; do r BackToEmpty $((b + s * 10 + sd / 200000)) 30 30000 4 $D/b1 8000 0 $sd; done
    done
    r BackToEmpty $((b + 5)) 30 200000 2 $D/b1 8000 4000000
    r BackToEmpty $((b + 6)) 30 300000 2 $D/b1 16000 10000000 2000000
    if [ "$mode" = soak ]; then
    for s in 1 2; do
        r Transform $((b + s)) 90 $D/b2 30 2 3 2
        r Transform $((b + s + 10)) 90 $D/b2 30 3 4 1
    done
    r Buffers many $((b + 1)) 150 90 $D/b3
    for s in 1 2 3; do r KeyLimits $((b + s)) 30000 $D/b4; done
    r IndexChurn $((b + 1)) 6000 $D/a6 1000 2000
    r Readers $((b + 1)) 30 5000 60 3 $D/a5 1000
    r Readers $((b + 2)) 30 20000 60 3 $D/a5 1000
    r GivenBack $D/gb 300
    r GivenBack $D/gb 300 moving
    $J -Xmx3g Huge $D/huge 16 >> $LOG 2>&1; tail -1 $LOG; grep -qE "^FAIL|^..:..:.. FAIL|Exception in thread" $LOG && fail=1
    fi
else
    r KillEmpty parent $((b + 1)) $D/b5 250 10 2500
    r Buffers kill $((b + 2)) $D/b3k 60 12
fi
echo "log: $LOG"
[ $fail = 0 ] && echo "ALL OK" || { echo "FAILURES: grep FAIL $LOG"; exit 1; }
