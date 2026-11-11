#!/bin/sh
# Builds and runs the 024-26 applications against build/bergdb-release.jar.
# Usage: run.sh quick   (about 2 minutes: each app once, small)
#        run.sh soak N  (round N of the long runs: many seeds, about 30 minutes)
# Each line of output that starts with FAIL is a wrong result; the script exits 1 then.
cd "$(dirname "$0")"
JAR=bergdb-release.jar
mkdir -p out data results
javac -cp $JAR -d out common/Common.java a1-deletes/*.java a2-churn/*.java a3-limits/*.java \
    a4-kill/*.java a5-readers/*.java a6-index-churn/*.java || exit 1
CP=$JAR:out
J="java -ea -Xmx2g -cp $CP"
mode=${1:-quick}
round=${2:-1}
LOG=results/$mode-$round-$(date +%H%M).log
fail=0
r() { echo "== $*" >> $LOG; $J "$@" 2>&1 | grep -v "^..:..:.. \(round\|tx\)" >> $LOG; tail -1 $LOG; grep -q "^FAIL" $LOG && fail=1; }

if [ "$mode" = quick ]; then
    r DeleteHeavy 1 8 3000 2 data/a1
    r Churn 1 30 3000 4000 data/a2
    r Churn 2 8 2000 8000 data/a2 1000 20 0.25 0 400000 queue
    r Limits data/a3
    r WorstCase data/wc 5000
    r Kill parent 1 data/a4 10 5 1500
    r Readers 1 8 4000 20 3 data/a5 1000
    r IndexChurn 1 2000 data/a6 1000
    mkdir -p out7 && javac -cp $JAR -d out7 common/Common.java a7-upgrade/Upgrade.java || exit 1
    for m in "bergdb-2026.4.jar write" "$JAR open" "bergdb-2026.4.jar check"; do
        set -- $m; echo "== Upgrade $2" >> $LOG; java -cp $1:out7 Upgrade $2 data/a7 >> $LOG 2>&1; tail -1 $LOG
        grep -q "^FAIL" $LOG && fail=1
    done
else
    b=$((round * 100))
    for s in 1 2 3 4; do
        for ns in 8 14 30 62; do r DeleteHeavy $((b + s)) $ns 6000 4 data/a1; done
    done
    r DeleteHeavy $((b + 9)) 8 20000 3 data/a1 400000
    r DeleteHeavy $((b + 10)) 30 30000 2 data/a1 1000000
    for s in 1 2 3; do
        r Churn $((b + s)) 8 3000 20000 data/a2 1000 20 0.25 0 400000
        r Churn $((b + s)) 30 8000 20000 data/a2 2000 10 0.1 2000000 400000
        r Churn $((b + s)) 62 5000 15000 data/a2 1000 50 0.9 0 400000
        r Churn $((b + s)) 8 5000 40000 data/a2 1000 20 0.25 0 400000 queue
        r Churn $((b + s)) 30 20000 30000 data/a2 1000 5 0.25 0 400000 queue
    done
    for s in 1 2; do
        r Readers $((b + s)) 8 5000 60 3 data/a5 0
        r Readers $((b + s + 10)) 30 5000 60 3 data/a5 1000
        r IndexChurn $((b + s)) 6000 data/a6 1000 2000
    done
    r IndexChurn $((b + 5)) 4000 data/a6 0 1000
    r Churn $((b + 7)) 30 30 300 data/a2 1000 500 0.25 0 400000 big
    r Limits data/a3
    r WorstCase data/wc 100000
fi
echo "log: $LOG"
[ $fail = 0 ] && echo "ALL OK" || { echo "FAILURES: grep FAIL $LOG"; exit 1; }
