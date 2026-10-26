#!/bin/sh
# 007-05, step 5 of 007-03: startup time against the section, in the night of 2026-10-27
# (Frans, 2026-10-26: "Schedule Step 5 tonight at 04:00; I assume night.sh is done by then;
# report to news.md."). Started at 04:00. Waits until F53 is quiet (no java/night.sh, gate,
# lake or other JVM but the editor's) for 5 minutes, at most until 06:30; starts s1's part
# (s1-step5.sh, detached there); makes and starts the F53 databases (warm OS cache: the
# first start counts the reads by phase, the next two are timed); fetches s1's outputs;
# copies everything to out/ here, writes out/summary.txt, and adds an entry to news.md.
# Usage: sh f53-step5.sh SCRATCH, where SCRATCH has cls/ (StartupBench compiled) and
# bergdb/java/build/bergdb.jar. Databases go to SCRATCH/data; the 50M ones are deleted.
# TEST=1: tiny databases, no wait, no s1, news to SCRATCH/out/news-test.md (a check of this
# script).
set -u
TEST=${TEST:-0}
S=$1
ITEM=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$ITEM/../../.." && pwd)
OUT=$S/out
DATA=$S/data
CP=$S/cls:$S/bergdb/java/build/bergdb.jar
S1=root@s1
mkdir -p "$OUT" "$DATA"
FAIL=0
log() { echo "$(date '+%F %T') $*" >> "$OUT/runs.txt"; }
news() { sh "$REPO/tools/news.sh" "$1" "007-05 step 5" "$2"; }
now() { date +%H%M | awk '{ print $1 + 0 }'; }
busy() {
    ps -Ao args | grep -E "bin/java|java/night\.sh|level[0-9]\.sh|before-commit|lake |tracecheck" \
        | grep -v -E "grep|vscode|Code Helper" | grep -q .
}

if [ "$TEST" = 1 ]; then export NEWS_FILE=$OUT/news-test.md; fi
log "waiting for a quiet F53; load $(sysctl -n vm.loadavg)"
n=0
[ "$TEST" = 1 ] && n=10
while [ $n -lt 10 ]; do
    if busy; then n=0; else n=$((n + 1)); fi
    if [ "$(now)" -ge 630 ] && [ "$(now)" -lt 1200 ]; then
        log "not quiet by 06:30; not run"
        ps -Ao args | grep -E "bin/java|night\.sh|lake " | grep -v grep >> "$OUT/runs.txt"
        news "needs a look" "Step 5 of 007-03 did not run: F53 was not quiet by 06:30 (another JVM, gate or night.sh). See $OUT/runs.txt."
        exit 1
    fi
    sleep 30
done
log "quiet; load $(sysctl -n vm.loadavg); bergdb.jar from $(git -C "$S/bergdb" log --oneline -1 | cut -c1-7)"

# s1, detached, in parallel: another machine.
if [ "$TEST" = 1 ]; then
    log "TEST: s1 not started"
elif scp -q "$ITEM/s1-step5.sh" "$S1:/opt/bergdb-bench/007/" \
        && ssh -o BatchMode=yes "$S1" 'cd /opt/bergdb-bench/007 && rm -rf out data && nohup sh s1-step5.sh > s1-step5.log 2>&1 &'; then
    log "s1 started"
else
    log "s1 not started"; FAIL=$((FAIL + 1))
fi

start() {   # start NAME RUN PHASES HEAP BUDGET
    java -Xms$4 -Xmx$4 -XX:+UseZGC -cp "$CP" -Dst.mode=start -Dst.dir="$DATA/$1" -Dst.phases=$3 \
        -Dst.budget=$5 bergdb.core.StartupBench > "$OUT/$1-start$2.txt" 2>&1 \
        || { log "$1 start $2 FAILED"; FAIL=$((FAIL + 1)); return 1; }
    log "$1 start $2: $(grep -o '"startupSec": [0-9.e-]*' "$OUT/$1-start$2.txt")"
}
cfg() {     # cfg NAME KEYS VALSIZE SD UPDATES MAKEHEAP MAKEBUDGET STARTHEAP STARTBUDGET LATEST
    name=$1
    if [ "$(now)" -gt "${10}" ]; then log "$name skipped: past ${10}"; return; fi
    rm -rf "$DATA/$name"
    log "$name make"
    java -Xms$6 -Xmx$6 -XX:+UseParallelGC -cp "$CP" -Dst.mode=make -Dst.dir="$DATA/$name" -Dst.keys=$2 \
        -Dst.valsize=$3 -Dst.sd=$4 -Dst.updates=$5 -Dst.budget=$7 bergdb.core.StartupBench \
        > "$OUT/$name-make.txt" 2>&1 || { log "$name make FAILED"; FAIL=$((FAIL + 1)); return; }
    log "$name: $(grep 'make done' "$OUT/$name-make.txt" | cut -c12-)"
    start "$name" 1 1 $8 $9 && start "$name" 2 0 $8 $9 && start "$name" 3 0 $8 $9
}

if [ "$TEST" = 1 ]; then
cfg t-sd2   100000 8 2000000 100000 2g 0 2g 50000000 2359
cfg t-v10k  5000 10000 2000000 5000 2g 0 2g 50000000 2359
else
#   name          keys      val    sd          updates   make heap, budget   start heap, budget  latest
cfg f53-10m-sd50   10000000 8      50000000    2000000   20g 0               16g 4000000000      715
cfg f53-10m-sd200  10000000 8      200000000   3000000   20g 0               16g 4000000000      715
cfg f53-10m-sd1000 10000000 8      1000000000  12000000  20g 0               16g 4000000000      700
cfg f53-2m-v100    2000000  100    200000000   2000000   12g 0               8g  2000000000      715
cfg f53-200k-v10k  200000   10000  200000000   100000    12g 0               8g  2000000000      715
cfg f53-50m-sd200  50000000 8      200000000   3000000   22g 8000000000      20g 6000000000      600
cfg f53-50m-sd1000 50000000 8      1000000000  10000000  22g 8000000000      20g 6000000000      530
rm -rf "$DATA"/f53-50m-*
fi

# s1's outputs, when it is done (at most until 09:30).
mkdir -p "$OUT/s1"
[ "$TEST" = 1 ] || while ! ssh -o BatchMode=yes "$S1" test -f /opt/bergdb-bench/007/out/DONE 2>/dev/null; do
    if [ "$(now)" -ge 930 ]; then log "s1 not done by 09:30"; FAIL=$((FAIL + 1)); break; fi
    sleep 60
done
[ "$TEST" = 1 ] || scp -q "$S1:/opt/bergdb-bench/007/out/*" "$OUT/s1/" || { log "s1 outputs not fetched"; FAIL=$((FAIL + 1)); }
grep -q -i "exit [1-9]" "$OUT/s1/runs.txt" 2>/dev/null && { log "s1 had failures"; FAIL=$((FAIL + 1)); }

python3 "$ITEM/summary.py" "$OUT" > "$OUT/summary.txt" 2>&1
log "done, $FAIL failures"
if [ "$TEST" = 1 ]; then cat "$OUT/summary.txt"; ITEMOUT=$OUT/item-test; else ITEMOUT=$ITEM/out; fi
mkdir -p "$ITEMOUT"
cp -R "$OUT"/. "$ITEMOUT/" 2>/dev/null
if [ $FAIL = 0 ]; then
    news OK "Step 5 of 007-03 ran: startup times against the section on F53 (warm) and s1 (cold), with the reads by phase. Table: items/007-bounds/05-startup-time/out/summary.txt; the analysis follows in 007-05."
else
    news FAILED "Step 5 of 007-03 ran with $FAIL failures (see items/007-bounds/05-startup-time/out/runs.txt); what ran is in out/summary.txt there."
fi
