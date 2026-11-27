#!/bin/sh
# bergdb 028-66: section 1's measurement as an A/B of two builds, for the timing run that
# Frans's decision of 2026-11-27 asks for before C lands (C against main). ReclaimCost on
# disk as in section 1 (disk=1, live=20000000: K = 1, uniform, values of 1,000 bytes, the
# default f and startup distance, 7 cuts, no rate limit; a FileStream with its per-append
# forces), REF and CAND in ABBA order, ROUNDS rounds (default 2: 4 runs each). For each
# run it prints the lines that show the cut's deletes: STEADY (transactions a second),
# DISK (bytes on disk over the stream kept, mean and max) and DISK PARTS (the files that end
# before fp and are not yet deleted, of them those taken off by the storage's cut, and the
# files on disk, means), and at the end the median of each figure for each build.
#
# Usage, from the repository's root:
#   sh items/028-todo/66-cut-deletes-lag/probes/ab-reclaimcost.sh REF CAND OUT
# REF and CAND are directories that hold a bergdb.jar and its stress/ classes, as a tree's
# java/build after java/build.sh; OUT, a new directory, gets each run's output and the
# summary (summary.txt). The data directories are in OUT and deleted after each run
# (ReclaimCost deletes its own). Environment: JAVA_HOME (the PATH's java otherwise), ROUNDS,
# LIVE (default 20000000; a smaller one only to try the script, not a measurement), HEAP
# (default 8g).
#
# Kind: timing (bergdb 028-23): the figures are the result. It needs a quiet machine: no
# night.sh, week.sh, level script, build or other session's tests beside it. It checks
# nothing itself; it prints the load average before each run, which the reader checks.
# About a minute a run on F53 (an estimate).
REF=${1:?REF dir}
CAND=${2:?CAND dir}
OUT=${3:?OUT dir}
ROUNDS=${ROUNDS:-2}
LIVE=${LIVE:-20000000}
HEAP=${HEAP:-8g}
if [ -n "${JAVA_HOME:-}" ]; then JAVA=$JAVA_HOME/bin/java; else JAVA=java; fi
for d in "$REF" "$CAND"; do
    [ -f "$d/bergdb.jar" ] && [ -d "$d/stress" ] || { echo "no bergdb.jar and stress/ in $d"; exit 1; }
done
[ -e "$OUT" ] && { echo "$OUT exists"; exit 1; }
mkdir -p "$OUT" || exit 1
OUT=$(cd "$OUT" && pwd)

run() {     # run SIDE DIR N
    f=$OUT/$1-$3.txt
    echo "== $1 run $3 ($2), load: $(uptime | sed 's/.*load averages*: //')" | tee "$f"
    "$JAVA" -Xmx$HEAP -Ddisk=1 -Dlive=$LIVE -Ddir="$OUT/data-$1-$3" \
        -cp "$2/bergdb.jar:$2/stress" bergdb.core.ReclaimCost >> "$f" 2>&1
    rc=$?
    grep -E '^(STEADY|DISK|RECLAIMCOST OK)' "$f"
    [ $rc = 0 ] && grep -q '^RECLAIMCOST OK' "$f" || { echo "AB RECLAIMCOST FAILED: $f"; exit 1; }
    rm -rf "$OUT/data-$1-$3"
}

n=0
i=0
while [ $i -lt "$ROUNDS" ]; do
    n=$((n + 1)); run ref "$REF" $n; run cand "$CAND" $n
    n=$((n + 1)); run cand "$CAND" $n; run ref "$REF" $n
    i=$((i + 1))
done

# The medians: transactions a second, the disk's mean over the stream kept, the files not
# yet deleted, of them taken off by the storage's cut, and the files.
median() { sort -n | awk '{ a[NR] = $1 } END { if (NR % 2) print a[(NR + 1) / 2]; else print (a[NR / 2] + a[NR / 2 + 1]) / 2 }'; }
for side in ref cand; do
    tx=$(cat "$OUT"/$side-*.txt | sed -n 's/^STEADY.*, \([0-9]*\) transactions\/s.*/\1/p' | median)
    disk=$(cat "$OUT"/$side-*.txt | sed -n 's/^DISK: .*mean \([0-9.]*\),.*/\1/p' | median)
    lag=$(cat "$OUT"/$side-*.txt | sed -n 's/^DISK PARTS.*not yet deleted, mean \([0-9.]*\),.*/\1/p' | median)
    queued=$(cat "$OUT"/$side-*.txt | sed -n "s/^DISK PARTS.*storage's cut, mean \([0-9.]*\);.*/\1/p" | median)
    files=$(cat "$OUT"/$side-*.txt | sed -n 's/^DISK PARTS.*; files, mean \([0-9.]*\).*/\1/p' | median)
    echo "$side: transactions/s $tx; disk / stream kept $disk; not yet deleted $lag, of them" \
        "taken off by the storage's cut $queued; files $files"
done | tee "$OUT/summary.txt"
echo "AB RECLAIMCOST DONE: $OUT/summary.txt"
