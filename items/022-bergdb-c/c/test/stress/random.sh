#!/bin/sh
# Random cross runs by the thousand (bergdb 012-14, done item 1): Gen's workloads for
# seeds FROM to TO, Java against C, in batches of BATCH seeds, each batch one run of
# cross.sh's random set (the runs, the files, the scans, the dumps, 3 random crash cuts a
# workload, C's runs under the budgets 1 and 64000). Each seed gets parameters wider
# than Gen's own draws, by its number modulo 6 (the mode):
#   0  Gen's own draws
#   1  restarts 5-20, setters 3-10, reads 3-10
#   2  reclaim: retain 1-3 s, startup distance 100-2000, restarts 0-10
#   3  node size 8, startup distance 100-1000, 1000-4000 transactions
#   4  large values: valmax 1000-5000, huge 5-30 per mille, big 10-30 %
#   5  deletes 30-70 %, long keys 50-90 %, empty 5-20 %, 5-50 keys
# The other parameters are Gen's draws from the seed.
#
# Usage: test/stress/random.sh FROM TO [BATCH] [JOBS]
#   BATCH   seeds a batch (40); JOBS batches at once (2)
#   OUT     (environment) the output directory, /Users/f/fl/bench/022/out/random by default
# Needs C's test build (build/test, ./build.sh) and a JDK. A batch's report is
# OUT/b-FROM/report.txt; a failed batch keeps its directories. The summary, a line a
# batch, is OUT/summary.txt. Stops early, after the running batches, if the file
# OUT/STOP exists. The script is one compound command, read whole before it runs.

{
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
CDIR=$(cd "$HERE/../.." && pwd)
FROM=$1; TO=$2; BATCH=${3:-40}; JOBS=${4:-2}
OUT=${OUT:-/Users/f/fl/bench/022/out/random}
mkdir -p "$OUT"
[ -n "${JAVA_HOME:-}" ] || JAVA_HOME=/opt/homebrew/opt/openjdk
export JAVA_HOME

params() {  # SEED: the Gen parameters of the seed, "K=V,..." or empty
    awk -v s="$1" 'BEGIN {
        srand(s); m = s % 6
        if (m == 1) printf "restarts=%d,setters=%d,reads=%d", 5 + int(rand() * 16), 3 + int(rand() * 8), 3 + int(rand() * 8)
        if (m == 2) printf "retain=%d,sd=%d,restarts=%d", 1 + int(rand() * 3), 100 + int(rand() * 1901), int(rand() * 11)
        if (m == 3) printf "maxnode=8,sd=%d,n=%d", 100 + int(rand() * 901), 1000 + int(rand() * 3001)
        if (m == 4) printf "valmax=%d,huge=%d,big=%d", 1000 + int(rand() * 4001), 5 + int(rand() * 26), 10 + int(rand() * 21)
        if (m == 5) printf "del=%d,long=%d,empty=%d,keys=%d", 30 + int(rand() * 41), 50 + int(rand() * 41), 5 + int(rand() * 16), 5 + int(rand() * 46)
    }'
}

batch() {   # B E: one batch, seeds B to E
    d=$OUT/b-$1
    rm -rf "$d"; mkdir -p "$d"
    s=$1
    while [ "$s" -le "$2" ]; do
        p=$(params "$s")
        if [ -n "$p" ]; then echo "gen:$s:$p"; else echo "gen:$s"; fi
        s=$((s + 1))
    done > "$d.specs"
    t0=$(date +%s)
    sh "$CDIR/test/cross/cross.sh" random SPECFILE="$d.specs" OUTDIR="$d" C="$CDIR/build/test" \
        > "$d.log" 2>&1
    st=$?
    echo "$(date '+%H:%M:%S') seeds $1-$2 exit $st $(( $(date +%s) - t0 )) s: $(tail -1 "$d/report.txt")" >> "$OUT/summary.txt"
}

sh "$CDIR/test/cross/java-build.sh" > "$OUT/java-build.txt" 2>&1 || { cat "$OUT/java-build.txt"; exit 1; }
s=$FROM
while [ "$s" -le "$TO" ]; do
    [ -f "$OUT/STOP" ] && break
    n=0
    while [ $n -lt "$JOBS" ] && [ "$s" -le "$TO" ]; do
        e=$((s + BATCH - 1)); [ "$e" -gt "$TO" ] && e=$TO
        batch "$s" "$e" &
        s=$((e + 1)); n=$((n + 1))
    done
    wait
done
echo "$(date '+%H:%M:%S') random.sh $FROM-$TO ended at seed $((s - 1))" >> "$OUT/summary.txt"
}
