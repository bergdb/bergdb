#!/bin/sh
# Allocation failures in turn (bergdb 012-14, done item 7), the long version: small Gen
# workloads of several shapes, each run by build/test/bergdb-allocfail (under the
# sanitizers) once per allocation number, that allocation failing (allocfail.c's
# header has the checks). The gate runs the short one (test/stress/allocfail.wl).
#
# Usage: test/stress/allocfail.sh
#   OUT    (environment) /Users/f/fl/bench/022/out/allocfail by default
#   BASES  (environment) "SEED:BUDGET:K=V,..." each (Gen's parameters), in place of
#          the six; BUDGET 0 for none
#   JOBS   (environment) workloads at once (3)
# Needs C's test build and build/java/classes (Gen). Prints ALLOCFAIL SET OK or FAILED.
{
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
CDIR=$(cd "$HERE/../.." && pwd)
OUT=${OUT:-/Users/f/fl/bench/022/out/allocfail}
JOBS=${JOBS:-3}
[ -n "${JAVA_HOME:-}" ] || JAVA_HOME=/opt/homebrew/opt/openjdk
JAVA=$JAVA_HOME/bin/java
CLASSES=$CDIR/build/java/classes
T0=$(date +%s)
BASES=${BASES:-"1301:1000:n=10,restarts=2,retain=1,sd=300,maxnode=8,reads=2,setters=2
1302:0:n=12,restarts=1,retain=0,sd=200,maxnode=14,reads=3
1303:2000:n=8,restarts=3,retain=1,sd=100,maxnode=8,huge=100,valmax=2000
1304:1:n=10,restarts=1,retain=2,sd=500,del=50,long=60
1305:500:n=15,restarts=0,retain=1,sd=1000,maxnode=8,setters=4
1306:0:n=6,restarts=4,retain=0,sd=100,maxnode=62,reads=4"}
rm -rf "$OUT"; mkdir -p "$OUT/bin"
cp "$CDIR/build/test/bergdb-allocfail" "$OUT/bin/"

one() {     # SEED BUDGET PARAMS
    # shellcheck disable=SC2046
    "$JAVA" -cp "$CLASSES" bergdb.cross.Gen "$1" $(echo "$3" | tr , ' ') > "$OUT/$1.wl"
    b=""; [ "$2" != 0 ] && b="-budget $2"
    t0=$(date +%s)
    # shellcheck disable=SC2086
    "$OUT/bin/bergdb-allocfail" $b "$OUT/$1.wl" "$OUT/$1" > "$OUT/$1.txt" 2>&1
    echo "$1 (budget $2; $3): exit $? $(( $(date +%s) - t0 )) s: $(grep '^allocfail runs' "$OUT/$1.txt")" > "$OUT/$1.sum"
}

n=0
for b in $BASES; do
    seed=${b%%:*}; rest=${b#*:}
    one "$seed" "${rest%%:*}" "${rest#*:}" &
    n=$((n + 1))
    if [ "$n" -ge "$JOBS" ]; then wait; n=0; fi
done
wait
cat "$OUT"/*.sum | tee "$OUT/summary.txt"
RUNS=$(sed -n 's/.*allocfail runs=\([0-9]*\).*/\1/p' "$OUT/summary.txt" | awk '{ s += $1 } END { print s + 0 }')
REF=$(sed -n 's/.* refused=\([0-9]*\).*/\1/p' "$OUT/summary.txt" | awk '{ s += $1 } END { print s + 0 }')
FAI=$(sed -n 's/.* failed=\([0-9]*\).*/\1/p' "$OUT/summary.txt" | awk '{ s += $1 } END { print s + 0 }')
ABS=$(sed -n 's/.* absorbed=\([0-9]*\).*/\1/p' "$OUT/summary.txt" | awk '{ s += $1 } END { print s + 0 }')
if grep -q 'exit [1-9]' "$OUT/summary.txt"; then
    echo "ALLOCFAIL SET FAILED: $(grep -c 'exit [1-9]' "$OUT/summary.txt") workloads ($OUT)"
    exit 1
fi
echo "ALLOCFAIL SET OK: $(echo $BASES | wc -w | tr -d ' ') workloads, $RUNS runs: $REF refused, $FAI failed databases, $ABS absorbed ($(( $(date +%s) - T0 )) s)"
}
