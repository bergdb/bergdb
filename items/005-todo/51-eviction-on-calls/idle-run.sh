#!/bin/sh
# 005-51's measurement (2026-10-27, 006-09's W4): an idle JVM, and an idle database whose
# eviction thread has run (IdleEvict), on the code before 005-51 (565499f) and with it
# (c2aab10), one process at a time, as 005-14's idle-run.sh: start, wait for READY, SETTLE
# s more, then 005-14's procstat over MEASURE s, then SIGTERM (IdleEvict prints its
# threads' CPU since T0).
# Usage: idle-run.sh WORK ROUNDS SETTLE MEASURE OUTDIR
#   WORK: a directory with the clones before/ and after/ (java/build.sh run), and procstat.
ROUNDS=$2; SETTLE=$3; MEASURE=$4; OUT=$5; W=$1
T=$(cd "$(dirname "$0")" && pwd)
JAVA=${JAVA:-/opt/homebrew/opt/openjdk/bin/java}
mkdir -p "$OUT"
for b in before after; do
    mkdir -p "$W/classes-$b"
    javac -d "$W/classes-$b" -cp "$W/$b/java/build/bergdb.jar" "$T/IdleEvict.java" || exit 1
done
r=1
while [ "$r" -le "$ROUNDS" ]; do
    for cfg in "after jvm" "before db" "after db"; do
        set -- $cfg; b=$1; mode=$2
        name=$b-$mode-r$r
        log=$OUT/$name.log
        "$JAVA" -cp "$W/$b/java/build/bergdb.jar:$W/classes-$b" IdleEvict "$mode" "$W/data-$name" "$SETTLE" > "$log" 2>&1 &
        pid=$!
        n=0
        while ! grep -q '^READY' "$log" 2>/dev/null; do
            sleep 0.2; n=$((n + 1)); [ $n -gt 600 ] && { echo "no READY: $name"; kill $pid; exit 1; }
        done
        sleep "$SETTLE"; sleep 1
        "$W/procstat" $pid > "$OUT/$name.t0"
        sleep "$MEASURE"
        "$W/procstat" $pid > "$OUT/$name.t1"
        kill -TERM $pid; wait $pid 2>/dev/null
        rm -rf "$W/data-$name"
        echo "$(date +%H:%M:%S) $name done"
    done
    r=$((r + 1))
done
echo "IDLE RUN DONE"
