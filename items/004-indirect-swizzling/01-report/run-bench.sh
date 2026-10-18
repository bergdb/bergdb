#!/bin/sh
# The runs of IndirectionBench for 004-01 (bergdb item 004).
# Usage: sh run-bench.sh OUTDIR THREADS [SIZES]
#   OUTDIR   where the compiled classes go and the output file is written
#   THREADS  reader threads (1 or 4 in the report)
#   SIZES    the key counts, default "20000 8000000"
# Needs JAVA_HOME or java and javac on the PATH. Each variant runs in a JVM of its own.
# The handle variants use the layout "before" (a handle allocated right before its
# object); handleacq also runs with the layouts child, parent and scattered.
set -e
OUT=$1
THREADS=$2
SIZES=${3:-"20000 8000000"}
JAVA=${JAVA_HOME:+$JAVA_HOME/bin/}java
JAVAC=${JAVA_HOME:+$JAVA_HOME/bin/}javac
HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$OUT/classes"
"$JAVAC" -d "$OUT/classes" "$HERE/IndirectionBench.java"
LOG="$OUT/bench-t$THREADS.txt"
"$JAVA" -version 2>&1 | head -1 > "$LOG"
for n in $SIZES; do
    for v in direct lockstamp lock stamp handle handleacq handleclock hash chm; do
        "$JAVA" -Xms4g -Xmx4g -cp "$OUT/classes" IndirectionBench $v $n $THREADS before >> "$LOG"
    done
    for layout in child parent scattered; do
        "$JAVA" -Xms4g -Xmx4g -cp "$OUT/classes" IndirectionBench handleacq $n $THREADS $layout >> "$LOG"
    done
done
cat "$LOG"
