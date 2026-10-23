#!/bin/sh
# Part B of 004-02 (bergdb item 004): a handle's place after collections. This item's copy
# of IndirectionBench (argument AGE), one thread, KEYS keys, four treatments:
#   g1     G1 as in 004-01 (collections may run while the tree is built), age none
#   alloc  G1 with a young generation (-Xmn) that holds the whole build, age none: the tree
#          in allocation order (the two full collections before the lookups keep the order)
#   young  the same, age young: one young collection copies the whole tree first
#   zgc    ZGC (generational), age none
# and per treatment direct, and handleacq in the layouts before, parent and scattered.
# Usage: sh run-b.sh OUTDIR
# Environment: HEAP (default 3000m), YOUNG (default 1700m), KEYS (default 8000000).
# Needs JAVA_HOME, or java and javac on the PATH. Writes DONE to OUTDIR/done.
set -e
OUT=$1
HERE=$(cd "$(dirname "$0")" && pwd)
HEAP=${HEAP:-3000m}
YOUNG=${YOUNG:-1700m}
KEYS=${KEYS:-8000000}
JAVA=${JAVA_HOME:+$JAVA_HOME/bin/}java
JAVAC=${JAVA_HOME:+$JAVA_HOME/bin/}javac
mkdir -p "$OUT/classes" "$OUT/gc"
rm -f "$OUT/done"
"$JAVAC" -d "$OUT/classes" "$HERE/IndirectionBench.java"
LOG="$OUT/b.txt"
"$JAVA" -version 2>&1 | head -n 1 > "$LOG"
echo "# $(uname -sm), $(hostname), heap $HEAP, young $YOUNG, keys $KEYS, started $(date)" >> "$LOG"

cpu() {
    if [ -r /proc/stat ]; then head -n 1 /proc/stat; else echo "cpu 0 0 0 0 0 0 0 0"; fi
}
steal() {
    echo "$1|$2" | awk -F'|' '{ split($1, a, " "); split($2, b, " "); t = 0;
        for (i = 2; i <= 9; i++) t += b[i] - a[i];
        printf "# steal %.2f%% of %d ticks\n", t ? 100 * (b[9] - a[9]) / t : 0, t }'
}
treatment() {   # treatment NAME AGE JVM-FLAGS...
    name=$1
    age=$2
    shift 2
    for vl in "direct before" "handleacq before" "handleacq parent" "handleacq scattered"; do
        set -- $vl "$@"
        v=$1
        layout=$2
        shift 2
        printf "%-6s " "$name" >> "$LOG"
        c0=$(cpu)
        "$JAVA" "$@" "-Xlog:gc:file=$OUT/gc/$name-$v-$layout.log" -cp "$OUT/classes" \
            IndirectionBench $v $KEYS 1 $layout $age >> "$LOG" 2>&1
        steal "$c0" "$(cpu)" >> "$LOG"
    done
}
treatment g1 none -Xms$HEAP -Xmx$HEAP
treatment alloc none -Xms$HEAP -Xmx$HEAP -Xmn$YOUNG
treatment young young -Xms$HEAP -Xmx$HEAP -Xmn$YOUNG
treatment zgc none -Xms$HEAP -Xmx$HEAP -XX:+UseZGC
echo "finished $(date)" >> "$LOG"
echo DONE > "$OUT/done"
