#!/bin/sh
# 005-14: load-check.suite on two clones, alternating (A B, B A, A B), with performance.sh.
# Usage: load-check.sh CLONE_A CLONE_B OUTDIR   (each clone built; JAVA_HOME as for performance.sh)
A=$1; B=$2; OUT=$3
T=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$OUT"
JAVA_HOME=${JAVA_HOME:-/opt/homebrew/opt/openjdk}; export JAVA_HOME
run() {
    c=$1; r=$2; label=$(basename "$c")-r$r
    (cd "$c/java" && SUITE=$T/load-check.suite sh stress/performance.sh reference "$label") > "$OUT/$label.txt" 2>&1
    s=$(sed -n 's/^PERFORMANCE RUN DONE: \(.*\) (summary.*/\1/p' "$OUT/$label.txt")
    [ -n "$s" ] || { echo "run $label failed"; tail -5 "$OUT/$label.txt"; exit 1; }
    mkdir -p "$OUT/$label"
    (cd "$s" && find . -name 'write.result.json' -o -name 'write.stdout.txt') | while read -r f; do
        mkdir -p "$OUT/$label/$(dirname "$f")"; cp "$s/$f" "$OUT/$label/$f"
    done
    echo "$(date +%H:%M:%S) $label done"
}
run "$A" 1; run "$B" 1; run "$B" 2; run "$A" 2; run "$A" 3; run "$B" 3
echo "LOAD CHECK DONE"
