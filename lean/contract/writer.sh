#!/bin/sh
# The model's writer against the writer's contract on Java's traces (bergdb
# 030-10): runs `writercheck` (WriterCheck.lean) on the traces of format 3 that
# java/stress/treeconf.sh has written to java/build/traces/tree-SET/.
#
# Usage: lean/contract/writer.sh [SET ...]     (default: small drain reclaim)
# Needs: the traces (java/build.sh; cd lean && lake build treecheck;
# java/stress/treeconf.sh small, drain, reclaim) and the checker
# (cd lean/contract && lake build writercheck).
# PAR=N runs N traces at once (default 6). Prints the summary of each set, then
# WRITER OK or WRITER FAILED; the lines of every trace go to
# java/build/traces/tree-SET/writer.txt.
cd "$(dirname "$0")"
CHECK=$PWD/.lake/build/bin/writercheck
[ -x "$CHECK" ] || { echo "WRITER FAILED: no checker; run lake build writercheck in lean/contract/"; exit 1; }
SETS=${*:-small drain reclaim}
PAR=${PAR:-6}
FAILED=0
for set in $SETS; do
    dir=../../java/build/traces/tree-$set
    ls $dir/*.trace > /dev/null 2>&1 || { echo "WRITER FAILED: no traces in $dir"; exit 1; }
    ls $dir/*.trace | xargs -P $PAR -n 1 sh -c '"$0" "$1" > "$1.writer" 2>&1' "$CHECK"
    cat $dir/*.trace.writer | grep -v -E '^(total:|WRITER)' > $dir/writer.txt
    N=$(ls $dir/*.trace | wc -l | tr -d ' ')
    OK=$(cat $dir/*.trace.writer | grep -c '^WRITER OK')
    TX=$(grep -h '^total:' $dir/*.trace.writer | awk '{t += $4; o += $6} END {print t " transactions, " o " operations"}')
    rm -f $dir/*.trace.writer
    echo "tree-$set: $N traces, $TX; $OK pass"
    [ "$N" = "$OK" ] || { FAILED=$((FAILED + 1)); grep 'first: ' $dir/writer.txt | sed 's/.*first: /   first: /' | sort | uniq -c | sort -rn | head -5; }
    grep -o 'shape faults: [^;]*' $dir/writer.txt | sort | uniq -c | sort -rn | head -3
done
if [ $FAILED -eq 0 ]; then
    echo "WRITER OK"
else
    echo "WRITER FAILED: $FAILED sets"
    exit 1
fi
