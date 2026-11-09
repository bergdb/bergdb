#!/bin/sh
# bergdb 020-26: runs TLC on configs one after another, each stopped after MINUTES, and
# appends a line per run to results.tsv: name, result, distinct states, depth, time.
# Usage: sh queue.sh MINUTES WORKERS cfg/A.cfg cfg/B.cfg ... [-- TLC OPTIONS]
cd "$(dirname "$0")"
MIN=$1; W=$2; shift 2
CFGS=""
while [ $# -gt 0 ] && [ "$1" != "--" ]; do CFGS="$CFGS $1"; shift; done
[ "$1" = "--" ] && shift
for c in $CFGS; do
    name=$(basename "$c" .cfg)
    t0=$(date +%s)
    sh run.sh "$c" "$W" "$@" &
    pid=$!
    stopped=""
    while kill -0 $pid 2>/dev/null; do
        if [ $(( $(date +%s) - t0 )) -gt $(( MIN * 60 )) ] && [ -z "$stopped" ]; then
            pkill -f "metadir states/$name " ; stopped=yes
        fi
        sleep 5
    done
    log=logs/$name.log
    t=$(( $(date +%s) - t0 ))
    if grep -q "is violated" "$log"; then
        r="VIOLATED $(grep -o 'Invariant [A-Za-z]* is violated\|Temporal properties were violated' "$log" | head -1 | tr ' ' '_')"
    elif grep -q "Temporal properties were violated" "$log"; then
        r="VIOLATED temporal"
    elif grep -q "No error has been found" "$log" || grep -q "^exit 0" "$log"; then
        r="OK"
    elif [ -n "$stopped" ]; then
        r="STOPPED"
    else
        r="ERROR"
    fi
    ds=$(grep -o '[0-9,]* distinct states found' "$log" | tail -1 | cut -d' ' -f1)
    depth=$(grep -o 'depth of the complete state graph search is [0-9]*' "$log" | grep -o '[0-9]*$')
    printf '%s\t%s\t%s\t%s\t%ss\t%s\n' "$name" "$r" "$ds" "${depth:--}" "$t" "$(date '+%Y-%m-%d %H:%M')" >> results.tsv
done
