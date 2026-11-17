#!/bin/sh
# Runs a trace checker of this package on traces in PAR parts at once (bergdb
# 030-13), for check.sh and bridge-check.sh: the traces, largest first, are dealt
# to PAR parts (default 4), the checker runs once per part, and OUT gets each
# part's lines but its own summary, then one `total:` line, the numbers of the
# parts' `total:` lines summed place by place. Exits with 1 if a part fails.
#
# Usage: lean/contract/par.sh CHECKER OUT TRACE...
CHECK=$1; OUT=$2; shift 2
PAR=${PAR:-4}
i=0
for t in $(ls -S "$@"); do
    echo $t >> $OUT.list$((i % PAR))
    i=$((i + 1))
done
FAILED=0
pids=""
p=0
while [ $p -lt $PAR ]; do
    if [ -f $OUT.list$p ]; then
        "$CHECK" $(cat $OUT.list$p) > $OUT.part$p 2>&1 &
        pids="$pids $!"
    fi
    p=$((p + 1))
done
for pid in $pids; do
    wait $pid || FAILED=1
done
: > $OUT
p=0
while [ $p -lt $PAR ]; do
    if [ -f $OUT.part$p ]; then
        grep -v '^total: \|^CONTRACT \(OK\|FAILED\)\|^BRIDGE \(OK\|FAILED\)' $OUT.part$p >> $OUT
        grep '^total: ' $OUT.part$p >> $OUT.totals
    fi
    p=$((p + 1))
done
# The numbers of the total lines summed place by place; the words of the first.
awk '{ for (k = 1; k <= NF; k++) { w = $k; n = w; gsub(/[^0-9]/, "", n);
         if (n != "" && w ~ /^[(]?[0-9]+[),;]*$/) { s[k] += n; pre[k] = w; sub(/[0-9]+.*/, "", pre[k]);
             post[k] = w; sub(/^[(]?[0-9]+/, "", post[k]) }
         else if (NR == 1) word[k] = w }
       if (NF > nf) nf = NF }
     END { line = ""; for (k = 1; k <= nf; k++) line = line (k > 1 ? " " : "") \
             ((k in s) ? pre[k] s[k] post[k] : word[k]); print line }' $OUT.totals >> $OUT
rm -f $OUT.list* $OUT.part* $OUT.totals
exit $FAILED
