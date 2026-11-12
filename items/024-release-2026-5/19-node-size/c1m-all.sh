#!/bin/sh
# 024-19's counts at 1M keys on format 7 (merges, option 2, CRC32C), 2026-11-12: in one slot
# (slot.sh take), three sets at a time, each a series of one-core JVMs (c1m.sh, c1m2.sh).
# Usage: sh c1m-all.sh GROUP; GROUP 1 = A B M, 2 = C D E F, 3 = G H I. Sizes above 62 only
# where the set has no deletes (D runs 8 to 62).
S=/Users/f/fl/repos/bergdb/items/024-release-2026-5/19-node-size
D=$(sh /Users/f/fl/bench/2026-11-11/slot.sh take nsize "counts 024-19 1M group $1")
trap 'sh /Users/f/fl/bench/2026-11-11/slot.sh release $D' EXIT
echo "slot $D $(date +%H:%M:%S) load: $(uptime)"
case $1 in
1) sh $S/c1m.sh A & sh $S/c1m.sh B & sh $S/c1m.sh M & ;;
2) (sh $S/c1m2.sh C; sh $S/c1m2.sh F) & sh $S/c1m2.sh D 8 14 30 62 & sh $S/c1m2.sh E & ;;
3) sh $S/c1m2.sh G & sh $S/c1m2.sh H & sh $S/c1m2.sh I & ;;
esac
wait
for s in a b c d e f g h i; do rm -rf /Users/f/fl/bench/2026-11-11/nsize/data/$s; done
echo "done $(date +%H:%M:%S) load: $(uptime)"
