#!/bin/sh
# The builder's defaults (eviction on, cache 200 MB) at 3M KVs, two key shapes (bergdb 024-08).
# Takes the heavy-run lock; releases it at the end.
B=/Users/f/fl/bench/2026-11-11
cd $B/mem || exit 1
until mkdir $B/heavy.lock 2>/dev/null; do sleep 30; done
echo "mem MEM probe with eviction at 3M KVs (no timing) $(date '+%H:%M:%S')" > $B/heavy.lock/owner
echo "$(date '+%H:%M:%S') start" > out/ev3m-steps.txt
./run.sh ev-k13rand-3m n=3000000 keys=fmt:/k/%010d order=random setup=default dir=$B/mem/data/e1 gets=100000
echo "$(date '+%H:%M:%S') k13 done rc=$?" >> out/ev3m-steps.txt
du -sk data/e1 >> out/ev3m-steps.txt; rm -rf data/e1
./run.sh ev-hex32-3m n=3000000 keys=hex:32 setup=default dir=$B/mem/data/e2 gets=100000
echo "$(date '+%H:%M:%S') hex32 done rc=$?" >> out/ev3m-steps.txt
du -sk data/e2 >> out/ev3m-steps.txt; rm -rf data/e2
rm -rf $B/heavy.lock
echo "$(date '+%H:%M:%S') released" >> out/ev3m-steps.txt
