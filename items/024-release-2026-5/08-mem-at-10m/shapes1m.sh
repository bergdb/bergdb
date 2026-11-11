#!/bin/sh
# Key shapes at 1M KVs (bergdb 024-08): MEM's method with other keys.
cd /Users/f/fl/bench/2026-11-11/mem || exit 1
r() { name=$1; shift; ./run.sh $name n=1000000 "$@"; grep "^MEM\|^fill\|WALK handles\|one key" out/$name.txt; }
r rnd6-1m keys=rnd:6
r rnd8-1m keys=rnd:8
r rnd13-1m keys=rnd:13
r rnd16-1m keys=rnd:16
r hex32-1m keys=hex:32
r rnd36-1m keys=rnd:36
r decrand-1m keys=dec order=random
r fmtkrand-1m keys=fmt:/k/%010d order=random
