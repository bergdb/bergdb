#!/bin/sh
# More key shapes at 1M KVs (bergdb 024-08): one byte of key length across a segment boundary.
cd /Users/f/fl/bench/2026-11-11/mem || exit 1
r() { name=$1; shift; ./run.sh $name n=1000000 "$@"; grep "^MEM\|^fill\|WALK handles\|one key\|capacity" out/$name.txt; }
r w6-1m keys=fmt:%06d
r w7-1m keys=fmt:%07d
r w8-1m keys=fmt:%08d
r w13-1m keys=fmt:%013d
r w14-1m keys=fmt:%014d
r kk14-1m keys=fmt:/kk/%010d
r key15-1m keys=fmt:/key/%010d
r key16-1m keys=fmt:/keys/%010d
r dec-v100-1m keys=dec value=100
r off-v100-1m keys=off:1000000 value=100
