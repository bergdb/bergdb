#!/bin/sh
# 024-31: one WriteBench run in one heavy slot: slotrun.sh VARIANT NAME [-D...]
S=/Users/f/fl/bench/2026-11-11/slot.sh
d=$(sh $S take pace "024-31 WriteBench $2 10M keys bytes")
sh /Users/f/fl/bench/2026-11-12/pace/w/run.sh "$@"
sh $S release $d
