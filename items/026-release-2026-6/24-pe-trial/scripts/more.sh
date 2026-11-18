#!/bin/sh
# bergdb 026-24: petrial pe (no contract) on every trace of the sets, for cmp1's `more` count.
BIN=$1; TR=$2; OUT=$3; SETS=$4; P=${5:-4}
for set in $SETS; do mkdir -p $OUT/$set; for f in $TR/$set/*.trace; do echo "$set $f"; done; done | xargs -P $P -L 1 sh -c '
  test -e /Users/f/fl/bench/2026-11-18/STOP && exit 0
  set=$0; f=$1; o='"$OUT"'/$set/$(basename $f .trace).txt
  test -s $o && grep -q "^PETRIAL" $o && exit 0
  '"$BIN"' pe $f > $o 2>&1'
echo MORE DONE
