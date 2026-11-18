#!/bin/sh
# bergdb 026-24: petrial MODE --contract on every trace of the sets, at most P
# processes at a time (default 4); mode pe also --paired. A job does not
# start once /Users/f/fl/bench/2026-11-18/STOP exists. A run whose output
# ends with a PETRIAL line is not run again.
# Usage: runall.sh BIN TRACEDIR OUTDIR "SETS" "MODES" [P]
BIN=$1; TR=$2; OUT=$3; SETS=$4; MODES=$5; P=${6:-4}
for set in $SETS; do
  for mode in $MODES; do
    mkdir -p $OUT/$set/$mode
    for f in $TR/$set/*.trace; do
      echo "$set $mode $f"
    done
  done
done | xargs -P $P -L 1 sh -c '
  test -e /Users/f/fl/bench/2026-11-18/STOP && exit 0
  set=$0; mode=$1; f=$2
  o='"$OUT"'/$set/$mode/$(basename $f .trace).txt
  test -s $o && grep -q "^PETRIAL" $o && exit 0
  extra=""; test "$mode" = pe && extra="--paired"
  '"$BIN"' $mode --contract $extra $f > $o 2>&1'
echo RUNALL DONE
