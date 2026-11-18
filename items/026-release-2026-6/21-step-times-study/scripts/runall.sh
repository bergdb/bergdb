#!/bin/sh
# The study's runs (bergdb 026-21, section 3): every trace of every set in
# every mode of `steptimes`, with the contract, at most 4 processes at a time.
# A job does not start once /Users/f/fl/bench/2026-11-18/STOP exists.
# A run whose output ends with a STEPTIMES line is not run again.
# Usage: runall.sh STUDYDIR TRACEDIR OUTDIR "SETS" "MODES" [BINARY]
# (BINARY: steptimes, or steptimes2, the same program under a second name)
STUDY=$1; TR=$2; OUT=$3; SETS=$4; MODES=$5
BIN=$STUDY/.lake/build/bin/${6:-steptimes}
for set in $SETS; do
  for mode in $MODES; do
    mkdir -p $OUT/$set/$mode
    for f in $TR/$set/*.trace; do
      echo "$set $mode $f"
    done
  done
done | xargs -P 4 -L 1 sh -c '
  test -e /Users/f/fl/bench/2026-11-18/STOP && exit 0
  set=$0; mode=$1; f=$2
  o='"$OUT"'/$set/$mode/$(basename $f .trace).txt
  test -s $o && grep -q "^STEPTIMES" $o && exit 0
  '"$BIN"' $mode --contract $f > $o 2>&1'
echo RUNALL DONE
