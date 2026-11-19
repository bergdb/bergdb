#!/bin/sh
# Fuzzing of the readers of bytes that 2026.4 added (bergdb 020-16): FormatFuzzer's six
# areas, each against its spec: objects (ObjectFormat's full check and lookup, 020-07),
# keys (IndexKeys and IndexDefinition, 020-10), data (DataObjects' get, 020-09), kinds
# (what a stored value is, through a database: every get, listing and index), starts (what
# a start reads of the indexes) and guesses (the format-1 guess, UTF-8, bkeys).
#
# Usage: java/stress/fuzz.sh [MINUTES [SEED]]
#   MINUTES (default 8) is the whole run, in turns of a minute, the areas in turn, each
#   turn a new seed: SEED, SEED + 1, ... (default: the day's number times 1000, so each day
#   new seeds). Prints each turn's counts, then FUZZ OK, or FUZZ FAILED and the failure's
#   area, seed and iteration, which this repeats alone:
#     java -ea -cp java/build/bergdb.jar bergdb.pubimp.FormatFuzzer AREA SEED 10 ITERATION
#
# One JVM at a time, on one core (-XX:ActiveProcessorCount=1). Needs java/build
# (java/build.sh). Output: java/build/fuzz/fuzz.txt. Not a commit gate: the unit group
# runs a few thousand iterations of each area (FormatFuzzer's testFuzz*), about 2 seconds.
#
# Kind: functional (bergdb 028-23): the result does not depend on the machine's speed or
# load: MINUTES is a budget, not a limit; the full check's bound linear in a value's
# length fails only at five times the bound, where a check that is not linear lands, and a
# check between the two is counted as slow, not failed (FormatFuzzer.measure).

cd "$(dirname "$0")/.." || exit 2
echo "Kind: functional"
JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi

MINUTES=${1:-8}
SEED=${2:-$(( $(date +%s) / 86400 * 1000 ))}
OUT=build/fuzz
mkdir -p $OUT
LOG=$OUT/fuzz.txt
: > $LOG

[ -f build/bergdb.jar ] || { echo "FUZZ FAILED: no build/bergdb.jar (run java/build.sh)"; exit 2; }

echo "fuzz.sh: $MINUTES minutes from seed $SEED, $(date)" | tee -a $LOG
STATUS=0
TURN=0
while [ $TURN -lt "$MINUTES" ]; do
    for AREA in objects keys data kinds starts guesses; do
        [ $TURN -lt "$MINUTES" ] || break
        S=$((SEED + TURN))
        $JAVA -ea -XX:ActiveProcessorCount=1 -Xmx1g -cp build/bergdb.jar \
            bergdb.pubimp.FormatFuzzer $AREA $S 60 > $OUT/turn.txt 2>&1
        R=$?
        grep '^FormatFuzzer' $OUT/turn.txt | cut -c1-400 | tee -a $LOG
        if [ $R -ne 0 ]; then
            cat $OUT/turn.txt >> $LOG
            echo "fuzz.sh: area $AREA, seed $S failed (log: java/$LOG)" | tee -a $LOG
            STATUS=1
        fi
        TURN=$((TURN + 1))
    done
done
if [ $STATUS -eq 0 ]; then echo "FUZZ OK" | tee -a $LOG; else echo "FUZZ FAILED" | tee -a $LOG; fi
exit $STATUS
