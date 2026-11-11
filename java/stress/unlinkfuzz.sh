#!/bin/sh
# UnlinkFuzz, the fuzzer of the Dag's delete path (the upward unlink, the root collapse and
# the take-back of bergdb 023-05), on a fixed list of configurations (bergdb 024-09, step
# A1). Until then it ran by hand only, and a branch with a klong left to a node taken back
# (fault 12 of bergdb 023-08, review C) passed before-commit.sh and level1.sh to level4.sh;
# UnlinkFuzz finds that fault in seconds, in the "big-long" configurations below.
#
# Usage: java/stress/unlinkfuzz.sh [SEED]
#   Each configuration runs two blocks of rounds, a round a seed: the fixed block, seeds 1,
#   2, ... (a regression run, the same every time), and the day's block, seeds SEED, SEED +
#   1, ... (default: the day's number times 1000, as fuzz.sh, so each day new seeds). Both
#   blocks have the number of rounds that the list gives the configuration, chosen so that a
#   block takes about 35 seconds on F53 and the script about 5 minutes. Prints one line a
#   configuration, then UNLINKFUZZ OK; or, after a line for each failure, UNLINKFUZZ FAILED
#   with the first failure's configuration, seed and message, and exits with status 1. A
#   block stops at its first failure, which this repeats alone, with the transactions:
#     java -ea PROPERTIES -cp java/build/bergdb.jar:java/build/stress bergdb.dag.UnlinkFuzz SEED 1
#
# The configurations (UnlinkFuzz's class comment has the properties): the gate runs of
# bergdb 023-09, section 5 (long keys in shuffled order with 10 percent of the keys twice in
# a transaction, at node sizes 8, 14 and 30; the same sorted; random keys, shuffled, 20
# percent twice); transactions of up to 40 long keys, sorted and shuffled, with and without
# keys twice, which make a segment root, split it in place and empty it in one transaction
# (bergdb 023-08, the check of fault 12, section 3.2); the draining runs of bergdb 023-05,
# P4 (mostly deletes on few keys, long keys, node size 6, and fifo, where the tree is a
# moving window); and fifo at the default sizes.
#
# PAR=N runs N JVMs at once (default 4), each on one core (-XX:ActiveProcessorCount=1).
# Needs java/build (java/build.sh). Output: java/build/unlinkfuzz/, a file for each block.
# Not a commit gate: before-commit.sh must stay fast, and a harness joins it only if it
# adds a few seconds. night.sh runs it.

cd "$(dirname "$0")/.." || exit 2
JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi

SEED=${1:-$(( $(date +%s) / 86400 * 1000 ))}
PAR=${PAR:-4}
OUT=build/unlinkfuzz
CP=build/bergdb.jar:build/stress

[ -f build/bergdb.jar ] || { echo "UNLINKFUZZ FAILED: no build/bergdb.jar (run java/build.sh)"; exit 2; }
mkdir -p $OUT
find $OUT -type f -delete

configs() {
    # name, rounds of a block, UnlinkFuzz's properties
    echo "long-shuffle-dup     18 -Dshape=long -Dorder=shuffle -Ddup=10"
    echo "long-shuffle-dup-b14 18 -Dmaxnode=14 -Dshape=long -Dorder=shuffle -Ddup=10"
    echo "long-shuffle-dup-b30 18 -Dmaxnode=30 -Dshape=long -Dorder=shuffle -Ddup=10"
    echo "long-sorted-dup      18 -Dshape=long -Ddup=10"
    echo "random-shuffle-dup   27 -Dorder=shuffle -Ddup=20"
    echo "big-long-sorted      350 -Dshape=long -Dops=40 -Dn=30"
    echo "big-long-shuffle     350 -Dshape=long -Dops=40 -Dn=30 -Dorder=shuffle"
    echo "big-long-sorted-dup  350 -Dshape=long -Dops=40 -Dn=30 -Ddup=10"
    echo "big-long-shuffle-dup 350 -Dshape=long -Dops=40 -Dn=30 -Dorder=shuffle -Ddup=10"
    echo "drain-30             32 -Dmaxnode=8 -Dkeys=30 -Ddel=70 -Dops=10 -Dn=200"
    echo "drain-120            28 -Dmaxnode=8 -Dkeys=120 -Ddel=60 -Dops=40 -Dn=100"
    echo "drain-long           11 -Dmaxnode=8 -Dshape=long -Dkeys=200 -Ddel=80 -Dops=30 -Dn=100"
    echo "drain-b6             14 -Dmaxnode=6 -Dkeys=60 -Ddel=55 -Dops=20 -Dn=200"
    # P4's fifo runs had 2,000 and 3,000 keys in 200 transactions, minutes a round.
    echo "fifo-big             10 -Dmaxnode=8 -Dshape=fifo -Dkeys=400 -Dops=30 -Dn=60"
    echo "fifo-big-b14         8 -Dmaxnode=14 -Dshape=fifo -Dkeys=600 -Dops=40 -Dn=60"
    echo "fifo                 11 -Dshape=fifo -Dn=100"
}

# One block: the rounds from seed $3 of configuration $1, output in $OUT/$1-$2.txt.
block() {
    $JAVA -ea -XX:ActiveProcessorCount=1 -Xmx1g -Dquiet=1 $5 -cp $CP \
        bergdb.dag.UnlinkFuzz $3 $4 > $OUT/$1-$2.txt 2>&1
}

echo "unlinkfuzz.sh: fixed seeds from 1, the day's from $SEED, $PAR JVMs at once, $(date)"
START=$(date +%s)
configs > $OUT/configs.txt
running=0
while read name rounds props; do
    for b in fixed day; do
        if [ $b = fixed ]; then first=1; else first=$SEED; fi
        block $name $b $first $rounds "$props" &
        running=$((running + 1))
        if [ $running -ge $PAR ]; then
            wait
            running=0
        fi
    done
done < $OUT/configs.txt
wait

FAILED=0
FIRST=
while read name rounds props; do
    line="   $name: $rounds rounds from seed 1 and from seed $SEED:"
    for b in fixed day; do
        if [ $b = fixed ]; then first=1; else first=$SEED; fi
        f=$OUT/$name-$b.txt
        if grep -q "^Done: $rounds rounds, 0 failures" $f; then
            line="$line ok"
            continue
        fi
        FAILED=$((FAILED + 1))
        s=$(sed -n 's/^FAIL seed=\([0-9]*\) .*/\1/p' $f | head -1)
        if [ -n "$s" ]; then
            what="seed $s: $(grep '^FAIL seed=' $f | head -1 | sed 's/^FAIL seed=[0-9]* //' | cut -c1-200)"
            again="java -ea $props -cp java/$CP bergdb.dag.UnlinkFuzz $s 1"
        else
            what="no result from seed $first ($(tail -1 $f | cut -c1-200))"
            again="java -ea $props -cp java/$CP bergdb.dag.UnlinkFuzz $first $rounds"
        fi
        line="$line FAILED"
        echo "unlinkfuzz.sh: configuration $name failed, $what (log: java/$f); repeat: $again"
        [ -n "$FIRST" ] || FIRST="configuration $name, $what; repeat: $again"
    done
    echo "$line $(grep -ho 'nodes taken back by the climb [0-9]* (roots [0-9]*)' $OUT/$name-fixed.txt | sed 's/ by the climb//')"
done < $OUT/configs.txt

T=$(( $(date +%s) - START ))
if [ $FAILED -eq 0 ]; then
    echo "UNLINKFUZZ OK ($(awk '{n += 2 * $2} END {print n}' $OUT/configs.txt) rounds, $T s)"
    exit 0
fi
echo "UNLINKFUZZ FAILED: $FAILED blocks ($T s); the first: $FIRST"
exit 1
