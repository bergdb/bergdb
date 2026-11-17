#!/bin/sh
# The full ratchet test of the dirty top-node window (bergdb 023-10; 023-06, section 18.6,
# item 3; 023-08, Q6), for the night of 2026-11-10. Written 2026-11-10.
#
# Start (from any directory; it needs no terminal):
#   nohup /Users/f/fl/bench/2026-11-10/ratchet/night-ratchet.sh \
#       > /Users/f/fl/bench/2026-11-10/ratchet/runs/full/driver.txt 2>&1 &
# Start it only when the marker /Users/f/fl/bench/2026-11-10/ratchet/READY exists.
# "night-ratchet.sh smoke" checks the script in about a minute (runs/full-smoke/).
#
# What it runs, one at a time, on the builds in this directory: wt-main (main, 51987a7b,
# no unlink at the delete) and wt-core (023-core, 2c67f887). The probe CleanupRatchet
# (probe/) is compiled apart, into classes-main and classes-core, against each build's
# bergdb.jar; nothing in java/src changes.
#   1. queue, main and 023-core: T4's queue (1,000 live keys, a put and a delete a
#      transaction), 1,000,000 transactions; every 200,000 a disturbance: 1,000,000 keys
#      put and deleted, 100 a transaction, then a restart. The twin: the same queue with
#      the restarts and no disturbance.
#   2. drive, main and 023-core: the same with T1's drive (overwrites of "/a.txt" with
#      1,000 bytes) instead of the queue, the workload in which the window forms.
# Measures at every 10,000 transactions, and before and after each disturbance and
# restart: D, D's top nodes, the inversions, objects, kept bytes, reclaim's cuts. D and
# the top nodes are also sampled every 100 transactions.
#
# Outputs: runs/full/<run>-<build>.txt, runs/full/summary.txt (summary.py: per segment
# between disturbances, the twin's and the disturbed database's top nodes, inversions and
# whether the most stays within the twin's steady most + a_n). Last line of the driver:
# "RATCHET FULL DONE" and the marker runs/full/DONE.
#
# Expected duration: about 10 minutes (each of the four runs 1 to 4 minutes; the scaled
# runs of 023-10 took 0.5 to 2.8 minutes on a busy F53); allow 30. Memory: one JVM at a
# time, -Xmx12g: main's reclaim stops cutting after the first mass delete, so its runs
# keep about 2 to 2.5 GB of stream in memory, and a restart copies it (023-10, 4.3: a
# scaled run with 3.95 GB kept ran out of an 8 GB heap at a restart).

R=/Users/f/fl/bench/2026-11-10/ratchet
OUT=$R/runs/full
M=1000000; DIST=200000; N=1000000; EVERY=10000
if [ "$1" = smoke ]; then   # a check of this script in about a minute, not the test
    OUT=$R/runs/full-smoke; M=20000; DIST=5000; N=5000; EVERY=5000
fi
mkdir -p $OUT
rm -f $OUT/DONE

if [ ! -f $R/READY ] && [ "$1" != smoke ]; then
    echo "no READY marker in $R; not started"
    exit 1
fi

for b in main core; do
    if [ ! -f $R/wt-$b/java/build/bergdb.jar ]; then
        echo "missing $R/wt-$b/java/build/bergdb.jar"
        exit 1
    fi
    mkdir -p $R/classes-$b
    javac --release 17 -nowarn -d $R/classes-$b -cp $R/wt-$b/java/build/bergdb.jar \
        $R/probe/CleanupRatchet.java || exit 1
done

one() {   # name build args...
    name=$1; b=$2; shift 2
    echo "$(date +%H:%M:%S) start $name $b: $*"
    ( cd $R/wt-$b/java && /usr/bin/time -p java -ea -Xmx12g \
        -cp $R/classes-$b:build/bergdb.jar bergdb.core.CleanupRatchet "$@" ) \
        > $OUT/$name-$b.txt 2>&1
    rc=$?
    echo "$(date +%H:%M:%S) end $name $b: exit $rc"
    if [ $rc -ne 0 ] || grep -q "Exception\|Error" $OUT/$name-$b.txt; then
        echo "FAILED: $name $b (see $OUT/$name-$b.txt)"
        FAILED="$FAILED $name-$b"
    fi
}
FAILED=""

echo "$(date) RATCHET FULL start"
for b in main core; do
    one queue-1m-200k $b work=queue m=$M dist=$DIST n=$N every=$EVERY
done
for b in main core; do
    one drive-1m-200k $b work=drive m=$M dist=$DIST n=$N every=$EVERY
done

: > $OUT/summary.txt
for f in $OUT/queue-1m-200k-main.txt $OUT/queue-1m-200k-core.txt \
        $OUT/drive-1m-200k-main.txt $OUT/drive-1m-200k-core.txt; do
    python3 $R/summary.py $f >> $OUT/summary.txt 2>&1
    echo >> $OUT/summary.txt
done
grep -h "^|\|steady\|dist=\|rising\|Exception\|Error" $OUT/summary.txt
date > $OUT/DONE
if [ -n "$FAILED" ]; then
    echo "$(date) RATCHET FULL DONE, FAILED:$FAILED"
else
    echo "$(date) RATCHET FULL DONE"
fi
