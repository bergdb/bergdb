#!/bin/sh
# bergdb 031-06, review 3: its probes. Usage, from the repository's root, after
# java/build.sh:
#   sh items/031-release-2026-7/06-one-record-an-action/review-3-probes/run.sh OUT WHAT
# WHAT: evict (EvictChargeProbe: the stream with and without eviction and the warm-up, steps
# of up to 128 KiB), mw (MwWarmProbe: the warm-up with several writers), cost (WarmCostProbe:
# the reads that the warm-up adds), stop (StopWarmProbe: what execute() throws at a stop),
# tail (S4*: 028-67's start on tails that a crash and its recovery leave). Kind: functional
# (counts and bytes; no time is measured).
OUT=${1:?out dir}
WHAT=${2:?evict, mw, cost, stop or tail}
J=${JAR:-java/build/bergdb.jar}
P=items/031-release-2026-7/06-one-record-an-action/review-3-probes
mkdir -p "$OUT/classes"
javac -nowarn -cp $J -d "$OUT/classes" $P/*.java || exit 1
C="-cp $OUT/classes:$J"
w() { echo "== $*"; java -ea -Xmx6g "$@" 2>&1 | grep -v "^\s*at "; }
case $WHAT in
evict)
    # The pairs with and without restarts (the last argument) must print the same stream.
    w $C bergdb.core.EvictChargeProbe 20000 1000 600 300000 200 5000000 30 0
    w $C bergdb.core.EvictChargeProbe 20000 1000 600 300000 200 5000000 8 0
    w $C bergdb.core.EvictChargeProbe 20000 1000 600 300000 200 5000000 8 97
    w $C bergdb.core.EvictChargeProbe 100000 30 3000 2000 50 3000000 30 0
    w $C bergdb.core.EvictChargeProbe 100000 30 3000 2000 50 3000000 30 211
    w $C bergdb.core.EvictChargeProbe 100000 30 3000 400000 100 3000000 8 0
    w $C bergdb.core.EvictChargeProbe 50000 100 4000 600000 100 4000000 8 0
    w $C bergdb.core.EvictChargeProbe 50000 100 4000 600000 100 4000000 8 53
    w $C bergdb.core.EvictChargeProbe 30000 200 1500 1000000 200 5000000 30 0
    ;;
mw)
    for n in 1 2 4; do
        w $C bergdb.core.MwWarmProbe 100000 200 20000 200 20 5000000 $n
    done
    for n in 2 4 8; do
        w -Dhold=50000 -Dpause=200000 $C bergdb.core.MwWarmProbe 100000 200 20000 200 20 5000000 $n
    done
    ;;
cost)
    w $C bergdb.core.WarmCostProbe 20000 200 10000 2000 20 1
    w $C bergdb.core.WarmCostProbe 20000 200 10000 2000 20 4
    ;;
stop)
    w $C bergdb.core.StopWarmProbe 300
    ;;
tail)
    w $C bergdb.core.S4RestartAfterTornSizeProbe "$OUT/rs"
    w $C bergdb.core.S4TornSweepFileProbe "$OUT/sw"
    w $C bergdb.core.S4TornFillProbe
    w $C bergdb.core.S4TornFillFileProbe "$OUT/fs" 100000 5,6,8,40,1000,50000
    w $C bergdb.core.S4TornSweepProbe
    w $C bergdb.core.S4Version155Probe
    ;;
esac
echo "RUN DONE $WHAT"
