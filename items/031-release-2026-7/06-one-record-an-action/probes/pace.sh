#!/bin/sh
# bergdb 031-06, landing step 3 (the pace): UndercountProbe (what a pass of parts' steps
# is not charged), and PaceProbe (the review's RvPace, F2 and F3: reclaim's share of the
# growth against the internal fraction, the stream kept against the live data, under small
# and large commits). Usage, from the repository's root, after java/build.sh:
#   sh items/031-release-2026-7/06-one-record-an-action/probes/pace.sh OUT
# with JAR set for another jar (UndercountProbe prints step 3's figures: compile it against
# a jar of step 3; runs/undercount.txt has the run before it). Kind: functional (figures of
# size; no time is measured).
OUT=${1:?out dir}
J=${JAR:-java/build/bergdb.jar}
P=items/031-release-2026-7/06-one-record-an-action/probes
mkdir -p "$OUT"
javac -nowarn -cp $J -d "$OUT" $P/PaceProbe.java $P/UndercountProbe.java || exit 1
C="-cp $OUT:$J"
p() { echo "== $*"; java -Xmx6g "$@" 2>&1 | grep -v "^\s*at "; }
p $C bergdb.core.UndercountProbe 30000
# F2: commits of one small put
p $C bergdb.core.PaceProbe 20000 200 20000 200 20
p $C bergdb.core.PaceProbe 20000 200 20000 200 20 8
p $C bergdb.core.PaceProbe 20000 10 30000 100 20 8
p -Ddeep=true $C bergdb.core.PaceProbe 20000 10 30000 100 20 8
# F3 (028-71): large commits of one put
p $C bergdb.core.PaceProbe 4000 1000 6000 20000 200
p $C bergdb.core.PaceProbe 4000 1000 3000 100000 200
p $C bergdb.core.PaceProbe 4000 1000 1500 300000 200
p $C bergdb.core.PaceProbe 4000 1000 600 1000000 200
# Commits of many small puts at random keys, whose index nodes are most of the growth
p -Dputs=200 -Dhot=20000 $C bergdb.core.PaceProbe 4000 1000 1500 20000 200
p -Dputs=500 -Dhot=20000 $C bergdb.core.PaceProbe 4000 1000 1000 25000 200
echo PACE DONE
