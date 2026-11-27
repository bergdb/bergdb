#!/bin/sh
# bergdb 031-06, the review's probes (review-fable.md): how each was run, from the
# repository's root, after java/build.sh. OUT is a directory for the classes.
# RvPace also ran on 031-05's jar (4135ba2a, built in a worktree) with
# -Dproto315.eager=true. Kind: functional (the times that RvP1 prints are figures).
OUT=${1:?out dir}
J=${JAR:-java/build/bergdb.jar}
mkdir -p "$OUT"
javac -nowarn -cp $J -d "$OUT" review-probes/Rv*.java || exit 1
r() { echo "== $*"; java -ea -Xmx6g "$@" 2>&1 | grep -v "^\s*at "; }
C="-cp $OUT:$J"
# Copies dropped at keys the action writes, and restarts (section 3)
r $C bergdb.core.RvFront 1 4000
r $C bergdb.core.RvFront 2 4000 8
r -Dcold=2000 -Dlen=1500 $C bergdb.core.RvFront 4 5000
r -Dcold=2000 -Dlen=1500 $C bergdb.core.RvFront 5 5000 8
r -Dcold=2000 -Dlen=1500 $C bergdb.core.RvFront 6 6000 30
r -Dcold=2000 -Dlen=1500 -Dmaint=0 $C bergdb.core.RvFront 21 6000
r -Dcold=2000 -Dlen=1500 -Dmaint=0 $C bergdb.core.RvFront 22 6000 8
r -Dcold=2000 -Dlen=1500 -Dmaint=1 -Dcache=200000 $C bergdb.core.RvFront 23 6000 8
r -Dcold=2000 -Dlen=1500 -Dmaint=0 -Dsd=500 $C bergdb.core.RvFront 24 6000 30
# Cold values of up to 3 MB, a cache of 60 MB
r -Dcold=40 -Dlen=3000000 -Dcache=60000000 -Dmaint=1 $C bergdb.core.RvFront 31 1500
r -Dcold=40 -Dlen=3000000 -Dcache=60000000 -Dmaint=0 $C bergdb.core.RvFront 32 2500 8
# stop() and close() under writers
r $C bergdb.core.RvStop 1 150
r $C bergdb.core.RvStop 2 150 8
# Readers and provenance walks while commits carry steps and cuts
r $C bergdb.core.RvRead 3 12
r -Dcache=300000 $C bergdb.core.RvRead 4 12 8
# Pace and the stream kept (F2, F3); no -ea: figures of size only
p() { echo "== $*"; java -Xmx6g "$@" 2>&1 | grep -v "^\s*at "; }
p $C bergdb.core.RvPace 20000 200 20000 200 20
p $C bergdb.core.RvPace 20000 200 20000 200 20 8
p $C bergdb.core.RvPace 20000 10 30000 100 20 8
p -Ddeep=true $C bergdb.core.RvPace 20000 10 30000 100 20 8
p $C bergdb.core.RvPace 4000 1000 6000 20000 200
p -Dcap=2200000 $C bergdb.core.RvPace 4000 1000 3000 100000 200
p -Dcap=2200000 $C bergdb.core.RvPace 4000 1000 1500 300000 200
p -Dcap=2200000 $C bergdb.core.RvPace 20000 1000 2500 300000 500
# P1 figures (F4) and the step reserve (F7)
p $C bergdb.core.RvP1 100000 200 0 4000
p $C bergdb.core.RvP1 300 1000000 0 1500
p $C bergdb.core.RvP1 60000 1000 600000 14000
p $C bergdb.core.RvP1 60000 1000 600000 14000 30000000
p -Dreserve=1048576 $C bergdb.core.RvP1 60000 1000 600000 14000
# A long key of BergDB's own prefix through the Core API, copied by a step (F6)
r $C bergdb.core.RvLong 3000 8
r $C bergdb.core.RvLong 7000 8
# F5's consequence, at a record limit lowered after the key's transaction
r -Dlimit=100000 $C bergdb.core.RvLong 7000 8
echo "REVIEW PROBES DONE"
