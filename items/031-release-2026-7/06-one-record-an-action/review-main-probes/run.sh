#!/bin/sh
# bergdb 031-06, the probes of the review of the landed diff (review-main.md): how each was
# run, from the repository's root, after java/build.sh. OUT is a directory for the classes.
# Usage: sh items/031-release-2026-7/06-one-record-an-action/review-main-probes/run.sh OUT [reuse|room|clock|pass|sweep]
# Kind: functional.
OUT=${1:?out dir}
WHAT=${2:-all}
J=${JAR:-java/build/bergdb.jar}
P=items/031-release-2026-7/06-one-record-an-action/review-main-probes
mkdir -p "$OUT"
javac -nowarn -cp $J -d "$OUT" $P/*.java || exit 1
C="$OUT:$J"

# R1: a Trans executed again after its execution failed the database (runs/reuse.txt).
if [ $WHAT = all ] || [ $WHAT = reuse ]; then
    for seed in 1 2 3 4 5; do for n in 0 1; do for m in after before; do
        echo "== seed $seed node8 $n $m"
        java -ea -cp $C bergdb.core.RmReuseProbe $seed $n $m 2>&1 | grep -v "^\s*at "
    done; done; done
fi

# R2: the record's room at lowered limits (runs/room.txt).
# limit sd keys actions maintainEvery seed node8 valueBytes [bigEvery bigBytes]
room() { java -ea -Xmx4g -cp $C bergdb.core.RmRoomProbe "$@" 2>&1 | grep -v "^\s*at "; }
if [ $WHAT = all ] || [ $WHAT = room ]; then
    room 100000 20000 20000 30000 30000 1 1 30            # ReclaimRoomTester's startup distance
    room 100000 2000000 20000 30000 0 1 1 30              # commits of small puts only
    room 100000 2000000 20000 30000 30000 1 1 30          # then one maintain() call
    room 100000 2000000 20000 30000 0 1 1 30 200 80000    # commits, an 80 kB value every 200th
    room 100000 2000000 20000 30000 0 1 1 30 50 60000
    room 100000 1000000 20000 40000 20000 2 1 30
    room 200000 4000000 20000 40000 40000 3 1 30
    room 200000 4000000 20000 40000 40000 3 0 30          # node size 30
    room 1000000 4000000 20000 40000 40000 3 1 30
fi

# R3: a commit's time after a reader's currentTime(), with and without a restart
# (runs/clock.txt).
if [ $WHAT = all ] || [ $WHAT = clock ]; then
    echo "== still"; java -ea -cp $C bergdb.core.RmClockProbe still
    echo "== back"; java -ea -cp $C bergdb.core.RmClockProbe back
fi

# R4: one small put, then maintain() calls until they rest (runs/pass.txt).
if [ $WHAT = all ] || [ $WHAT = pass ]; then
    java -ea -cp $C bergdb.core.RmPassProbe 20000 100 1000
    java -ea -cp $C bergdb.core.RmPassProbe 100000 200 100000
fi

# Section 4: the item's P2CrashProbe (with landing.md's appendix applied) and the review's
# variants: -Dlimit (a lowered record limit, so that the record's room plans steps again),
# -Dbig and -Dbigkeys (actions of many keys), -Dreserve (split steps), -Dxform (value
# transformations, some giving deletes), -Ddeep (keys of 14 segments), -Dtornall (torn
# records of parts and setters too). runs/sweep-rm.txt, runs/sweep-rm2.txt.
sweep() { echo "== $PROPS $*"; java -ea -Xmx4g $PROPS -cp $C bergdb.core.P2CrashProbe "$@" 2>&1 | grep -v "^\s*at " | cut -c1-1500; }
if [ $WHAT = all ] || [ $WHAT = sweep ]; then
    PROPS="-Dmaint=15 -Dmaxv=100 -Dnode=8 -Dkeys=2000 -Dlimit=60000 -Dbig=20 -Dstride=2"; sweep 24 500 1000 all
    PROPS="-Dmaint=5 -Dmaxv=100 -Dnode=8 -Dkeys=2000 -Dlimit=40000 -Dbig=30 -Dstride=2 -Drestart=3"; sweep 25 600 2000 all
    PROPS="-Dmaint=2 -Dmaxv=100 -Dnode=8 -Dkeys=4000 -Dlimit=40000 -Dbig=50 -Dbigkeys=70 -Dstride=3 -Drestart=5"; sweep 29 900 4000 all
    PROPS="-Dmaint=10 -Dmaxv=300 -Dnode=8 -Dkeys=1500 -Dreserve=3000 -Dstride=2 -Dxform=1 -Ddeep=1 -Drestart=2"; sweep 27 500 1500 all
    PROPS="-Dmaint=10 -Dmaxv=300 -Dkeys=1500 -Dreserve=20000 -Dstride=2 -Dxform=1 -Devict=1 -Dlimit=80000 -Dbig=20"; sweep 28 500 1500 all
    PROPS="-Dmaint=8 -Dmaxv=2000 -Dnode=30 -Dkeys=800 -Dlimit=200000 -Dbig=25 -Dbigkeys=200 -Dstride=3 -Dxform=1 -Dreader=1 -Dclock=back"; sweep 30 600 5000 all
    PROPS="-Dmaint=8 -Dmaxv=500 -Dnode=8 -Dkeys=5000 -Dlimit=100000 -Dbig=25 -Dbigkeys=100 -Dstride=5 -Ddeep=1 -Devict=1 -Drestart=4"; sweep 31 800 20000 all
    PROPS="-Dmaint=30 -Dmaxv=100 -Dnode=8 -Dkeys=2000 -Dlimit=40000 -Dbig=30 -Dtorn=2 -Dxform=1 -Dtornall=true"; sweep 25 400 2000 torn
    PROPS="-Dmaint=40 -Dmaxv=3000 -Dnode=8 -Dkeys=300 -Dtorn=2 -Dtornall=true -Dbudget=1000"; sweep 21 400 2000 torn
    PROPS="-Dmaxv=100 -Dkeys=30 -Dnode=8 -Dmaint=50 -Dtorn=1 -Dtornall=true"; sweep 41 300 200 torn
    # Steps left out of a commit's record by the room (runs/sweep-rm2.txt)
    PROPS="-Dmaint=3 -Dmaxv=100 -Dnode=8 -Dkeys=3000 -Dlimit=30000 -Dbig=60 -Dbigkeys=40 -Dstride=3 -Drestart=4"; sweep 32 700 3000 all
    PROPS="-Dmaint=3 -Dmaxv=100 -Dnode=8 -Dkeys=3000 -Dlimit=24000 -Dbig=70 -Dbigkeys=30 -Dstride=3"; sweep 33 700 3000 all
fi
