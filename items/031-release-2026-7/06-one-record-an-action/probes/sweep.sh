#!/bin/sh
# bergdb 031-06: P2CrashProbe over 031-05's configurations (its p2crash-runs.txt), crash,
# pre (after the append, before apply) and stop at every record (every 3rd, 5th or 9th in
# the long ones), some with restarts in the continuation, and torn records.
# Usage, from the repository's root, after java/build.sh: sh items/.../probes/sweep.sh OUT
# Kind: functional.
OUT=${1:?out dir}
J=${JAR:-java/build/bergdb.jar}
mkdir -p "$OUT/classes"
javac -nowarn -cp $J -d "$OUT/classes" items/031-release-2026-7/06-one-record-an-action/probes/P2CrashProbe.java || exit 1
run() { echo "== $*"; java -ea -Xmx4g $PROPS -cp "$OUT/classes:$J" bergdb.core.P2CrashProbe "$@" 2>&1 | grep -v "^\s*at "; }
PROPS=""; run 1 150 10000 all
PROPS="-Dmaxv=6000"; run 2 400 2000 all
PROPS="-Dmaxv=6000"; run 3 400 2000 all
PROPS="-Dmaxv=6000"; run 11 400 2000 all
PROPS="-Dmaxv=3000"; run 12 400 10000 all
PROPS="-Dmaxv=20000 -Dbudget=1000"; run 13 300 50000 all
PROPS="-Dmaxv=2000"; run 14 600 1000 all
PROPS="-Dmaxv=6000 -Dbudget=10000"; run 15 400 5000 all
PROPS="-Dmaxv=400"; run 16 500 2000 all
PROPS="-Dmaint=15 -Dmaxv=3000 -Dnode=8 -Dkeys=1000"; run 21 400 2000 all
PROPS="-Dmaint=15 -Dmaxv=1000 -Dnode=30 -Dkeys=300"; run 22 400 5000 all
PROPS="-Dmaint=15 -Dmaxv=8000 -Dbudget=1000 -Dnode=8 -Dkeys=50"; run 23 300 20000 all
PROPS="-Dmaint=15 -Dmaxv=100 -Dnode=8 -Dkeys=2000"; run 24 500 1000 all
PROPS="-Dmaxv=6000 -Dstride=5"; run 31 2000 5000 all
PROPS="-Dmaxv=6000 -Dbudget=100000 -Dmaint=3 -Dstride=3"; run 32 1500 3000 all
PROPS="-Dmaxv=20000 -Dbudget=1000 -Dnode=8 -Dkeys=3000 -Dstride=9"; run 33 1000 2000 all
PROPS="-Dmaxv=100 -Dkeys=30 -Dnode=8 -Dmaint=50"; run 41 300 200 all
# Restarts in the continuation, every 7 and every 1 actions
PROPS="-Dmaxv=6000 -Drestart=7"; run 3 400 2000 all
PROPS="-Dmaint=15 -Dmaxv=100 -Dnode=8 -Dkeys=2000 -Drestart=1 -Dstride=4"; run 24 500 1000 all
PROPS="-Dmaxv=100 -Dkeys=30 -Dnode=8 -Dmaint=50 -Drestart=3"; run 41 300 200 all
# Torn records
PROPS="-Dmaxv=6000 -Dtorn=5"; run 3 400 2000 torn
PROPS="-Dmaint=15 -Dmaxv=3000 -Dnode=8 -Dkeys=1000 -Dtorn=5"; run 21 400 2000 torn
PROPS="-Dmaxv=100 -Dkeys=30 -Dnode=8 -Dmaint=50 -Dtorn=3"; run 41 300 200 torn
echo "SWEEP DONE"
