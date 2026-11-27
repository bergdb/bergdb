#!/bin/sh
# bergdb 031-06: FaultProbe (Codex's test 2) over seeds with commits and parts that carry
# B, S, P and C. Usage, from the repository's root: JAR=... sh items/.../probes/faults.sh OUT
# Kind: functional.
OUT=${1:?out dir}
J=${JAR:-java/build/bergdb.jar}
D=items/031-release-2026-7/06-one-record-an-action/probes
mkdir -p "$OUT/classes"
javac -nowarn -cp $J -d "$OUT/classes" $D/P2CrashProbe.java $D/FaultProbe.java || exit 1
run() { echo "== $PROPS $*"; java -ea -Xmx4g $PROPS -cp "$OUT/classes:$J" bergdb.core.FaultProbe "$@" 2>&1 | grep -v "^\s*at "; }
PROPS="-Dmaxv=100 -Dkeys=30 -Dnode=8 -Dmaint=50"; run 41 300 200 8
PROPS="-Dmaxv=6000 -Dmaint=0"; run 51 600 2000 8
PROPS="-Dmaxv=3000 -Dmaint=2"; run 52 800 1000 8
PROPS="-Dmaxv=2000 -Dmaint=4 -Dnode=8 -Dkeys=500"; run 53 800 1000 8
PROPS="-Dmaxv=20000 -Dbudget=1000 -Dkeys=100"; run 54 400 10000 8
PROPS="-Dmaxv=400 -Dmaint=15 -Dnode=30 -Dkeys=2000"; run 55 800 500 8
echo "FAULTS DONE"
