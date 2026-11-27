#!/bin/sh
# bergdb 031-06: ConcProbe, ten runs: 2 to 4 writer threads, a maintain() thread, a setter
# thread, two readers; then the replay of the logged actions on one thread.
# Usage, from the repository's root: JAR=... sh items/.../probes/conc.sh OUT
# Kind: functional (the threads' timing varies; the check is that the replay gives the same
# stream, whatever the timing was).
OUT=${1:?out dir}
J=${JAR:-java/build/bergdb.jar}
D=items/031-release-2026-7/06-one-record-an-action/probes
mkdir -p "$OUT/classes"
javac -nowarn -cp $J -d "$OUT/classes" $D/P2CrashProbe.java $D/ConcProbe.java || exit 1
run() { echo "== $PROPS $*"; java -ea -Xmx6g $PROPS -cp "$OUT/classes:$J" bergdb.core.ConcProbe "$@" 2>&1 | grep -v "^\s*at "; }
PROPS="-Dpause=200000"; run 11 8 2 0
PROPS="-Dpause=200000"; run 12 8 3 8
PROPS="-Dpause=100000"; run 13 8 4 30
PROPS="-Dpause=1000000"; run 14 8 2 8
PROPS="-Dpause=0"; run 15 5 3 0
PROPS="-Dpause=500000"; run 16 8 4 0
PROPS="-Dpause=200000"; run 17 8 3 30
PROPS="-Dpause=2000000"; run 18 8 2 0
PROPS="-Dpause=50000"; run 19 8 4 8
PROPS="-Dpause=300000"; run 20 8 3 0
echo "CONC DONE"
