#!/bin/sh
# bergdb 031-06: P2CrashProbe with the variants of Fable's review of 031-05 (its
# ReviewProbe): a reader's currentTime() before every action, a refused transaction before
# every action, a clock that goes back or stands still, eviction at every transaction.
# Usage, from the repository's root: JAR=... sh items/.../probes/sweep2.sh OUT
# Kind: functional.
OUT=${1:?out dir}
J=${JAR:-java/build/bergdb.jar}
mkdir -p "$OUT/classes"
javac -nowarn -cp $J -d "$OUT/classes" items/031-release-2026-7/06-one-record-an-action/probes/P2CrashProbe.java || exit 1
run() { echo "== $PROPS $*"; java -ea -Xmx4g $PROPS -cp "$OUT/classes:$J" bergdb.core.P2CrashProbe "$@" 2>&1 | grep -v "^\s*at "; }
for V in "-Dreader=1" "-Drefuse=1" "-Dclock=back" "-Devict=1" "-Dreader=1 -Drefuse=1 -Dclock=back -Devict=1"; do
PROPS="$V -Dmaxv=6000"; run 2 400 2000 all
PROPS="$V -Dmaxv=20000 -Dbudget=1000"; run 13 300 50000 all
PROPS="$V -Dmaint=15 -Dmaxv=3000 -Dnode=8 -Dkeys=1000"; run 21 400 2000 all
PROPS="$V -Dmaint=15 -Dmaxv=1000 -Dnode=30 -Dkeys=300"; run 22 400 5000 all
PROPS="$V -Dmaint=15 -Dmaxv=100 -Dnode=8 -Dkeys=2000"; run 24 500 1000 all
PROPS="$V -Dmaxv=20000 -Dbudget=1000 -Dnode=8 -Dkeys=3000 -Dstride=9"; run 33 1000 2000 all
PROPS="$V -Dmaxv=100 -Dkeys=30 -Dnode=8 -Dmaint=50"; run 41 300 200 all
done
PROPS="-Dclock=still -Dmaxv=6000"; run 2 400 2000 all
echo "SWEEP2 DONE"
