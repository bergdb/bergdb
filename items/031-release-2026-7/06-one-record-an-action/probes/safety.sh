#!/bin/sh
# bergdb 031-06: SafetyProbe (Codex's test 3) in several configurations: lowered record
# limits with sustained large commits, small step reserves, node sizes 8 and 30, the
# release's limits. Usage, from the repository's root: JAR=... sh items/.../probes/safety.sh OUT
# Kind: functional.
OUT=${1:?out dir}
J=${JAR:-java/build/bergdb.jar}
D=items/031-release-2026-7/06-one-record-an-action/probes
mkdir -p "$OUT/classes"
javac -nowarn -cp $J -d "$OUT/classes" $D/*.java || exit 1
run() { echo "== $PROPS $*"; java -ea -Xmx4g $PROPS -cp "$OUT/classes:$J" bergdb.core.SafetyProbe "$@" 2>&1 | grep -v "^\s*at "; }
PROPS="-Dlimit=200000 -Dreserve=2000"; run 1 6000
PROPS="-Dlimit=200000 -Dreserve=2000 -Dnode=8"; run 2 6000
PROPS="-Dlimit=100000 -Dreserve=500 -Dnode=8 -Dcold=600"; run 3 6000
PROPS="-Dlimit=300000 -Dreserve=100000 -Dnode=30 -Dhot=200"; run 4 6000
PROPS="-Dlimit=1000000 -Dreserve=4000 -Dsd=10000 -Dcold=2000"; run 5 5000
PROPS="-Dlimit=0 -Dreserve=4194304 -Dsd=20000 -Dcold=1000"; run 6 3000
PROPS="-Dlimit=150000 -Dreserve=300 -Dnode=8 -Dsd=500 -Dcold=200 -Dhot=20"; run 7 8000
echo "SAFETY DONE"
