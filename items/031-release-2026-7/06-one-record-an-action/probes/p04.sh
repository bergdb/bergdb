#!/bin/sh
# bergdb 031-06: 031-04's HoleProbe and IdleLiveProbe (its probes/, with M.java) as 031-05
# (section 7.5) ran them. Usage, from java/: JAR=... sh ../items/.../probes/p04.sh OUT
# Kind: functional.
OUT=${1:?out dir}
J=${JAR:-build/bergdb.jar}
D=../items/031-release-2026-7/04-maintain-budget/probes
mkdir -p $OUT/classes
javac -nowarn -cp $J -d $OUT/classes $D/M.java $D/HoleProbe.java $D/IdleLiveProbe.java || exit 1
for a in "4000 20000" "20000 20000"; do echo "== HoleProbe $a"; java -Xmx4g -cp $OUT/classes:$J bergdb.core.HoleProbe $a 2>&1 | tail -6; done
for a in "30000 1000000" "15000 1000000" "100000 1000000" "100000 5000000"; do echo "== IdleLiveProbe $a 20 10"; java -Xmx6g -cp $OUT/classes:$J bergdb.core.IdleLiveProbe $a 20 10 2>&1 | tail -6; done
echo "P04 DONE"
