#!/bin/sh
# Bergdb 005-04, option 4 (../04-a6-failures.md, "Outcome"): every A6 failure of the Java
# tier, with a line (SIG) that says which kind it is. Runs java/stress/A2A3Check2 with
# signature.diff applied, on the 21 configurations of docs/level2-alignment.md, 10.5, then on
# seven more that put many keys under a new first key segment in one transaction, at node
# sizes 8 to 62. A tool for this subitem only.
#
# Usage: sh java-tier.sh BERGDB OUT
#   BERGDB  a checkout of bergdb with java/ built (java/build.sh)
#   OUT     a directory for the outputs, one file per configuration
# About 5 minutes on one core. Prints one line per configuration, the SIG lines counted by
# kind, and the totals.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
B=$(cd "$1" && pwd)
mkdir -p "$2"
OUT=$(cd "$2" && pwd)
mkdir -p $OUT/src $OUT/classes
cp $B/java/stress/A2A3Check2.java $OUT/src/
(cd $OUT/src && patch -s A2A3Check2.java < $HERE/signature.diff)
javac --release 8 -Xlint:-options -nowarn -cp $B/java/build/bergdb.jar -d $OUT/classes \
    $OUT/src/A2A3Check2.java
CP=$B/java/build/bergdb.jar:$OUT/classes
set +e

n=0
while read cfg; do
    case "$cfg" in ""|\#*) continue ;; esac
    n=$((n + 1))
    start=$(date +%s)
    nice java -ea -DdebugA6=1 $cfg -cp $CP bergdb.dag.A2A3Check2 > $OUT/c-$n.txt 2>&1
    end=$(date +%s)
    echo "$n [$((end - start)) s] $cfg | $(grep -o '^  transactions [0-9]*' $OUT/c-$n.txt | sed 's/^ *//')" \
        "| A6 $(grep -o 'adopted index nodes .*' $OUT/c-$n.txt)" \
        "| A-COPY $(grep -o 'failing [0-9]* (transactions [0-9]*)' $OUT/c-$n.txt)"
    grep '^SIG ' $OUT/c-$n.txt | sed -E 's/\(dead klong of [0-9]+, live of [0-9]+\)/(older)/' \
        | sort | uniq -c | sed 's/^/      /'
    grep -i "exception\|error" $OUT/c-$n.txt | head -3
done <<EOF
# The 21 configurations of docs/level2-alignment.md, 10.5.
-Dmaxnode=8 -Dkeys=200 -Dn=300 -Dops=1 -Ddel=0 -Dseeds=10
-Dmaxnode=8 -Dkeys=200 -Dn=300 -Dops=1 -Ddel=25 -Dlong=1 -Dseeds=10
-Dmaxnode=8 -Dkeys=200 -Dn=300 -Dops=4 -Ddel=0 -Dseeds=10
-Dmaxnode=8 -Dkeys=200 -Dn=300 -Dops=4 -Ddel=25 -Dlong=1 -Dseeds=10
-Dmaxnode=8 -Dkeys=40 -Dn=1 -Dops=40 -Dexact=1 -Ddel=0 -Dseeds=1
-Dmaxnode=8 -Dkeys=1000 -Dn=50 -Dops=40 -Dexact=1 -Ddel=0 -Dseeds=10
-Dmaxnode=8 -Dkeys=1000 -Dn=50 -Dops=40 -Dexact=1 -Ddel=25 -Dlong=1 -Dseeds=10
-Dmaxnode=62 -Dkeys=100000 -Dn=20 -Dops=400 -Dexact=1 -Ddel=0 -Dseeds=10
-Dmaxnode=14 -Dkeys=300 -Dn=50 -Dops=40 -Dexact=1 -Ddel=40 -Dlong=1 -Dseeds=10
-Dmaxnode=8 -Dkeys=200 -Dn=300 -Dops=4 -Ddel=25 -Dlong=1 -Dunsorted=1 -Dseeds=10
-Dmaxnode=8 -Dkeys=500 -Dn=2000 -Dops=4 -Ddel=20 -Dlong=1 -Dseeds=3
-Dmaxnode=14 -Dkeys=1000 -Dn=1000 -Dops=8 -Ddel=20 -Dseeds=3
-Dmaxnode=30 -Dkeys=3000 -Dn=1000 -Dops=20 -Ddel=20 -Dlong=1 -Dseeds=3
-Dmaxnode=62 -Dkeys=3000 -Dn=500 -Dops=40 -Ddel=20 -Dseeds=3
-Dmaxnode=30 -Dkeys=2000 -Dn=500 -Dops=4 -Ddel=20 -Dlong=1 -Dunsorted=1 -Dseeds=3
-Dmaxnode=30 -Dkeys=500 -Dn=2000 -Dops=20 -Ddel=20 -Dlong=1 -Dseeds=3
-Dmaxnode=8 -Dkeys=500 -Dn=2000 -Dops=10 -Ddel=20 -Dlong=1 -Dseeds=3
-Dmaxnode=14 -Dkeys=500 -Dn=2000 -Dops=3 -Ddel=20 -Dlong=1 -Dseeds=3
-Dmaxnode=62 -Dkeys=1000 -Dn=2000 -Dops=40 -Ddel=20 -Dseeds=3
-Dmaxnode=30 -Dkeys=100 -Dn=400 -Dops=3 -Ddel=20 -Dlong=1 -Dseeds=3
-Dmaxnode=30 -Dkeys=3000 -Dn=12000 -Dops=3 -Ddel=20 -Dseeds=1
# Seven more: large transactions with two-segment keys, node sizes 8 to 62.
-Dmaxnode=62 -Dkeys=1000 -Dn=5 -Dexact=1 -Dops=2000 -Ddel=0 -Dlong=1 -Dseeds=3
-Dmaxnode=62 -Dkeys=1000 -Dn=20 -Dexact=1 -Dops=1000 -Ddel=20 -Dlong=1 -Dunsorted=1 -Dseeds=3
-Dmaxnode=30 -Dkeys=1000 -Dn=20 -Dexact=1 -Dops=400 -Ddel=20 -Dlong=1 -Dseeds=5
-Dmaxnode=30 -Dkeys=1000 -Dn=20 -Dexact=1 -Dops=400 -Ddel=20 -Dlong=1 -Dunsorted=1 -Dseeds=5
-Dmaxnode=14 -Dkeys=1000 -Dn=50 -Dexact=1 -Dops=100 -Ddel=20 -Dlong=1 -Dseeds=5
-Dmaxnode=14 -Dkeys=300 -Dn=200 -Dops=60 -Ddel=30 -Dlong=1 -Dunsorted=1 -Dseeds=5
-Dmaxnode=8 -Dkeys=1000 -Dn=200 -Dops=40 -Ddel=30 -Dlong=1 -Dunsorted=1 -Dseeds=10
EOF
echo "totals: A6 failures (SIG lines) $(cat $OUT/c-*.txt | grep -c '^SIG '), of an unknown kind" \
    "$(cat $OUT/c-*.txt | grep '^SIG ' | grep -c OTHER), not below the old parent" \
    "$(cat $OUT/c-*.txt | grep -c 'NOT below')"
