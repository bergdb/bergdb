#!/bin/sh
# The contract checker's own test of the top (bergdb 030-08), beside faults.sh
# (030-09): faults made by hand in the top lines of a good trace must each make
# `contractcheck` fail with C5 (the top's clauses, the roots' link, the SKIPT lines)
# or L2 (a LIVE 0 line that is not `findTop`); the good trace must pass. The faults:
# a top node's lowest skip pointer naming another top node than the one before it,
# its skip pointers left out, two of them out of the order of their index, a second
# new top node in one transaction, a SKIPT line with another time, and a LIVE 0 line
# naming another top node.
#
# Usage: lean/contract/faults-top.sh
# Needs: the checker (cd lean/contractcheck && lake build contractcheck) and java/build
# (java/build.sh). Prints one line per fault and FAULTS OK or FAULTS FAILED.
cd "$(dirname "$0")"
CHECK=$(pwd)/../contractcheck/.lake/build/bin/contractcheck
[ -x "$CHECK" ] || { echo "FAULTS FAILED: no checker; run lake build in lean/contractcheck/"; exit 1; }
JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi
DIR=${TMPDIR:-/tmp}/contract-faults-top.$$
mkdir -p $DIR
CP=../../java/build/bergdb.jar:../../java/build/stress
# The good trace: the small set's hot configuration, 100 transactions, about 33 top
# nodes, with LIVE lines.
PROPS="-Dn=100 -Dkeys=1 -Dmaxnode=8 -Dsd=200 -Dops=1 -Dtree=1 -Dlive=1"
$JAVA -ea $PROPS -cp $CP bergdb.core.TraceExport 1 $DIR/good.trace > $DIR/good.txt 2>&1 \
    || { echo "FAULTS FAILED: TraceExport: $(tail -1 $DIR/good.txt)"; exit 1; }
G=$DIR/good.trace
FAILED=0

# expect NAME FILE CHECK: the checker must fail FILE, with CHECK (C5 or L2) failing.
expect() {
    "$CHECK" $2 > $DIR/$1.out 2>&1
    if [ $? = 0 ]; then
        echo "   $1: WRONG, passes"
        FAILED=$((FAILED + 1))
    elif grep -q "$3 [1-9]" $DIR/$1.out; then
        echo "   $1: fails: $(grep -v '^total: \|^CONTRACT' $DIR/$1.out | grep -o 'first: .*' | head -1 | cut -c1-90)"
    else
        echo "   $1: WRONG, fails but not $3: $(head -1 $DIR/$1.out | cut -c1-110)"
        FAILED=$((FAILED + 1))
    fi
}

"$CHECK" $G > $DIR/good.out 2>&1 && echo "   good: passes" \
    || { echo "   good: WRONG, fails: $(head -1 $DIR/good.out | cut -c1-110)"; FAILED=$((FAILED + 1)); }
# The first transaction from TX 30 on that makes a top node with two skip pointers or more.
T=$(awk '/^TX /{tx=$2} tx>=30 && /^ADD [0-9]+ [0-9]+ S /{n[tx]++; if (n[tx]==2) {print tx; exit}}' $G)
[ -n "$T" ] || { echo "FAULTS FAILED: no top node with two skip pointers"; exit 1; }
# Its lowest skip pointer names the top node of its second.
awk -v t=$T '/^TX /{tx=$2} tx==t && /^ADD [0-9]+ [0-9]+ S / {n++; if (n==1) a=NR; if (n==2) y=$6} {l[NR]=$0}
    END {for (i=1; i<=NR; i++) {if (i==a) {split(l[i], f, " "); f[6]=y; print f[1],f[2],f[3],f[4],f[5],f[6]} else print l[i]}}' $G > $DIR/skipwrong.trace
expect skipwrong $DIR/skipwrong.trace C5
awk -v t=$T '/^TX /{tx=$2} !(tx==t && /^ADD [0-9]+ [0-9]+ S /){print}' $G > $DIR/skipnone.trace
expect skipnone $DIR/skipnone.trace C5
awk -v t=$T '/^TX /{tx=$2} tx==t && /^ADD [0-9]+ [0-9]+ S / && !d {held=$0; d=1; next}
    {print} tx==t && /^ADD [0-9]+ [0-9]+ S / && d==1 {print held; d=2}' $G > $DIR/skiporder.trace
expect skiporder $DIR/skiporder.trace C5
awk -v t=$T '/^TX /{tx=$2} {print} tx==t && /^ADD 0 [0-9]+ T /{print "ADD 0 " t " T 999999"}
    tx==t && /^ADD [0-9]+ [0-9]+ R /{print "ADD 999999 " t " R " $5}' $G > $DIR/twotops.trace
expect twotops $DIR/twotops.trace C5
awk '/^TX /{tx=$2} tx>=30 && /^SKIPT / && !d {$3=$3+1; d=1} {print}' $G > $DIR/skipt.trace
expect skipt $DIR/skipt.trace C5
# A LIVE 0 line from TX 30 on that names another top node than the first: the first.
Z=$(awk '/^ADD 0 0 T /{print $5; exit}' $G)
awk -v z=$Z '/^TX /{tx=$2} tx>=30 && /^LIVE 0 [0-9]+ [0-9]+$/ && $4!=z && !d {$4=z; d=1} {print}' $G > $DIR/livetop.trace
expect livetop $DIR/livetop.trace L2

rm -rf $DIR
if [ $FAILED -eq 0 ]; then
    echo "FAULTS OK"
else
    echo "FAULTS FAILED: $FAILED"
    exit 1
fi
