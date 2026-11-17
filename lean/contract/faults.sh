#!/bin/sh
# The contract checker's own test (bergdb 030-09): faults made by hand in a good
# trace, and one made in Java, must each make `contractcheck` fail; the good trace
# must pass. The faults are those of 030-06, findings 1, 2 and 7: an ERROR line, a
# line of an unknown kind, a transaction left out, a trace cut, no DONE line, a
# wrong DONE, a KN line for a node that no NEW line made, a node made without its
# KN line, a value made without its V entry, an ADD line at another time, a second
# KN line for a node, an OP line of an unknown kind, a LIVE line of a key node or of
# the root (the top search) that is not the package's; and from Java (TraceExport's
# fault=I) a klong of an existing node changed in memory, which the exporter must
# show as an ERROR line and as a KN line from its klong diff.
#
# Usage: lean/contract/faults.sh
# Needs: the checker (cd lean/contract && lake build contractcheck) and java/build
# (java/build.sh). Prints one line per fault and FAULTS OK or FAULTS FAILED.
cd "$(dirname "$0")"
CHECK=$(pwd)/.lake/build/bin/contractcheck
[ -x "$CHECK" ] || { echo "FAULTS FAILED: no checker; run lake build in lean/contract/"; exit 1; }
JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi
DIR=${TMPDIR:-/tmp}/contract-faults.$$
mkdir -p $DIR
CP=../../java/build/bergdb.jar:../../java/build/stress
# The good trace: the small set's mixed configuration, 60 transactions, with LIVE lines.
PROPS="-Dn=60 -Dkeys=20 -Dmaxnode=8 -Dsd=200 -Dops=4 -Ddel=25 -Dnodel=10 -Dempty=10 -Dtree=1 -Dlive=1"
$JAVA -ea $PROPS -cp $CP bergdb.core.TraceExport 1 $DIR/good.trace > $DIR/good.txt 2>&1 \
    || { echo "FAULTS FAILED: TraceExport: $(tail -1 $DIR/good.txt)"; exit 1; }
G=$DIR/good.trace
FAILED=0

# expect NAME PASS|FAIL FILE: runs the checker on FILE.
expect() {
    "$CHECK" $3 > $DIR/$1.out 2>&1
    status=$?
    if [ $2 = PASS ]; then ok=$((status == 0)); word=passes; else ok=$((status != 0)); word=fails; fi
    if [ $ok = 1 ]; then
        echo "   $1: $word: $(grep -v '^total: \|^CONTRACT' $DIR/$1.out | head -1 | sed 's/^[^:]*: //' | cut -c1-110)"
    else
        echo "   $1: WRONG, expected $2: $(head -1 $DIR/$1.out | cut -c1-110)"
        FAILED=$((FAILED + 1))
    fi
}

expect good PASS $G
awk '{print} /^TREE /{print "ERROR T(5) changed or removed entries of node 7"}' $G > $DIR/error.trace
expect error FAIL $DIR/error.trace
awk '{print} /^TX 12$/{print "XYZ 1 2"}' $G > $DIR/unknown.trace
expect unknown FAIL $DIR/unknown.trace
awk '/^TX 20$/{skip=1} !skip{print} /^END 20$/{skip=0}' $G > $DIR/gap.trace
expect gap FAIL $DIR/gap.trace
awk '{print} /^END 29$/{exit}' $G > $DIR/cut.trace
expect cut FAIL $DIR/cut.trace
grep -v '^DONE' $G > $DIR/nodone.trace
expect nodone FAIL $DIR/nodone.trace
sed 's/^DONE .*/DONE 70/' $G > $DIR/wrongdone.trace
expect wrongdone FAIL $DIR/wrongdone.trace
awk '/^TX 30$/{t=1} t && /^KN / && !d{$2=999999; d=1} {print}' $G > $DIR/knnonew.trace
expect knnonew FAIL $DIR/knnonew.trace
# A key node made in TX 30 or after: its KN line left out.
X=$(awk '/^TX /{tx=$2} tx>=30 && /^NEW .* I$/{print $2; exit}' $G)
awk -v x=$X '!($1=="KN" && $2==x){print}' $G > $DIR/nokn.trace
expect nokn FAIL $DIR/nokn.trace
Y=$(awk '/^TX /{tx=$2} tx>=30 && /^NEW .* D$/{print $2; exit}' $G)
awk -v y=$Y '!($1=="ADD" && $2==y && $4=="V"){print}' $G > $DIR/nov.trace
expect nov FAIL $DIR/nov.trace
awk '/^TX 30$/{t=1} t && /^ADD / && !d{$3=$3+1; d=1} {print}' $G > $DIR/addtime.trace
expect addtime FAIL $DIR/addtime.trace
awk '/^TX 30$/{t=1} {print} t && /^KN / && !d{print; d=1}' $G > $DIR/twokn.trace
expect twokn FAIL $DIR/twokn.trace
awk '/^TX 30$/{t=1} t && /^OP / && !d{$2="X"; d=1} {print}' $G > $DIR/opx.trace
expect opx FAIL $DIR/opx.trace
awk '/^TX 30$/{t=1} t && /^LIVE [1-9][0-9]* [0-9]* [0-9]/ && !d{$NF=999999; d=1} {print}' $G > $DIR/livekey.trace
expect livekey FAIL $DIR/livekey.trace
grep -q 'L1 [1-9]' $DIR/livekey.out || { echo "   livekey: WRONG, not L1"; FAILED=$((FAILED + 1)); }
awk '/^TX 30$/{t=1} t && /^LIVE 0 [0-9]* [0-9]/ && !d{$NF=""; d=1} {print}' $G > $DIR/livetop.trace
expect livetop FAIL $DIR/livetop.trace
grep -q 'L1 [1-9]' $DIR/livetop.out || { echo "   livetop: WRONG, not L1"; FAILED=$((FAILED + 1)); }

# From Java: a klong of an existing node changed in memory at the last record, R(60).
$JAVA -ea $PROPS -Dfault=60 -cp $CP bergdb.core.TraceExport 1 $DIR/java.trace > $DIR/java.txt 2>&1
grep -q '^fault: node' $DIR/java.txt || { echo "   java: WRONG, no fault made: $(head -1 $DIR/java.txt)"; FAILED=$((FAILED + 1)); }
expect java FAIL $DIR/java.trace
# The same trace without its ERROR line: the KN line of the klong diff alone must fail it.
grep -v '^ERROR' $DIR/java.trace > $DIR/javanoerror.trace
expect javanoerror FAIL $DIR/javanoerror.trace
grep -q 'C3 [1-9]' $DIR/javanoerror.out || { echo "   javanoerror: WRONG, not C3, the frame"; FAILED=$((FAILED + 1)); }

rm -rf $DIR
if [ $FAILED -eq 0 ]; then
    echo "FAULTS OK"
else
    echo "FAULTS FAILED: $FAILED"
    exit 1
fi
