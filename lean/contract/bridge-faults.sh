#!/bin/sh
# The bridge checker's own test (bergdb 030-07): faults made by hand in good
# traces must each make `bridgecheck` fail; the good traces must pass. The
# faults: a key entry with another compare value than its klong (K); a delete
# entry with another compare value than its bitmap's (K); a value made without
# its NEW line (N); a key node made on level 0 (L, A4); a top node's skip
# pointer left out (TOP, R4); a top node's root pointer to another node (TOP,
# the link); a touched node left out of the TOUCH line (TOUCH); the primordial
# top node's root pointer to another node (the start); and, since bergdb 030-11,
# a trace that is not whole: an ERROR line, no DONE line, a trace cut after a
# transaction (`completeFault`).
#
# Usage: lean/contract/bridge-faults.sh
# Needs: the checker (cd lean/contract && lake build bridgecheck) and the traces
# of the small and the reclaim set (java/stress/treeconf.sh small, reclaim).
# Prints one line per fault and BRIDGE FAULTS OK or BRIDGE FAULTS FAILED.
cd "$(dirname "$0")"
CHECK=$(pwd)/.lake/build/bin/bridgecheck
[ -x "$CHECK" ] || { echo "BRIDGE FAULTS FAILED: no checker; run lake build in lean/contract/"; exit 1; }
G=../../java/build/traces/tree-small/mixed-1.trace
R=../../java/build/traces/tree-reclaim/r-del-1.trace
[ -f "$G" ] && [ -f "$R" ] || { echo "BRIDGE FAULTS FAILED: no traces (treeconf.sh small, reclaim)"; exit 1; }
DIR=${TMPDIR:-/tmp}/bridge-faults.$$
mkdir -p $DIR
FAILED=0

# expect NAME PASS|FAIL FILE: runs the checker on FILE.
expect() {
    "$CHECK" $3 > $DIR/$1.out 2>&1
    status=$?
    if [ $2 = PASS ]; then ok=$((status == 0)); word=passes; else ok=$((status != 0)); word=fails; fi
    if [ $ok = 1 ]; then
        echo "   $1: $word: $(grep -v '^total: \|^BRIDGE' $DIR/$1.out | head -1 | sed 's/^.*failures: //' | cut -c1-120)"
    else
        echo "   $1: WRONG, expected $2: $(head -1 $DIR/$1.out | cut -c1-110)"
        FAILED=$((FAILED + 1))
    fi
}

# fault NAME FILE AWK-PROGRAM: the trace FILE changed by the awk program must fail.
fault() {
    awk "$3" $2 > $DIR/$1.trace
    cmp -s $2 $DIR/$1.trace && { echo "   $1: WRONG, the fault changed nothing"; FAILED=$((FAILED + 1)); return; }
    expect $1 FAIL $DIR/$1.trace
}

expect good PASS $G
expect good-reclaim PASS $R
# The first key entry of TX 1 gets another compare value; its KN line is as it was.
fault key-entry $G '!d && /^ADD [0-9]+ 1 K / { $5 = $5 + 8; d = 1 } { print }'
# The first delete entry gets another compare value.
fault delete-entry $G '!d && /^ADD [0-9]+ [0-9]+ D 1 / { $6 = $6 + 8; d = 1 } { print }'
# The first value of TX 1 has no NEW line.
fault no-new $G '!d && /^NEW [0-9]+ 0 D$/ { d = 1; next } { print }'
# The first key node made in TX 2 is on level 0.
fault level-0 $G 'tx == 2 && !d && /^NEW [0-9]+ [1-9][0-9]* I$/ { $3 = 0; d = 1 } /^TX / { tx = $2 } { print }'
# The first skip pointer of a top node is left out.
fault no-skip $G '!d && /^ADD [0-9]+ [0-9]+ S / { d = 1; next } { print }'
# The root pointer of the top node made in TX 2 names another node.
fault root-pointer $G 'tx == 2 && !d && /^ADD [0-9]+ 2 R / { $5 = $5 - 2; d = 1 } /^TX / { tx = $2 } { print }'
# The first TOUCH line loses its last node.
fault touch $R '!d && /^TOUCH / { NF = NF - 1; d = 1 } { print }'
# The primordial top node names another key node.
fault start $G '!d && /^ADD [0-9]+ 0 R / { $5 = $5 + 2; d = 1 } { print }'
# An ERROR line after the head (bergdb 030-11).
fault error-line $G '/^TX 0$/ && !d { print "ERROR a change the lines cannot express"; d = 1 } { print }'
# No DONE line.
fault no-done $G '!/^DONE / { print }'
# Cut after TX 9: TX 10 and the rest left out.
fault cut $G '/^TX 10$/ { c = 1 } !c { print }'

rm -rf $DIR
if [ $FAILED -eq 0 ]; then
    echo "BRIDGE FAULTS OK"
else
    echo "BRIDGE FAULTS FAILED: $FAILED"
    exit 1
fi
