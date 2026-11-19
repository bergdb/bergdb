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
# transaction (`completeFault`); since bergdb 030-14, the kinds of the key
# nodes that do not follow their levels (KIND, K-LEVEL: the TREE line's h set
# to 0, so that every level is a segment leaf's); and since bergdb 030-15 a line
# that does not parse whole by the grammar of trace format 3 (027-02): the faults
# of an independent review (030-15) in the good trace and in the hand-made trace
# test/small.trace (a bare OP or GET line, a SCAN in the direction BANANA, an OP
# line in TX 0, a key entry that is not its klong's), and lines out of their
# order. A GET with a wrong answer passes this checker: the reads are the
# contract checker's (check.sh runs both). Since bergdb 030-19, the three points of
# an independent review (Codex, review 3), which the trace's wholeness
# (`completeFault`) now fails in both checkers: a delete bitmap wider than Java's 62
# bits (2^64 added to a bitmap of a KN line; the review's B 2^64 with an empty delete
# entry), a PROBE line that fails, and reads left out (every GET and SCAN line, the
# SCAN line of one transaction).
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
# The first key node made in TX 4 is on level 0 (TX 2 until bergdb 028-15, when TX 1
# became the creating start's KV of the startup distance; TX 3 until bergdb 028-13, when
# TX 2 became the exporter's setting of the startup distance after the start).
fault level-0 $G 'tx == 4 && !d && /^NEW [0-9]+ [1-9][0-9]* I$/ { $3 = 0; d = 1 } /^TX / { tx = $2 } { print }'
# The TREE line's h is 0: every level is a segment leaf's, and the inner nodes fail KIND.
fault kind-h0 $G '/^TREE / && !d { $4 = 0; d = 1 } { print }'
# The first skip pointer of a top node is left out.
fault no-skip $G '!d && /^ADD [0-9]+ [0-9]+ S / { d = 1; next } { print }'
# The root pointer of the top node made in TX 4 names another node (TX 2 until bergdb
# 028-15, TX 3 until bergdb 028-13).
fault root-pointer $G 'tx == 4 && !d && /^ADD [0-9]+ 4 R / { $5 = $5 - 2; d = 1 } /^TX / { tx = $2 } { print }'
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
# bergdb 030-15: lines that do not parse whole by the grammar, in TX 5.
fault bare-op $G '{ print } /^TX 5$/ { t = 1 } t && !d && /^OP / { print "OP"; d = 1 }'
fault bare-get $G '{ print } /^TX 5$/ { t = 1 } t && !d && /^GET / { print "GET"; d = 1 }'
fault banana $G '/^TX 5$/ { t = 1 } t && !d && /^SCAN / { $3 = "BANANA"; d = 1 } { print }'
fault tx0-op $G '{ print } /^TX 0$/ { print "OP P 1 8 99" }'
fault order $G '/^TX 5$/ { t = 1 } t && !d && /^GD/ { g = $0; d = 1; next } { print } g != "" && /^DIRTY/ { print g; g = "" }'
# bergdb 030-19: the first B klong of a KN line with 2^64 added: the same bits 0 to 63,
# read as the bitmap itself until 030-19.
L=$(awk '/^KN .* B /{print NR; exit}' $G)
B=$(awk -v l=$L 'NR==l{for (k=1; k<NF; k++) if ($k=="B") {print $(k+1); exit}}' $G)
W=$(echo "18446744073709551616 + $B" | bc)
export L W
fault bitmap64 $G 'NR == ENVIRON["L"] { for (k = 1; k < NF; k++) if ($k == "B") { $(k + 1) = ENVIRON["W"]; break } }
    { print }'
fault probe-fail $G '/^END 5$/ { print "PROBE 5 fail wrong values after restart" } { print }'
fault no-reads $G '!/^GET / && !/^SCAN / { print }'
fault no-scan $G '/^TX / { tx = $2 } !(tx == 5 && /^SCAN /) { print }'
# The review's own faults, in a hand-made trace of two transactions that passes.
S=test/small.trace
expect small PASS $S
fault s-bare-op $S '{ print } /^OP P/ { print "OP" }'
fault s-bare-get $S '{ print } /^GET / { print "GET" }'
fault s-banana $S '/^SCAN 1 F / { $3 = "BANANA" } { print }'
fault s-tx0-op $S '{ print } /^TX 0$/ { print "OP P 1 8 99" }'
fault s-wrong-entry $S '/^ADD 3 1 K 56 4$/ { $5 = 64 } { print }'
# bergdb 030-19: the third review's (Codex) faults.
fault s-bitmap $S '{ if ($0 == "KN 3 1 2 T 1 K 56 4") print "KN 3 1 3 T 1 K 56 4 B 18446744073709551616"; else print }
    /^ADD 3 1 K 56 4$/ { print "ADD 3 1 D 0" }'
fault s-probe-fail $S '/^END 1$/ { print "PROBE 1 fail wrong values after restart" } { print }'
fault s-no-reads $S '!/^GET / && !/^SCAN / { print }'

rm -rf $DIR
if [ $FAILED -eq 0 ]; then
    echo "BRIDGE FAULTS OK"
else
    echo "BRIDGE FAULTS FAILED: $FAILED"
    exit 1
fi
