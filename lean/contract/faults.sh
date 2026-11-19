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
# show as an ERROR line and as a KN line from its klong diff. Since bergdb 030-15,
# a line that does not parse whole by the grammar of trace format 3 (027-02): the
# faults of an independent review (030-15) in the good trace and in the hand-made
# trace test/small.trace (a bare OP or GET line, a SCAN in the direction BANANA,
# an OP line in TX 0, a GET with a wrong answer), and a number with an underscore,
# two spaces between tokens, lines out of their order, a TX without its BASE line.
# Since bergdb 030-17, K-LEVEL: the TREE line's h set to 0 (KIND alone fails).
# Since bergdb 030-19, the three points of an independent review (Codex, review 3):
# a delete bitmap wider than Java's 62 bits (2^64 added to a bitmap of a KN line,
# which was read as the bitmap itself, and the review's B 2^64 with an empty delete
# entry, read as an empty bitmap; and 2^62 added, which C1 caught), a PROBE line that
# fails (a PROBE line that is ok passes), and reads left out: every GET and SCAN line,
# the GET lines or the SCAN line of one transaction, one GET line of one.
#
# Usage: lean/contract/faults.sh
# Needs: the checker (cd lean/contractcheck && lake build contractcheck) and java/build
# (java/build.sh). Prints one line per fault and FAULTS OK or FAULTS FAILED.
cd "$(dirname "$0")"
CHECK=$(pwd)/../contractcheck/.lake/build/bin/contractcheck
[ -x "$CHECK" ] || { echo "FAULTS FAILED: no checker; run lake build in lean/contractcheck/"; exit 1; }
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
awk '/^TX 30$/{t=1} t && /^LIVE 0 [0-9]* [0-9]/ && !d{NF=NF-1; d=1} {print}' $G > $DIR/livetop.trace
expect livetop FAIL $DIR/livetop.trace
grep -q 'L1 [1-9]' $DIR/livetop.out || { echo "   livetop: WRONG, not L1"; FAILED=$((FAILED + 1)); }

# bergdb 030-15: lines that do not parse whole by the grammar, in the good trace's TX 30.
awk '/^TX 30$/{t=1} {print} t && /^OP / && !d{print "OP"; d=1}' $G > $DIR/bareop.trace
expect bareop FAIL $DIR/bareop.trace
awk '/^TX 30$/{t=1} {print} t && /^GET / && !d{print "GET"; d=1}' $G > $DIR/bareget.trace
expect bareget FAIL $DIR/bareget.trace
awk '/^TX 30$/{t=1} t && /^SCAN / && !d{$3="BANANA"; d=1} {print}' $G > $DIR/banana.trace
expect banana FAIL $DIR/banana.trace
awk '{print} /^TX 0$/{print "OP P 1 8 99"}' $G > $DIR/tx0op.trace
expect tx0op FAIL $DIR/tx0op.trace
awk '/^TX 30$/{t=1} t && /^GET / && !d{$NF=($NF=="-" ? 7 : "-"); d=1} {print}' $G > $DIR/wrongget.trace
expect wrongget FAIL $DIR/wrongget.trace
awk '/^TX 30$/{t=1} t && /^BASE [0-9][0-9]/ && !d{$2=substr($2,1,1) "_" substr($2,2); d=1} {print}' $G > $DIR/underscore.trace
expect underscore FAIL $DIR/underscore.trace
awk '/^TX 30$/{t=1} t && /^OP P / && !d{sub(/^OP P /, "OP  P "); d=1} {print}' $G > $DIR/twospaces.trace
expect twospaces FAIL $DIR/twospaces.trace
awk '/^TX 30$/{t=1} t && /^GD/ && !d{g=$0; d=1; next} {print} g!="" && /^DIRTY/{print g; g=""}' $G > $DIR/order.trace
expect order FAIL $DIR/order.trace
awk '/^TX 30$/{t=1} t && /^BASE / && !d{d=1; next} {print}' $G > $DIR/nobase.trace
expect nobase FAIL $DIR/nobase.trace
# bergdb 030-17: K-LEVEL, the kind of each key node from its level with the TREE
# line's h: h set to 0 makes every key node a segment leaf by its level, so every
# inner node fails KIND, and nothing else.
awk '/^TREE / && !d{$4=0; d=1} {print}' $G > $DIR/kindh0.trace
expect kindh0 FAIL $DIR/kindh0.trace
grep -q 'KIND [1-9]' $DIR/kindh0.out || { echo "   kindh0: WRONG, not KIND"; FAILED=$((FAILED + 1)); }
grep -q 'C1 0, C2 0, C3 0, R1 0, L1 0, C4 0, C5 0' $DIR/kindh0.out \
    || { echo "   kindh0: WRONG, a clause other than KIND"; FAILED=$((FAILED + 1)); }
# bergdb 030-19: a delete bitmap is a number below 2^62 (Java's has 62 bits, 027-02,
# section 4). The first B klong of a KN line from TX 30 on gets 2^64 added: the same
# bits 0 to 63, so the checker read it as the bitmap itself until 030-19 and passed
# the trace; with 2^62 added, bit 62 deletes a klong after the bitmap (C1 caught it).
L=$(awk '/^TX /{tx=$2} tx>=30 && /^KN .* B /{print NR; exit}' $G)
B=$(awk -v l=$L 'NR==l{for (k=1; k<NF; k++) if ($k=="B") {print $(k+1); exit}}' $G)
W64=$(echo "18446744073709551616 + $B" | bc)
W62=$(echo "4611686018427387904 + $B" | bc)
WIDE='NR==l{for (k=1; k<NF; k++) if ($k=="B") {$(k+1)=w; break}} {print}'
awk -v l=$L -v w=$W64 "$WIDE" $G > $DIR/bitmap64.trace
expect bitmap64 FAIL $DIR/bitmap64.trace
awk -v l=$L -v w=$W62 "$WIDE" $G > $DIR/bitmap62.trace
expect bitmap62 FAIL $DIR/bitmap62.trace
# A PROBE line that fails (run B's or run E's check, 027-02, section 2) fails the trace;
# one that is ok does not.
awk '/^END 30$/{print "PROBE 30 fail wrong values after restart"} {print}' $G > $DIR/probefail.trace
expect probefail FAIL $DIR/probefail.trace
awk '/^END 30$/{print "PROBE 30 ok"} {print}' $G > $DIR/probeok.trace
expect probeok PASS $DIR/probeok.trace
# Reads left out: every TX i > 0 has n GET lines, n > 0 the same in each, and one SCAN line.
grep -v '^GET \|^SCAN ' $G > $DIR/noreads.trace
expect noreads FAIL $DIR/noreads.trace
awk '/^TX /{tx=$2} !(tx==30 && /^GET /){print}' $G > $DIR/nogets.trace
expect nogets FAIL $DIR/nogets.trace
awk '/^TX /{tx=$2} !(tx==30 && /^SCAN /){print}' $G > $DIR/noscan.trace
expect noscan FAIL $DIR/noscan.trace
awk '/^TX /{tx=$2} tx==30 && /^GET / && !d{d=1; next} {print}' $G > $DIR/oneget.trace
expect oneget FAIL $DIR/oneget.trace
# The review's own faults, in a hand-made trace of two transactions that passes.
S=test/small.trace
expect small PASS $S
awk '{print} /^OP P/{print "OP"}' $S > $DIR/s-bareop.trace
expect s-bareop FAIL $DIR/s-bareop.trace
awk '{print} /^GET /{print "GET"}' $S > $DIR/s-bareget.trace
expect s-bareget FAIL $DIR/s-bareget.trace
sed 's/^SCAN 1 F /SCAN 1 BANANA /' $S > $DIR/s-banana.trace
expect s-banana FAIL $DIR/s-banana.trace
awk '{print} /^TX 0$/{print "OP P 1 8 99"}' $S > $DIR/s-tx0op.trace
expect s-tx0op FAIL $DIR/s-tx0op.trace
sed 's/^GET 1 2 56 64 5$/GET 1 2 56 64 999/' $S > $DIR/s-wrongget.trace
expect s-wrongget FAIL $DIR/s-wrongget.trace
# bergdb 030-19: the third review's (Codex) faults: B 2^64 with an empty delete entry,
# a PROBE line that fails, the GET and SCAN lines left out.
awk '{print} /^ADD 3 1 K 56 4$/{print "ADD 3 1 D 0"}' $S \
    | sed 's/^KN 3 1 2 T 1 K 56 4$/KN 3 1 3 T 1 K 56 4 B 18446744073709551616/' \
    > $DIR/s-bitmap.trace
expect s-bitmap FAIL $DIR/s-bitmap.trace
awk '/^END 1$/{print "PROBE 1 fail wrong values after restart"} {print}' $S > $DIR/s-probefail.trace
expect s-probefail FAIL $DIR/s-probefail.trace
grep -v '^GET \|^SCAN ' $S > $DIR/s-noreads.trace
expect s-noreads FAIL $DIR/s-noreads.trace

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
