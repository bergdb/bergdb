#!/bin/sh
# The trace checker's C-STEP, its own test (bergdb 030-27): faults made by hand in
# the STEP lines and OP lines of a good trace must each make `tracecheck` fail, by
# the name of the check that finds them; the good trace must pass, with an
# iteration of more than one step, and (since bergdb 031-06, one record an action) a
# step in the record of a commit with an action. The trace: TraceExport with reclaim,
# tree=1 and steps=1 (027-02, section 4), seed 1, 300 transactions. Since bergdb 031-06
# a step's copies are OP C lines (the copy mark), in the record of a commit or of a part
# beside the action's operations, and every record has its action as submitted (ACT
# lines); the comment line of a TX gives copies=N. The faults:
#   noputs   the OP C lines of the first step with two copies or more left out: an
#            old KV the step met is not written by the record (STEP-puts)
#   nextkey  the first step that does not end its iteration (eod 0) leaves lastKey
#            as it was: the next step's lastKey before is not it (STEP-chain)
#   eod      that step with eod 1: its lastKey after is not the range's last key
#            (STEP-range)
#   first    the first step with a lastKey before (STEP-chain)
#   cut      the first step with c = t0 + 2 (STEP-c)
#   outside  the first step's lastKey after the key [8], before every key of the
#            range (STEP-range)
#   noeod    the step at the first CUT line's first available time with eod 0: the
#            iteration of the cut has no last step with eod there (CUT-steps)
#   nostep   the first STEP line left out (STEP-line)
#   extra    a STEP line in TX 3, a user transaction (STEP-line)
#   badline  a STEP line whose eod is 2 (STEP-form)
# Since bergdb 030-34, in the second step with three copies or more:
#   value    its first copy of a key of one segment (a user key; the row's key has four
#            segments) with the value 12345: a copy with another value than the scan
#            read (STEP-values)
#   del      an OP D line of a user key added: the key of the first user key's copy of the
#            next such step, a key that reclaim rewrites later; since bergdb 031-06 an
#            operation neither the action's nor reclaim's (STEP-action; STEP-ops until then)
#   put      an OP P line of that key added, with the value 12345 (STEP-action)
# Since bergdb 030-39 (F1), the row at the model's key (`reclaimRowKey`, Check/Steps.lean):
#   row      every put of the row's key, `-current.txt` under `/#i/dreclaim/`, made a put of
#            the key [8]: a step that puts no row and puts another key; until 2026-11-23,
#            when C-STEP took the row's key from the trace's first step, the trace passed
#            (STEP-ops)
# Since bergdb 031-06 (one record an action), the copy mark and the action as submitted:
#   unmark   the first copy of the first step with a copy written as OP P: a put without
#            the mark that is neither the action's nor reclaim's (STEP-action)
#   mark     in the first step's record of a commit whose action puts a key, the action's
#            put (its OP P line) written as OP C: the action's put is not in the record as
#            given, and a copy at a key the action writes (STEP-action)
#   actval   that put with the value 12345: not the action as submitted (STEP-action)
#   actdrop  that put left out of the record (STEP-action)
#   copyuser an OP C line in TX 3, a commit's record without a step (STEP-action)
# Since bergdb 030-31 also a second good trace, with restarts and crashes of run A, RESTART
# and RESUME lines, which must pass with a crash and an iteration with a step before a
# restart and the next after it, and its faults. Since bergdb 031-06 it is conformance.sh
# crash's c-vals (restart=5, crash=3, 200 keys of up to 200 bytes): with one record an
# action, the small configuration of before (restart=10, crash=2, 30 keys of 20 bytes) ends
# each iteration in one step, and no iteration spans a restart. The faults:
#   rmiss    the first RESUME line left out (STEP-resume)
#   rc       the first RESUME line with an iteration, its c plus 1 (STEP-resume)
#   rlast    the first RESUME line with a lastKey, its lastKey - (STEP-resume)
#   re       the first RESUME line with an iteration and no lastKey, its E the key [8]
#            (STEP-resume)
#
# Usage: lean/test-traces/step-faults.sh
# Needs: the checker (cd lean && lake build tracecheck) and java/build (java/build.sh).
# Prints one line per fault and STEP FAULTS OK or STEP FAULTS FAILED. About 1 minute.
#
# Kind: functional (bergdb 028-23): the result does not depend on the machine's speed or
# load.
cd "$(dirname "$0")/.."
echo "Kind: functional"
CHECK=$(pwd)/.lake/build/bin/tracecheck
[ -x "$CHECK" ] || { echo "STEP FAULTS FAILED: no checker; run lake build in lean/"; exit 1; }
JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi
CP=../java/build/bergdb.jar:../java/build/stress
DIR=${TMPDIR:-/tmp}/step-faults.$$
mkdir -p $DIR
PROPS="-Dn=300 -Dkeys=200 -Dmaxnode=14 -Dsd=1000 -Dops=8 -Ddel=25 -Dretain=2 -Dtree=1 -Dsteps=1"
$JAVA -ea $PROPS -cp $CP bergdb.core.TraceExport 1 $DIR/good.trace > $DIR/good.txt 2>&1 \
    || { echo "STEP FAULTS FAILED: TraceExport: $(tail -1 $DIR/good.txt)"; exit 1; }
G=$DIR/good.trace
FAILED=0

# expect NAME PASS|CHECK FILE: runs the checker on FILE; it must pass, or fail with
# CHECK among C-STEP's failures.
expect() {
    "$CHECK" $3 > $DIR/$1.out 2>&1
    status=$?
    line=$(grep '^C-STEP' $DIR/$1.out)
    if [ $2 = PASS ]; then
        if [ $status = 0 ] && echo "$line" | grep -q ': 0 of '; then
            echo "   $1: passes: $(echo "$line" | sed 's/.*fail; //')"
            return
        fi
    elif [ $status != 0 ] && echo "$line" | grep -q "[(, ]$2 [0-9]"; then
        echo "   $1: fails, $2: $(grep -A1 '^C-STEP' $DIR/$1.out | tail -1 | sed 's/^ *//' | cut -c1-110)"
        return
    fi
    echo "   $1: WRONG, expected $2: $(echo "$line" | cut -c1-110) $(tail -1 $DIR/$1.out)"
    FAILED=$((FAILED + 1))
}

# fault NAME CHECK AWK-PROGRAM [AWK-OPTIONS]: the good trace changed by the program must
# fail with CHECK.
fault() {
    awk $4 "$3" $G > $DIR/$1.trace
    cmp -s $G $DIR/$1.trace && { echo "   $1: WRONG, the fault changed nothing"; FAILED=$((FAILED + 1)); return; }
    expect $1 $2 $DIR/$1.trace
}

expect good PASS $G
# An iteration of more than one step: fewer iterations than STEP lines.
grep '^C-STEP' $DIR/good.out | sed -E 's/.*; ([0-9]+) STEP lines, ([0-9]+) iterations.*/\1 \2/' \
    | awk '{exit !($1 > $2)}' \
    || { echo "   good: WRONG, no iteration of more than one step"; FAILED=$((FAILED + 1)); }

# A step in the record of a commit with an action (bergdb 031-06).
awk '/^TX /{st = 0} /kind=step/ {st = 1} st && /^ACT /{f = 1} END {exit !f}' $G \
    || { echo "   good: WRONG, no step in the record of a commit with an action"; FAILED=$((FAILED + 1)); }

fault noputs STEP-puts 'BEGIN {s = -1} /^TX /{tx = $2}
    /kind=step/ && !d {split($7, a, "="); if (a[2] >= 2) {s = tx; d = 1}}
    !(tx == s && /^OP C /) {print}'
fault nextkey STEP-chain '/^STEP / && $4 == "-" && $NF == "0" && !d {print "STEP " $2 " " $3 " - - 0"; d = 1; next} {print}'
fault eod STEP-range '/^STEP / && $4 == "-" && $NF == "0" && !d {$NF = "1"; d = 1} {print}'
fault first STEP-chain '/^STEP / && $4 == "-" && !d {
    lp = ""; for (i = 5; i < NF; i++) lp = lp " " $i
    print "STEP " $2 " " $3 lp lp " " $NF; d = 1; next} {print}'
fault cut STEP-c '/^STEP / && !d {$3 = $2 + 2; d = 1} {print}'
fault outside STEP-range '/^STEP / && $4 == "-" && !d {print "STEP " $2 " " $3 " - 1 8 " $NF; d = 1; next} {print}'
F=$(awk '/^CUT /{print $3; exit}' $G)
fault noeod CUT-steps '/^TX /{tx = $2} /^STEP / && tx == f {$NF = "0"} {print}' "-v f=$F"
fault nostep STEP-line '/^STEP / && !d {d = 1; next} {print}'
S1=$(grep -m1 '^STEP ' $G)
fault extra STEP-line '{print} /^TX 3$/{gsub(/_/, " ", s); print s}' "-v s=$(echo $S1 | tr ' ' '_')"
fault badline STEP-form '/^STEP / && !d {$NF = "2"; d = 1} {print}'
# The values and the step's other operations (bergdb 030-34).
SECOND='/^TX /{tx = $2} /kind=step/ {split($7, a, "="); if (a[2] >= 3) {n++; if (n == 2) s = tx}}'
K=$(awk '/kind=step/ {split($7, a, "="); if (a[2] >= 3) n++} n == 3 && /^OP C 1 / {print $4; exit}' $G)
fault value STEP-values "$SECOND"' tx == s && /^OP C 1 / && !d {$NF = "12345"; d = 1} {print}'
fault del STEP-action "$SECOND"' {print} tx == s && /^BASE / {print "OP D 1 " k}' "-v k=$K"
fault put STEP-action "$SECOND"' {print} tx == s && /^BASE / {print "OP P 1 " k " 12345"}' "-v k=$K"
# The row at the model's key (bergdb 030-39, F1).
ROW="OP P 4 20647455483566584 1827222139585973240 1827860140839935416 873028302074282016 "
fault row STEP-ops 'index($0, "'"$ROW"'") == 1 {print "OP P 1 8 " $NF; next} {print}'
# The copy mark and the action as submitted (bergdb 031-06).
fault unmark STEP-action '/^TX /{tx = $2} /kind=step/ {st = 1} /^TX /{st = 0}
    st && /^OP C / && !d {sub(/^OP C/, "OP P"); d = 1} {print}'
T2=$(awk '/^TX /{tx = $2; st = 0} /kind=step/ {st = 1} st && /^ACT P / {print tx; exit}' $G)
L2=$(awk '/^TX /{tx = $2; st = 0} /kind=step/ {st = 1} st && /^ACT P / {sub(/^ACT/, "OP"); print; exit}' $G)
fault mark STEP-action 'BEGIN {gsub(/_/, " ", l)} /^TX /{tx = $2} tx == t && $0 == l && !d {sub(/^OP P/, "OP C"); d = 1} {print}' "-v t=$T2 -v l=$(echo $L2 | tr ' ' '_')"
fault actval STEP-action 'BEGIN {gsub(/_/, " ", l)} /^TX /{tx = $2} tx == t && $0 == l && !d {$NF = "12345"; d = 1} {print}' "-v t=$T2 -v l=$(echo $L2 | tr ' ' '_')"
fault actdrop STEP-action 'BEGIN {gsub(/_/, " ", l)} /^TX /{tx = $2} tx == t && $0 == l && !d {d = 1; next} {print}' "-v t=$T2 -v l=$(echo $L2 | tr ' ' '_')"
fault copyuser STEP-action '{print} /^TX 3$/{getline; print; print "OP C 1 8 1"}'

# Restarts and crashes (bergdb 030-31).
PROPS="-Dn=400 -Dkeys=200 -Dmaxnode=8 -Dsd=500 -Dops=6 -Ddel=20 -Dvalsize=200 -Dretain=1 -Drestart=5 -Dcrash=3 -Dtree=1 -Dsteps=1"
$JAVA -ea $PROPS -cp $CP bergdb.core.TraceExport 1 $DIR/good2.trace > $DIR/good2.txt 2>&1 \
    || { echo "STEP FAULTS FAILED: TraceExport: $(tail -1 $DIR/good2.txt)"; exit 1; }
G=$DIR/good2.trace
expect good2 PASS $G
grep '^C-STEP' $DIR/good2.out | sed -E 's/.*restarts \(([0-9]+) crashes\), [0-9]+ with an iteration in progress, ([0-9]+) iterations with a step before.*/\1 \2/' \
    | awk '{exit !($1 > 0 && $2 > 0)}' \
    || { echo "   good2: WRONG, no crash, or no iteration with a step before a restart and after it"; FAILED=$((FAILED + 1)); }
fault rmiss STEP-resume '/^RESUME / && !d {d = 1; next} {print}'
fault rc STEP-resume '/^RESUME [0-9]/ && !d {$3 = $3 + 1; d = 1} {print}'
fault rlast STEP-resume '/^RESUME [0-9]/ && $4 != "-" && !d {
    e = ""; for (i = 5 + $4; i <= NF; i++) e = e " " $i
    print "RESUME " $2 " " $3 " -" e; d = 1; next} {print}'
fault re STEP-resume '/^RESUME [0-9]/ && $4 == "-" && !d {print "RESUME " $2 " " $3 " - 1 8"; d = 1; next} {print}'

rm -rf $DIR
if [ $FAILED -eq 0 ]; then
    echo "STEP FAULTS OK"
else
    echo "STEP FAULTS FAILED: $FAILED"
    exit 1
fi
