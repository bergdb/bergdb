#!/bin/sh
# 025-02's gate (2026-11-14): checks a cleanup clone's lean/ before it lands.
# Usage: sh gate.sh CLONE OUTDIR [TOP]
#   CLONE   the clone (its lean/ is built and checked as it is in the working tree)
#   OUTDIR  where the logs go; OUTDIR/summary.txt ends with "GATE PASS" or "GATE FAIL: ..."
#   TOP     the top theorem's full name (default SIS.Tree.invGetScanOK_merges_flat; after
#           step 3, SIS.Tree.invGetScanOK_merges)
# Checks: lake build (default targets) and treetest; no sorry/admit/axiom/native_decide/
# implemented_by/extern in lean/; Guard.lean: no axiom of ours and no sorryAx, the audit list
# on the standard axioms, the trusted closure's fingerprint equal to the base's
# (base/guard-base.txt), TOP's statement equal to the base's flat top's (premises' names
# included); test-traces/run.sh (the trace checker's tests); every SIS/Tree module imported;
# the line counts per area. One heavy slot for the whole gate.
CLONE=$1; OUT=$2; TOP=${3:-SIS.Tree.invGetScanOK_merges_flat}
C=/Users/f/fl/bench/2026-11-14/cleanup; T=$C/tools
mkdir -p $OUT; : > $OUT/summary.txt
fail() { echo "GATE FAIL: $1" >> $OUT/summary.txt; cat $OUT/summary.txt; [ -n "$S" ] && sh /Users/f/fl/bench/2026-11-11/slot.sh release $S; exit 1; }
S=$(sh /Users/f/fl/bench/2026-11-11/slot.sh take gate-$(basename $(dirname $CLONE)) "025-02 gate: lake build + guard")
cd $CLONE/lean || fail "no $CLONE/lean"
echo "head: $(git -C $CLONE log --oneline -1 | cut -c1-100); uncommitted lean files: $(git -C $CLONE status --porcelain -- lean | wc -l | tr -d ' ')" >> $OUT/summary.txt
( time lake build ) > $OUT/lake.txt 2>&1; e=$?
echo "lake build: exit $e, $(grep -o 'Build completed successfully ([0-9]* jobs)' $OUT/lake.txt), $(grep real $OUT/lake.txt | tr -s ' \t' ' ')" >> $OUT/summary.txt
[ $e = 0 ] || fail "lake build"
lake build treetest > $OUT/lake-treetest.txt 2>&1 || fail "lake build treetest"
grep -rn -E '\bsorry\b|\badmit\b|^axiom |^private axiom |native_decide|implemented_by|@\[extern' --include='*.lean' SIS Check BergDB *.lean > $OUT/forbidden.txt
echo "forbidden: $(wc -l < $OUT/forbidden.txt | tr -d ' ') lines" >> $OUT/summary.txt
[ -s $OUT/forbidden.txt ] && fail "forbidden words (forbidden.txt)"
sed "s/^SIS.Tree.invGetScanOK_merges_flat\$/$TOP/" $T/audit.txt > $OUT/audit.txt
GUARD_AUDIT=$OUT/audit.txt GUARD_OUT=$OUT/guard.txt lake env lean $T/Guard.lean > $OUT/guard-run.txt 2>&1 || fail "Guard.lean did not run (guard-run.txt)"
grep -q '^AXIOMS ours: 0$' $OUT/guard.txt || fail "an axiom or sorryAx of ours (guard.txt)"
grep -E '^AXIOMS (BAD|MISSING)' $OUT/guard.txt > $OUT/axioms-bad.txt
echo "audit: $(grep -c '^AXIOMS ok' $OUT/guard.txt) theorems on the standard axioms, $(wc -l < $OUT/axioms-bad.txt | tr -d ' ') bad or missing" >> $OUT/summary.txt
[ -s $OUT/axioms-bad.txt ] && fail "axioms (axioms-bad.txt)"
grep '^FP ' $C/base/guard-base.txt > $OUT/fp-base.txt; grep '^FP ' $OUT/guard.txt > $OUT/fp-new.txt
diff $OUT/fp-base.txt $OUT/fp-new.txt > $OUT/fp-diff.txt
echo "trusted closure: $(wc -l < $OUT/fp-new.txt | tr -d ' ') constants, $(grep -c '^[<>]' $OUT/fp-diff.txt) lines differ from the base" >> $OUT/summary.txt
[ -s $OUT/fp-diff.txt ] && fail "the trusted closure changed (fp-diff.txt)"
b=$(grep '^SIG SIS.Tree.invGetScanOK_merges_flat :' $C/base/guard-base.txt | sed 's/^SIG [^ ]* ://')
n=$(grep "^SIG $TOP :" $OUT/guard.txt | sed 's/^SIG [^ ]* ://')
[ -n "$n" ] && [ "$b" = "$n" ] || fail "the top theorem's statement differs from the base's (guard.txt SIG lines)"
b=$(grep '^NAMES SIS.Tree.invGetScanOK_merges_flat :' $C/base/guard-base.txt | sed 's/^NAMES [^ ]* ://')
n=$(grep "^NAMES $TOP :" $OUT/guard.txt | sed 's/^NAMES [^ ]* ://')
[ -n "$n" ] && [ "$b" = "$n" ] || fail "the top theorem's premises' names differ from the base's (guard.txt NAMES lines)"
echo "top theorem: $TOP, statement and premises' names as the base's" >> $OUT/summary.txt
sh test-traces/run.sh > $OUT/test-traces.txt 2>&1
grep -q '^FAIL' $OUT/test-traces.txt && fail "test-traces/run.sh (test-traces.txt)"
echo "test-traces: $(grep -c '^ok' $OUT/test-traces.txt) ok" >> $OUT/summary.txt
for f in SIS/Tree/*.lean; do m=$(echo ${f%.lean} | tr / .); grep -rqx "import $m" SIS SIS.lean Check *.lean BergDB 2>/dev/null || echo "NOT IMPORTED: $m"; done > $OUT/graph.txt
echo "not imported: $(wc -l < $OUT/graph.txt | tr -d ' ')" >> $OUT/summary.txt
[ -s $OUT/graph.txt ] && fail "modules outside the import graph (graph.txt)"
sh $T/lines.sh $CLONE/lean > $OUT/lines.txt; cat $OUT/lines.txt >> $OUT/summary.txt
sh /Users/f/fl/bench/2026-11-11/slot.sh release $S; S=
echo "GATE PASS" >> $OUT/summary.txt
cat $OUT/summary.txt
