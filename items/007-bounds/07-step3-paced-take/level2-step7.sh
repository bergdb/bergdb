#!/bin/sh
# level2.sh's step 7 (conformance with the Lean model), as in level2.sh full, run on
# its own because level2.sh stopped at step 6 (BryanRepro), which fails on main
# since eaec93e (005-46) too. Run from java/ in the clone.
JAVA=${JAVA:-java}
CP=build/bergdb.jar:build/stress
LOG=build/level2
CONF_SEEDS=10
fail() { echo "STEP 7 FAILED: $1 (log: $2)"; exit 1; }
echo "7. Conformance with the Lean model"
n=0
for cfg in "-Dops=4 -Ddel=25 -Dlong=1" \
    "-Dops=40 -Dexact=1 -Dn=50 -Dkeys=1000 -Ddel=25 -Dlong=1" \
    "-Dmaxnode=62 -Dkeys=1000 -Dn=2000 -Dops=40 -Ddel=20 -Dseeds=3"; do
    n=$((n + 1))
    F=$LOG/a2a3-$n.txt
    $JAVA -ea $cfg -cp $CP bergdb.dag.A2A3Check2 > $F 2>&1
    grep -q 'violating A3 0, A5 0;' $F && grep -q 'NET (A2): .* not current 0 ' $F \
        && grep -q 'in step 3 only 0, in model only 0 ' $F \
        && grep -q 'adopted index nodes not below the old parent 0 (transactions 0)' $F \
        && grep -q 'nodes without exactly one 0 (transactions 0)' $F \
        && grep -q 'A-COPY .* failing 0 (transactions 0)' $F || fail "A2A3Check2" $F
    echo "   a2a3-$n: $(grep -o '^  transactions [0-9]*' $F | sed 's/^ *//'): OK"
done
(cd ../lean && lake build) > $LOG/lake.txt 2>&1 || fail "the Lean checker, lake build" $LOG/lake.txt
echo "   lake build: $(tail -1 $LOG/lake.txt)"
sh stress/conformance.sh small $CONF_SEEDS > $LOG/conformance.txt 2>&1
grep -q '^CONFORMANCE OK' $LOG/conformance.txt || fail "conformance.sh small" $LOG/conformance.txt
echo "   conformance: $(grep '^   traces:' $LOG/conformance.txt | sed 's/^ *//')"
echo "STEP 7 OK"
