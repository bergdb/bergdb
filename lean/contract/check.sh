#!/bin/sh
# The writer's contract and the bridge's clauses on Java's traces (bergdb 030-04,
# section 7.4 (d); 030-07; since 030-15 one script for both): runs `contractcheck`
# (ContractCheck.lean) and `bridgecheck` (BridgeCheck.lean) on the traces of format 3
# that java/stress/treeconf.sh has written to java/build/traces/tree-SET/. A trace
# passes only if both checkers pass it: each checks a part of what a trace says (an
# independent review, 030-15: a GET with a wrong answer fails only the contract
# checker, an ADD entry that is not its klong's only the bridge checker). Each
# checker's verdict on a trace is a function with a soundness theorem:
# `contractVerdict_sound` (Contract/Verdict.lean: MeetsTop) and
# `fullHistoryOk_meets` (Contract/Proof/BridgeHistory.lean: MeetsFull).
#
# Usage: lean/contract/check.sh [SET ...]     (default: small drain)
# Needs: the traces (java/build.sh; cd lean && lake build treecheck;
# java/stress/treeconf.sh small; java/stress/treeconf.sh drain; and reclaim for the
# bridge checker's own test) and the checkers (cd lean/contractcheck && lake build;
# no Mathlib, bergdb 028-24).
# Prints the summaries of each set, then CONTRACT OK (both checkers passed every
# trace) or CONTRACT FAILED; the lines of every trace go to
# java/build/traces/tree-SET/contract.txt and bridge.txt. First the checkers' own
# tests: faults.sh (bergdb 030-09, 030-15, 030-19), faults-top.sh (030-08) and
# bridge-faults.sh (030-07, 030-15, 030-19; if the small and the reclaim set are there):
# faults made in a trace must fail it. About 2 minutes for small, drain and reclaim.
# The bridge's clauses in the model's words too: bridge-check.sh, or
# ../contractcheck/.lake/build/bin/bridgecheck --model TRACE...
# PAR=N checks a set in N parts at once with each checker (default 4; par.sh,
# bergdb 030-13): the medium set 1359 s (contract) and 4097 s (bridge) in one part.
cd "$(dirname "$0")"
CHECK=../contractcheck/.lake/build/bin/contractcheck
BCHECK=../contractcheck/.lake/build/bin/bridgecheck
[ -x "$CHECK" ] && [ -x "$BCHECK" ] || { echo "CONTRACT FAILED: no checkers; run lake build in lean/contractcheck/"; exit 1; }
./faults.sh > /dev/null 2>&1 || { echo "CONTRACT FAILED: the checker's own test, lean/contract/faults.sh"; exit 1; }
./faults-top.sh > /dev/null 2>&1 || { echo "CONTRACT FAILED: the checker's own test of the top, lean/contract/faults-top.sh"; exit 1; }
if ls ../../java/build/traces/tree-small/mixed-1.trace ../../java/build/traces/tree-reclaim/r-del-1.trace > /dev/null 2>&1; then
    ./bridge-faults.sh > /dev/null 2>&1 || { echo "CONTRACT FAILED: the bridge checker's own test, lean/contract/bridge-faults.sh"; exit 1; }
else
    echo "(bridge-faults.sh not run: it needs the small and the reclaim set)"
fi
SETS=${*:-small drain}
FAILED=0
for set in $SETS; do
    dir=../../java/build/traces/tree-$set
    ls $dir/*.trace > /dev/null 2>&1 || { echo "CONTRACT FAILED: no traces in $dir"; exit 1; }
    sh par.sh "$CHECK" $dir/contract.txt $dir/*.trace &
    pc=$!
    sh par.sh "$BCHECK" $dir/bridge.txt $dir/*.trace &
    pb=$!
    wait $pc; sc=$?
    wait $pb; sb=$?
    echo "tree-$set: contract: $(grep '^total: ' $dir/contract.txt | sed 's/^total: //')"
    echo "tree-$set: bridge: $(grep '^total: ' $dir/bridge.txt | sed 's/^total: //')"
    # The traces that either checker failed.
    BAD=$(grep -h 'first: \|: not whole: \|: unreadable: \|: the verdict' $dir/contract.txt $dir/bridge.txt \
        | sed 's/: .*//' | sort -u)
    if [ -n "$BAD" ]; then
        echo "tree-$set: $(echo "$BAD" | wc -l | tr -d ' ') traces failed, the first:"
        echo "$BAD" | head -5 | sed 's/^/   /'
    fi
    if [ $sc -ne 0 ] || [ $sb -ne 0 ]; then FAILED=$((FAILED + 1)); fi
done
if [ $FAILED -eq 0 ]; then
    echo "CONTRACT OK"
else
    echo "CONTRACT FAILED: $FAILED sets"
    exit 1
fi
