#!/bin/sh
# The gate of the contract package (bergdb 030-04, section 7.6):
#   1. `lake build` passes in lean/contract/;
#   2. no `sorry`, no `admit`, no `native_decide` and no `axiom` declaration in it;
#   3. `#print axioms` of the theorems (Axioms.lean) shows only `propext`,
#      `Classical.choice` and `Quot.sound`;
#   4. with a base commit as the first argument: no file changed since it outside
#      lean/contract/ and items/030-proofs/; but java/ (then java/before-commit.sh
#      must print BEFORE COMMIT OK, which this script does not run) and the trace
#      format, items/027-algorithms/02-trace-format.md (bergdb 030-09: the exporter
#      and its format change with the checker).
#   5. (bergdb 030-15) the statements are pinned: every file of the trusted closure
#      of the main theorems (Statements.lean prints them) is in statements.pin, and
#      every file in statements.pin has the hash written there (pin.sh writes the
#      file; it lists which files and why). With BASE: no commit since BASE that
#      changed a pinned file without changing statements.pin (a commit is checked if
#      its parent has statements.pin), so that a change of a statement is always
#      visible in review; and the pinned files changed since BASE are listed.
# Usage: lean/contract/gate.sh [BASE]. Prints GATE OK or GATE FAILED.
cd "$(dirname "$0")"
FAILED=0
lake build > /tmp/contract-gate-build.$$ 2>&1 || { echo "1. lake build failed"; tail -20 /tmp/contract-gate-build.$$; FAILED=1; }
grep -q 'warning' /tmp/contract-gate-build.$$ && { echo "1. lake build has warnings"; grep 'warning' /tmp/contract-gate-build.$$ | head -5; }
rm -f /tmp/contract-gate-build.$$
[ $FAILED -eq 0 ] && echo "1. lake build passes"
BAD=$(grep -n -w -E 'sorry|admit|native_decide' *.lean Contract/*.lean Contract/Proof/*.lean | grep -v '^Axioms.lean')
BADAX=$(grep -n -E '^[[:space:]]*(private |protected )?axiom ' *.lean Contract/*.lean Contract/Proof/*.lean)
if [ -n "$BAD$BADAX" ]; then echo "2. found:"; echo "$BAD$BADAX"; FAILED=1; else echo "2. no sorry, admit, native_decide or axiom"; fi
AX=$(lake env lean Axioms.lean 2>&1)
echo "$AX" | sed 's/^/   /'
OTHER=$(echo "$AX" | sed -n 's/.*depends on axioms: \[\(.*\)\]/\1/p' | tr ',' '\n' | sed 's/ //g' | grep -v -x -E 'propext|Classical.choice|Quot.sound')
M=$(echo "$AX" | grep -c "depends on axioms\|does not depend on any axioms")
L=$(grep -c '^#print axioms' Axioms.lean)
if [ "$M" -eq "$L" ] && [ -z "$OTHER" ] && ! echo "$AX" | grep -q 'error'; then echo "3. the standard axioms only ($L theorems)"; else echo "3. axioms: not the standard three only: $OTHER"; FAILED=1; fi
if [ -n "$1" ]; then
    ALLOWED='lean/contract/|items/030-proofs/|java/|items/027-algorithms/02-trace-format.md'
    OUT=$(git diff --name-only "$1" HEAD | grep -v -E "^($ALLOWED)")
    DIRTY=$(git status --porcelain | grep -v -E " ($ALLOWED)")
    if [ -n "$OUT$DIRTY" ]; then echo "4. changed outside:"; echo "$OUT$DIRTY"; FAILED=1; else echo "4. no file changed outside lean/contract/, items/030-proofs/, java/ and 027-02 since $1"
        git diff --name-only "$1" HEAD | grep -q '^java/' && echo "   java/ changed: java/before-commit.sh must print BEFORE COMMIT OK"; fi
fi
PIN=lean/contract/statements.pin
CLOSURE=$(lake env lean Statements.lean 2>&1)
STMT=$(echo "$CLOSURE" | grep '^lean/')
if [ -z "$STMT" ] || echo "$CLOSURE" | grep -q 'error'; then
    echo "5. Statements.lean failed:"; echo "$CLOSURE" | head -5; FAILED=1
else
    ROOT=$(cd ../.. && pwd)
    UNPINNED=$(for f in $STMT; do grep -q "  $f\$" $ROOT/$PIN || echo "$f"; done)
    CHANGED=$(cd $ROOT && shasum -a 256 -c $PIN 2>&1 | grep -v ': OK$')
    LATE=""
    if [ -n "$1" ]; then
        PINNED=$(sed 's/^[0-9a-f]*  //' $ROOT/$PIN)
        for c in $(git rev-list --no-merges "$1"..HEAD); do
            git cat-file -e "$c^:$PIN" 2> /dev/null || continue
            FILES=$(git diff-tree --no-commit-id --name-only -r "$c")
            echo "$FILES" | grep -q -x "$PIN" && continue
            HIT=$(echo "$FILES" | grep -x -F "$PINNED")
            [ -n "$HIT" ] && LATE="$LATE $(git log -1 --format=%h "$c"):$(echo $HIT | tr ' ' ',')"
        done
    fi
    if [ -n "$UNPINNED$CHANGED$LATE" ]; then
        echo "5. the statements' pins:"
        [ -n "$UNPINNED" ] && echo "   not in $PIN (run pin.sh):" && echo "$UNPINNED" | sed 's/^/     /'
        [ -n "$CHANGED" ] && echo "   changed, not as pinned (run pin.sh, commit the pin file with the change):" \
            && echo "$CHANGED" | sed 's/^/     /'
        [ -n "$LATE" ] && echo "   commits that changed pinned files without $PIN:$LATE"
        FAILED=1
    else
        echo "5. the statements pinned: $(echo "$STMT" | wc -l | tr -d ' ') files of the main theorems' closure, $(wc -l < $ROOT/$PIN | tr -d ' ') pinned"
        if [ -n "$1" ]; then
            MOVED=$(git diff --name-only "$1" HEAD | grep -x -F "$(sed 's/^[0-9a-f]*  //' $ROOT/$PIN)")
            [ -n "$MOVED" ] && echo "   pinned files changed since $1 (review them):" && echo "$MOVED" | sed 's/^/     /'
        fi
    fi
fi
if [ $FAILED -eq 0 ]; then echo "GATE OK"; else echo "GATE FAILED"; exit 1; fi
