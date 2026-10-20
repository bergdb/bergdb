#!/bin/sh
# Tests of the trace checker (WP C2): runs it on the hand-made traces here and
# checks the expected outcome of each. Usage, in lean/: sh test-traces/run.sh
cd "$(dirname "$0")/.."
fail=0
expect() {
    out=$(lake exe tracecheck "test-traces/$1" 2>&1)
    if echo "$out" | grep -q "$2"; then
        echo "ok   $1: $2"
    else
        echo "FAIL $1: expected $2"
        echo "$out" | sed 's/^/     /'
        fail=1
    fi
}
expect example.trace "TRACECHECK OK"
expect a3.trace "A3 fails for nodes 9"
expect badref.trace "references of node 5"
expect badlive.trace "live of 5 at 1"
expect adopt.trace "TREE (one current parent) fails for nodes 11"
expect adopt.trace "adoptions below the old parent .*: 1 of 3 transactions"
expect adopt.trace "TRACECHECK FAILED: C-A"
expect adopt2.trace "A6' (no adoption) fails for pointers .(7, 15)"
expect adopt2.trace "adoptions below the old parent .*: 0 of 3 transactions"
expect adopt2.trace "TRACECHECK FAILED: C-A"
expect copy.trace "A-COPY fails for pointers .(13, 15)"
expect copy.trace "TRACECHECK FAILED: C-A"
expect badfirst.trace "R(3) read, cut back true, the rule says false"
expect badfirst.trace "C-L4 .*: 0 of 5 FIRST lines"
expect snapfirst.trace "C-L first touches: 0 of 5 FIRST lines fail"
expect snapfirst.trace "C-L4 .*: 1 of 5 FIRST lines take a snapshot"
expect snapfirst.trace "TRACECHECK OK"
expect badskip.trace "caches time 5"
expect badskip.trace "C-S steps: 1 of 9 transactions fail (skip 1)"
expect touch.trace "touchUp fails for nodes 7"
expect touch.trace "C-S steps: 0 of 2 transactions fail"
expect cut.trace "C-CUT cuts: 1 of 1 CUT lines (and PHYSCUT lines) fail (CUT-reach 1, CUT-top 1)"
expect cut.trace "C-S steps: 0 of 3 transactions fail"
expect stale.trace "C-CUT cuts: 1 of 1 CUT lines (and PHYSCUT lines) fail (CUT-stale 1)"
expect physcut.trace "C-CUT cuts: 1 of 1 CUT lines (and PHYSCUT lines) fail (CUT-stale 1)"
expect slot.trace "C-P slots .*: 0 of 3 transactions fail; 4 SLOT lines, 4 checked"
expect slot.trace "TRACECHECK OK"
expect badslot.trace "the slot of 3 for 5 names R(0), its latest version is R(2)"
expect badslot.trace "TRACECHECK FAILED: C-P"
[ $fail = 0 ] && echo "TRACE TESTS OK" || echo "TRACE TESTS FAILED"
