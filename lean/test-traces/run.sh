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
[ $fail = 0 ] && echo "TRACE TESTS OK" || echo "TRACE TESTS FAILED"
