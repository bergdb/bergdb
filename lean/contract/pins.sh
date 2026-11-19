#!/bin/sh
# The pins checked without a build (bergdb 030-28): every file listed in
# lean/contract/statements.pin has the SHA-256 written there. gate.sh checks the
# same and more (step 5: also that the main theorems' closure is all pinned), but
# it builds the contract package with Mathlib and runs with proof work only; this
# check needs nothing but shasum, and java/stress/level2.sh runs it (so night.sh
# does), so that a change of a pinned file outside proof work fails the same
# night. A pinned file changed on purpose: run pin.sh (it needs the build) and
# commit statements.pin with the change, as gate.sh requires.
#
# First its own test, in a temporary copy of the pinned files and the pin file:
# the copy as it is must pass; with a byte appended to one pinned file (the first
# listed, and lean/SIS/Tree/Pe.lean, the tree checker's writer) it must fail, and
# with a pinned file removed.
#
# Usage: lean/contract/pins.sh. Prints PINS OK or PINS FAILED (with the files that
# differ). About a second.
cd "$(dirname "$0")/../.." || exit 1
PIN=lean/contract/statements.pin
[ -s $PIN ] || { echo "PINS FAILED: no $PIN"; exit 1; }

# pins_ok DIR: DIR's files have the hashes of DIR's pin file; else prints the files
# that differ and fails.
pins_ok() {
    OUT=$(cd "$1" && shasum -a 256 -c $PIN 2>&1)
    S=$?
    BAD=$(echo "$OUT" | grep -v ': OK$')
    [ $S -eq 0 ] && [ -z "$BAD" ] && return 0
    echo "$BAD"
    return 1
}

FILES=$(sed 's/^[0-9a-f]*  //' $PIN)
T=$(mktemp -d "${TMPDIR:-/tmp}/pins.XXXXXX") || { echo "PINS FAILED: no temporary directory"; exit 1; }
trap 'rm -rf "$T"' EXIT
for f in $FILES; do
    [ -f "$f" ] || continue
    mkdir -p "$T/$(dirname "$f")" && cp "$f" "$T/$f"
done
mkdir -p "$T/lean/contract" && cp $PIN "$T/$PIN"
SELF=""
FIRST=$(echo "$FILES" | head -1)
if pins_ok "$T" > /dev/null; then
    for f in "$FIRST" lean/SIS/Tree/Pe.lean; do
        [ -f "$T/$f" ] || { SELF="$SELF $f is not pinned or missing;"; continue; }
        cp "$T/$f" "$T/$f.orig" && printf ' ' >> "$T/$f"
        pins_ok "$T" > /dev/null && SELF="$SELF $f changed and passed;"
        mv "$T/$f.orig" "$T/$f"
    done
    mv "$T/$FIRST" "$T/$FIRST.gone"
    pins_ok "$T" > /dev/null && SELF="$SELF $FIRST removed and passed;"
    mv "$T/$FIRST.gone" "$T/$FIRST"
fi
# The copy holds what the tree holds, so it fails its unchanged check only where the
# tree does; that failure is reported below.
if [ -n "$SELF" ]; then echo "PINS FAILED: its own test:$SELF"; exit 1; fi
if BAD=$(pins_ok .); then
    echo "the pins' own test: a changed and a removed pinned file fail, as they must"
    echo "$(wc -l < $PIN | tr -d ' ') files have their pinned hashes ($PIN)"
    echo "PINS OK"
else
    echo "changed, not as pinned (if on purpose: lean/contract/pin.sh, and commit $PIN with the change):"
    echo "$BAD" | sed 's/^/   /'
    echo "PINS FAILED"
    exit 1
fi
