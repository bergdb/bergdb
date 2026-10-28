#!/bin/sh
# The write path's checks against Java's streams (bergdb 012-09, part 1),
# on the directories that side A (Java) of a cross set wrote and kept
# (test/cross/cross.sh SET KEEP=1):
#   take      bergdb-takecheck on every directory: C's take replayed on C's
#             parsed records; each record's startup position and index
#             nodes, in order, as Java's; and on the crash variants that
#             side A recovered and ran on (crash/W/CUT/a), across the fill
#   reappend  bergdb-reappend on every directory that no reclaim cut: the
#             records re-appended through C's append path, with the
#             workload's restarts from Run's output (run.txt), and the
#             directory compared with Java's, file by file, byte by byte
#   clock     bergdb-clockcheck on the same: the workload's clock replayed
#             on C's DbClock, every transaction's time and every now as
#             Java's (wl/NAME.wl, run.txt)
#
# Usage: test/cross/writecheck.sh [SETDIR] [C=DIR]
#   SETDIR  a set's output (default build/cross/quick)
#   C=DIR   the C tools (default build/release)
# Output: build/writecheck/ (the tools' outputs; C's directories are deleted
# when they equal Java's). The last line is "WRITECHECK OK: ..." or
# "WRITECHECK FAILED: ..."; the exit status 0 or 1.
{
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
CDIR=$(cd "$HERE/../.." && pwd)
SETDIR=$CDIR/build/cross/quick
TOOLS=$CDIR/build/release
for arg in "$@"; do
    case "$arg" in
    C=*) TOOLS=$(cd "${arg#C=}" && pwd) || exit 2 ;;
    *) SETDIR=$(cd "$arg" && pwd) || exit 2 ;;
    esac
done
OUT=$CDIR/build/writecheck
rm -rf "$OUT"
mkdir -p "$OUT/dirs"
if ! ls -d "$SETDIR"/a/*/db > /dev/null 2>&1; then
    echo "WRITECHECK FAILED: no directories in $SETDIR/a (run cross.sh with KEEP=1)"
    exit 1
fi

FAILS=0
"$TOOLS/bergdb-takecheck" "$SETDIR"/a/*/db > "$OUT/takecheck.txt" 2>&1
TAKE=$(tail -1 "$OUT/takecheck.txt")
case "$TAKE" in
"TAKECHECK OK"*) ;;
*) FAILS=$((FAILS + 1)); grep -B1 'error' "$OUT/takecheck.txt" | head -20 ;;
esac

CRASH=""
if ls -d "$SETDIR"/crash/*/*/a > /dev/null 2>&1; then
    "$TOOLS/bergdb-takecheck" "$SETDIR"/crash/*/*/a > "$OUT/takecheck-crash.txt" 2>&1
    CRASH=$(tail -1 "$OUT/takecheck-crash.txt")
    case "$CRASH" in
    "TAKECHECK OK"*) CRASH="; crash variants: $(echo "$CRASH" | sed 's/^TAKECHECK OK: //; s/, [0-9]* transactions taken.*//')" ;;
    *) FAILS=$((FAILS + 1)); grep -B1 'error' "$OUT/takecheck-crash.txt" | head -20 ;;
    esac
fi

EQUAL=0
SKIPPED=0
CLOCKS=0
CLOCKSKIP=0
: > "$OUT/reappend.txt"
: > "$OUT/clockcheck.txt"
for w in "$SETDIR"/a/*/; do
    w=${w%/}
    name=$(basename "$w")
    run=""
    [ -f "$w/run.txt" ] && run="-run $w/run.txt"
    # shellcheck disable=SC2086
    "$TOOLS/bergdb-reappend" $run "$w/db" "$OUT/dirs/$name" >> "$OUT/reappend.txt" 2>&1
    case $? in
    0) EQUAL=$((EQUAL + 1)); rm -rf "$OUT/dirs/$name" ;;
    3) SKIPPED=$((SKIPPED + 1)); rm -rf "$OUT/dirs/$name" ;;
    *) FAILS=$((FAILS + 1)); tail -1 "$OUT/reappend.txt" ;;
    esac
    if [ -f "$SETDIR/wl/$name.wl" ] && [ -f "$w/run.txt" ]; then
        "$TOOLS/bergdb-clockcheck" "$SETDIR/wl/$name.wl" "$w/db" "$w/run.txt" \
                >> "$OUT/clockcheck.txt" 2>&1
        case $? in
        0) CLOCKS=$((CLOCKS + 1)) ;;
        3) CLOCKSKIP=$((CLOCKSKIP + 1)) ;;
        *) FAILS=$((FAILS + 1)); tail -1 "$OUT/clockcheck.txt" ;;
        esac
    fi
done

SUMMARY="${TAKE#TAKECHECK * }$CRASH; reappend: $EQUAL directories equal, $SKIPPED skipped (a reclaim cut); clock: $CLOCKS workloads' times equal, $CLOCKSKIP skipped"
if [ "$FAILS" = 0 ]; then
    echo "WRITECHECK OK: $SUMMARY"
    exit 0
fi
echo "WRITECHECK FAILED: $FAILS; $SUMMARY (build/writecheck/)"
exit 1
}
