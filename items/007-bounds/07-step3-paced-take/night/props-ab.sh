#!/bin/sh
# minutes: 12
# bergdb 007-07: Props (MEM, CORE, SS) before and after 007-07, for 006-10's W1.2. Runs
# 005-46's night/props.sh (four rounds of each build in turns, ABBA) on two preserved builds:
# main-cefb473 (main just before 007-07) and d4b-f89846d (007-07's code). props.sh writes
# into its own directory's out/, so this script runs a copy of 005-46's night/ in W, and the
# raw output stays out of the repository. Written 2026-10-28 by Claude (Opus 5.5, Claude Code).
#
# Usage: sh props-ab.sh            the runs (about 6 minutes, stopped at 12)
#        SMOKE=1 sh props-ab.sh    one round of each build, about 80 s; fails unless the
#                                  summary has every value and a CORE mean for each build
# Environment: W (default /Users/f/fl/bench/006-10/w1props), with W/builds/main-cefb473 and
# W/builds/d4b-f89846d, clones at those commits built with java/build.sh.

W=${W:-/Users/f/fl/bench/006-10/w1props}
SRC=$(cd "$(dirname "$0")/../../../005-todo/46-stream-file-lock/night" && pwd) || exit 2
for j in main-cefb473 d4b-f89846d; do
    [ -f "$W/builds/$j/java/build/bergdb.jar" ] || { echo "props-ab: no $W/builds/$j/java/build/bergdb.jar" >&2; exit 2; }
done
rm -rf "$W/night" && mkdir -p "$W/night" || exit 2
cp "$SRC/props.sh" "$SRC/lib.sh" "$SRC/nightsum.py" "$W/night/" || exit 2
B="$W/builds" JARS="main-cefb473 d4b-f89846d" sh "$W/night/props.sh"
rc=$?
if [ "${SMOKE:-0}" = 1 ]; then s="$W/builds/smoke/summary.txt"; else s="$W/night/out/summary.txt"; fi
echo "props-ab: exit $rc; summary $s"
[ -f "$s" ] && cat "$s"
exit $rc
