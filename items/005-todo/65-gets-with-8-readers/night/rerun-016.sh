#!/bin/sh
# minutes: 30
# bergdb 005-65's rerun with the fix, for release 2026.2 (016-05; 005-65, State and Plan for
# 2026.2): threads.sh on the four builds in /Users/f/fl/bench/006-10/e65-builds, in turns
# ABCD DCBA: bf19075 (the first night's reference), 5a6befd (main before the fix), 988fe1a
# (the fix) and 4f7cd60 (the first night's HEAD, whose jar loads the database). About 21
# minutes: the 10M load, then 8 runs. The conductor's step 65-rerun in night 1's window 2.
# Created 2026-11-03 by Frans Lundberg.
# Usage: sh rerun-016.sh, from any directory. SMOKE=1: threads.sh's smoke (about a minute,
# outputs in $B/smoke); it prints "threads (SMOKE): OK, 0 problems; ..." when the parsed
# summary is complete.
# Outputs: threads.sh's: night/out/ (threads/NAME.txt and .json, runs.txt, summary.txt),
# the GC logs in $B/raw/threads. Exit status: threads.sh's (0 OK, 1 a run or the summary
# failed, 2 a missing prerequisite).

HERE=$(cd "$(dirname "$0")" && pwd)
B=/Users/f/fl/bench/006-10/e65-builds
BUILDS="bf19075 5a6befd 988fe1a 4f7cd60"
export B BUILDS
exec sh "$HERE/threads.sh"
