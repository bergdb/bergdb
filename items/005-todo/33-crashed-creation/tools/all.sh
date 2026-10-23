#!/bin/sh
# All cases, one after the other; outputs in runs/. About 4 minutes on F53.
# Usage: items/005-todo/33-crashed-creation/tools/all.sh
# Temporary directories go to PROBE_TMP, or to TMPDIR.

set -e
cd "$(dirname "$0")/.."
T=${PROBE_TMP:-${TMPDIR:-/tmp}}/probe-005-33
R=runs
mkdir -p $R
tools/run.sh cuts > $R/cuts.txt 2>&1
tools/run.sh pub $T > $R/pub.txt 2>&1
tools/run.sh flushes 500 > $R/flushes.txt 2>&1
tools/run.sh kill $T 300 400 > $R/kill.txt 2>&1
rm -rf $T
echo ALL DONE
