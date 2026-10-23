#!/bin/sh
# All cases, one after the other; outputs in runs/. About 5 minutes on F53.
# Usage: items/005-todo/32-fix-failed-start-storage/tools/all.sh
# Temporary directories go to PROBE_TMP, or to TMPDIR.

set -e
cd "$(dirname "$0")/.."
T=${PROBE_TMP:-${TMPDIR:-/tmp}}/probe-005-32
R=runs
mkdir -p $R
tools/run.sh pub $T 10 > $R/pub.txt 2>&1
tools/run.sh key $T 10 > $R/key.txt 2>&1
JAVA_OPTS="-ea --finalization=disabled" tools/run.sh key $T 10 > $R/key-no-finalization.txt 2>&1
tools/run.sh closehang > $R/closehang.txt 2>&1
tools/run.sh twice $T > $R/twice.txt 2>&1
tools/run.sh race $T 20 > $R/race-assertions-on.txt 2>&1
JAVA_OPTS=-da tools/run.sh race $T 20 > $R/race-assertions-off.txt 2>&1
rm -rf $T
echo ALL DONE
