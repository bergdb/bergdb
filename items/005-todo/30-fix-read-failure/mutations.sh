#!/bin/sh
# bergdb 005-30: each part of the fix taken out in a copy of java/ (mutate.py), to see
# that a test fails without it: A, a read that fails on the storage does not fail the
# database; B, no state check in getTrans(); C, a failed sync does not fail it; D, an
# interrupted sync fails it; E, a read while stopping fails it; F, a format error in
# getTrans() fails it; G, a read below the cut in getTrans() fails it. Runs the unit tests
# of DbTesterFailure and the f-tests of DbTesterFailure, DbTesterStream and DbTester on each.
#
# Usage: mutations.sh JAVA_DIR WORK_DIR
#   JAVA_DIR: the java/ directory with the fix; WORK_DIR: an empty scratch directory.

set -e
JAVA_DIR=$1
WORK=$2
HERE=$(cd "$(dirname "$0")" && pwd)
for m in A B C D E F G; do
    rm -rf "$WORK/$m"
    mkdir -p "$WORK/$m"
    rsync -a --exclude build "$JAVA_DIR/" "$WORK/$m/java/"
    python3 -I "$HERE/mutate.py" "$WORK/$m/java/src/bergdb/core/Db.java" $m
    (cd "$WORK/$m/java" && ./build.sh > build.log 2>&1)
    echo "== mutation $m"
    (cd "$WORK/$m/java" && java -ea -cp build/bergdb.jar bergdb.dev.Unit -c DbTesterFailure 2>&1 |
        grep -E "FAILED!|SUCCESS|FAILURE" || true)
    (cd "$WORK/$m/java" && java -ea -cp build/bergdb.jar bergdb.dev.F \
        -c 'DbTesterFailure|DbTesterStream|bergdb.core.DbTester$' 2>&1 |
        grep -E "FAILED!|SUCCESS|FAILURE" || true)
done
