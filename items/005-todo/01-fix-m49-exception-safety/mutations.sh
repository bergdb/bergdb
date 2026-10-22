#!/bin/sh
# bergdb 005-01: each part of the fix taken out in a copy of java/, to see that a test
# fails without it (mutate.py): A, the fix taken out (transactionEnd() in a finally
# around the puts, as before, and no fail-stop); B, the fail-stop without the change of
# transactionEnd(); C, no state check under the write lock. Runs DbTesterFailure's unit
# tests and the f-tests of DbTesterFailure and DbTesterStream on each.
#
# Usage: mutations.sh JAVA_DIR WORK_DIR
#   JAVA_DIR: the java/ directory with the fix; WORK_DIR: an empty scratch directory.

set -e
JAVA_DIR=$1
WORK=$2
HERE=$(cd "$(dirname "$0")" && pwd)
for m in A B C; do
    rm -rf "$WORK/$m"
    mkdir -p "$WORK/$m"
    rsync -a --exclude build "$JAVA_DIR/" "$WORK/$m/java/"
    python3 -I "$HERE/mutate.py" "$WORK/$m/java/src/bergdb/core/Db.java" $m
    (cd "$WORK/$m/java" && ./build.sh > build.log 2>&1)
    echo "== mutation $m"
    (cd "$WORK/$m/java" && java -ea -cp build/bergdb.jar bergdb.dev.Unit -c DbTesterFailure 2>&1 |
        grep -E "FAILED!|^[A-Za-z.]*(Exception|Error)|SUCCESS|FAILURE" || true)
    (cd "$WORK/$m/java" && java -ea -cp build/bergdb.jar bergdb.dev.F -c "DbTesterFailure|DbTesterStream" 2>&1 |
        grep -E "FAILED!|^[A-Za-z.]*(Exception|Error)|SUCCESS|FAILURE" || true)
done
