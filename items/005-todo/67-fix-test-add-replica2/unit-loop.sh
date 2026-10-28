#!/bin/sh
# bergdb 005-67. Runs the unit tests (bergdb.dev.Unit, as before-commit.sh does) N
# times with nice -n 10 and prints each failure of a StorageManagerTester test, the
# other failures counted.
# Usage: unit-loop.sh JAR N OUTDIR

JAR=$1
N=$2
OUT=$3
JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi
mkdir -p "$OUT"

failed=0
other=0
i=0
start=$(date +%s)
while [ $i -lt "$N" ]; do
    i=$((i + 1))
    nice -n 10 $JAVA -ea -cp "$JAR" bergdb.dev.Unit > "$OUT/unit.txt" 2>&1
    if ! grep -q '^SUCCESS' "$OUT/unit.txt"; then
        if grep -q 'FAILED! bergdb.storage.StorageManagerTester' "$OUT/unit.txt"; then
            failed=$((failed + 1))
            cp "$OUT/unit.txt" "$OUT/unit-failed-$i.txt"
            echo "run $i FAILED: $(grep -A2 'FAILED! bergdb.storage.StorageManagerTester' "$OUT/unit.txt" | tr '\n' ' ' | cut -c1-240)"
        else
            other=$((other + 1))
            cp "$OUT/unit.txt" "$OUT/unit-other-$i.txt"
            echo "run $i FAILED elsewhere: $(grep -m1 'FAILED!' "$OUT/unit.txt")"
        fi
    fi
done
echo "unit runs $N, StorageManagerTester failed $failed, other failures $other ($(( $(date +%s) - start )) s)"
