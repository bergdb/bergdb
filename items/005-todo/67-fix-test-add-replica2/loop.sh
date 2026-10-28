#!/bin/sh
# bergdb 005-67. Runs one unit test alone, each run in a JVM of its own, N times,
# and prints each failure (the assertion and its line) and the counts.
# Usage: loop.sh JAR N [CLASS_PATTERN] [METHOD_PATTERN] [JVM_OPTIONS]
#   loop.sh java/build/bergdb.jar 1000
# The defaults run StorageManagerTester.testAddReplica2. With nice -n 10.

JAR=$1
N=$2
C=${3:-.*StorageManagerTester}
M=${4:-testAddReplica2}
OPTS=${5:-}
JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi

pass=0
fail=0
i=0
start=$(date +%s)
while [ $i -lt "$N" ]; do
    i=$((i + 1))
    out=$(nice -n 10 $JAVA -ea $OPTS -cp "$JAR" bergdb.dev.Unit -c "$C" -m "$M" 2>&1)
    if echo "$out" | grep -q '^SUCCESS'; then
        pass=$((pass + 1))
    else
        fail=$((fail + 1))
        what=$(echo "$out" | grep -m1 -E 'Error|Exception')
        where=$(echo "$out" | grep -m1 -o 'StorageManagerTester.java:[0-9]*')
        echo "run $i FAILED: $what ($where)"
    fi
done
echo "runs $N, failed $fail, passed $pass ($(( $(date +%s) - start )) s)"
