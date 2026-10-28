#!/bin/sh
# bergdb 005-67. The forced interleavings, on an instrumented copy (probe/forced.py) of
# the code before and of the code with the fix, 100 runs each in one JVM (probe/Loop67.java).
# Usage: [N_PAUSE=50] forced-runs.sh JAR   (JAR: an instrumented copy's build/bergdb.jar)
#   N_PAUSE: the runs of testAddReplicaWhileAppending with the sync's pause (5 by default:
#   on the code before each waits for ever, and ends at the timeout of 5 s).
# The instrumented copy of a commit:
#   git archive COMMIT java | tar -x -C DIR; python3 -I probe/forced.py DIR/java
#   (cd DIR/java && ./build.sh)
# Needs CLS, a directory with the probe's classes:
#   javac -cp JAR -d $CLS probe/Loop67.java probe/WhileAppending67.java

JAR=$1
CLS=${CLS:-cls}
JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi
run() {
    echo "--- $*"
    nice -n 10 $JAVA -ea "$@"
}
echo "bergdb 005-67, forced interleavings, $(date '+%Y-%m-%d %H:%M'), $JAR"
run -cp $CLS:$JAR Loop67 testAddReplica2 100
for d in 2 5 10 50; do
    run -Dr67.replicaFlushDelay=$d -cp $CLS:$JAR Loop67 testAddReplica2 100
done
for d in 1 3 10 50; do
    run -Dr67.afterAppend=$d -cp $CLS:$JAR Loop67 testAddReplica2 100
done
run -cp $CLS:$JAR Loop67 testAddReplicaWhileAppending 20 5000
run -Dr67.syncPause=30 -cp $CLS:$JAR Loop67 testAddReplicaWhileAppending ${N_PAUSE:-5} 5000
echo "(WhileAppending67 has a writer of its own, without and then with the write lock: StorageManager's contract, not the test; the same on both copies.)"
run -Dr67.syncPause=30 -cp $CLS:$JAR WhileAppending67 5
run -Dr67.syncPause=30 -cp $CLS:$JAR WhileAppending67 5 lock
