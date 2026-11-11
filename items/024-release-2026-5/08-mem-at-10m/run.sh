#!/bin/sh
# MemProbe's runner (bergdb 024-08): run.sh NAME args...  Output in out/NAME.txt, histogram
# in out/NAME.hist.txt. JVM as 024-03's: G1, -Xms8g -Xmx8g, JDK 27 defaults otherwise.
B=/Users/f/fl/bench/2026-11-11/mem
NAME=$1; shift
exec /opt/homebrew/opt/openjdk/bin/java -Xms8g -Xmx8g -XX:+UseG1GC $JOPTS \
    -cp $B/classes:$B/clone/java/build/bergdb.jar bergdb.core.MemProbe \
    hist=$B/out/$NAME.hist.txt "$@" > $B/out/$NAME.txt 2>&1
