#!/bin/sh
# PF1's runner (bergdb 024-03): pf1.sh VER CMD dir=... args...  (VER 3 or 4)
B=/Users/f/fl/bench/2026-11-11/pf1
V=$1; shift
JAR=/Users/f/fl/repos/bergdb/releases/2026.$V/bergdb-2026.$V.jar
exec /opt/homebrew/opt/openjdk/bin/java -Xms8g -Xmx8g -XX:+UseG1GC -cp $B/c$V:$JAR bergdb.core.PF1 "$@"
