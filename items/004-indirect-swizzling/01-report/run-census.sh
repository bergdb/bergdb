#!/bin/sh
# The runs of IndexCensus for 004-01 (bergdb item 004), against bergdb.jar as it is.
# Usage: sh run-census.sh OUTDIR [BERGDB_JAR]
#   OUTDIR      where the compiled classes go and the output files are written
#   BERGDB_JAR  default: java/build/bergdb.jar of this repository (build it first with
#               java/build.sh)
# Needs JAVA_HOME or java and javac on the PATH.
set -e
OUT=$1
HERE=$(cd "$(dirname "$0")" && pwd)
JAR=${2:-$HERE/../../../java/build/bergdb.jar}
JAVA=${JAVA_HOME:+$JAVA_HOME/bin/}java
JAVAC=${JAVA_HOME:+$JAVA_HOME/bin/}javac
mkdir -p "$OUT/classes"
"$JAVAC" -nowarn -cp "$JAR" -d "$OUT/classes" "$HERE/IndexCensus.java"
for kt in int4 pre16 rnd16; do
    "$JAVA" -Xms8g -Xmx8g -Dkeys=1000000 -Dkeytype=$kt -Dvalsize=8 -Dthreads=4 \
        -cp "$JAR:$OUT/classes" bergdb.core.IndexCensus > "$OUT/census-$kt.txt" 2>&1
    cat "$OUT/census-$kt.txt"
done
