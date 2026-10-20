#!/bin/sh
# 005-10: the Java part of the unused-code analysis, from a clean build.
#
# Usage: java-analysis.sh <bergdb clone> <out dir> <proguard.jar>
#
# Builds the clone with java/build.sh, then runs: classes.py (class-level
# reachability), Index.java (the javac source index), pg.py and ProGuard
# (member-level reachability for the configurations api, run, noapi, all,
# keep), and combine.py (both together). Needs a JDK with jmods (JAVA_HOME
# or the java on the path) and python3.

set -e
REPO=$1
OUT=$2
PROGUARD=$3
TOOLS=$(cd "$(dirname "$0")" && pwd)
JAVA=${JAVA_HOME:+$JAVA_HOME/bin/}java
JHOME=$("$JAVA" -XshowSettings:properties -version 2>&1 | sed -n 's/^ *java.home = //p')

mkdir -p "$OUT/pg" "$OUT/idx" "$OUT/c"
(cd "$REPO/java" && ./build.sh > "$OUT/build.txt" 2>&1)
python3 -I "$TOOLS/classes.py" "$REPO" "$OUT" > "$OUT/classes.txt"
"$JAVA" -Xmx4g "$TOOLS/Index.java" "$OUT/idx" "$REPO/java/in/icu-for-bergdb.jar" \
    "$REPO/java/src" "$REPO/java/src-dev" "$REPO/java/src-icu" "$REPO/java/stress" \
    > "$OUT/idx/index.txt" 2> "$OUT/idx/index-warnings.txt"
python3 -I "$TOOLS/pg.py" "$REPO" "$OUT/pg" "$JHOME/jmods" > "$OUT/pg/pg.txt"
for n in api run noapi all keep; do
    "$JAVA" -jar "$PROGUARD" @"$OUT/pg/pg-$n.pro" > "$OUT/pg/log-$n.txt" 2>&1
done
python3 -I "$TOOLS/combine.py" "$REPO" "$OUT/pg" "$OUT/idx" "$OUT/c" > "$OUT/c/combine.txt"
cat "$OUT/classes.txt" "$OUT/pg/pg.txt" "$OUT/c/combine.txt"
