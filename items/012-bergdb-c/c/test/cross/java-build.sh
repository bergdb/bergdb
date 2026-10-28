#!/bin/sh
# Compiles BergDB Java's Core Layer from java/src together with the cross
# harness's Java sources in test/cross/java/ and java/stress/StreamDigest.java
# (package bergdb.core, whose configurations the exporter reads; bergdb
# 012-05) into build/java/classes (bergdb
# 012-01, section 6.3), as java/stress/core-build.sh compiles the Core Layer
# alone: an empty class path and source path, so that nothing outside the
# Core Layer can be used. The Core Layer's packages are java/deps.py's
# (--layer core). The harness's classes may be in package bergdb.core, to
# reach the parsers. Never touches java/build/.
#
# Usage: test/cross/java-build.sh      (from any directory)
# Then:  java -ea -cp build/java/classes bergdb.core.StreamScan ...
# Needs a JDK (JAVA_HOME or PATH) and python3. Prints JAVA BUILD OK.

set -e
C=$(cd "$(dirname "$0")/../.." && pwd)
JAVA=$(cd "$C/../../../java" && pwd)
if [ -n "$JAVA_HOME" ]; then PATH=$JAVA_HOME/bin:$PATH; fi
OUT=$C/build/java

rm -rf "$OUT/classes" "$OUT/empty"
mkdir -p "$OUT/classes" "$OUT/empty"
PKGS=$(cd "$JAVA" && python3 -I deps.py src --layer core --list)
: > "$OUT/sources.txt"
for p in $PKGS; do
    ls "$JAVA/src/bergdb/$(echo $p | tr . /)"/*.java >> "$OUT/sources.txt"
done
echo "$JAVA/stress/StreamDigest.java" >> "$OUT/sources.txt"
find "$C/test/cross/java" -name '*.java' >> "$OUT/sources.txt" 2>/dev/null || true
(cd "$OUT/empty" && javac --release 17 -encoding UTF-8 -nowarn -Xlint:-options \
    -cp "$OUT/empty" -sourcepath "$OUT/empty" -implicit:none -d "$OUT/classes" \
    @"$OUT/sources.txt") > "$OUT/javac.txt" 2>&1 || { cat "$OUT/javac.txt"; echo "JAVA BUILD FAILED"; exit 1; }
echo "JAVA BUILD OK: $(wc -l < "$OUT/sources.txt" | tr -d ' ') source files into build/java/classes"
