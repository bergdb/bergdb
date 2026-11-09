#!/bin/sh
# Runs the examples (bergdb 012-03, 012-13) and compares them with Java:
#   1. get_many_prefix prints Java's output, which its top comment holds
#      (012-03's probe of the same calls on Java's Db);
#   2. core_demo and Java's CoreDemo (006-08; java/stress/core-build/) on
#      each other's databases:
#      C's core_demo on a new directory, then Java's CoreDemo on it; and
#      Java's CoreDemo on a new directory, then C's core_demo on it. All four
#      print the same text (CoreDemo's reads hold for an existing database
#      with these keys too: they read at its own transactions' times).
#
# Usage: examples/compare.sh [BUILD]   (BUILD: build/release by default)
# Needs build.sh's programs, a JDK (JAVA_HOME, or /opt/homebrew/opt/openjdk,
# or java on PATH) and the Core Layer's classes in build/java/classes, which
# test/cross/java-build.sh makes (run here if missing), from the Java that
# JAVA_REF chooses (the release that C matches by default, bergdb 015-02);
# CoreDemo.java is taken from the same Java tree. Prints EXAMPLES OK.

set -e
C=$(cd "$(dirname "$0")/.." && pwd)
B=$C/${1:-build/release}
if [ -z "${JAVA_HOME:-}" ] && [ -d /opt/homebrew/opt/openjdk ]; then
    JAVA_HOME=/opt/homebrew/opt/openjdk
fi
if [ -n "${JAVA_HOME:-}" ]; then PATH=$JAVA_HOME/bin:$PATH; export JAVA_HOME; fi
OUT=$C/build/examples
rm -rf "$OUT"
mkdir -p "$OUT/classes"

fail() {
    echo "EXAMPLES FAILED: $1"
    exit 1
}

# 1. get_many_prefix against the output in its comment.
awk 'NR < 40 && /^ \*   / { sub(/^ \*   /, ""); print }' "$C/examples/get_many_prefix.c" \
    > "$OUT/get_many_prefix-java.txt"
"$B/get_many_prefix" > "$OUT/get_many_prefix.txt" || fail "get_many_prefix exit $?"
cmp -s "$OUT/get_many_prefix.txt" "$OUT/get_many_prefix-java.txt" \
    || { diff "$OUT/get_many_prefix.txt" "$OUT/get_many_prefix-java.txt"; fail "get_many_prefix"; }
echo "get_many_prefix: Java's output ($(wc -l < "$OUT/get_many_prefix.txt" | tr -d ' ') lines)"

# 2. core_demo and CoreDemo on each other's databases.
[ -d "$C/build/java/classes/bergdb/core" ] && [ -f "$C/build/java/java-dir.txt" ] \
    || sh "$C/test/cross/java-build.sh" > "$OUT/java-build.txt" \
    || { cat "$OUT/java-build.txt"; fail "the Java build"; }
DEMO=$(cat "$C/build/java/java-dir.txt")/stress/core-build/CoreDemo.java   # 006-08's
javac --release 17 -encoding UTF-8 -nowarn -cp "$C/build/java/classes" -d "$OUT/classes" "$DEMO" \
    || fail "javac CoreDemo.java"
java_demo() {
    java -ea -cp "$C/build/java/classes:$OUT/classes" CoreDemo "$1"
}
"$B/core_demo" "$OUT/c-first" > "$OUT/c-first-c.txt" || fail "core_demo on a new directory"
java_demo "$OUT/c-first" > "$OUT/c-first-java.txt" || fail "CoreDemo on core_demo's database"
java_demo "$OUT/java-first" > "$OUT/java-first-java.txt" || fail "CoreDemo on a new directory"
"$B/core_demo" "$OUT/java-first" > "$OUT/java-first-c.txt" || fail "core_demo on CoreDemo's database"
for f in c-first-java java-first-java java-first-c; do
    cmp -s "$OUT/c-first-c.txt" "$OUT/$f.txt" \
        || { diff "$OUT/c-first-c.txt" "$OUT/$f.txt"; fail "core_demo and CoreDemo differ ($f)"; }
done
grep -q '^CoreDemo OK' "$OUT/c-first-c.txt" || fail "core_demo's last line"
echo "core_demo: the same $(wc -l < "$OUT/c-first-c.txt" | tr -d ' ') lines as Java's CoreDemo, each on the other's database"
echo "EXAMPLES OK"
