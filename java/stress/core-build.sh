#!/bin/sh
# Builds the Core Layer alone, from src/, and uses it (bergdb 006-08; a tool
# of the build since 2026-10-28, 005-56). The Core Layer is bergdb.core and the
# packages it may use, directly or not, according to the package.html files
# (P12 in 010-01). A step of night.sh; not a commit gate. Steps, stopping at
# the first failure:
#   1. deps.py --layer core: each Core Layer package's uses against its
#      package.html.
#   2. javac on the Core Layer's sources alone, with an empty class path and
#      source path, so that nothing else can be used; bergdb-core.jar.
#   3. jdeps: the JDK modules that the jar needs.
#   4. CoreDemo (core-build/), user code that calls Db directly, against
#      bergdb-core.jar alone: execute, getOne, getMany, getTrans, a restart.
#   5. The Core Layer's own Nano tests, group unit (or the groups given), on
#      bergdb-core.jar alone, by CoreUnit (core-build/).
#
# Usage: java/stress/core-build.sh [GROUP...]
#   GROUP is unit (the default) or f. About 15 s with unit; with f, about 70 s
#   more. night.sh runs it with unit and f.
# Output in build/core-build/. Prints CORE BUILD OK, or CORE BUILD FAILED and
# exits with status 1. Needs a JDK (javac, jar, jdeps, java; JAVA_HOME or
# PATH) and python3. Does not use build.sh or build/bergdb.jar.

set -e
cd "$(dirname "$0")/.."
if [ -n "$JAVA_HOME" ]; then PATH=$JAVA_HOME/bin:$PATH; fi

TEST_GROUPS=${*:-unit}
SRC=src
HERE=stress/core-build
OUT=$(pwd)/build/core-build

fail() {
    echo "CORE BUILD FAILED: $1"
    exit 1
}

rm -rf "$OUT"
mkdir -p "$OUT/src" "$OUT/classes" "$OUT/user" "$OUT/empty"

echo "1. The Core Layer's packages against their package.html"
python3 -I deps.py "$SRC" --layer core > "$OUT/deps.txt" || { cat "$OUT/deps.txt"; fail "deps.py"; }
PKGS=$(python3 -I deps.py "$SRC" --layer core --list)
echo "   $(tail -1 "$OUT/deps.txt"): $(echo $PKGS)"

echo "2. javac, the Core Layer alone"
for p in $PKGS; do
    d=bergdb/$(echo $p | tr . /)
    mkdir -p "$OUT/src/$d"
    cp "$SRC/$d"/*.java "$OUT/src/$d/"
done
(cd "$OUT/empty" && javac --release 17 -encoding UTF-8 -nowarn -Xlint:-options \
    -cp "$OUT/empty" -sourcepath "$OUT/empty" -implicit:none -d "$OUT/classes" \
    $(find "$OUT/src" -name '*.java')) > "$OUT/javac.txt" 2>&1 || { cat "$OUT/javac.txt"; fail "javac"; }
jar cf "$OUT/bergdb-core.jar" -C "$OUT/classes" .
echo "   $(find "$OUT/src" -name '*.java' | wc -l | tr -d ' ') source files," \
    "$(find "$OUT/classes" -name '*.class' | wc -l | tr -d ' ') classes," \
    "bergdb-core.jar $(wc -c < "$OUT/bergdb-core.jar" | tr -d ' ') bytes"

echo "3. jdeps"
jdeps -summary "$OUT/bergdb-core.jar" > "$OUT/jdeps.txt" 2>&1 || { cat "$OUT/jdeps.txt"; fail "jdeps"; }
sed 's/^/   /' "$OUT/jdeps.txt"

echo "4. CoreDemo, calls Db directly"
javac --release 17 -Xlint:-options -cp "$OUT/bergdb-core.jar" -d "$OUT/user" \
    $HERE/CoreDemo.java $HERE/CoreUnit.java > "$OUT/javac-user.txt" 2>&1 \
    || { cat "$OUT/javac-user.txt"; fail "javac of CoreDemo and CoreUnit"; }
java -ea -cp "$OUT/bergdb-core.jar:$OUT/user" CoreDemo "$OUT/db" > "$OUT/demo.txt" 2>&1 \
    || { cat "$OUT/demo.txt"; fail "CoreDemo"; }
sed 's/^/   /' "$OUT/demo.txt"

echo "5. The Core Layer's tests"
for g in $TEST_GROUPS; do
    java -ea -cp "$OUT/bergdb-core.jar:$OUT/user" CoreUnit $g $PKGS > "$OUT/test-$g.txt" 2>&1 || true
    grep -q '^SUCCESS' "$OUT/test-$g.txt" || fail "the $g tests (log: java/build/core-build/test-$g.txt)"
    echo "   $g: $(grep '^SUCCESS' "$OUT/test-$g.txt")"
done

echo "CORE BUILD OK"
