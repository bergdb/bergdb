#!/bin/sh
# The Core without its test code: built, used and measured (bergdb 006-08,
# sections 3 to 5). Steps, stopping at the first failure:
#   1. A copy of the Core Layer's sources (deps.py) without nanotest, the
#      tester files and the Pack lists; strip.py removes the test code in the
#      other files. One line of production code uses nanotest
#      (KeyNode.checkLastTimeIndex); the copy throws AssertionError instead.
#   2. javac on that copy alone, with an empty class path: bergdb-core-notest.jar.
#   3. javac on Db.java and DbBuilder.java, with the copy as source path: the
#      classes that Db and DbBuilder need, directly or not (-implicit:class);
#      bergdb-core-db.jar, its size without debug information (-g:none), and
#      the JDK modules it needs (jdeps).
#   4. CoreDemo on bergdb-core-db.jar alone.
#   5. CoreSame, a fixed workload, on the Core Layer as it is, with its tests
#      (bergdb-core.jar, as core-build.sh builds it), and on bergdb-core-db.jar:
#      the same stream, byte for byte, and the same state.
#   6. For comparison: all of java/src and java/src-icu without test code,
#      the ICU jar on the class path, not in the jar; bergdb-notest.jar.
#   7. Lines and code lines (lines.py) of each; closure-lines.txt has each
#      file of step 3.
#
# Usage: sh core-size.sh REPO
#   REPO is a bergdb repository. About 20 s.
# Output in $OUT (default: a new temporary directory). Needs a JDK (javac,
# jar, jdeps) and python3.

set -e
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "${1:?usage: sh core-size.sh REPO}" && pwd)
SRC=$REPO/java/src
ICU=$REPO/java/in/icu-for-bergdb.jar
OUT=${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/bergdb-core-size.XXXXXX")}

fail() {
    echo "CORE SIZE FAILED: $1"
    exit 1
}

# Copies the packages $2... of java/src to $1, without the test code.
copy_stripped() {
    to=$1
    shift
    for p in "$@"; do
        d=bergdb/$(echo $p | tr . /)
        mkdir -p "$to/$d"
        cp "$SRC/$d"/*.java "$to/$d/"
    done
    rm -rf "$to/bergdb/nanotest"
    find "$to" \( -name '*Tester*.java' -o -name Pack.java -o -name PackForPub.java \) -delete
    python3 -I "$HERE/strip.py" "$to"
    k=$to/bergdb/dag/KeyNode.java
    old='Assert.assertEquals(Klong.TYPE_TIME, Klong.getType(klong));'
    new='if (Klong.getType(klong) != Klong.TYPE_TIME) throw new AssertionError();'
    [ "$(grep -cF "$old" "$k")" = 1 ] || fail "KeyNode's use of Assert is not as expected"
    python3 -I -c 'import sys; p, a, b = sys.argv[1:]; s = open(p).read(); open(p, "w").write(s.replace(a, b))' \
        "$k" "$old" "$new"
}

# javac on the sources $3... into $1, with the class path $2, nothing else.
compile() {
    to=$1 cp=$2
    shift 2
    mkdir -p "$to"
    (cd "$OUT/empty" && javac --release 17 -encoding UTF-8 -nowarn -Xlint:-options \
        -cp "$cp" -sourcepath "$OUT/empty" -implicit:none -d "$to" "$@") \
        > "$to.txt" 2>&1 || { cat "$to.txt"; fail "javac into $to"; }
}

size() {
    wc -c < "$1" | tr -d ' '
}

# Prints the source files of the classes under $1, from the source tree $2.
sources_of() {
    (cd "$1" && find . -name '*.class') | sed 's#^\./##; s#\$.*##; s#\.class$##' | sort -u |
        sed "s#^#$2/#; s#\$#.java#"
}

LAYER=$(python3 -I "$HERE/deps.py" "$SRC" core --list)
PKGS=$(echo "$LAYER" | grep -v '^nanotest$')
mkdir -p "$OUT/empty"

echo "1. The Core Layer without nanotest and test code: $(echo $PKGS)"
copy_stripped "$OUT/src" $PKGS

echo "2. javac, the copy alone"
compile "$OUT/notest" "$OUT/empty" $(find "$OUT/src" -name '*.java')
jar cf "$OUT/bergdb-core-notest.jar" -C "$OUT/notest" .
echo "   $(find "$OUT/src" -name '*.java' | wc -l | tr -d ' ') source files," \
    "$(find "$OUT/notest" -name '*.class' | wc -l | tr -d ' ') classes," \
    "bergdb-core-notest.jar $(size "$OUT/bergdb-core-notest.jar") bytes"

echo "3. javac, what Db and DbBuilder need"
mkdir -p "$OUT/db" "$OUT/db-g-none"
for v in db db-g-none; do
    g=; [ $v = db-g-none ] && g=-g:none
    (cd "$OUT/empty" && javac --release 17 -encoding UTF-8 -nowarn -Xlint:-options $g \
        -cp "$OUT/empty" -sourcepath "$OUT/src" -implicit:class -d "$OUT/$v" \
        "$OUT/src/bergdb/core/Db.java" "$OUT/src/bergdb/core/DbBuilder.java") \
        > "$OUT/javac-$v.txt" 2>&1 || { cat "$OUT/javac-$v.txt"; fail "javac on Db"; }
    jar cf "$OUT/bergdb-core-$v.jar" -C "$OUT/$v" .
done
sources_of "$OUT/db" "$OUT/src" > "$OUT/closure.txt"
echo "   $(wc -l < "$OUT/closure.txt" | tr -d ' ') source files," \
    "$(find "$OUT/db" -name '*.class' | wc -l | tr -d ' ') classes," \
    "bergdb-core-db.jar $(size "$OUT/bergdb-core-db.jar") bytes," \
    "$(size "$OUT/bergdb-core-db-g-none.jar") with -g:none"
jdeps -summary "$OUT/bergdb-core-db.jar" | sed 's/^/   /'

echo "4. CoreDemo on bergdb-core-db.jar alone"
mkdir -p "$OUT/user-db"
javac --release 17 -Xlint:-options -cp "$OUT/bergdb-core-db.jar" -d "$OUT/user-db" \
    "$HERE/CoreDemo.java" "$HERE/CoreSame.java"
java -ea -cp "$OUT/bergdb-core-db.jar:$OUT/user-db" CoreDemo "$OUT/demo-db" > "$OUT/demo.txt" 2>&1 \
    || { cat "$OUT/demo.txt"; fail "CoreDemo"; }
echo "   $(tail -1 "$OUT/demo.txt")"

echo "5. CoreSame on the Core Layer with its tests and on bergdb-core-db.jar"
compile "$OUT/layer" "$OUT/empty" $(for p in $LAYER; do ls "$SRC/bergdb/$(echo $p | tr . /)"/*.java; done)
jar cf "$OUT/bergdb-core.jar" -C "$OUT/layer" .
mkdir -p "$OUT/user-layer"
javac --release 17 -Xlint:-options -cp "$OUT/bergdb-core.jar" -d "$OUT/user-layer" "$HERE/CoreSame.java"
java -ea -cp "$OUT/bergdb-core.jar:$OUT/user-layer" CoreSame "$OUT/same-layer" > "$OUT/same-layer.txt" 2>&1 \
    || { cat "$OUT/same-layer.txt"; fail "CoreSame on bergdb-core.jar"; }
java -ea -cp "$OUT/bergdb-core-db.jar:$OUT/user-db" CoreSame "$OUT/same-db" > "$OUT/same-db.txt" 2>&1 \
    || { cat "$OUT/same-db.txt"; fail "CoreSame on bergdb-core-db.jar"; }
cmp -s "$OUT/same-layer.txt" "$OUT/same-db.txt" \
    || { diff "$OUT/same-layer.txt" "$OUT/same-db.txt"; fail "CoreSame: the two differ"; }
sed 's/^/   both: /' "$OUT/same-db.txt"

echo "6. All of java/src and java/src-icu without test code"
ALL=$(cd "$SRC" && find bergdb -name '*.java' | sed 's#/[^/]*$##' | sort -u | tr / . | sed 's/^bergdb\.//')
copy_stripped "$OUT/all-src" $ALL
compile "$OUT/all" "$ICU" $(find "$OUT/all-src" "$REPO/java/src-icu" -name '*.java')
jar cf "$OUT/bergdb-notest.jar" -C "$OUT/all" .
echo "   $(find "$OUT/all-src" "$REPO/java/src-icu" -name '*.java' | wc -l | tr -d ' ') source files," \
    "$(find "$OUT/all" -name '*.class' | wc -l | tr -d ' ') classes," \
    "bergdb-notest.jar $(size "$OUT/bergdb-notest.jar") bytes; the ICU jar $(size "$ICU") bytes"

echo "7. Lines"
ORIG=$(for p in $LAYER; do ls "$SRC/bergdb/$(echo $p | tr . /)"/*.java; done)
echo "   The Core Layer, with its tests:     $(python3 -I "$HERE/lines.py" $ORIG)"
echo "   The Core Layer, without:            $(python3 -I "$HERE/lines.py" $(find "$OUT/src" -name '*.java'))"
echo "   What Db and DbBuilder need:         $(python3 -I "$HERE/lines.py" $(cat "$OUT/closure.txt"))"
echo "   All, without test code:             $(python3 -I "$HERE/lines.py" \
    $(find "$OUT/all-src" "$REPO/java/src-icu" -name '*.java'))"
echo "   All of java/src, with its tests:    $(python3 -I "$HERE/lines.py" $(find "$SRC" -name '*.java'))"
python3 -I "$HERE/lines.py" --each $(cat "$OUT/closure.txt") | sed "s#$OUT/src/##" > "$OUT/closure-lines.txt"

echo "CORE SIZE OK (output: $OUT)"
