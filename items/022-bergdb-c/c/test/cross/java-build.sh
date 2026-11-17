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
# Which Java (bergdb 015-02, 022-01, 022-02): C matches a release of BergDB,
# not the Java of the day (Frans, 2026-11-05). JAVA_REF chooses the Java tree:
#   JAVA_REF=2026.4    the default since 022-07: release 2026.4 as released (tag
#                      release-2026.4, record format 6): the java/ of
#                      releases/2026.4/bergdb-2026.4-src.zip, checked against
#                      releases/2026.4/SHA256SUMS and extracted once into
#                      build/java-src/bergdb-2026.4/java/
#   JAVA_REF=git:HASH  the java/ of the commit HASH in this repository's Git: its
#                      java/src, java/stress and java/deps.py by git archive, as
#                      a release's source zip holds them, extracted once into
#                      build/java-src/git-HASH/java/. Until 2026.4's tag the
#                      default was the release candidate of 2026.4, main at
#                      d00096e, 2026-11-09 18:42 (bergdb 022-02 and 022-04; record
#                      format 5, which C no longer writes or reads):
#                      git:d00096e4d4a423dd36622617d32d0dc5ee00bf6a
#   JAVA_REF=2026.3    the release of the 2026.3 port (bergdb 022-01), the same
#                      way. The harness's CorruptSet.java does not compile
#                      against it (CorruptStreamTester.Config takes the keys
#                      since 021-11); int.git's branch 022 keeps 2026.3's harness
#   JAVA_REF=REL       another release in releases/REL/ the same way: 2026.2,
#                      the release of 012's port (bergdb 015-02), which has no
#                      CorruptStreamTester for CorruptSet.java (022-01, step 4)
#   JAVA_REF=tree      the repository's java/, as it is in the working tree
#   JAVA_REF=DIR       the java/ directory DIR (holding src/, stress/, deps.py)
# The classes are made again at every run. build/java/java-dir.txt names the
# tree compiled and build/java/java-ref.txt the choice, for the other scripts
# (examples/compare.sh takes CoreDemo.java from the same tree).
#
# Usage: test/cross/java-build.sh      (from any directory)
# Then:  java -ea -cp build/java/classes bergdb.core.StreamScan ...
# Needs a JDK (JAVA_HOME or PATH), python3, and unzip and shasum for a
# release, git and tar for a commit. Prints JAVA BUILD OK.

set -e
C=$(cd "$(dirname "$0")/../.." && pwd)
REPO=$(cd "$C/../../.." && pwd)
REF=${JAVA_REF:-2026.4}
case "$REF" in
tree)
    JAVA=$REPO/java ;;
/*|./*|../*)
    JAVA=$(cd "$REF" && pwd) ;;
git:*)
    H=${REF#git:}
    SRC=$C/build/java-src
    JAVA=$SRC/git-$H/java
    if [ ! -f "$SRC/git-$H.complete" ]; then
        FULL=$(git -C "$REPO" rev-parse -q --verify "$H^{commit}") \
            || { echo "no commit $H in $REPO's Git; fetch it, as: git fetch /Users/f/fl/repos/bergdb main:refs/remotes/repo/main"
                 echo "JAVA BUILD FAILED"; exit 1; }
        rm -rf "$SRC/git-$H" "$SRC/git-$H.tar"
        mkdir -p "$SRC/git-$H"
        git -C "$REPO" archive -o "$SRC/git-$H.tar" "$FULL" java/src java/stress java/deps.py
        tar -x -f "$SRC/git-$H.tar" -C "$SRC/git-$H"
        rm -f "$SRC/git-$H.tar"
        echo "$FULL" > "$SRC/git-$H/commit.txt"
        : > "$SRC/git-$H.complete"
    fi ;;
*)
    ZIP=$REPO/releases/$REF/bergdb-$REF-src.zip
    SRC=$C/build/java-src
    JAVA=$SRC/bergdb-$REF/java
    if [ ! -f "$SRC/bergdb-$REF.complete" ]; then
        [ -f "$ZIP" ] || { echo "no $ZIP"; echo "JAVA BUILD FAILED"; exit 1; }
        (cd "$REPO/releases/$REF" && grep " bergdb-$REF-src.zip\$" SHA256SUMS \
            | shasum -a 256 -c -) > /dev/null \
            || { echo "$ZIP does not match its SHA256SUMS"; echo "JAVA BUILD FAILED"; exit 1; }
        rm -rf "$SRC/bergdb-$REF"
        mkdir -p "$SRC"
        unzip -q -o "$ZIP" "bergdb-$REF/java/src/*" "bergdb-$REF/java/stress/*" \
            "bergdb-$REF/java/deps.py" -d "$SRC"
        : > "$SRC/bergdb-$REF.complete"
    fi ;;
esac
[ -d "$JAVA/src/bergdb" ] || { echo "no Java tree at $JAVA"; echo "JAVA BUILD FAILED"; exit 1; }
if [ -n "$JAVA_HOME" ]; then PATH=$JAVA_HOME/bin:$PATH; fi
OUT=$C/build/java

rm -rf "$OUT/classes" "$OUT/empty" "$OUT/java-dir.txt" "$OUT/java-ref.txt"
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
echo "$JAVA" > "$OUT/java-dir.txt"
echo "$REF" > "$OUT/java-ref.txt"
echo "JAVA BUILD OK: $(wc -l < "$OUT/sources.txt" | tr -d ' ') source files of Java $REF ($JAVA) into build/java/classes"
