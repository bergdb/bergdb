#!/bin/sh
# Builds BergDB from this directory (src/, src-dev/, src-icu/) with a current JDK.
# Output:
#   build/bergdb.jar          src, src-dev and ICU; Main-Class bergdb.dev.Run. The jar of
#                             the tests, the level scripts, night.sh and the tools.
#   build/bergdb-release.jar  the jar for users, which a release ships (bergdb 020-10,
#                             section 7): the classes and resources of src only, no
#                             Main-Class; until step B2 of 020-10 removes ICU, also those
#                             of src-icu and ICU (bergdb.icu50).
#   build/stress/             the stress tests.
# Run tests: java -ea -jar build/bergdb.jar bergdb.dev.Unit
# (also bergdb.dev.F and bergdb.dev.Night, with -cp build/bergdb.jar).
#
# Fails unless the release jar passes three checks, about a second in all (files in
# build/release-jar/):
#   1. Its entries are bergdb.jar's but for those in a directory of src-dev (so not
#      bergdb.Help either), none is under bergdb/dev/, bergdb/test/, bergdb/demo/ or
#      frans/, and its manifest has no Main-Class.
#   2. jdeps --missing-deps: every class that it uses is in it or in the JDK.
#   3. stress/release-jar/ReleaseDemo.java, user code compiled and run with the release
#      jar alone on the class path: no class of src-dev; the Pub API's String and byte[]
#      values and Db, through a restart.

set -e
cd "$(dirname "$0")"
HERE=$(pwd)

JAVAC=${JAVAC:-javac}
JAR=${JAR:-jar}
JAVA=${JAVA:-java}
JDEPS=${JDEPS:-jdeps}
SRC=.
ICU=$SRC/in/icu-for-bergdb.jar
OUT=build
REL=$OUT/bergdb-release.jar
CHECK=$OUT/release-jar

# Removes the files this script makes, not the directories: Finder can put a
# .DS_Store in a directory at any time, and removing the directory then fails.
mkdir -p $OUT/classes $OUT/stress $CHECK
find $OUT/classes $OUT/stress $CHECK -type f -delete
rm -f $OUT/bergdb.jar $OUT/MANIFEST.MF $REL

$JAVAC --release 17 -encoding UTF-8 -nowarn -Xlint:-options -d $OUT/classes -cp $ICU \
    $(find $SRC/src $SRC/src-dev $SRC/src-icu -name '*.java')

# Non-Java resources, as in the original build.xml.
for d in src src-dev; do
    (cd $SRC/$d && find . -type f ! -name '*.java' ! -name '*.html') |
        while read f; do
            mkdir -p "$OUT/classes/$(dirname "$f")"
            cp "$SRC/$d/$f" "$OUT/classes/$f"
        done
done

(cd $OUT/classes && unzip -q -o ../../$ICU -x 'META-INF/*')
find $OUT/classes -name .DS_Store -delete
printf 'Main-Class: bergdb.dev.Run\n' > $OUT/MANIFEST.MF
$JAR cfm $OUT/bergdb.jar $OUT/MANIFEST.MF -C $OUT/classes .
echo "Built $OUT/bergdb.jar"

# The release jar (bergdb 020-10, section 7).
release_failed() {
    echo "BUILD FAILED: $REL: $1" >&2
    exit 1
}

# dirs TREE: the directories of the source tree TREE that hold a file, one per line.
dirs() {
    (cd $SRC/$1 && find . -mindepth 2 -type f ! -name .DS_Store) |
        sed -e 's|^\./||' -e 's|/[^/]*$||' | sort -u
}

dirs src-dev > $CHECK/dev-dirs.txt
{ dirs src; dirs src-icu; unzip -Z1 $ICU | grep -v -e '/$' -e '^META-INF/' | sed 's|/[^/]*$||'; } |
    sort -u > $CHECK/release-dirs.txt
SPLIT=$(comm -12 $CHECK/dev-dirs.txt $CHECK/release-dirs.txt | tr '\n' ' ')
if [ -n "$SPLIT" ]; then
    release_failed "a package of src-dev is one of src, src-icu or ICU too: $SPLIT"
fi
# The files of build/classes in those directories, not in their subdirectories.
RELFILES=$(while read d; do
    if [ -d "$OUT/classes/$d" ]; then (cd $OUT/classes && find "$d" -maxdepth 1 -type f); fi
done < $CHECK/release-dirs.txt)
(cd $OUT/classes && $JAR cf "$HERE/$REL" $RELFILES)

# Check 1: the entries and the manifest.
unzip -Z1 $OUT/bergdb.jar | grep -v '/$' |
    awk 'NR == FNR { dev[$0] = 1; next } { d = $0; sub(/\/[^\/]*$/, "", d); if (!(d in dev)) print }' \
        $CHECK/dev-dirs.txt - | sort > $CHECK/expected.txt
unzip -Z1 $REL | grep -v '/$' | sort > $CHECK/entries.txt
if ! cmp -s $CHECK/expected.txt $CHECK/entries.txt; then
    diff $CHECK/expected.txt $CHECK/entries.txt | head -20 >&2
    release_failed "its entries are not bergdb.jar's without src-dev's (<: bergdb.jar, >: it)"
fi
if grep -E '^(bergdb/dev/|bergdb/test/|bergdb/demo/|frans/)' $CHECK/entries.txt > $CHECK/refused.txt; then
    head -5 $CHECK/refused.txt >&2
    release_failed "it holds classes of src-dev"
fi
if unzip -p $REL META-INF/MANIFEST.MF | grep -i '^Main-Class' >&2; then
    release_failed "its manifest has a Main-Class"
fi

# Check 2: jdeps prints each use of a class that is not there.
$JDEPS --missing-deps $REL > $CHECK/jdeps.txt 2>&1 || { cat $CHECK/jdeps.txt >&2; release_failed "jdeps"; }
if [ -s $CHECK/jdeps.txt ]; then
    head -20 $CHECK/jdeps.txt >&2
    release_failed "it uses classes that it does not hold (jdeps --missing-deps)"
fi

# Check 3: user code against it alone.
$JAVA -ea -cp $REL stress/release-jar/ReleaseDemo.java $CHECK/db > $CHECK/demo.txt 2>&1 ||
    { cat $CHECK/demo.txt >&2; release_failed "ReleaseDemo"; }
echo "Built $REL ($(wc -l < $CHECK/entries.txt | tr -d ' ') files): $(tail -1 $CHECK/demo.txt)"

# Stress tests, see stress/*.java.
$JAVAC --release 17 -Xlint:-options -cp $OUT/bergdb.jar -d $OUT/stress stress/*.java
echo "Built stress tests in $OUT/stress/"
