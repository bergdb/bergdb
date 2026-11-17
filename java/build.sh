#!/bin/sh
# Builds BergDB from this directory (src/, src-dev/) with a current JDK.
# Output:
#   build/bergdb.jar          src and src-dev; Main-Class bergdb.dev.Run. The jar of the
#                             tests, the level scripts, night.sh and the tools.
#   build/bergdb-release.jar  the jar for users, which a release ships (bergdb 020-10,
#                             section 7): the classes and resources of src only, no
#                             Main-Class. Neither jar has ICU since 020-10's step B2.
# Both jars hold META-INF/LICENSE and META-INF/NOTICE, the repository's (Apache-2.0); a
# copy of java/ alone, as stress/performance.sh builds, has no ../LICENSE, and its jars
# have neither.
# Both jars seal the packages bergdb.pub and bergdb.pubimp (the review of 020-10's B3): no
# class of another jar or directory joins them, so none outside BergDB extends DbValue or
# reads their package-private members. A probe in one of them runs with build/classes on
# the class path, not a jar.
#   build/stress/             the stress tests.
# Run tests: java -ea -jar build/bergdb.jar bergdb.dev.Unit
# (also bergdb.dev.F and bergdb.dev.Night, with -cp build/bergdb.jar).
#
# Fails unless the release jar passes three checks, about a second in all (files in
# build/release-jar/):
#   1. Its entries are bergdb.jar's but for those in a directory of src-dev (so not
#      bergdb.Help either), none is under bergdb/dev/, bergdb/test/, bergdb/demo/,
#      frans/, bergdb/icu50/ or bergdb/pubimpicu/ (ICU's, gone), its manifest has no
#      Main-Class and seals bergdb/pub/ and bergdb/pubimp/, and its META-INF/LICENSE and
#      META-INF/NOTICE are the repository's (if ../LICENSE is there).
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
OUT=build
REL=$OUT/bergdb-release.jar
CHECK=$OUT/release-jar
LEGAL=$OUT/legal

# Removes the files this script makes, not the directories: Finder can put a
# .DS_Store in a directory at any time, and removing the directory then fails.
mkdir -p $OUT/classes $OUT/stress $CHECK $LEGAL/META-INF
find $OUT/classes $OUT/stress $CHECK $LEGAL -type f -delete
rm -f $OUT/bergdb.jar $OUT/MANIFEST.MF $OUT/RELEASE-MANIFEST.MF $REL

$JAVAC --release 17 -encoding UTF-8 -nowarn -Xlint:-options -d $OUT/classes -cp $OUT/classes \
    $(find $SRC/src $SRC/src-dev -name '*.java')

# Non-Java resources, as in the original build.xml.
for d in src src-dev; do
    (cd $SRC/$d && find . -type f ! -name '*.java' ! -name '*.html') |
        while read f; do
            mkdir -p "$OUT/classes/$(dirname "$f")"
            cp "$SRC/$d/$f" "$OUT/classes/$f"
        done
done

find $OUT/classes -name .DS_Store -delete
SEALED='Name: bergdb/pub/\nSealed: true\n\nName: bergdb/pubimp/\nSealed: true\n'
printf "Main-Class: bergdb.dev.Run\n\n$SEALED" > $OUT/MANIFEST.MF
printf "Manifest-Version: 1.0\n\n$SEALED" > $OUT/RELEASE-MANIFEST.MF
LEGALFILES=
if [ -f ../LICENSE ]; then
    cp ../LICENSE ../NOTICE $LEGAL/META-INF/
    LEGALFILES="-C $HERE/$LEGAL META-INF/LICENSE -C $HERE/$LEGAL META-INF/NOTICE"
fi
$JAR cfm $OUT/bergdb.jar $OUT/MANIFEST.MF -C $OUT/classes . $LEGALFILES
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
dirs src > $CHECK/release-dirs.txt
SPLIT=$(comm -12 $CHECK/dev-dirs.txt $CHECK/release-dirs.txt | tr '\n' ' ')
if [ -n "$SPLIT" ]; then
    release_failed "a package of src-dev is one of src too: $SPLIT"
fi
# The files of build/classes in those directories, not in their subdirectories.
RELFILES=$(while read d; do
    if [ -d "$OUT/classes/$d" ]; then (cd $OUT/classes && find "$d" -maxdepth 1 -type f); fi
done < $CHECK/release-dirs.txt)
(cd $OUT/classes && $JAR cfm "$HERE/$REL" "$HERE/$OUT/RELEASE-MANIFEST.MF" $RELFILES $LEGALFILES)

# Check 1: the entries and the manifest.
unzip -Z1 $OUT/bergdb.jar | grep -v '/$' |
    awk 'NR == FNR { dev[$0] = 1; next } { d = $0; sub(/\/[^\/]*$/, "", d); if (!(d in dev)) print }' \
        $CHECK/dev-dirs.txt - | sort > $CHECK/expected.txt
unzip -Z1 $REL | grep -v '/$' | sort > $CHECK/entries.txt
if ! cmp -s $CHECK/expected.txt $CHECK/entries.txt; then
    diff $CHECK/expected.txt $CHECK/entries.txt | head -20 >&2
    release_failed "its entries are not bergdb.jar's without src-dev's (<: bergdb.jar, >: it)"
fi
REFUSED='^(bergdb/dev/|bergdb/test/|bergdb/demo/|frans/|bergdb/icu50/|bergdb/pubimpicu/)'
if grep -E "$REFUSED" $CHECK/entries.txt > $CHECK/refused.txt; then
    head -5 $CHECK/refused.txt >&2
    release_failed "it holds classes of src-dev, or of ICU, which 020-10's B2 removed"
fi
if unzip -p $REL META-INF/MANIFEST.MF | grep -i '^Main-Class' >&2; then
    release_failed "its manifest has a Main-Class"
fi
for d in pub pubimp; do
    if ! unzip -p $REL META-INF/MANIFEST.MF | tr -d '\r' |
            awk -v n="Name: bergdb/$d/" '$0 == n { s = 1; next } s && /^Sealed: true$/ { f = 1 }
                /^$/ { s = 0 } END { exit !f }'; then
        release_failed "its manifest does not seal bergdb/$d/"
    fi
done
if [ -n "$LEGALFILES" ]; then
    for f in LICENSE NOTICE; do
        unzip -p $REL META-INF/$f | cmp -s - ../$f || release_failed "its META-INF/$f is not ../$f"
    done
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
