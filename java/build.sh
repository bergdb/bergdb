#!/bin/sh
# Builds BergDB from this directory (src/, src-dev/, src-icu/) with a current JDK.
# Output: build/bergdb.jar and build/stress/.
# Run tests: java -ea -jar build/bergdb.jar bergdb.dev.Unit
# (also bergdb.dev.F and bergdb.dev.Night, with -cp build/bergdb.jar).

set -e
cd "$(dirname "$0")"

JAVAC=${JAVAC:-javac}
JAR=${JAR:-jar}
SRC=.
ICU=$SRC/in/icu-for-bergdb.jar
OUT=build

# Removes the files this script makes, not the directories: Finder can put a
# .DS_Store in a directory at any time, and removing the directory then fails.
mkdir -p $OUT/classes $OUT/stress
find $OUT/classes $OUT/stress -type f -delete
rm -f $OUT/bergdb.jar $OUT/MANIFEST.MF

$JAVAC --release 8 -encoding UTF-8 -nowarn -Xlint:-options -d $OUT/classes -cp $ICU \
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

# Stress tests, see stress/*.java.
$JAVAC --release 8 -Xlint:-options -cp $OUT/bergdb.jar -d $OUT/stress stress/*.java
echo "Built stress tests in $OUT/stress/"
