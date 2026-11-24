#!/bin/sh
# Builds the Javadoc of the Pub API: the packages bergdb.pub and
# bergdb.pub.util, with src/overview-pub.html as the overview, as the Pub API
# was defined by build.xml's javadoc target (2015). The titles name the release
# that src/bergdb/core/BuildInfo.java says (2026-11-24).
#
# Usage: java/javadoc-pub.sh
#   A few seconds.
#
# Output in build/javadoc-pub/; open build/javadoc-pub/index.html. Checks the
# comments with doclint, all groups but "missing" (a member without a comment
# is allowed). Prints JAVADOC PUB OK, or JAVADOC PUB FAILED and exits with
# status 1 on any warning or error. Set JAVA_HOME or PATH for the JDK.

cd "$(dirname "$0")"

JAVADOC=${JAVADOC:-javadoc}
if [ -n "$JAVA_HOME" ]; then JAVADOC=$JAVA_HOME/bin/javadoc; fi

OUT=build/javadoc-pub
rm -rf $OUT

# The release, as BuildInfo says it (such as 2026.6, or 2026.7-dev between releases).
REL=$(sed -n 's/.*String RELEASE = Util\.identity("\([^"]*\)");.*/\1/p' src/bergdb/core/BuildInfo.java)
if [ -z "$REL" ]; then echo "JAVADOC PUB FAILED: no release in BuildInfo.java"; exit 1; fi
TITLE="BergDB $REL Pub API"

if $JAVADOC -quiet -Werror -Xdoclint:all,-missing -encoding UTF-8 \
        -d $OUT -sourcepath src -overview src/overview-pub.html \
        -doctitle "$TITLE" -windowtitle "$TITLE" \
        bergdb.pub bergdb.pub.util; then
    echo "JAVADOC PUB OK: $OUT/index.html"
else
    echo "JAVADOC PUB FAILED"
    exit 1
fi
