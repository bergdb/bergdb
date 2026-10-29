#!/bin/sh
# Builds the Javadoc of the Pub API: the packages bergdb.pub and
# bergdb.pub.util, with src/overview-pub.html as the overview, as the Pub API
# was defined by build.xml's javadoc target (2015).
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

if $JAVADOC -quiet -Werror -Xdoclint:all,-missing -encoding UTF-8 \
        -d $OUT -sourcepath src -overview src/overview-pub.html \
        -doctitle "BergDB Pub API" -windowtitle "BergDB Pub API" \
        bergdb.pub bergdb.pub.util; then
    echo "JAVADOC PUB OK: $OUT/index.html"
else
    echo "JAVADOC PUB FAILED"
    exit 1
fi
