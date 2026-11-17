#!/bin/sh
# Bergdb 005-40: what a start does with a stream it cannot read: one of another format,
# or one opened with a wrong crypto key. Compiles the probes against java/build/bergdb.jar
# of this tree (build it first with java/build.sh) and against the 2017 code (0257e0b,
# built here once, as 006-02 builds it), then runs a case.
#
#   run.sh format    FormatProbe: today's code on streams whose version bytes are changed
#   run.sh crypto    FormatProbe: a start with a wrong crypto key, or none, after a crash in
#                    a meta block, then a start with the right key
#   run.sh keys [N]  FormatProbe: N wrong keys (default 2560) at three cuts in a meta block,
#                    each on its own copy; how often the right key then fails
#   run.sh cross     CrossVersion: databases of 2017 started by today's code, and the other
#                    way round, as written and with a torn last record
#   run.sh all [P]   all four, into runs/Pformat.txt, Pcrypto.txt, Pkeys.txt and
#                    Pcross.txt, P a prefix (none for the runs before the fix, after- for
#                    those after it); about 2 minutes on F53
#
# Temporary directories go to PROBE_TMP, or to TMPDIR.

set -e
TOOLS=$(cd "$(dirname "$0")" && pwd)
cd "$TOOLS/../../../.."
OUT=java/build/probe-005-40
T=${PROBE_TMP:-${TMPDIR:-/tmp}}/probe-005-40
OLD=$OUT/2017

build() {
    if [ ! -f $OLD/classes/bergdb/pub/Factory.class ]; then
        rm -rf $OLD
        mkdir -p $OLD/src $OLD/classes
        git archive 0257e0b java | tar -x -C $OLD/src
        j=$OLD/src/java
        javac --release 8 -encoding UTF-8 -nowarn -Xlint:-options -d $OLD/classes \
            -cp $j/in/icu-for-bergdb.jar \
            $(find $j/src $j/src-dev $j/src-icu -name '*.java') > $OLD/javac.log 2>&1
    fi
    mkdir -p $OUT/new $OUT/old
    javac --release 8 -Xlint:-options -nowarn -cp java/build/bergdb.jar -d $OUT/new \
        "$TOOLS/FormatProbe.java" "$TOOLS/CrossVersion.java"
    javac --release 8 -Xlint:-options -nowarn -cp $OLD/classes -d $OUT/old \
        "$TOOLS/CrossVersion.java"
}

NEW_CP=$OUT/new:java/build/bergdb.jar
OLD_CP=$OUT/old:$OLD/classes:$OLD/src/java/in/icu-for-bergdb.jar

new() { java -ea -cp $NEW_CP CrossVersion "$@"; }
old() { java -ea -cp $OLD_CP CrossVersion "$@"; }

format() {
    java -ea -cp $NEW_CP bergdb.core.FormatProbe format
}

crypto() {
    java -ea -cp $NEW_CP bergdb.core.FormatProbe crypto
}

keys() {
    java -ea -cp $NEW_CP bergdb.core.FormatProbe keys ${1:-2560}
}

cross() {
    rm -rf $T
    mkdir -p $T
    echo "Today's code: $(git log -1 --format='%h %s' | cut -c1-60)"
    echo "The 2017 code: 0257e0b (the 2017 import)"
    echo
    echo "X0. 2017 creates, 2017 starts:"
    old create $T/x0 20
    old start $T/x0
    echo "X1. Today's code creates, today's code starts:"
    new create $T/x1 20
    new start $T/x1
    echo "X2. 2017 creates, today's code starts:"
    old create $T/x2 20
    new start $T/x2
    echo "X3. Today's code creates, 2017 starts:"
    new create $T/x3 20
    old start $T/x3
    echo "X4. 2017 creates, the last 10 bytes cut, today's code starts, then 2017:"
    old create $T/x4 20
    old cut $T/x4 10
    new start $T/x4
    old start $T/x4
    echo "X5. Today's code creates, the last 10 bytes cut, 2017 starts, then today's code:"
    new create $T/x5 20
    new cut $T/x5 10
    old start $T/x5
    new start $T/x5
    rm -rf $T
}

build
case "$1" in
    format) format;;
    crypto) crypto;;
    keys) keys "$2";;
    cross) cross;;
    all)
        P=${2:-}
        mkdir -p "$TOOLS/../runs"
        format > "$TOOLS/../runs/${P}format.txt" 2>&1
        crypto > "$TOOLS/../runs/${P}crypto.txt" 2>&1
        keys > "$TOOLS/../runs/${P}keys.txt" 2>&1
        cross > "$TOOLS/../runs/${P}cross.txt" 2>&1
        echo "ALL DONE";;
    *) echo "usage: run.sh format | crypto | keys [N] | cross | all [P]" >&2; exit 2;;
esac
