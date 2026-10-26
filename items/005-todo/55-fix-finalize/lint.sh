#!/bin/sh
# Lists the uses of deprecated API in BergDB's Java code (bergdb 005-55): compiles src,
# src-dev and src-icu as java/build.sh does, but with -Xlint:deprecation,removal instead
# of -nowarn, at --release 17 (build.sh's) and at --release 27, into a temporary directory.
# Usage: lint.sh JAVA OUT; JAVA is a java/ directory, OUT a directory for the two lists.
set -e
JAVA=$(cd "$1" && pwd)
OUT=$2
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)
CLASSES=$(mktemp -d)
cd "$JAVA"
for r in 17 27; do
    javac --release $r -encoding UTF-8 -Xlint:-options -Xlint:deprecation,removal \
        -Xmaxwarns 1000 -d "$CLASSES" -cp in/icu-for-bergdb.jar \
        $(find src src-dev src-icu -name '*.java') > "$OUT/lint-release$r.txt" 2>&1 || true
    echo "--release $r: $(grep -c 'warning:' "$OUT/lint-release$r.txt") warnings"
done
rm -rf "$CLASSES"
