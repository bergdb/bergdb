#!/bin/sh
# The jcstress tests of bergdb item 009 (items/009-handles/02-implementation-plan.md, 3.5):
# the barriers of the lock-free fast path (3.4, C1 to C5), and a control that shows a race.
# A tool of item 009, not a gate: jcstress is not in BergDB's build.
#
# Usage, from java/: stress/jcstress/run.sh JCSTRESS_DIR [MODE [JAR]]
#   JCSTRESS_DIR  holds jcstress-core-0.16.jar and its dependencies jopt-simple-4.6.jar,
#                 jna-5.8.0.jar and jna-platform-5.8.0.jar (Maven Central:
#                 org.openjdk.jcstress:jcstress-core:0.16).
#   MODE          jcstress's mode: sanity, quick, default (the default here) or tough.
#   JAR           BergDB's jar, build/bergdb.jar by default.
# Writes build/jcstress/: the classes, jcstress's results (results/index.html) and out.txt.
# Prints the tests' verdicts; exits 1 if a test failed.
set -e
D=${1:?JCSTRESS_DIR}
MODE=${2:-default}
JAR=${3:-build/bergdb.jar}
JAR=$(cd "$(dirname "$JAR")" && pwd)/$(basename "$JAR")
CP=$D/jcstress-core-0.16.jar:$D/jopt-simple-4.6.jar:$D/jna-5.8.0.jar:$D/jna-platform-5.8.0.jar
OUT=build/jcstress
rm -rf $OUT
mkdir -p $OUT/classes
javac -nowarn --release 17 -cp "$CP:$JAR" -processorpath "$CP" -d $OUT/classes stress/jcstress/*.java
cd $OUT
java -cp "$CP:classes:$JAR" org.openjdk.jcstress.Main -v -m "$MODE" -t 'bergdb\.jcstress\..*' > out.txt 2>&1 || true
# Each test's outcomes, summed over its runs (jcstress's results/ has them per JVM mode).
sed -n '/^RUN RESULTS:/,$p' out.txt | grep -v "^ *$"
sed -n '/^RUN RESULTS:/,$p' out.txt | grep -A1 -E "Failed tests:|Error tests:" | grep -q -v "No matches\|tests:\|^--\|^ *$" && exit 1
grep -q "^RUN RESULTS:" out.txt
