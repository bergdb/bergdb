#!/bin/sh
# The measurements of stored objects, bergdb 020-08, section 7 (step 4): ObjectBench
# (stress/ObjectBench.java) on a reference build and on this tree's build, each run in its
# own JVM, in ABBA order (ref, cand, cand, ref, ref, cand, ...), RUNS JVMs for each build;
# then the median of each figure over its build's runs, and the candidate's ratio to the
# reference. Written 2026-11-09.
#
# Usage: java/stress/objectbench.sh REF [quick|full] [RUNS]
#   REF   the reference's java/ directory, built (REF/build/bergdb.jar): a preserved
#         format-1 build, such as the parent of 0a6d8f4, made outside the repository:
#           mkdir -p DIR && git archive 238b249 java | tar -x -C DIR && sh DIR/java/build.sh
#   quick small sizes, about 10 s a JVM (the default); full: 1,000,000 objects, about 45 s
#         a JVM on F53.
#   RUNS  JVMs for each build: 1 by default with quick, 5 with full (about 8 minutes).
#
# Builds this tree first (build.sh, which compiles ObjectBench against it, for the
# candidate); then compiles ObjectBench again against REF's jar, for the reference, into
# build/objectbench/RUN/ref-classes/: the same source, but for the package of DbObject,
# bergdb.pubimp in a jar from before 020-10's B3 (fcc151b), which moved it to bergdb.pub
# (bergdb 020-12, section 2). Both JVMs get the same flags (JVMFLAGS, by default
# -Xms8g -Xmx8g). Output in build/objectbench/RUN/: each JVM's output, summary.txt. The
# load averages at the start and the end go into the summary: a run on a machine that is
# not quiet is marked so (a measurement for the record needs a quiet machine: nothing else
# running, other sessions' QUIET-BLOCK markers and ps checked first). Set JAVA_HOME or PATH
# for the JDK (java, javac and jar).

cd "$(dirname "$0")/.." || exit 1
REF=$1
MODE=${2:-quick}
if [ -z "$REF" ] || [ ! -f "$REF/build/bergdb.jar" ]; then
    echo "usage: java/stress/objectbench.sh REF [quick|full] [RUNS]; REF/build/bergdb.jar missing"
    exit 2
fi
case "$MODE" in
quick) RUNS=${3:-1} ;;
full) RUNS=${3:-5} ;;
*) echo "mode quick or full, not $MODE"; exit 2 ;;
esac
JAVA=${JAVA:-java}
JAVAC=${JAVAC:-javac}
JARTOOL=${JARTOOL:-jar}
if [ -n "$JAVA_HOME" ]; then
    JAVA=$JAVA_HOME/bin/java
    JAVAC=$JAVA_HOME/bin/javac
    JARTOOL=$JAVA_HOME/bin/jar
fi
JVMFLAGS=${JVMFLAGS:--Xms8g -Xmx8g}

./build.sh > /dev/null || { echo "OBJECTBENCH FAILED: build"; exit 1; }
OUT=build/objectbench/$(date +%Y-%m-%d-%H%M%S)
mkdir -p $OUT/ref-src $OUT/ref-classes
SUMMARY=$OUT/summary.txt

# ObjectBench for the reference, compiled against its jar (see above).
if $JARTOOL tf "$REF/build/bergdb.jar" | grep -q '^bergdb/pub/DbObject\.class$'; then
    REFDBOBJECT=bergdb.pub.DbObject
    cp stress/ObjectBench.java $OUT/ref-src/
else
    REFDBOBJECT=bergdb.pubimp.DbObject
    sed 's/^import bergdb\.pub\.DbObject;$/import bergdb.pubimp.DbObject;/' \
        stress/ObjectBench.java > $OUT/ref-src/ObjectBench.java
fi
$JAVAC --release 17 -Xlint:-options -cp "$REF/build/bergdb.jar" -d $OUT/ref-classes \
    $OUT/ref-src/ObjectBench.java \
    || { echo "OBJECTBENCH FAILED: ObjectBench does not compile against REF's jar"; exit 1; }
{
    echo "ObjectBench, $MODE, $RUNS JVMs a build, $(date '+%Y-%m-%d %H:%M')"
    echo "reference: $REF ($(cat "$REF/../COMMIT.txt" 2>/dev/null | cut -c1-60))"
    echo "reference's ObjectBench: compiled against its jar, DbObject from $REFDBOBJECT"
    echo "candidate: $(git log -1 --format='%h %s' | cut -c1-60)$(git diff --quiet HEAD -- . || echo ', with changes')"
    echo "JDK: $($JAVA -version 2>&1 | head -1); flags: $JVMFLAGS"
    echo "load at the start: $(uptime | sed 's/.*load averages*: //')"
} > $SUMMARY

# run BUILD N: one JVM; BUILD is ref or cand.
run() {
    if [ $1 = ref ]; then
        CP=$REF/build/bergdb.jar:$OUT/ref-classes
    else
        CP=build/bergdb.jar:build/stress
    fi
    echo "  $1 $2"
    $JAVA $JVMFLAGS -cp $CP bergdb.core.ObjectBench $MODE > $OUT/$1-$2.txt 2>&1 \
        || { tail -5 $OUT/$1-$2.txt; echo "OBJECTBENCH FAILED: $1 run $2 (log: java/$OUT/$1-$2.txt)"; exit 1; }
}

i=1
while [ $i -le $RUNS ]; do
    if [ $((i % 2)) = 1 ]; then run ref $i; run cand $i; else run cand $i; run ref $i; fi
    i=$((i + 1))
done

LOAD_END=$(uptime | sed 's/.*load averages*: //')
echo "load at the end: $LOAD_END" >> $SUMMARY
QUIET=yes
for l in $(sed -n 's/^load at the start: //p' $SUMMARY) $LOAD_END; do
    l=$(echo $l | tr -d ,)
    if [ "$(echo "$l > 1.5" | bc)" = 1 ]; then QUIET=no; fi
done
if [ $QUIET = no ]; then
    echo "NOT QUIET: a load average above 1.5; the figures show that the tool works, not the costs" >> $SUMMARY
fi
echo >> $SUMMARY

# The medians: for each figure, its build's values over the runs.
grep -h '^RESULT' $OUT/ref-*.txt | sed 's/^/ref /' > $OUT/all.txt
grep -h '^RESULT' $OUT/cand-*.txt | sed 's/^/cand /' >> $OUT/all.txt
awk '
function median(s,   n, a, i, j, t) {
    n = split(s, a, " ")
    for (i = 1; i <= n; i++) for (j = i + 1; j <= n; j++) if (a[j] + 0 < a[i] + 0) { t = a[i]; a[i] = a[j]; a[j] = t }
    return n % 2 ? a[(n + 1) / 2] : (a[n / 2] + a[n / 2 + 1]) / 2
}
{
    key = $3; vals[$1 "," key] = vals[$1 "," key] " " $4; unit[key] = $5
    if (!(key in seen)) { seen[key] = 1; order[++n] = key }
}
END {
    printf "%-30s %12s %12s %8s  %s\n", "figure", "format 1", "candidate", "ratio", "unit"
    for (i = 1; i <= n; i++) {
        k = order[i]
        r = ("ref," k) in vals ? median(vals["ref," k]) : ""
        c = ("cand," k) in vals ? median(vals["cand," k]) : ""
        ratio = (r != "" && c != "" && r + 0 != 0) ? sprintf("%.2f", c / r) : "-"
        printf "%-30s %12s %12s %8s  %s\n", k, r, c, ratio, unit[k]
    }
}' $OUT/all.txt >> $SUMMARY
cat $SUMMARY
echo "OBJECTBENCH OK: java/$SUMMARY"
