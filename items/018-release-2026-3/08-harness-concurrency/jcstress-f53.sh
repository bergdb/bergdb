#!/bin/sh
# Harness 6.6 (bergdb 018-08, section 4): the eight jcstress tests of java/stress/jcstress/ in
# jcstress's default mode on F53, on main's committed code at the time it starts. Run by
# chain.sh after night.sh large, or by hand: sh /Users/f/fl/bench/006-13/night/jcstress-f53.sh
# 2026-11-06, agent j66 of coord-1106.
#
# 1. Waits, up to 20 minutes, while a QUIET-BLOCK marker other than q1's exists (q1's block-q.sh
#    waits for this run by its quiet check, so its marker does not hold this one back); then skips.
# 2. Clones /Users/f/fl/repos/bergdb (its committed HEAD) into OUT/repo and builds the jar.
# 3. Runs java/stress/jcstress/run.sh in default mode with JDK 27 (the PATH) and 016-08's jars,
#    under a limit of 40 minutes (about 5 to 10 minutes expected on F53's 10 cores).
# OUT=/Users/f/fl/bench/006-13/night/jcstress-f53: repo/, out.txt (jcstress's output),
# results.txt (its RUN RESULTS), run.txt (run.sh's), summary.txt. The last line printed is the
# one-line summary.
# Test: SMOKE=1 runs step 3 as jcstress's sanity mode on PlainPublication only, on 2 CPUs
# (-c 2), in OUT-smoke, without the wait of step 1.
OUT=/Users/f/fl/bench/006-13/night/jcstress-f53
LIB=/Users/f/fl/bench/016/jcstress-lib
SMOKE=${SMOKE:-0}
[ "$SMOKE" = 1 ] && OUT=$OUT-smoke
export PATH=/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin:$PATH
summary() { echo "$*" > $OUT/summary.txt; echo "$*"; }
rm -rf $OUT
mkdir -p $OUT
echo "start $(date '+%F %T')"

if [ "$SMOKE" != 1 ]; then
    i=0
    while :; do
        m=$(ls /Users/f/fl/bench/quiet-block-*/QUIET-BLOCK /Users/f/fl/bench/coord/*/QUIET-BLOCK \
            2>/dev/null | grep -v -- '-q1/QUIET-BLOCK$')
        [ -z "$m" ] && break
        if [ $i -ge 40 ]; then
            summary "JCSTRESS F53 SKIPPED: marker $m still there after 20 minutes"; exit 3
        fi
        echo "$(date '+%T') waiting for $m"; i=$((i + 1)); sleep 30
    done
fi

git clone -q /Users/f/fl/repos/bergdb $OUT/repo || { summary "JCSTRESS F53 ERROR: clone failed"; exit 2; }
cd $OUT/repo/java || exit 2
C=$(git rev-parse --short HEAD)
echo "commit $C, $(java -version 2>&1 | head -1)"
sh build.sh > $OUT/build.txt 2>&1 || { summary "JCSTRESS F53 ERROR: build of $C failed"; exit 2; }

T0=$(date +%s)
if [ "$SMOKE" = 1 ]; then
    CP=$LIB/jcstress-core-0.16.jar:$LIB/jopt-simple-4.6.jar:$LIB/jna-5.8.0.jar:$LIB/jna-platform-5.8.0.jar
    mkdir -p build/jcstress/classes
    javac -nowarn --release 17 -cp "$CP:build/bergdb.jar" -processorpath "$CP" \
        -d build/jcstress/classes stress/jcstress/*.java > $OUT/run.txt 2>&1
    (cd build/jcstress && timeout 300 java -cp "$CP:classes:../bergdb.jar" org.openjdk.jcstress.Main \
        -v -m sanity -c 2 -t 'bergdb\.jcstress\.PlainPublication' > out.txt 2>&1)
    RC=$?
else
    timeout 2400 sh stress/jcstress/run.sh $LIB default > $OUT/run.txt 2>&1
    RC=$?
fi
T=$(( ($(date +%s) - T0) / 60 ))
cp build/jcstress/out.txt $OUT/out.txt 2>/dev/null
echo "end $(date '+%F %T'), exit $RC, $T minutes"
sed -n '/^RUN RESULTS:/,$p' $OUT/out.txt > $OUT/results.txt 2>/dev/null
grep -E '\[(OK|FAILED|ERROR)\] bergdb' $OUT/results.txt
N=$(grep -c -E '\[OK\] bergdb' $OUT/results.txt)
F=$(grep -c -E '\[(FAILED|ERROR)\] bergdb' $OUT/results.txt)
if [ $RC = 124 ]; then
    summary "JCSTRESS F53 ERROR: stopped after 40 minutes on $C ($N OK so far, $F failed); $OUT"
elif [ $RC = 0 ] && [ $F = 0 ] && [ $N -gt 0 ]; then
    summary "JCSTRESS F53 OK: $N tests [OK], none failed, on $C, $T minutes; $OUT/out.txt"
else
    summary "JCSTRESS F53 FAILED: exit $RC, $N OK, $F failed or in error, on $C; see $OUT/out.txt"
fi
[ $F = 0 ] && [ $RC = 0 ]
