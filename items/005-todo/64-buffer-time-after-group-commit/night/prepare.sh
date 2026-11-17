#!/bin/sh
# bergdb 005-64: prepares the night's steps by day (run-f53.sh, trickle.sh, run-s1.sh), so that
# they compile nothing. Written 2026-10-28 by Claude (Opus 5.5, Claude Code). Run 2026-10-28 on
# the build main-bf9fc7f (made with: cd CLONE/java && nice -n 10 sh stress/performance.sh build
# main-bf9fc7f; main's HEAD ffb890a, before 007-07).
#
# 1. The harness (PerfUtil, Perf, PerfTool of CLONE/java/stress) compiled into the build, where
#    performance.sh's prepare_target looks for it (harness- and the first 12 hex digits of the
#    SHA-256 of the three files).
# 2. TOOLS = CLONE/java/build/perf/005-64-tools: classes/ (MixedProbe, TrickleProbe, and
#    005-13's ForceProbe, compiled against the build's jar), cpu64.jar (the CPU agent,
#    tools/CpuAgent.java), procstat (005-14's tools/procstat.c, cc -O2).
# 3. The package for s1, CLONE/java/build/perf/005-64-s1-package: performance.sh and the
#    harness sources; the build (identity.env, the jar, the harness compiled); tools/ (the
#    classes, cpu64.jar, table.py); night/ (rounds.sh, s1-runner.sh, the suites and the mixed
#    configurations); builds.env (BUILD, s1's JAVA_HOME, HEAP).
#
# Usage: sh prepare.sh       Environment: CLONE (default /Users/f/fl/bench/006-10/w3), BUILD
#   (default main-bf9fc7f), JAVA_HOME (default /opt/homebrew/opt/openjdk), S1JAVA (default
#   /opt/bergdb-bench/jdk-27), S1HEAP (default 2g: 005-48's a-1k-x100 ran out of 1 GB on s1).
# For another build: performance.sh build LABEL in CLONE/java, then BUILD=LABEL sh prepare.sh,
# and the same BUILD in the environment of the three scripts.

set -u
T=$(cd "$(dirname "$0")" && pwd)
ITEM=$(dirname "$T")
CLONE=${CLONE:-/Users/f/fl/bench/006-10/w3}
BUILD=${BUILD:-main-bf9fc7f}
JAVA_HOME=${JAVA_HOME:-/opt/homebrew/opt/openjdk}
J=$JAVA_HOME/bin
B=$CLONE/java/build/perf/builds/$BUILD
JAR=$B/java/build/bergdb.jar
TOOLS=$CLONE/java/build/perf/005-64-tools
P=$CLONE/java/build/perf/005-64-s1-package
[ -f "$JAR" ] || { echo "prepare.sh: no build $B (performance.sh build $BUILD)"; exit 1; }

# 1. The harness.
S=$CLONE/java/stress
H=harness-$(cd "$S" && cat PerfUtil.java Perf.java PerfTool.java | shasum -a 256 | cut -c1-12)
if [ ! -d "$B/$H" ]; then
    rm -rf "$B/$H.tmp"
    mkdir -p "$B/$H.tmp"
    (cd "$S" && nice -n 10 "$J/javac" --release 17 -Xlint:-options -encoding UTF-8 -cp "$JAR" -d "$B/$H.tmp" \
        PerfUtil.java Perf.java PerfTool.java) || exit 1
    mv "$B/$H.tmp" "$B/$H"
fi

# 2. The tools.
rm -rf "$TOOLS"
mkdir -p "$TOOLS/classes" "$TOOLS/agent"
nice -n 10 "$J/javac" --release 17 -nowarn -cp "$JAR" -d "$TOOLS/classes" \
    "$ITEM/tools/MixedProbe.java" "$ITEM/tools/TrickleProbe.java" "$ITEM/../13-buffer-time/tools/ForceProbe.java" || exit 1
nice -n 10 "$J/javac" --release 17 -nowarn -d "$TOOLS/agent" "$ITEM/tools/CpuAgent.java" || exit 1
printf 'Premain-Class: CpuAgent\n' > "$TOOLS/agent/manifest.txt"
"$J/jar" cfm "$TOOLS/cpu64.jar" "$TOOLS/agent/manifest.txt" -C "$TOOLS/agent" . || exit 1
if [ "$(uname -s)" = Darwin ]; then
    cc -O2 -o "$TOOLS/procstat" "$ITEM/../14-calm-when-idle/tools/procstat.c" || exit 1
fi

# 3. The package for s1.
rm -rf "$P"
mkdir -p "$P/java/stress" "$P/java/build/perf/builds/$BUILD/java/build" "$P/tools" "$P/night"
for f in performance.sh PerfUtil.java Perf.java PerfTool.java; do
    cp "$S/$f" "$P/java/stress/" || exit 1
done
cp "$B/identity.env" "$P/java/build/perf/builds/$BUILD/"
cp "$JAR" "$P/java/build/perf/builds/$BUILD/java/build/"
cp -R "$B/$H" "$P/java/build/perf/builds/$BUILD/"
cp -R "$TOOLS/classes" "$TOOLS/cpu64.jar" "$P/tools/"
cp "$ITEM/tools/table.py" "$P/tools/"
for f in rounds.sh s1-runner.sh bufftime.suite smoke.suite mixed.txt smoke-mixed.txt; do
    cp "$T/$f" "$P/night/" || exit 1
done
printf 'BUILD=%s\nJAVA_HOME=%s\nHEAP=%s\n' "$BUILD" "${S1JAVA:-/opt/bergdb-bench/jdk-27}" "${S1HEAP:-2g}" > "$P/builds.env"
echo "prepared: $H in $B; $TOOLS; $P ($(du -sh "$P" | cut -f1))"
