#!/bin/sh
# The Level 3 soak (bergdb 011-06, task 2; bergdb item 001, WP P2), written
# 2026-10-16. Runs java/stress/Soak.java in one JVM with fixed flags (G1, or ZGC as a
# separate configuration; a fixed heap, not pretouched; assertions off; unified GC and
# safepoint logging, as performance.sh), then "Soak finish" on its result.
#
# Usage: java/stress/soak.sh NAME [PROP=VALUE ...]
#   NAME   The run: java/build/soak/NAME/ (it must not exist). PROPs are Soak's soak.*
#          properties without the prefix, for example n=20000 measure=600.
#
# The run directory gets a copy of the build (bin/), so that build.sh may run meanwhile
# (it deletes java/build/classes and java/build/stress, not java/build/soak), the disposable
# data directory (data/, with Soak's marker file; deleted at the end unless KEEPDATA=1),
# source.txt (commit, changed files, jar, JVM, flags, machine, start), stdout.txt (the
# progress), gc.log and result.json. Do not run the gates, performance.sh or a full Lean
# build during a measured run (bergdb item 001, plan 2.7). Exit code: Soak's (0: SOAK OK).
#
# Environment: JAVA_HOME (the JDK; the PATH's otherwise), HEAP=12g (-Xms and -Xmx), GC=g1|zgc,
# KEEPDATA=1, JFLAGS="..." (extra JVM flags, recorded in source.txt: for example
# -Devictbudget=N, the capacity controller's budget in bytes, bergdb item 001, WP P4; Soak's
# database is built with noEvict(), so without it nothing is evicted). Needs java/build
# (java/build.sh).

cd "$(dirname "$0")/.." || exit 1
JAVADIR=$(pwd)
ROOT=$(cd .. && pwd)

NAME=$1
[ -n "$NAME" ] || { echo "usage: $0 NAME [PROP=VALUE ...]"; exit 2; }
shift
case $NAME in
    */*|.*) echo "soak.sh: NAME is a plain name"; exit 2 ;;
esac

if [ -n "${JAVA_HOME:-}" ]; then JAVA=$JAVA_HOME/bin/java; else JAVA=${JAVA:-java}; fi
HEAP=${HEAP:-12g}
GC=${GC:-g1}
case $GC in
    g1) GCFLAGS="-XX:+UseG1GC" ;;
    zgc) GCFLAGS="-XX:+UseZGC" ;;
    *) echo "soak.sh: GC must be g1 or zgc"; exit 2 ;;
esac

RUN=$JAVADIR/build/soak/$NAME
[ -e "$RUN" ] && { echo "soak.sh: $RUN exists (choose another name)"; exit 2; }
[ -f build/bergdb.jar ] && [ -f build/stress/bergdb/core/Soak.class ] \
    || { echo "soak.sh: no build (run java/build.sh)"; exit 2; }
mkdir -p "$RUN/bin" "$RUN/data" || exit 1
cp build/bergdb.jar "$RUN/bin/" && cp -R build/stress "$RUN/bin/stress" || exit 1

{
    echo "name $NAME"
    echo "commit $(git -C "$ROOT" rev-parse HEAD 2>/dev/null)"
    echo "changed files (java/src, java/src-dev, java/stress):"
    git -C "$ROOT" status --porcelain -- java/src java/src-dev java/stress 2>/dev/null | sed 's/^/  /'
    echo "jar sha256 $(shasum -a 256 "$RUN/bin/bergdb.jar" | cut -d' ' -f1)"
    echo "java $JAVA: $("$JAVA" -version 2>&1 | tr '\n' ' ')"
    echo "flags $GCFLAGS -da -Xms$HEAP -Xmx$HEAP -Xlog:gc*,safepoint:file=gc.log:uptime,level,tags${JFLAGS:+ $JFLAGS}"
    echo "properties $*"
    echo "machine $(sysctl -n hw.model 2>/dev/null) $(sysctl -n machdep.cpu.brand_string 2>/dev/null)," \
        "$(sysctl -n hw.ncpu 2>/dev/null) cores, $(sysctl -n hw.memsize 2>/dev/null) bytes," \
        "$(sw_vers -productVersion 2>/dev/null)"
    echo "disk free $(df -k "$RUN" | awk 'NR==2 {printf "%.0f GB", $4/1048576}')"
    echo "started $(date '+%Y-%m-%d %H:%M:%S %Z')"
} > "$RUN/source.txt"

PROPS=
for p in "$@"; do
    case $p in
        *=*) PROPS="$PROPS -Dsoak.$p" ;;
        *) echo "soak.sh: not PROP=VALUE: $p"; exit 2 ;;
    esac
done

CP=$RUN/bin/bergdb.jar:$RUN/bin/stress
# shellcheck disable=SC2086
"$JAVA" $GCFLAGS -da "-Xms$HEAP" "-Xmx$HEAP" "-Xlog:gc*,safepoint:file=$RUN/gc.log:uptime,level,tags" ${JFLAGS:-} \
    "-Dsoak.out=$RUN" "-Dsoak.dir=$RUN/data" $PROPS \
    -cp "$CP" bergdb.core.Soak > "$RUN/stdout.txt" 2>&1
rc=$?
echo "ended $(date '+%Y-%m-%d %H:%M:%S %Z'), exit code $rc" >> "$RUN/source.txt"
if [ -f "$RUN/result.json" ]; then
    "$JAVA" -cp "$CP" bergdb.core.Soak finish "$RUN" >> "$RUN/stdout.txt" 2>&1
fi
if [ "${KEEPDATA:-0}" != 1 ]; then
    find "$RUN/data" -type f -delete && rmdir "$RUN/data"
fi
grep -E "^(SOAK|FAILURE|FINISH)" "$RUN/stdout.txt"
exit $rc
