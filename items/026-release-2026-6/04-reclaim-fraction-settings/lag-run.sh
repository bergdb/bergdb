#!/bin/sh
# 026-04: FracRuns work=d with iteration logging. Usage: sh r.sh OUTNAME n=... fs=... [props]
cd /Users/f/fl/bench/2026-11-13/frac/clone/java || exit 1
o=$1; shift
$JAVA_HOME/bin/java -Xmx6g --add-opens java.base/java.util=ALL-UNNAMED -cp build/bergdb.jar:build/stress \
  bergdb.core.FracRuns work=d dir=build/frac-data-$o g4its=1 "$@" > /Users/f/fl/bench/2026-11-13/frac/$o.txt 2>&1
echo "$o exit $? $(date +%H:%M:%S)"
