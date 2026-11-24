#!/bin/sh
# bergdb 028-19: JFR profiles (settings=profile) of CCBench at 10M keys, one kind and size, for
# the builds given, one after the other. Usage: sh prof-cc.sh OUT KIND TSIZE OPS BUILD...
set -u
OUT=$1; KIND=$2; TS=$3; OPS=$4; shift 4
D=$(cd "$(dirname "$0")/.." && pwd)
JAVA=${JAVA:-/opt/homebrew/opt/openjdk/bin/java}
mkdir -p "$OUT"
for b in "$@"; do
    B=$D/$b/java/build
    rm -rf "$OUT/data"
    "$JAVA" -XX:+UseG1GC -da -Xms8g -Xmx8g -Dtranscheck=0 \
        -XX:StartFlightRecording=filename=$OUT/$b-$KIND-$TS.jfr,settings=profile \
        -Dcc.n=10000000 -Dcc.valsize=8 -Dcc.ops=$OPS -Dcc.warm=20000 -Dcc.tsizes=$TS -Dcc.kinds=$KIND \
        -Dcc.dir=$OUT/data -cp $B/cc:$B/stress:$B/bergdb.jar bergdb.core.CCBench > "$OUT/$b-$KIND-$TS.txt" 2>&1
    rm -rf "$OUT/data"
    "$JAVA" -version > /dev/null 2>&1
    jfr=$(dirname "$JAVA")/jfr
    "$jfr" print --json --stack-depth 64 --events jdk.ExecutionSample "$OUT/$b-$KIND-$TS.jfr" > "$OUT/$b-$KIND-$TS.cpu.json"
    "$jfr" print --json --stack-depth 64 --events jdk.ObjectAllocationSample "$OUT/$b-$KIND-$TS.jfr" > "$OUT/$b-$KIND-$TS.alloc.json"
done
