#!/bin/sh
# bergdb 005-76: 005-64's harness and rotated rounds, the two affected workloads.
# First: CLONE=REPO BUILD=LABEL sh ../64-buffer-time-after-group-commit/night/prepare.sh
# Usage: BUILD=LABEL sh run-f53.sh
# OUT must be new. The caller waits for correctness tests and other benchmark work to end.
set -eu
T=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$T/../../.." && pwd)
JAVADIR=$ROOT/java
: "${BUILD:?set BUILD to the preserved candidate build}"
JAVA_HOME=${JAVA_HOME:-/opt/homebrew/opt/openjdk}
OUT=${OUT:-$T/runs/f53}
TOOLS=$JAVADIR/build/perf/005-64-tools
HEAP=${HEAP:-8g}
ROUNDS=3
export JAVA_HOME
[ ! -e "$OUT" ] || { echo "OUT already exists: $OUT"; exit 1; }
mkdir -p "$OUT"
JAR=$JAVADIR/build/perf/builds/$BUILD/java/build/bergdb.jar

probe() {
    "$JAVA_HOME/bin/java" -cp "$JAR:$TOOLS/classes" ForceProbe "$OUT/probe-data" 200 \
        > "$OUT/forceprobe-$1.txt" 2>&1
    rm -rf "$OUT/probe-data"
}
probe before
# Let the force probe's I/O settle before performance.sh samples idle CPU.
sleep 30
JAVADIR=$JAVADIR BUILD=$BUILD SUITEF=$T/throughput.suite MIXEDF=$T/mixed.txt \
    ROUNDS=$ROUNDS OUT=$OUT TOOLS=$TOOLS HEAP=$HEAP DEADLINE=0 COOLDOWN=5 FORCE=0 \
    sh "$T/../64-buffer-time-after-group-commit/night/rounds.sh"
probe after
python3 -I "$T/../64-buffer-time-after-group-commit/tools/table.py" \
    --check "$T/throughput.suite" "$T/mixed.txt" "$OUT" > "$OUT/check.txt"
python3 - "$OUT" <<'PY'
import json
from pathlib import Path
import sys
root = Path(sys.argv[1])
rows = []
for path in sorted(root.glob('rounds/r*/*/run*/write.result.json')):
    data = json.loads(path.read_text())
    rows.append({'scenario': path.parts[-3], 'round': int(path.parts[-4][1:]),
                 'metrics': data['metrics'], 'source': str(path)})
(root/'metrics.json').write_text(json.dumps(rows, indent=2) + '\n')
PY
python3 -I "$T/summarize.py" "$OUT/metrics.json" > "$OUT/table.md"
cat "$OUT/check.txt"
echo "005-76 F53 DONE: $OUT/table.md"
