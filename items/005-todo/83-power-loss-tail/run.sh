#!/bin/sh
# Reproduce bergdb 005-83's tail experiment against a frozen committed Java tree.
# Usage: sh run.sh OUTDIR [case-substring]
# Optional: BASE_REF (default 3ad171d), REQUIRE_RECOVERY=true, FIXTURE_DIR, JAVA, JAVAC.
# No production files are edited. REQUIRE_RECOVERY makes known hole failures exit 1.
set -eu
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
ROOT=$(CDPATH= cd -- "$HERE/../../.." && pwd)
OUT=$1
FILTER=${2:-}
BASE_REF=${BASE_REF:-3ad171d}
JAVA=${JAVA:-java}
JAVAC=${JAVAC:-javac}
[ ! -e "$OUT" ] || { echo "Refusing existing OUTDIR: $OUT" >&2; exit 2; }
mkdir -p "$OUT/source" "$OUT/classes"
OUT=$(CDPATH= cd -- "$OUT" && pwd)
git -C "$ROOT" rev-parse "$BASE_REF" > "$OUT/source-commit.txt"
git -C "$ROOT" archive "$BASE_REF" java > "$OUT/source.tar"
tar -xf "$OUT/source.tar" -C "$OUT/source"
rm "$OUT/source.tar"
"$OUT/source/java/build.sh" > "$OUT/build.txt" 2>&1
cp "$HERE/PowerLossTailProbe.java" "$OUT/PowerLossTailProbe.java"
cp "$HERE/RefusedStartProbe.java" "$OUT/RefusedStartProbe.java"
cp "$HERE/analyze.py" "$OUT/analyze.py"
cp "$HERE/run.sh" "$OUT/run-used.sh"
"$JAVAC" --release 17 -encoding UTF-8 -cp "$OUT/source/java/build/bergdb.jar" \
    -d "$OUT/classes" "$OUT/PowerLossTailProbe.java" "$OUT/RefusedStartProbe.java"
"$JAVA" -version > "$OUT/java-version.txt" 2>&1
shasum -a 256 "$OUT/source/java/build/bergdb.jar" "$OUT/PowerLossTailProbe.java" \
    "$OUT/RefusedStartProbe.java" "$OUT/analyze.py" "$OUT/run-used.sh" \
    > "$OUT/artifacts.sha256"
status=0
"$JAVA" -ea -Xmx256m -DrequireRecovery="${REQUIRE_RECOVERY:-false}" \
    -cp "$OUT/classes:$OUT/source/java/build/bergdb.jar" \
    bergdb.core.PowerLossTailProbe "$OUT/probe" "$FILTER" > "$OUT/probe.txt" 2>&1 || status=$?
python3 "$OUT/analyze.py" "$OUT/probe" > "$OUT/analysis.txt"
if [ -n "${FIXTURE_DIR:-}" ]; then
    "$JAVA" -ea -Xmx256m -cp "$OUT/classes:$OUT/source/java/build/bergdb.jar" \
        bergdb.core.RefusedStartProbe "$FIXTURE_DIR" "$OUT/refused-start-copy" \
        > "$OUT/refused-start.txt" 2>&1
fi
grep '^PROBE COMPLETE ' "$OUT/probe.txt"
exit "$status"
