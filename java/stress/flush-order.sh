#!/bin/sh
# Native syscall audit of FlushOrderProbe. This is separate from the simulated
# power-loss gate. macOS needs clang and Python 3; Linux needs strace and Python 3.
set -eu
cd "$(dirname "$0")/.."
JAVA=${JAVA:-java}
if [ -n "${JAVA_HOME:-}" ]; then JAVA="$JAVA_HOME/bin/java"; fi
OUT=${OUT:-build/flush-order}
mkdir -p "$OUT"
if [ ! -f build/bergdb.jar ]; then ./build.sh; fi

case "$(uname -s)" in
    Darwin)
        clang -dynamiclib -O2 -Wall -Wextra stress/native/trace-flush-macos.c -o "$OUT/trace-flush.dylib"
        TRACE=$(cd "$OUT" && pwd)/native.txt
        LIBRARY=$(cd "$OUT" && pwd)/trace-flush.dylib
        BERGDB_FLUSH_TRACE="$TRACE" DYLD_INSERT_LIBRARIES="$LIBRARY" \
            "$JAVA" -ea -cp build/bergdb.jar:build/stress bergdb.stream.FlushOrderProbe > "$OUT/probe.txt" 2>&1
        python3 stress/validate-flush-trace.py "$TRACE"
        ;;
    Linux)
        command -v strace >/dev/null
        strace -f -y -o "$OUT/native.txt" -e trace=openat,write,fsync,fdatasync,unlink,unlinkat \
            "$JAVA" -ea -cp build/bergdb.jar:build/stress bergdb.stream.FlushOrderProbe > "$OUT/probe.txt" 2>&1
        python3 stress/validate-flush-trace.py "$OUT/native.txt" linux
        ;;
    *) echo "Native flush audit unsupported on $(uname -s)" >&2; exit 1 ;;
esac
grep '^FLUSH PROBE OK' "$OUT/probe.txt"
cat "$OUT/probe.txt"
