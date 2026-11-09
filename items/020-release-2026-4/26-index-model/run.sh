#!/bin/sh
# bergdb 020-26: runs TLC on IndexModel.tla with a config.
# Usage: sh run.sh CONFIG [WORKERS] [extra TLC options]; the log is logs/CONFIG.log.
# The JDK at /opt/homebrew/opt/openjdk; tla2tools.jar 1.7.4 (SHA-1 bee4a54f...) in tools/.
# XMX sets the heap (default 6g).
cd "$(dirname "$0")"
CFG=$1; shift
W=${1:-3}; [ $# -gt 0 ] && shift
NAME=$(basename "$CFG" .cfg)
mkdir -p logs states
/opt/homebrew/opt/openjdk/bin/java -Xmx${XMX:-6g} -XX:+UseParallelGC -cp tools/tla2tools.jar \
    tlc2.TLC -workers "$W" -metadir "states/$NAME" -config "$CFG" "$@" IndexModel.tla \
    > "logs/$NAME.log" 2>&1
echo "exit $?" >> "logs/$NAME.log"
rm -rf "states/$NAME"
