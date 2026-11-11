#!/bin/sh
# T7's runner with a heap of its own (bergdb 024-07): HEAP=512m t7h.sh VARIANT CMD args...
# As t7.sh but for the heap: for the case of section 3, the nodes that the last touch pins.
B=/Users/f/fl/bench/2026-11-11/touch
V=$1; shift
H=${HEAP:-8g}
exec /opt/homebrew/opt/openjdk/bin/java -Xms$H -Xmx$H -XX:+UseG1GC -cp $B/c$V:$B/$V.jar bergdb.core.T7 "$@"
