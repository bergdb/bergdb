#!/bin/sh
# 028-12: one TakeBytesProbe run. Usage: run.sh NAME HEAP [-Dtb.x=y ...]
# Needs $W/clone/java/build/bergdb.jar (java/build.sh) and the probe compiled into $W/cls:
#   javac -d $W/cls -cp $W/clone/java/build/bergdb.jar TakeBytesProbe.java
# Output: $W/out/NAME.txt. Takes one heavy-run slot for the run (counts, not timing).
W=${W:-/Users/f/fl/bench/2026-11-13/takebytes}
name=$1; heap=$2; shift 2
cd "$W" || exit 1
mkdir -p out
slot=$(sh /Users/f/fl/bench/2026-11-11/slot.sh take takebytes "028-12 probe $name")
echo "$(date '+%F %T') start $name: $*" >> out/runs.txt
nice -n 10 java -Xms$heap -Xmx$heap -XX:+UseParallelGC -cp cls:clone/java/build/bergdb.jar "$@" \
    bergdb.core.TakeBytesProbe > out/$name.txt 2>&1
sh /Users/f/fl/bench/2026-11-11/slot.sh release $slot
echo "$(date '+%F %T') end $name: $(tail -1 out/$name.txt)" >> out/runs.txt
