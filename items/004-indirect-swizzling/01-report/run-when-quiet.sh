#!/bin/sh
# Waits until the machine is quiet (no trace checks, no other JVMs but the editor's,
# 1-minute load below 1.5 for 10 checks in a row, 30 s apart), then reruns item 004's
# measurements. Writes progress to $Q/log.txt and DONE to $Q/done when finished.
Q=/private/tmp/claude-502/-Users-f-fl-repos-f1/378df0a9-ebc3-4ca7-99f5-338ad14c88b7/scratchpad/quiet
R=/Users/f/fl/repos/bergdb/items/004-indirect-swizzling/01-report
export JAVA_HOME=/opt/homebrew/opt/openjdk
busy() {
    ps -Ao args | grep -E "tracecheck|bin/java" | grep -v -E "grep|vscode" | grep -q . && return 0
    l=$(sysctl -n vm.loadavg | awk '{print $2}')
    awk -v l="$l" 'BEGIN { exit !(l >= 1.5) }'
}
echo "waiting from $(date)" > $Q/log.txt
n=0
while [ $n -lt 10 ]; do
    if busy; then n=0; else n=$((n + 1)); fi
    sleep 30
done
echo "quiet at $(date): $(uptime)" >> $Q/log.txt
for t in 1 2 4 8; do
    echo "bench $t start $(uptime)" >> $Q/log.txt
    sh $R/run-bench.sh $Q/bench $t > /dev/null 2>&1
    echo "bench $t end $(uptime)" >> $Q/log.txt
done
echo "census start $(uptime)" >> $Q/log.txt
sh $R/run-census.sh $Q/census > /dev/null 2>&1
echo "census end $(uptime)" >> $Q/log.txt
J=$JAVA_HOME/bin/java
for t in 2 8; do
    echo "census int4 t$t start $(uptime)" >> $Q/log.txt
    $J -Xms8g -Xmx8g -Dkeys=1000000 -Dkeytype=int4 -Dvalsize=8 -Dthreads=$t -Dupdates=0 \
        -cp /Users/f/fl/repos/bergdb/java/build/bergdb.jar:$Q/census/classes \
        bergdb.core.IndexCensus > $Q/census/census-int4-t$t.txt 2>&1
    echo "census int4 t$t end $(uptime)" >> $Q/log.txt
done
echo DONE > $Q/done
