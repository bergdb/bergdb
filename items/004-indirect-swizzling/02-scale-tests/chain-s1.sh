#!/bin/sh
# s1's queue for 004-02 after part A's first session (out/a1, started by hand at 10:24 on
# 2026-10-23): the blocks of plan-s1.sh, then part A a second time, then at 08:00 the next
# morning a third time. Started with nohup; writes out/plan.log, out/a2.log, out/a3.log and
# DONE to out/chain-done.
B=/opt/bergdb-bench
I=$B/item/02-scale-tests
export JAVA_HOME=$B/jdk-27
sh "$I/plan-s1.sh" b c m 1m 10m 30m rep > "$B/out/plan.log" 2>&1 || echo "PLAN FAILED" >> "$B/out/plan.log"
sh "$I/run-a.sh" "$B/out/a2" "$B/bergdb.jar" > "$B/out/a2.log" 2>&1
while [ "$(date +%H)" != "08" ]; do sleep 60; done
sh "$I/run-a.sh" "$B/out/a3" "$B/bergdb.jar" > "$B/out/a3.log" 2>&1
echo DONE > "$B/out/chain-done"
