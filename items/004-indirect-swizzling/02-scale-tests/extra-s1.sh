#!/bin/sh
# s1, 2026-10-23 evening: after part A's second session (out/a2/done), the reads on the
# stopped 30M load (block 18m) and the repeats (block rep), before part A's third session at
# 08:00 (chain-s1.sh). Started with nohup; writes out/extra.log.
B=/opt/bergdb-bench
while [ ! -f "$B/out/a2/done" ]; do sleep 30; done
sh "$B/item/02-scale-tests/plan-s1.sh" 18m rep > "$B/out/extra.log" 2>&1 || echo "EXTRA FAILED" >> "$B/out/extra.log"
echo DONE >> "$B/out/extra.log"
