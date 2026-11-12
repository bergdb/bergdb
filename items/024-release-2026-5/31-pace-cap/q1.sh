#!/bin/sh
# 024-31 queue 1: main's steady runs at 200 and 1000 MB, for the worst points (pick.py).
cd /Users/f/fl/bench/2026-11-12/pace/w || exit 1
sh slotrun.sh main main-upd-sd200 -Dwb.sd=200000000
sh slotrun.sh main main-upd-sd1000 -Dwb.sd=1000000000
echo "$(date '+%F %T') Q1 DONE" >> out/runs.txt
