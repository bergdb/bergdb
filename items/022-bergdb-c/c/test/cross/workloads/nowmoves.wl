bergdb-workload 1
# A "now" that moves a transaction's time (bergdb 012-09, part 1, finding F4; 012-01,
# 4.4): DbClock gives a transaction a time later than the last currentTime's, so a now
# at a clock that has not moved since decides the next transaction's time. Without
# restarts, so that C's bergdb-run runs it whole (012-09 proper); clock.wl has the
# restarts' case (C3). cross.sh runs it in the quick and full sets.

set maxnode 8
set sd 1000
clock 500               # the creation reads it
t 1000 p /a s:1
clock 2000
now                     # 2000, kept as the last read time
t - p /b s:2            # 2001: later than the now (2000 without it)
t - p /c s:3            # 2002
clock 3000
now                     # 3000
now                     # 3000 again
t - p /d s:4 d /a       # 3001
t - p /e s:5            # 3002
t 4000 p /f s:6
t - d /f                # 4001
now                     # 4001: the last transaction's; the clock is behind it
t - p /g s:7            # 4002
t 5000                  # an empty transaction
clock 6000
now                     # 6000
t -                     # 6001, empty
check latest
get latest /a /b /c /d /e /f /g
get 2001 /a /b
