bergdb-workload 1
# The clock's rules, by hand (bergdb 012-09, part 1; 012-01, 4.4; 012-02, 8.1): a
# transaction's time is later than the last transaction's and the last currentTime's,
# so a "now" moves the next transaction's time when the clock has not moved since; a
# start forgets the last currentTime (012-02, 10.3, C3; 005-71). cross.sh runs it in
# the quick and full sets; test/cross/writecheck.sh replays its times on C's DbClock.

set maxnode 8
set sd 1000
clock 500               # the creation reads it
t 1000 p /a s:1
clock 2000
now                     # 2000, kept as the last read time
t - p /b s:2            # 2001: later than the now
t - p /c s:3            # 2002
clock 3000
now                     # 3000
restart                 # C3: the last read time is 0 after the start
t - p /d s:4            # 3000, not 3001
now                     # 3000
t - p /e s:5            # 3001
t 4000 p /f s:6
t - d /f                # 4001
now                     # 4001: the last transaction's; the clock is behind it
t 5000                  # an empty transaction
clock 6000
now
restart
restart                 # an empty segment: a start and a close
t - p /g s:7            # 6000: the now before the restarts is forgotten
