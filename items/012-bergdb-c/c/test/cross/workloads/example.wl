bergdb-workload 1
# Every kind of line of the workload format (bergdb 012-05, section 6.1), by hand.
# cross.sh runs it in the quick and full sets.

set maxnode 8           # 8, 14, 30 or 62; 30 if not set
set sd 100              # the startup distance (DbBuilder.startupDistance)
set retain 50000000     # the retain duration in time units (5 s), or "forever"
set fraction 0.25       # reclaim's internal fraction
set budget 64000        # the cache budget (cacheSizeIndicator); none: no eviction
clock 500               # the test clock, read by the creation
t 1000 p /k/1 s:v1 p /k/2 x:00ff d /k/3
t 1010 p /big z:300000 p /r r:7:5000
now                     # currentTime(), printed
t - p /k/4 s:v4         # at the clock's time as it is
t 1020                  # an empty transaction
t 1030 p /sp%20ace/%C3%BC s:%23not%20a%20comment p /k/1 s: d /k/2 p /k/2 s:put%20wins
t 1040 p /long/abcdefghijklmnopqrstuvwxyz/1 r:0:100 d /k/4
sync
restart
setsd 400000
setretain forever
setfraction 0.1
setbudget 1000000
check 1005              # the whole state at time 1005, as a digest
check latest
get latest /k/1 /k/2 /k/3 /big
get 1005 /k/1
clock 2000
t 30000000 p /k/5 r:18446744073709551615:9
restart
restart                 # an empty segment: a start and a close
t - p /k/6 s:last
now
check 1
