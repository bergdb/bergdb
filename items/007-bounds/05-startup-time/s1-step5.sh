#!/bin/sh
# 007-05, step 5 of 007-03 on s1: cold startups, after the OS cache is dropped (root).
# Makes two databases of 10M key24 keys (8-byte values) at startup distances of 50 and 200
# MB, with 2M and 3M random updates after the load, then starts each: twice cold (the first
# with the reads counted by phase) and once warm. 1000 MB is left out: D, about 1 GB of
# node bytes at 10M keys (005-38), does not fit s1's 3.8 GB with a heap and an OS cache.
# Started by f53-step5.sh, detached (nohup). Expects /opt/bergdb-bench/007/cls/ and
# bergdb/java/build/bergdb.jar; writes out/, and out/DONE at the end.
set -u
B=/opt/bergdb-bench/007
J=/opt/bergdb-bench/jdk-27/bin/java
CP=$B/cls:$B/bergdb/java/build/bergdb.jar
OUT=$B/out
DATA=$B/data
mkdir -p "$OUT" "$DATA"
rm -f "$OUT/DONE"
log() { echo "$(date '+%F %T') $*" >> "$OUT/runs.txt"; }
cold() { sync; echo 3 > /proc/sys/vm/drop_caches; }
run() {     # run OUTFILE MINUTES JAVA-ARGS...
    f=$1; m=$2; shift 2
    timeout "${m}m" "$J" -cp "$CP" "$@" bergdb.core.StartupBench > "$OUT/$f" 2>&1
    s=$?
    log "$f: exit $s; $(grep -E 'make done|start:' "$OUT/$f" | cut -c1-160)"
    return $s
}
cfg() {     # cfg NAME SD UPDATES
    name=$1; sd=$2; u=$3; d=$DATA/$name
    rm -rf "$d"
    run "$name-make.txt" 200 -Xms2500m -Xmx2500m -XX:+UseParallelGC -Dst.mode=make -Dst.dir="$d" \
        -Dst.keys=10000000 -Dst.sd="$sd" -Dst.updates="$u" -Dst.budget=1200000000 || return
    S="-Xms2500m -Xmx2500m -XX:+UseZGC -Dst.mode=start -Dst.dir=$d -Dst.budget=600000000"
    cold; run "$name-cold1.txt" 120 $S -Dst.phases=1
    cold; run "$name-cold2.txt" 120 $S -Dst.phases=0
    run "$name-warm.txt" 60 $S -Dst.phases=0
}
log "start; load $(cut -d' ' -f1-3 /proc/loadavg)"
cfg s1-10m-sd50 50000000 2000000
cfg s1-10m-sd200 200000000 3000000
log "done"
touch "$OUT/DONE"
