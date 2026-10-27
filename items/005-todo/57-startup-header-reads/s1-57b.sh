#!/bin/sh
# bergdb 005-57 on s1, second run: the prototype with part 2 as well (proto2: the writer's
# reads too), cold starts of both databases, twice; then the time after a cold start: a copy
# of the 50 MB database, the OS cache dropped, a start and 300 transactions of 1,000 random
# updates (they write, so on a copy), for the current code, the prototype and proto2.
# Expects $B/{head,proto,proto2}.jar and $B/cls-{head,proto,proto2}/; writes $B/out/,
# out/DONE2 at the end. Usage, detached: nohup sh s1-57b.sh > s1-57b.log 2>&1 &
set -u
B=/opt/bergdb-bench/005-57
J=/opt/bergdb-bench/jdk-27/bin/java
DATA=/opt/bergdb-bench/007/data
OUT=$B/out
mkdir -p "$OUT"
rm -f "$OUT/DONE2"
log() { echo "$(date '+%F %T') $*" >> "$OUT/runs.txt"; }
cold() { sync; echo 3 > /proc/sys/vm/drop_caches; }
run() {     # run VERSION NAME TAG DIR [JAVA-ARGS...]
    v=$1; name=$2; tag=$3; d=$4; shift 4
    f=$OUT/$name-$v-$tag.txt
    timeout 60m "$J" -Xms2500m -Xmx2500m -XX:+UseZGC -cp "$B/cls-$v:$B/$v.jar" -Dst.dir="$d" \
        -Dst.budget=600000000 -Dst.phases=0 "$@" bergdb.core.StartBench > "$f" 2>&1
    s=$?
    log "$name $v $tag: exit $s; $(grep -o -E '"(startupSec|afterSec)": [0-9.e-]*' "$f" | tr '\n' ' ')"
}
log "start (b); load $(cut -d' ' -f1-3 /proc/loadavg)"
for db in s1-10m-sd50 s1-10m-sd200; do
    for r in 1 2; do
        cold; run proto2 $db cold$r "$DATA/$db"
    done
done
for v in head proto proto2; do
    rm -rf "$B/clone"
    cp -a "$DATA/s1-10m-sd50" "$B/clone"
    cold; run $v s1-10m-sd50 after "$B/clone" -Dst.after=300
done
rm -rf "$B/clone"
log "done (b)"
touch "$OUT/DONE2"
