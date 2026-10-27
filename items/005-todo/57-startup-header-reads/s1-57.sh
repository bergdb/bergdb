#!/bin/sh
# bergdb 005-57 on s1: cold starts of 007-05's two databases (10M key24 keys, 8-byte values,
# startup distances of 50 and 200 MB, in /opt/bergdb-bench/007/data) with release 2026.1's
# jar (rel), the current code (head) and the prototype, rule 4 by position (proto); the OS
# cache dropped before each start (root). Twice timed (st.phases=0), the versions in turn;
# then once counted by phase; then the prototype with its check (rule 4 by id beside it, with
# the reads). A start writes nothing to the database (checked on F53). Expects
# $B/{rel,head,proto}.jar and $B/cls-{rel,head,proto}/; writes $B/out/, out/DONE at the end.
# Usage, detached: nohup sh s1-57.sh > s1-57.log 2>&1 &
set -u
B=/opt/bergdb-bench/005-57
J=/opt/bergdb-bench/jdk-27/bin/java
DATA=/opt/bergdb-bench/007/data
OUT=$B/out
mkdir -p "$OUT"
rm -f "$OUT/DONE"
log() { echo "$(date '+%F %T') $*" >> "$OUT/runs.txt"; }
cold() { sync; echo 3 > /proc/sys/vm/drop_caches; }
run() {     # run VERSION DB TAG PHASES [JAVA-ARGS...]
    v=$1; db=$2; tag=$3; ph=$4; shift 4
    f=$OUT/$db-$v-$tag.txt
    timeout 30m "$J" -Xms2500m -Xmx2500m -XX:+UseZGC -cp "$B/cls-$v:$B/$v.jar" -Dst.dir="$DATA/$db" \
        -Dst.budget=600000000 -Dst.phases="$ph" "$@" bergdb.core.StartBench > "$f" 2>&1
    s=$?
    log "$db $v $tag: exit $s; $(grep -o '"startupSec": [0-9.e-]*' "$f")"
}
log "start; load $(cut -d' ' -f1-3 /proc/loadavg)"
for db in s1-10m-sd50 s1-10m-sd200; do
    for r in 1 2; do
        for v in rel head proto; do
            cold; run $v $db cold$r 0
        done
    done
    for v in rel head proto; do
        cold; run $v $db counted 1
    done
    cold; run proto $db check 0 -Dbergdb.rule4.check=true
done
log "done"
touch "$OUT/DONE"
