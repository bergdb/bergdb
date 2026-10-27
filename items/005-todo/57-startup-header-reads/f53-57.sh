#!/bin/sh
# bergdb 005-57 on F53: warm starts of 007-05's two databases (10M key24 keys, 8-byte values,
# startup distances of 50 and 200 MB, in ~/fl/bench/007-05/data) with release 2026.1's jar
# (rel), the current code (head) and the prototype, rule 4 by position (proto); and the time
# after a start. Waits until F53 is quiet (no other JVM but the editor's, no gate or lake).
# Per database: a start to warm the OS cache; three timed starts of each version, in turn;
# one counted by phase of each; the prototype with its check (rule 4 by id beside it); and,
# on an APFS clone of the database (the updates write to it), a start followed by N
# transactions of 1,000 random updates, counted by source and timed (N: 300 at 50 MB, 800 at
# 200 MB, so that D's nodes from the section are written). A start writes nothing to the
# database (checked: the listing and the last file's SHA-1 are the same after one).
# Usage: sh f53-57.sh SCRATCH, where SCRATCH has rel/bergdb-2026.1.jar,
# bergdb-head/java/build/bergdb.jar, bergdb-proto/java/build/bergdb.jar,
# bergdb-proto2/java/build/bergdb.jar and cls-{rel,head,proto,proto2}/ (StartBench compiled
# against each); writes SCRATCH/out/. VERSIONS (default "rel head proto") and PARTS (default
# "warm counted check after") choose what runs; the second run, of the prototype with part 2,
# was VERSIONS=proto2 PARTS="warm counted after".
set -u
S=$1
VERSIONS=${VERSIONS:-rel head proto}
PARTS=${PARTS:-warm counted check after}
DATA=$HOME/fl/bench/007-05/data
OUT=$S/out
mkdir -p "$OUT"
rm -f "$OUT/DONE"
log() { echo "$(date '+%F %T') $*" >> "$OUT/runs.txt"; }
has() { case " $PARTS " in *" $1 "*) return 0 ;; esac; return 1; }
jar() {
    case $1 in
    rel) echo "$S/rel/bergdb-2026.1.jar" ;;
    head) echo "$S/bergdb-head/java/build/bergdb.jar" ;;
    proto) echo "$S/bergdb-proto/java/build/bergdb.jar" ;;
    proto2) echo "$S/bergdb-proto2/java/build/bergdb.jar" ;;
    esac
}
busy() {
    ps -Ao args | grep -E "bin/java|java/night\.sh|level[0-9]\.sh|before-commit|lake |tracecheck" \
        | grep -v -E "grep|vscode|Code Helper" | grep -q .
}
run() {     # run VERSION DB TAG PHASES DIR [JAVA-ARGS...]
    v=$1; db=$2; tag=$3; ph=$4; d=$5; shift 5
    f=$OUT/$db-$v-$tag.txt
    java -Xms16g -Xmx16g -XX:+UseZGC -cp "$S/cls-$v:$(jar $v)" -Dst.dir="$d" -Dst.budget=4000000000 \
        -Dst.phases="$ph" "$@" bergdb.core.StartBench > "$f" 2>&1
    s=$?
    log "$db $v $tag: exit $s; $(grep -o -E '"(startupSec|afterSec)": [0-9.e-]*' "$f" | tr '\n' ' ')"
}

n=0
while [ $n -lt 6 ]; do
    if busy; then n=0; else n=$((n + 1)); fi
    sleep 10
done
log "quiet; load $(sysctl -n vm.loadavg); versions $VERSIONS; parts $PARTS"
for db in f53-10m-sd50 f53-10m-sd200; do
    first=${VERSIONS%% *}
    if has warm; then
        run $first $db warmup 0 "$DATA/$db"
        for r in 1 2 3; do
            for v in $VERSIONS; do
                run $v $db warm$r 0 "$DATA/$db"
            done
        done
    fi
    if has counted; then
        for v in $VERSIONS; do
            run $v $db counted 1 "$DATA/$db"
        done
    fi
    if has check; then
        run proto $db check 0 "$DATA/$db" -Dbergdb.rule4.check=true
    fi
    if has after; then
        case $db in *sd50) u=300 ;; *) u=800 ;; esac
        for v in $VERSIONS; do
            for ph in 1 0; do
                rm -rf "$S/clone"
                cp -c -R "$DATA/$db" "$S/clone"
                run $v $db after$ph $ph "$S/clone" -Dst.after=$u
            done
        done
        rm -rf "$S/clone"
    fi
done
log "done"
touch "$OUT/DONE"
