#!/bin/sh
# Power loss (bergdb 012-14, done item 2; the design in 14-robustness.md, 6.5): Gen's
# workloads, with syncs added, run by C's bergdb-power (test/stress/power.c: tools/run.c
# under the I/O seam's model of volatile bytes, forced bytes and durable names, as Java's
# FileStreamPowerLossTester.ModelIo), which writes the image a power loss leaves at each
# write, tear, force, directory force and delete. Each image is then started by both
# dumpers (Java's Dump, C's bergdb-dump of the test build, under the sanitizers), each on
# a copy of its own, and run on by both runners (a restart and 20 transactions, as
# cross.sh's crash variants). Checked per image:
#   - no acknowledged byte lost: the image holds the stream, contiguously, up to the
#     length acknowledged by the last bergdb_sync or bergdb_close that returned before it
#     (bergdb-power's check), and C's recovered stream is at least that long;
#   - no short file before a newer one (bergdb-power's check; 005-47, 022-01 step 3): with
#     a new name durable at its creation (NAMES=now), the stream's old last file must be
#     forced before a new file is made, else an image has a short file before a newer one;
#     and no gap (022-02, D7): with a name that may be durable before one made earlier
#     (NAMES=reorder), each new file and the directory must be forced before the file
#     takes a byte, else an image has a later file without an earlier one;
#   - both start it (a power loss never leaves a database that does not start; but a torn
#     first write of the creation, before any acknowledged sync, which both refuse alike,
#     005-33's DatabaseNotCreatedException), with the
#     same exit status and the same dump; C's recovery writes Java's bytes (the
#     directories after the starts, from reclaim's decided cut);
#   - the runs after: the same text, exit 0, the same files.
# And per workload: bergdb-power's text and files are bergdb-run's (the seam passes on).
#
# Usage: test/stress/power.sh
#   OUT    (environment) /Users/f/fl/bench/022/out/power by default
#   BASES  (environment) the workloads, "SEED:K=V,..." each (Gen's), in place of the six
#   SYNC   (environment) the chance of a sync after a transaction line (0.15)
#   JOBS   (environment) workloads at once (3)
#   NAMES  (environment) when C's model takes a new name to be durable: reorder (the
#          default since 022-02, D7: as now, and also images in which a name is durable
#          before the names made before it since the last force of the directory), now
#          (at its creation, as a delete is; 022-01, step 3) or dirforce (after the next
#          force of the directory, as Java's ModelIo; 012-14's runs)
#   OMIT   (environment) file, dir, switch or newfile: the negative control (bergdb-power
#          -omit): then the run must find a lost acknowledged byte (file; dir, which sets
#          NAMES=dirforce) or a short file before a newer one or a gap (switch: the force of
#          the old last file before a new file left out; newfile, which sets NAMES=reorder:
#          D7's forces of a new file and of the directory after it left out), and prints
#          POWER CONTROL CAUGHT
#   JAVAIMG=1  (environment) the other way: the images are Java's, from
#          FileStreamPowerLossTester's ModelIo on Java's Db (test/stress/java/PowerImages.java,
#          its runTrace workload: node size 30, startup distance 20,000, retain 2 s, a
#          100 kB buffer flushed every 10 ms); BASES are then "SEED:TRANSACTIONS,PER_EVENT"
#          (default "17:600,3 19:600,3 23:800,2"); the same checks of each image, but
#          the acknowledged length, which Java's own test checks by time
# Needs C's test and release builds and build/java/classes. Prints POWER OK or POWER
# FAILED. The script is one compound command, read whole before it runs.

{
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
CDIR=$(cd "$HERE/../.." && pwd)
OUT=${OUT:-/Users/f/fl/bench/022/out/power}
SYNC=${SYNC:-0.15}
JOBS=${JOBS:-3}
OMIT=${OMIT:-}
NAMES=${NAMES:-reorder}
[ "$OMIT" = dir ] && NAMES=dirforce
[ "$OMIT" = newfile ] && NAMES=reorder
[ -n "${JAVA_HOME:-}" ] || JAVA_HOME=/opt/homebrew/opt/openjdk
JAVA=$JAVA_HOME/bin/java
CLASSES=$CDIR/build/java/classes
CT=$CDIR/build/test
CR=$CDIR/build/release
export ASAN_OPTIONS=exitcode=86
T0=$(date +%s)
BASES=${BASES:-"1101:n=600,retain=1,sd=1000,valmax=2000,big=20
1102:n=500,maxnode=8,sd=200,restarts=3,retain=0
1103:n=900,maxnode=14,retain=2,sd=5000,restarts=4,huge=20
1104:n=400,retain=0,restarts=2,setters=5
1105:n=1200,retain=1,sd=500,valmax=3000,huge=30,restarts=2
1106:n=300,maxnode=62,sd=100000,retain=0"}

JAVAIMG=${JAVAIMG:-}
if [ -n "$JAVAIMG" ]; then
    case "$BASES" in 1101:*) BASES="17:600,3 19:600,3 23:800,2" ;; esac
fi
rm -rf "$OUT"; mkdir -p "$OUT/bin/test" "$OUT/bin/release"
if [ -n "$JAVAIMG" ]; then
    mkdir -p "$OUT/jclasses"
    "$JAVA_HOME/bin/javac" -nowarn -cp "$CLASSES" -d "$OUT/jclasses" "$HERE/java/PowerImages.java" \
        > "$OUT/javac.txt" 2>&1 || { cat "$OUT/javac.txt"; echo "POWER FAILED: javac"; exit 1; }
fi
# Copies of C's tools, so that a build during the run does not change them.
cp "$CT/bergdb-power" "$CT/bergdb-dump" "$CT/bergdb-run" "$OUT/bin/test/"
cp "$CR/bergdb-run" "$OUT/bin/release/"
CT=$OUT/bin/test; CR=$OUT/bin/release

files_of() {    # DIR: "START NAME SIZE" of its .bergdb files, by start
    ls -ln "$1" 2>/dev/null | awk '$1 ~ /^-/ && $NF ~ /^[0-9]+\.bergdb$/ && length($NF) == 21 {
        print substr($NF, 1, 14) * 100000, $NF, $5 }' | sort -n
}
cut_file_start() {  # DIR CUT: the start of the file that holds position CUT (or the first)
    files_of "$1" | awk -v cut="$2" 'NR == 1 { s = $1 } $1 <= cut { s = $1 } END { print s + 0 }'
}
stream_bytes() {  # DIR FROM: the stream's bytes from position FROM to its end
    from=$(cut_file_start "$1" "$2")
    files_of "$1" | awk -v f="$from" '$1 >= f { print $2 }' | (cd "$1" && xargs cat) \
        | tail -c +$(( $2 - from + 1 ))
}
stream_end() {  # DIR: the stream's length
    files_of "$1" | awk 'END { print $1 + $3 }'
}
decided_cut() {  # OUT: firstAvailablePos of the last status line, 0 if none
    awk '/^status / { for (i = 2; i <= NF; i++) if ($i ~ /^firstAvailablePos=/) { split($i, a, "="); c = a[2] } }
        END { print c + 0 }' "$1"
}
same_db() {  # X Y CUT: the same other files and the same stream from CUT
    diff -rq "$1" "$2" > /dev/null 2>&1 && return 0
    for sf in "$1"/* "$2"/*; do
        sn=$(basename "$sf")
        case "$sn" in *.bergdb) continue ;; esac
        cmp -s "$1/$sn" "$2/$sn" || return 1
    done
    [ "$(stream_bytes "$1" "$3" | shasum | cut -c1-40)" = "$(stream_bytes "$2" "$3" | shasum | cut -c1-40)" ]
}
exit_of() { if [ -f "$1.exit" ]; then cat "$1.exit"; else echo missing; fi; }
maxnode_of() { awk '$1 == "set" && $2 == "maxnode" { m = $3 } END { print (m ? m : 30) }' "$1"; }
after_workload() {  # WORKLOAD: its settings, a restart, and 20 more transactions later on
    awk '
        $1 == "set" { print; next }
        ($1 == "t" || $1 == "clock") && $2 != "-" { if ($2 + 0 > t) t = $2 + 0 }
        END {
            t += 1000000
            print "restart"
            for (i = 0; i < 20; i++) {
                t += 1000
                printf "t %d p /after/%d s:after%d d /k/%d p /k/%d x:%02x\n", t, i, i, i, i + 1, i
            }
            print "check latest"
            print "sync"
        }' "$1" | { echo "bergdb-workload 1"; cat; }
}

base() {    # SEED PARAMS: one workload and its images; OUT/SEED/result.txt
    seed=$1; d=$OUT/$seed
    mkdir -p "$d"
    r=$d/result.txt
    if [ -n "$JAVAIMG" ]; then
        : > "$r"
        printf 'bergdb-workload 1\nset maxnode 30\nset sd 20000\nset retain 20000000\nclock 2000000000\n' > "$d/w.wl"
        after_workload "$d/w.wl" > "$d/after.wl"
        m=30
        # shellcheck disable=SC2046
        "$JAVA" -ea -Xmx1g -cp "$CLASSES:$OUT/jclasses" bergdb.core.PowerImages "$seed" \
            $(echo "$2" | tr , ' ') "$d/img" > "$d/power.err" 2>&1 \
            || echo "FAIL $seed: PowerImages: $(tail -3 "$d/power.err")" >> "$r"
        check_images
        return
    fi
    # shellcheck disable=SC2046
    "$JAVA" -cp "$CLASSES" bergdb.cross.Gen "$seed" $(echo "$2" | tr , ' ') > "$d/gen.wl"
    awk -v seed="$seed" -v p="$SYNC" 'BEGIN { srand(seed) } { print } $1 == "t" && rand() < p { print "sync" }' \
        "$d/gen.wl" > "$d/w.wl"
    after_workload "$d/w.wl" > "$d/after.wl"
    m=$(maxnode_of "$d/w.wl")
    omit=""; [ -n "$OMIT" ] && omit="-omit $OMIT"
    # shellcheck disable=SC2086
    "$CT/bergdb-power" -seed "$seed" $omit -names "$NAMES" "$d/img" "$d/w.wl" "$d/db" > "$d/power.txt" 2> "$d/power.err"
    pe=$?
    if [ -n "$OMIT" ]; then
        if [ "$OMIT" = switch ] || [ "$OMIT" = newfile ]; then
            caught='^power SHORT'; what="had a short file before a newer one, or a gap"
        else caught='^power LOST'; what="lost acknowledged bytes"; fi
        if grep -q "$caught" "$d/power.err"; then
            echo "CONTROL $seed caught: $(grep -c "$caught" "$d/power.err") images $what; $(tail -1 "$d/power.err")" > "$r"
        else
            echo "FAIL $seed: -omit $OMIT found nothing: $(tail -1 "$d/power.err")" > "$r"
        fi
        return
    fi
    : > "$r"
    [ "$pe" = 0 ] || echo "FAIL $seed: bergdb-power exit $pe: $(grep -v '^power images' "$d/power.err" | head -3)" >> "$r"
    "$CR/bergdb-run" "$d/w.wl" "$d/db-plain" > "$d/run.txt" 2> "$d/run.err"
    cmp -s "$d/run.txt" "$d/power.txt" || echo "FAIL $seed: bergdb-power's text is not bergdb-run's" >> "$r"
    diff -rq "$d/db" "$d/db-plain" > /dev/null || echo "FAIL $seed: bergdb-power's files are not bergdb-run's" >> "$r"
    check_images
}

check_images() {    # the images of base's $d, its workload's node size $m, into $r
    # The images: Java scans each (Dump's SCAN), then both start and run on their copies.
    : > "$d/scan.jobs"; : > "$d/a.jobs"; : > "$d/run-a.jobs"
    for i in "$d"/img/*/; do
        i=${i%/}
        mkdir -p "$i/src"
        for f in "$i"/*.bergdb; do [ -f "$f" ] && mv "$f" "$i/src/"; done
        cp -R "$i/src" "$i/a"; cp -R "$i/src" "$i/b"
        echo "scan $i/scan.txt $i/src" >> "$d/scan.jobs"
        echo "dump $i/dump-a.txt -maxnode $m $i/a $i/scan.txt" >> "$d/a.jobs"
        echo "run $i/run-a.txt -segments 1 $d/after.wl $i/a" >> "$d/run-a.jobs"
    done
    "$JAVA" -ea -Xmx1g -cp "$CLASSES" bergdb.core.Batch "$d/scan.jobs" > "$d/scan.log" 2>&1
    "$JAVA" -ea -Xmx1g -cp "$CLASSES" bergdb.core.Batch "$d/a.jobs" > "$d/a.log" 2>&1 &
    pj=$!
    for i in "$d"/img/*/; do
        i=${i%/}
        "$CT/bergdb-dump" -maxnode "$m" "$i/b" "$i/scan.txt" < /dev/null > "$i/dump-b.txt" 2> "$i/dump-b.txt.err"
        echo $? > "$i/dump-b.txt.exit"
    done
    wait $pj
    # The recovered directories, before the runs after change them.
    for i in "$d"/img/*/; do
        i=${i%/}
        n=$(basename "$i")
        ack=$(sed -n 's/.* ack=\([0-9]*\).*/\1/p' "$i/image.txt")
        ev=$(sed -n 's/^event=\([a-z_]*\).*/\1/p' "$i/image.txt")
        ea=$(exit_of "$i/dump-a.txt"); eb=$(exit_of "$i/dump-b.txt")
        echo "image $n $ev ack=$ack dump $ea $eb" >> "$d/images.txt"
        if [ "$ea" = 0 ] && [ "$eb" = 3 ] && grep -q "empty stream" "$i/dump-b.txt.err" 2>/dev/null; then
            # C's dumper does not create databases (012-09): the runs after start from
            # the image itself on both sides, and create the database.
            echo "EMPTY $n" >> "$r"
            [ "$ack" = 0 ] || echo "FAIL $seed/$n ($ev): an empty stream after the acknowledged $ack" >> "$r"
            rm -rf "$i/a" "$i/b"; cp -R "$i/src" "$i/a"; cp -R "$i/src" "$i/b"
            continue
        fi
        if [ "$ack" = 0 ] && grep -q '^start error=DatabaseNotCreatedException' "$i/dump-a.txt" \
                && grep -q '^start error=DatabaseNotCreatedException' "$i/dump-b.txt"; then
            # A torn first write of the creation, its file's name durable, before any
            # acknowledged sync (NAMES=now or reorder): both starts refuse it, as 005-33 has
            # it (BERGDB_NOT_CREATED; Java's FileStream, which forces a new name before the
            # first write, as C since 022-02's D7, gives the same image); the runs after are
            # refused alike.
            echo "NOTCREATED $n" >> "$r"
            : > "$i/notcreated"
        fi
        [ "$ea" = "$eb" ] || echo "FAIL $seed/$n ($ev): dump exits $ea and $eb" >> "$r"
        [ "$ea" = 0 ] || [ -f "$i/notcreated" ] || echo "FAIL $seed/$n ($ev): the start refused it, exit $ea: $(head -c 300 "$i/dump-a.txt.err" 2>/dev/null)" >> "$r"
        cmp -s "$i/dump-a.txt" "$i/dump-b.txt" || echo "FAIL $seed/$n ($ev): the dumps differ" >> "$r"
        same_db "$i/a" "$i/b" "$(decided_cut "$i/dump-a.txt")" \
            || echo "FAIL $seed/$n ($ev): the recovered directories differ" >> "$r"
        if [ "$eb" = 0 ]; then
            end=$(stream_end "$i/b"); [ -n "$end" ] || end=0
            [ "$end" -ge "$ack" ] || echo "FAIL $seed/$n ($ev): C's recovered stream ends at $end, before the acknowledged $ack" >> "$r"
        fi
    done
    "$JAVA" -ea -Xmx1g -cp "$CLASSES" bergdb.core.Batch "$d/run-a.jobs" > "$d/run-a.log" 2>&1 &
    pj=$!
    for i in "$d"/img/*/; do
        i=${i%/}
        "$CT/bergdb-run" -segments 1 "$d/after.wl" "$i/b" < /dev/null > "$i/run-b.txt" 2> "$i/run-b.txt.err"
        echo $? > "$i/run-b.txt.exit"
    done
    wait $pj
    for i in "$d"/img/*/; do
        i=${i%/}
        n=$(basename "$i")
        ra=$(exit_of "$i/run-a.txt"); rb=$(exit_of "$i/run-b.txt")
        if [ -f "$i/notcreated" ]; then
            [ "$ra" = "$rb" ] || echo "FAIL $seed/$n: runs after exit $ra and $rb" >> "$r"
        else
            [ "$ra" = 0 ] && [ "$rb" = 0 ] || echo "FAIL $seed/$n: runs after exit $ra and $rb" >> "$r"
        fi
        cmp -s "$i/run-a.txt" "$i/run-b.txt" || echo "FAIL $seed/$n: the runs after differ" >> "$r"
        same_db "$i/a" "$i/b" "$(decided_cut "$i/run-a.txt")" \
            || echo "FAIL $seed/$n: the files after the runs differ" >> "$r"
    done
    ni=$(ls -d "$d"/img/*/ | wc -l | tr -d ' ')
    nf=$(grep -c '^FAIL' "$r")
    ne=$(grep -c '^EMPTY' "$r")
    nn=$(grep -c '^NOTCREATED' "$r")
    echo "BASE $seed: $ni images, $nf failures, $ne empty (Java creates, C's dumper refuses), $nn torn creations (both refuse, 005-33); $(tail -1 "$d/power.err")" >> "$r"
    [ "$nf" = 0 ] && [ "${KEEP:-0}" != 1 ] && rm -rf "$d/img" "$d/db-plain"
}

running=0
for b in $BASES; do
    base "${b%%:*}" "${b#*:}" &
    running=$((running + 1))
    if [ "$running" -ge "$JOBS" ]; then wait; running=0; fi
done
wait

cat "$OUT"/*/result.txt | grep -v '^EMPTY\|^NOTCREATED' > "$OUT/summary.txt"
cat "$OUT/summary.txt"
FAILS=$(grep -c '^FAIL' "$OUT/summary.txt")
if [ -n "$OMIT" ]; then
    CAUGHT=$(grep -c '^CONTROL' "$OUT/summary.txt")
    if [ "$FAILS" = 0 ]; then
        echo "POWER CONTROL CAUGHT: -omit $OMIT (names $NAMES) caught in $CAUGHT workloads ($(( $(date +%s) - T0 )) s)"
        exit 0
    fi
    echo "POWER CONTROL FAILED: $FAILS workloads found nothing under -omit $OMIT (names $NAMES)"
    exit 1
fi
IMAGES=$(awk '/^BASE/ { n += $3 } END { print n + 0 }' "$OUT/summary.txt")
if [ "$FAILS" = 0 ]; then
    names=" (names $NAMES)"; [ -n "$JAVAIMG" ] && names=""
    echo "POWER OK: $(echo $BASES | wc -w | tr -d ' ') workloads$names, $IMAGES images started and run on by C and Java alike, no acknowledged byte lost, no short file ($(( $(date +%s) - T0 )) s)"
    exit 0
fi
echo "POWER FAILED: $FAILS failures ($(( $(date +%s) - T0 )) s)"
exit 1
}
