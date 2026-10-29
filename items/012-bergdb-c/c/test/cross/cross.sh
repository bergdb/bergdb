#!/bin/sh
# The cross tests of BergDB C with BergDB Java (bergdb 012-05; 012-01, section
# 6.4). For each workload of a set, side A and side B run it, each in a
# directory of its own, and the script compares: the files (names, sizes,
# bytes; for a workload that reclaims, the stream's bytes from the cut that reclaim
# decided, as each run makes its physical cut at its own moments), the runners'
# outputs, the scans (each directory by both scanners) and the dumps (each
# directory by both dumpers). Then the crash variants (copies of finished
# directories cut at chosen and random positions, recovered and dumped by
# both sides, then more transactions), the runs in turns (a workload's
# segments run alternately by A and B on one directory), and a planted
# difference (one byte flipped), which must be found and explained. Both
# scanners scan the crash variants too, and copies with bits flipped and
# files cut or removed (the corrupt variants, 012-06): a stream that Java
# refuses, C refuses, at the same place, and C's scanner never crashes.
#
# Usage: test/cross/cross.sh quick|full|scale [C=DIR] [SCALE=N] [KEEP=1]
#   quick   a minute or so: small configurations, a few seeds, a few cuts,
#           one workload in turns, and the hand-written workloads in
#           test/cross/workloads/; the C gate runs it
#   full    StreamDigest's twelve configurations at full size in their three
#           modes, CoreSame, a few hundred Gen seeds, about a thousand crash
#           cuts, workloads in turns; 10 to 20 minutes
#   scale   one workload of SCALE keys (10,000,000 by default), by hand,
#           outside other sessions' timed runs; the scans take the last
#           file only, the dumps -large
#   C=DIR   side B uses C's tools in DIR where they exist: bergdb-run,
#           bergdb-dump, bergdb-scan, which take the arguments of Java's
#           Run, Dump and StreamScan and print the same text; Java's
#           otherwise. Without C=, both sides are Java (two JVMs).
#   KEEP=1  keep the directories of passed workloads (default: deleted)
# Output: build/cross/SET/ (report.txt; workloads in wl/). The last line is
# "CROSS SET OK: ..." or "CROSS SET FAILED: ..."; the exit status 0 or 1.
# Needs JAVA_HOME (or java on PATH), python3 for the Java build. JAVA_OPTS
# (default -Xmx2g; scale -Xmx12g) goes to every JVM.

# The whole script is one compound command, which sh reads before it runs it, so that
# an edit of this file does not change a run in progress.
{
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
CDIR=$(cd "$HERE/../.." && pwd)
SET=${1:-}
shift 2>/dev/null || true
CTOOLS=""
SCALE=10000000
KEEP=0
for arg in "$@"; do
    case "$arg" in
    C=*) CTOOLS=$(cd "${arg#C=}" && pwd) || exit 2 ;;
    SCALE=*) SCALE=${arg#SCALE=} ;;
    KEEP=*) KEEP=${arg#KEEP=} ;;
    *) echo "cross.sh: unknown argument $arg"; exit 2 ;;
    esac
done
case "$SET" in
quick|full|scale) ;;
*) echo "Usage: test/cross/cross.sh quick|full|scale [C=DIR] [SCALE=N] [KEEP=1]"; exit 2 ;;
esac

if [ -z "${JAVA_HOME:-}" ] && [ -d /opt/homebrew/opt/openjdk ]; then
    JAVA_HOME=/opt/homebrew/opt/openjdk
fi
if [ -n "${JAVA_HOME:-}" ]; then
    JAVA=$JAVA_HOME/bin/java
    export JAVA_HOME
else
    JAVA=java
fi
# The heap: small, beside other sessions' runs; scale holds millions of keys in memory.
if [ -z "${JAVA_OPTS:-}" ]; then
    JAVA_OPTS=-Xmx2g; [ "$SET" = scale ] && JAVA_OPTS=-Xmx12g
fi
CLASSES=$CDIR/build/java/classes
OUT=$CDIR/build/cross/$SET
REPORT=$OUT/report.txt
T0=$(date +%s)
FAILS=0

say() {
    echo "$*"
    echo "$*" >> "$REPORT"
}

fail() {
    FAILS=$((FAILS + 1))
    say "DIFFERENCE $*"
}

# ======== Sides and jobs ========
#
# A job file has one job a line: "run OUT ARGS", "dump OUT ARGS" or "scan OUT PATH"
# (Batch.java). Java runs a job file in one JVM; C runs its tools one job at a time.
# Each job leaves OUT, OUT.exit and, if it threw, OUT.err.

# Side B's jobs that Java runs although C has the tool: their OUT paths, one a line, in
# $OUT/java-only.txt. C's bergdb-dump opens a database by the bounded startup (012-10;
# by a full replay of its stream with -replay, 012-08), reclaim's table and cut
# included (012-11). C's bergdb-run (012-09) creates a database and runs its
# transactions, starts an existing one (012-10), and reclaims (012-11): every run is
# C's (c_runs).
ctool() {   # KIND: the C tool's path for a job kind, if side B has it
    [ -n "$CTOOLS" ] || return 1
    t=$CTOOLS/bergdb-$1
    [ -x "$t" ] && echo "$t"
}

side_jobs() {   # SIDE JOBFILE: runs the jobs on side a or b
    side=$1
    jobs=$2
    [ -s "$jobs" ] || return 0
    if [ "$side" = b ] && [ -n "$CTOOLS" ]; then
        : > "$jobs.java"
        while read -r kind out rest; do
            [ -n "$kind" ] || continue
            if t=$(ctool "$kind") && ! grep -qxF "$out" "$OUT/java-only.txt" 2>/dev/null; then
                # shellcheck disable=SC2086
                "$t" $rest < /dev/null > "$out" 2> "$out.err"
                echo $? > "$out.exit"
                [ -s "$out.err" ] || rm -f "$out.err"
            else
                echo "$kind $out $rest" >> "$jobs.java"
            fi
        done < "$jobs"
        jobs=$jobs.java
        [ -s "$jobs" ] || return 0
    fi
    # shellcheck disable=SC2086
    "$JAVA" -ea $JAVA_OPTS -cp "$CLASSES" bergdb.core.Batch "$jobs" > "$jobs.log" 2>&1
}

both_sides() {  # JOBS_A JOBS_B: the two sides at once
    side_jobs a "$1" &
    pa=$!
    side_jobs b "$2"
    wait $pa
}

exit_of() {     # OUT: the job's exit status, or "missing"
    if [ -f "$1.exit" ]; then cat "$1.exit"; else echo missing; fi
}

# ======== Directories and positions ========

copy() {        # cp's arguments: APFS clones (copy on write) where the file system has them
    cp -c "$@" 2>/dev/null || cp "$@"
}

files_of() {    # DIR: "START NAME SIZE" of its .bergdb files, by start
    ls -ln "$1" 2>/dev/null | awk '$1 ~ /^-/ && $NF ~ /^[0-9]+\.bergdb$/ && length($NF) == 21 {
        print substr($NF, 1, 14) * 100000, $NF, $5 }' | sort -n
}

cut_file_start() {  # DIR CUT: the start of the file that holds position CUT (or the first)
    files_of "$1" | awk -v cut="$2" 'NR == 1 { s = $1 } $1 <= cut { s = $1 } END { print s + 0 }'
}

decided_cut() {  # RUNOUT: firstAvailablePos of the last status line, 0 if none
    awk '/^status / { for (i = 2; i <= NF; i++) if ($i ~ /^firstAvailablePos=/) { split($i, a, "="); c = a[2] } }
        END { print c + 0 }' "$1"
}

make_view() {   # DIR CUT VIEW: hard links to DIR's files from the file that holds CUT
    rm -rf "$3"
    mkdir -p "$3"
    from=$(cut_file_start "$1" "$2")
    files_of "$1" | while read -r start name size; do
        [ "$start" -ge "$from" ] && ln "$1/$name" "$3/$name"
    done
    for f in "$1"/*; do
        case "$f" in *.bergdb) ;; *) [ -f "$f" ] && ln "$f" "$3/$(basename "$f")" ;; esac
    done
}

split_view() {  # DIR FROM LAYOUT VIEW: DIR's stream bytes from FROM, a multiple of 200,000,
                # in files cut where LAYOUT's files begin (a workload that reclaims: each
                # side's physical cut and so its files differ, 012-02, C2; the views of both
                # sides then hold the same files when their bytes are the same)
    rm -rf "$4"
    mkdir -p "$4"
    stream_bytes "$1" "$2" > "$4/.stream"
    { echo "$2"; files_of "$3" | awk -v f="$2" '$1 > f { print $1 }'; } | {
        prev=""
        while read -r start; do
            [ -n "$prev" ] && dd if="$4/.stream" of="$4/$(printf '%014d' $((prev / 100000))).bergdb" \
                bs=100000 skip=$(( (prev - $2) / 100000 )) count=$(( (start - prev) / 100000 )) 2>/dev/null
            prev=$start
        done
        dd if="$4/.stream" of="$4/$(printf '%014d' $((prev / 100000))).bergdb" \
            bs=100000 skip=$(( (prev - $2) / 100000 )) 2>/dev/null
    }
    rm -f "$4/.stream"
    # A piece past the stream's end (a shorter stream) is no file.
    for f in "$4"/*.bergdb; do [ -s "$f" ] || rm -f "$f"; done
    for f in "$1"/*; do
        case "$f" in *.bergdb) ;; *) [ -f "$f" ] && ln "$f" "$4/$(basename "$f")" ;; esac
    done
}

stream_length() {  # DIR: the stream's length
    files_of "$1" | awk 'END { print $1 + $3 }'
}

stream_bytes() {  # DIR FROM: the stream's bytes from position FROM to its end
    from=$(cut_file_start "$1" "$2")
    files_of "$1" | awk -v f="$from" '$1 >= f { print $2 }' | (cd "$1" && xargs cat) \
        | tail -c +$(( $2 - from + 1 ))
}

tail_view() {   # DIR VIEW: one file with the stream's bytes from a meta block 2 MB or
                # less before its end (a position that is a multiple of 200,000)
    rm -rf "$2"
    mkdir -p "$2"
    len=$(stream_length "$1")
    from=$(( (len - 2000000) / 200000 * 200000 ))
    [ "$from" -lt 0 ] && from=0
    stream_bytes "$1" "$from" > "$2/$(printf '%014d' $((from / 100000))).bergdb"
    for f in "$1"/*; do
        case "$f" in *.bergdb) ;; *) [ -f "$f" ] && cp "$f" "$2/" ;; esac
    done
}

scan_around() {  # SCAN POS: the scan's lines around position POS
    awk -v p="$2" '
        { line[NR] = $0 }
        match($0, /^[a-z-]+ pos=[0-9]+/) {
            split(substr($0, RSTART, RLENGTH), a, "pos=")
            if (a[2] + 0 <= p + 0) at = NR
        }
        END { from = at - 2; if (from < 1) from = 1
              for (i = from; i <= at + 3 && i <= NR; i++) print "      " line[i] }' "$1"
}

# compare_dirs X Y CUT LABEL [SCANX SCANY]: the same files and bytes from the file that
# holds CUT (reclaim's decided cut; 0 without reclaim); files before it that both have
# must be equal too. On a difference: the first differing position and the scans' lines
# around it. Prints FIRSTDIFF=POS on standard output's last line for the caller, or nothing.
compare_dirs() {
    x=$1; y=$2; cut=$3; label=$4; sx=${5:-}; sy=${6:-}
    LAST_FIRSTDIFF=""
    if diff -rq "$x" "$y" > /dev/null 2>&1; then
        return 0            # the same files with the same bytes: the usual case
    fi
    from=$(cut_file_start "$x" "$cut")
    fx=$(files_of "$x" | awk -v f="$from" '$1 >= f'); fy=$(files_of "$y" | awk -v f="$from" '$1 >= f')
    names_x=$(echo "$fx" | awk '{ print $2 }'); names_y=$(echo "$fy" | awk '{ print $2 }')
    if [ "$names_x" != "$names_y" ]; then
        fail "$label: files from $from differ: $(echo $names_x) / $(echo $names_y)"
    fi
    first=""
    for name in $( (ls "$x"; ls "$y") | sort -u); do
        case "$name" in
        *.bergdb) start=$(echo "$name" | awk '{ print substr($0, 1, 14) * 100000 }')
            if [ "$start" -lt "$from" ]; then
                [ -f "$x/$name" ] && [ -f "$y/$name" ] || continue
            fi ;;
        *) start=-1 ;;
        esac
        if [ ! -f "$x/$name" ] || [ ! -f "$y/$name" ]; then
            [ "$start" -lt 0 ] && fail "$label: $name in one directory only"
            continue
        fi
        cmp -s "$x/$name" "$y/$name" && continue
        sxz=$(wc -c < "$x/$name" | tr -d ' '); syz=$(wc -c < "$y/$name" | tr -d ' ')
        off=$(cmp "$x/$name" "$y/$name" 2>/dev/null | sed -n 's/.* differ: char \([0-9]*\).*/\1/p')
        [ -n "$off" ] && off=$((off - 1))
        if [ -z "$off" ]; then
            off=$sxz; [ "$syz" -lt "$off" ] && off=$syz      # one is a prefix of the other
        fi
        if [ "$start" -lt 0 ]; then
            fail "$label: $name differs at byte $off"
            continue
        fi
        pos=$((start + off))
        fail "$label: $name (sizes $sxz, $syz) differs first at stream position $pos"
        [ -z "$first" ] && first=$pos
    done
    if [ -n "$first" ] && [ -n "$sx" ]; then
        say "    side A's scan around $first:"
        scan_around "$sx" "$first" | tee -a "$REPORT"
        if [ -n "$sy" ] && [ -f "$sy" ]; then
            say "    side B's scan around $first:"
            scan_around "$sy" "$first" | tee -a "$REPORT"
        fi
    fi
    LAST_FIRSTDIFF=$first
}

# compare_stream X Y CUT LABEL [SCANX SCANY]: for a workload that reclaims: the stream's
# bytes from CUT, reclaim's decided cut, the same (not the files, whose layout follows the
# physical cut: 012-01, 3.2 point 8; 012-02, C2 and Q1; 005-72), and the other files equal.
# On a difference: the first differing position and the scans' lines around it, and
# LAST_FIRSTDIFF as compare_dirs sets it.
compare_stream() {
    x=$1; y=$2; cut=$3; label=$4; sx=${5:-}; sy=${6:-}
    LAST_FIRSTDIFF=""
    for name in $( (ls "$x"; ls "$y") | sort -u); do
        case "$name" in
        *.bergdb) ;;
        *) if [ ! -f "$x/$name" ] || [ ! -f "$y/$name" ]; then
               fail "$label: $name in one directory only"
           elif ! cmp -s "$x/$name" "$y/$name"; then
               fail "$label: $name differs"
           fi ;;
        esac
    done
    tmp=$OUT/.cmp.$$
    stream_bytes "$x" "$cut" > "$tmp.x"
    stream_bytes "$y" "$cut" > "$tmp.y"
    if cmp -s "$tmp.x" "$tmp.y"; then
        rm -f "$tmp.x" "$tmp.y"
        return 0
    fi
    sxz=$(wc -c < "$tmp.x" | tr -d ' '); syz=$(wc -c < "$tmp.y" | tr -d ' ')
    off=$(cmp "$tmp.x" "$tmp.y" 2>/dev/null | sed -n 's/.* differ: char \([0-9]*\).*/\1/p')
    [ -n "$off" ] && off=$((off - 1))
    if [ -z "$off" ]; then
        off=$sxz; [ "$syz" -lt "$off" ] && off=$syz      # one is a prefix of the other
    fi
    rm -f "$tmp.x" "$tmp.y"
    first=$((cut + off))
    fail "$label: the streams from the decided cut at $cut (lengths $((cut + sxz)), $((cut + syz))) differ first at stream position $first"
    if [ -n "$sx" ]; then
        say "    side A's scan around $first:"
        scan_around "$sx" "$first" | tee -a "$REPORT"
        if [ -n "$sy" ] && [ -f "$sy" ]; then
            say "    side B's scan around $first:"
            scan_around "$sy" "$first" | tee -a "$REPORT"
        fi
    fi
    LAST_FIRSTDIFF=$first
}

compare_db() {  # WORKLOAD X Y CUT LABEL [SCANX SCANY]: compare_stream for a workload that
                # reclaims, compare_dirs for the others
    wl=$1; shift
    if [ "$(retain_of "$wl")" = 1 ]; then
        compare_stream "$@"
    else
        compare_dirs "$@"
    fi
}

compare_text() {  # X Y LABEL: two outputs, equal
    if ! cmp -s "$1" "$2"; then
        fail "$3: $1 and $2 differ:"
        diff "$1" "$2" | head -8 | sed 's/^/      /' | tee -a "$REPORT"
        return 1
    fi
    return 0
}

compare_scan() {  # X Y LABEL: two scans, equal but for the text of their error lines, which
                  # is each implementation's own (StreamScan's header): the same error
                  # lines at the same places
    cmp -s "$1" "$2" && return 0
    sed 's/^error .*/error/' "$1" > "$1.norm"
    sed 's/^error .*/error/' "$2" > "$2.norm"
    if ! cmp -s "$1.norm" "$2.norm"; then
        fail "$3: $1 and $2 differ:"
        diff "$1" "$2" | head -8 | sed 's/^/      /' | tee -a "$REPORT"
        return 1
    fi
    return 0
}

expect_exit() {  # OUT WANT LABEL
    e=$(exit_of "$1")
    if [ "$e" != "$2" ]; then
        fail "$3: exit status $e, not $2 ($1)"
        [ -f "$1.err" ] && head -5 "$1.err" | sed 's/^/      /' | tee -a "$REPORT"
    fi
}

maxnode_of() {  # WORKLOAD: its node size
    awk '$1 == "set" && $2 == "maxnode" { m = $3 } END { print (m ? m : 30) }' "$1"
}

retain_of() {   # WORKLOAD: 1 if it may reclaim (a retain setting or setter), else 0
    awk '($1 == "set" && $2 == "retain" && $3 != "forever") || ($1 == "setretain" && $2 != "forever") { r = 1 }
        END { print r + 0 }' "$1"
}

segments_of() { # WORKLOAD: the number of segments
    awk '$1 == "restart" { n++ } END { print n + 1 }' "$1"
}

c_runs() {      # WORKLOAD: 1 if C's bergdb-run runs it: every workload since 012-11
                # (restarts since 012-10, reclaim since 012-11); kept as the place to
                # send a kind of workload to Java
    echo 1
}

stream_sha() {  # DIR FROM: SHA-256 of the stream from position FROM to its end
    stream_bytes "$1" "$2" | shasum -a 256 | awk '{ print $1 }'
}

# ======== The sets ========

SPECS=""; CRASH=""; CUTS=0; RANDCUTS=0; TURNS=""; CORRUPT=""; FLIPS=0
case "$SET" in
quick)
    SPECS="sd:l2-sd100:restarts:n=300 sd:l2-sd1000-node8:reads:n=300 sd:l3-node14:restarts:n=600
        sd:l2-idle-1:plain:n=200 coresame:n=1500 gen:1:n=300 gen:2:n=300 gen:3:n=300,retain=2
        gen:4:n=200,maxnode=8,sd=100,restarts=3,retain=0 coresame:n=1500:plain
        gen:5:n=300,restarts=0,retain=0 gen:6:n=300,maxnode=8,sd=100,restarts=0,retain=0
        sd:l3-node14:plain:n=600 sd:l3-every1:reads:n=400 gen:7:n=400,restarts=0,retain=1
        gen:8:n=300,maxnode=8,sd=100,restarts=0,retain=1"
    CRASH="sd-l2-sd1000-node8-reads-n300 gen-4-n200-maxnode8-sd100-restarts3-retain0
        reclaim-crash"
    CUTS=4; RANDCUTS=3
    CORRUPT="gen-4-n200-maxnode8-sd100-restarts3-retain0 sd-l2-sd1000-node8-reads-n300"
    FLIPS=40
    TURNS="gen-4-n200-maxnode8-sd100-restarts3-retain0 sd-l3-node14-restarts-n600"
    ;;
full)
    for c in l2-sd100 l2-sd1000-node8 l2-sd10000-node14 l2-sd100000-node62 l2-every1 \
             l2-idle-1 l2-idle-2 l2-default-100MB l3-every1 l3-node8 l3-node14 l3-node62; do
        for m in plain reads restarts; do SPECS="$SPECS sd:$c:$m"; done
    done
    SPECS="$SPECS coresame coresame:plain"
    s=1; while [ $s -le 200 ]; do SPECS="$SPECS gen:$s"; s=$((s + 1)); done
    s=201; while [ $s -le 240 ]; do SPECS="$SPECS gen:$s:maxnode=8,sd=100,retain=0"; s=$((s + 1)); done
    # Without restarts and reclaim, for C's writer (012-09): random seeds, and small
    # startup distances and node size 8, where index writes and splits come often.
    s=241; while [ $s -le 280 ]; do SPECS="$SPECS gen:$s:restarts=0,retain=0"; s=$((s + 1)); done
    s=281; while [ $s -le 300 ]; do SPECS="$SPECS gen:$s:maxnode=8,sd=100,restarts=0,retain=0"; s=$((s + 1)); done
    # Without restarts, with reclaim, for C's reclaim (012-11, part 1): random retain
    # durations (forever in about 6 of 10), 2 s, and 1 s with node size 8 and startup
    # distance 100.
    s=301; while [ $s -le 340 ]; do SPECS="$SPECS gen:$s:restarts=0"; s=$((s + 1)); done
    s=341; while [ $s -le 380 ]; do SPECS="$SPECS gen:$s:restarts=0,retain=2"; s=$((s + 1)); done
    s=381; while [ $s -le 400 ]; do SPECS="$SPECS gen:$s:maxnode=8,sd=100,restarts=0,retain=1"; s=$((s + 1)); done
    CRASH="sd-l2-sd100-plain sd-l2-sd1000-node8-plain sd-l2-sd10000-node14-restarts sd-l2-every1-plain
        gen-201-maxnode8-sd100-retain0 gen-202-maxnode8-sd100-retain0 gen-203-maxnode8-sd100-retain0
        gen-204-maxnode8-sd100-retain0 reclaim-crash"
    CUTS=15; RANDCUTS=25
    CORRUPT="sd-l2-sd100-plain sd-l2-sd1000-node8-plain sd-l3-node8-restarts coresame
        gen-201-maxnode8-sd100-retain0 gen-3"
    FLIPS=80
    TURNS="sd-l2-sd100-restarts sd-l2-sd1000-node8-restarts sd-l3-node8-restarts coresame
        gen-201-maxnode8-sd100-retain0 gen-205-maxnode8-sd100-retain0"
    ;;
scale)
    SPECS="scale:$SCALE"
    ;;
esac

rm -rf "$OUT"
mkdir -p "$OUT"
: > "$REPORT"
: > "$OUT/java-only.txt"
say "cross.sh $SET, $(date '+%Y-%m-%d %H:%M'), side B: ${CTOOLS:-Java}"
sh "$HERE/java-build.sh" | tee -a "$REPORT" | grep -q "JAVA BUILD OK" || { say "CROSS $SET FAILED: the Java build"; exit 1; }

# shellcheck disable=SC2086
"$JAVA" $JAVA_OPTS -cp "$CLASSES" bergdb.core.Export "$OUT/wl" $SPECS > "$OUT/export.txt" 2>&1 \
    || { cat "$OUT/export.txt"; say "CROSS $SET FAILED: the export"; exit 1; }
if [ "$SET" != scale ]; then
    for f in "$HERE"/workloads/*.wl; do       # hand-written workloads
        [ -f "$f" ] && cp "$f" "$OUT/wl/" && echo "$OUT/wl/$(basename "$f")" >> "$OUT/export.txt"
    done
    if [ "$SET" = full ]; then
        for f in "$HERE"/workloads/full/*.wl; do  # hand-written, the full set's only
            [ -f "$f" ] && cp "$f" "$OUT/wl/" && echo "$OUT/wl/$(basename "$f")" >> "$OUT/export.txt"
        done
    fi
fi
WORKLOADS=$(sed 's|.*/||; s|\.wl$||' "$OUT/export.txt")
NW=$(echo $WORKLOADS | wc -w | tr -d ' ')
say "workloads: $NW, exported in $(( $(date +%s) - T0 )) s"

# ---- Runs ----
: > "$OUT/run-a.jobs"; : > "$OUT/run-b.jobs"
for w in $WORKLOADS; do
    for s in a b; do
        mkdir -p "$OUT/$s/$w"
        echo "run $OUT/$s/$w/run.txt $OUT/wl/$w.wl $OUT/$s/$w/db" >> "$OUT/run-$s.jobs"
    done
    if [ "$(c_runs "$OUT/wl/$w.wl")" = 0 ]; then
        echo "$OUT/b/$w/run.txt" >> "$OUT/java-only.txt"
    fi
done
both_sides "$OUT/run-a.jobs" "$OUT/run-b.jobs"
say "runs done in $(( $(date +%s) - T0 )) s"
if ctool run > /dev/null; then
    nj=$(grep -c '/run\.txt$' "$OUT/java-only.txt" | tr -d ' ')
    nr=0
    for w in $WORKLOADS; do
        if [ "$(retain_of "$OUT/wl/$w.wl")" = 1 ] && [ "$(c_runs "$OUT/wl/$w.wl")" = 1 ]; then
            nr=$((nr + 1))
        fi
    done
    say "side B's runs: C's of $((NW - nj)), $nr of them with reclaim; Java's of $nj"
fi

# ---- Views from the decided cut, scans and dumps ----
: > "$OUT/scan-a.jobs"; : > "$OUT/scan-b.jobs"; : > "$OUT/dump-a.jobs"; : > "$OUT/dump-b.jobs"
LARGE=""; [ "$SET" = scale ] && LARGE="-large"
for w in $WORKLOADS; do
    cut=$(decided_cut "$OUT/a/$w/run.txt")
    m=$(maxnode_of "$OUT/wl/$w.wl")
    for x in a b; do
        if [ "$SET" = scale ]; then
            # Gigabytes: the scans take the stream's last 2 MB or so, for the comparison
            # and for the dump's samples.
            tail_view "$OUT/$x/$w/db" "$OUT/$x/$w/view"
        elif [ "$(retain_of "$OUT/wl/$w.wl")" = 1 ]; then
            # Both sides from the same position, cut where side A's files begin.
            fa=$(cut_file_start "$OUT/a/$w/db" "$cut"); fb=$(cut_file_start "$OUT/b/$w/db" "$cut")
            [ "$fb" -gt "$fa" ] && fa=$fb
            split_view "$OUT/$x/$w/db" "$fa" "$OUT/a/$w/db" "$OUT/$x/$w/view"
        else
            make_view "$OUT/$x/$w/db" "$cut" "$OUT/$x/$w/view"
        fi
        for y in a b; do
            echo "scan $OUT/$x/$w/scan-by-$y.txt $OUT/$x/$w/view" >> "$OUT/scan-$y.jobs"
            rm -rf "$OUT/$x/$w/dumpdir-by-$y"
            copy -R "$OUT/$x/$w/db" "$OUT/$x/$w/dumpdir-by-$y"
            # C to Java: Java's dumps of C's directories run Java's audit (012-01, 1).
            audit=""; [ -n "$CTOOLS" ] && [ "$x$y" = ba ] && audit="-audit 1"
            echo "dump $OUT/$x/$w/dump-by-$y.txt -maxnode $m $LARGE $audit $OUT/$x/$w/dumpdir-by-$y $OUT/a/$w/scan-by-a.txt" >> "$OUT/dump-$y.jobs"
        done
    done
done
both_sides "$OUT/scan-a.jobs" "$OUT/scan-b.jobs"
both_sides "$OUT/dump-a.jobs" "$OUT/dump-b.jobs"
say "scans and dumps done in $(( $(date +%s) - T0 )) s"
if ctool dump > /dev/null; then
    nj=$(grep -c '/dump-by-b\.txt$' "$OUT/java-only.txt" | tr -d ' ')
    say "side B's dumps: C's of $(( $(wc -l < "$OUT/dump-b.jobs" | tr -d ' ') - nj )), Java's of $nj"
fi

# ---- Compare ----
for w in $WORKLOADS; do
    A=$OUT/a/$w; B=$OUT/b/$w
    before=$FAILS
    expect_exit "$A/run.txt" 0 "$w run A"
    expect_exit "$B/run.txt" 0 "$w run B"
    compare_text "$A/run.txt" "$B/run.txt" "$w run outputs"
    cut=$(decided_cut "$A/run.txt")
    compare_db "$OUT/wl/$w.wl" "$A/db" "$B/db" "$cut" "$w files" "$A/scan-by-a.txt" "$B/scan-by-b.txt"
    for x in a b; do
        for y in a b; do
            expect_exit "$OUT/$x/$w/scan-by-$y.txt" 0 "$w scan of $x by $y"
            expect_exit "$OUT/$x/$w/dump-by-$y.txt" 0 "$w dump of $x by $y"
            [ "$x$y" = aa ] && continue
            compare_text "$A/scan-by-a.txt" "$OUT/$x/$w/scan-by-$y.txt" "$w scan of $x by $y"
            compare_text "$A/dump-by-a.txt" "$OUT/$x/$w/dump-by-$y.txt" "$w dump of $x by $y"
        done
    done
    compare_db "$OUT/wl/$w.wl" "$A/dumpdir-by-a" "$B/dumpdir-by-b" "$cut" "$w files after the dumps"
    if [ -f "$OUT/wl/$w.digest" ]; then
        want=$(sed 's/.* sha256=//' "$OUT/wl/$w.digest")
        got=$(stream_sha "$A/db" "$cut")
        if [ "$want" != "$got" ]; then
            fail "$w: the stream from $cut is not StreamDigest's ($got, StreamDigest $want)"
        fi
    fi
    if [ $FAILS -eq $before ]; then
        echo "same $w" >> "$REPORT"
    else
        say "  $w: $((FAILS - before)) differences; its directories are kept in $OUT"
    fi
done
say "compared in $(( $(date +%s) - T0 )) s: $FAILS differences"

# ---- Crash variants ----
cut_copy() {    # SRC POS DEST: a copy of directory SRC as if the stream ended at POS
    rm -rf "$3"
    mkdir -p "$3"
    files_of "$1" | while read -r start name size; do
        [ "$start" -lt "$2" ] || continue
        copy "$1/$name" "$3/$name"
        end=$((start + size))
        [ "$end" -gt "$2" ] && truncate -s $(( $2 - start )) "$3/$name"
    done
    for f in "$1"/*; do
        case "$f" in *.bergdb) ;; *) [ -f "$f" ] && cp "$f" "$3/" ;; esac
    done
}

crash_positions() {  # SCAN N RANDOM SEED: chosen and random cut positions of a scanned stream
    awk -v n="$2" -v r="$3" -v seed="$4" '
        /^record pos=/ && / time=/ {
            for (i = 2; i <= NF; i++) { split($i, a, "="); f[a[1]] = a[2] }
            rec[++nr] = f["pos"]; size[nr] = f["size"]; last[nr] = f["lastPos"]
        }
        /^meta pos=/ { split($2, a, "="); meta[++nm] = a[2] }
        /^stream / { for (i = 2; i <= NF; i++) { split($i, a, "="); if (a[1] == "length") len = a[2] } }
        END {
            srand(seed)
            k = 0
            # Records spread over the stream: inside the header, the body, the last byte
            # left out, and the whole record.
            for (j = 1; j <= n && nr > 1; j++) {
                i = 2 + int((j - 1) * (nr - 1) / n)
                c[++k] = rec[i] + 3; c[++k] = rec[i] + 17; c[++k] = rec[i] + int(size[i] / 2)
                c[++k] = last[i]; c[++k] = last[i] + 1
            }
            # Meta blocks: at, before, inside and after them (a file end is at one).
            for (j = 2; j <= nm && j <= 1 + n; j++) {
                m = meta[j]; c[++k] = m - 1; c[++k] = m; c[++k] = m + 1; c[++k] = m + 127
                c[++k] = m + 128; c[++k] = m + 129
            }
            for (j = 1; j <= r; j++) c[++k] = rec[2] + int(rand() * (len - rec[2]))
            for (j = 1; j <= k; j++) if (c[j] > rec[1] && c[j] < len && !seen[c[j]]++) print c[j]
        }' "$1"
}

after_workload() {  # WORKLOAD: settings, a restart, and 20 more transactions later on
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

NCUTS=0
if [ -n "$CRASH" ]; then
    : > "$OUT/crash-scan.jobs"; : > "$OUT/crash-scan-b.jobs"
    : > "$OUT/crash-dump-a.jobs"; : > "$OUT/crash-dump-b.jobs"
    : > "$OUT/crash-run-a.jobs"; : > "$OUT/crash-run-b.jobs"
    seed=1
    for w in $CRASH; do
        [ -d "$OUT/a/$w/db" ] || { fail "crash: no workload $w"; continue; }
        # A workload that reclaims (012-11): copies of C's directory (side B, with C=) cut
        # at or after the stream's length at its last sync before the end. C's stream is
        # durable after a sync only, so every physical cut it made had its decision durable
        # by then, and such a copy is a crash; Java's directory makes its cuts at its own
        # moments, and a copy of it cut there might not be. Without C=: none.
        src=$OUT/a/$w/db; from=0
        if [ "$(retain_of "$OUT/wl/$w.wl")" = 1 ]; then
            if ! ctool run > /dev/null; then
                say "crash: $w reclaims; its crash variants need C's runs (C=)"; continue
            fi
            src=$OUT/b/$w/db
            from=$(awk '/^status / { for (i = 2; i <= NF; i++) if ($i ~ /^length=/) {
                split($i, a, "="); p = l; l = a[2] } } END { print p + 0 }' "$OUT/b/$w/run.txt")
        fi
        after_workload "$OUT/wl/$w.wl" > "$OUT/wl/$w.after.wl"
        m=$(maxnode_of "$OUT/wl/$w.wl")
        for p in $(crash_positions "$OUT/a/$w/scan-by-a.txt" "$CUTS" "$RANDCUTS" "$seed" \
                | awk -v f="$from" '$1 >= f'); do
            d=$OUT/crash/$w/$p
            cut_copy "$src" "$p" "$d/src"
            echo "scan $d/scan.txt $d/src" >> "$OUT/crash-scan.jobs"
            echo "scan $d/scan-b.txt $d/src" >> "$OUT/crash-scan-b.jobs"
            for s in a b; do
                copy -R "$d/src" "$d/$s"
                echo "dump $d/dump-$s.txt -maxnode $m $d/$s $d/scan.txt" >> "$OUT/crash-dump-$s.jobs"
                echo "run $d/run-$s.txt -segments 1 $OUT/wl/$w.after.wl $d/$s" >> "$OUT/crash-run-$s.jobs"
            done
            NCUTS=$((NCUTS + 1))
        done
        seed=$((seed + 1))
    done
    both_sides "$OUT/crash-scan.jobs" "$OUT/crash-scan-b.jobs"
    both_sides "$OUT/crash-dump-a.jobs" "$OUT/crash-dump-b.jobs"
    # The recovered directories: each side's dump started its copy of the cut, which recovered
    # it (the zero fill of a torn record, a meta block's fill; 012-02, 4.4). The two must be
    # equal before the runs after change them (012-10, done item 1: with C= side B's dumps are
    # C's bounded startup, so this compares C's recovery with Java's).
    before=$FAILS
    for w in $CRASH; do
        [ -d "$OUT/crash/$w" ] || continue
        for d in "$OUT/crash/$w"/*; do
            compare_db "$OUT/wl/$w.wl" "$d/a" "$d/b" "$(decided_cut "$d/dump-a.txt")" \
                "crash $w at $(basename "$d"), files after the recovery" "$d/scan.txt"
        done
    done
    say "crash variants: $NCUTS directories recovered by both sides' starts (their dumps), $((FAILS - before)) differences"
    both_sides "$OUT/crash-run-a.jobs" "$OUT/crash-run-b.jobs"
    before=$FAILS
    for w in $CRASH; do
        [ -d "$OUT/crash/$w" ] || continue
        for d in "$OUT/crash/$w"/*; do
            p=$(basename "$d")
            ea=$(exit_of "$d/dump-a.txt"); eb=$(exit_of "$d/dump-b.txt")
            [ "$ea" = "$eb" ] || fail "crash $w at $p: dump exit $ea and $eb"
            ra=$(exit_of "$d/run-a.txt"); rb=$(exit_of "$d/run-b.txt")
            [ "$ra" = "$rb" ] || fail "crash $w at $p: run exit $ra and $rb"
            [ "$ea" = 0 ] && [ "$ra" = 0 ] || echo "crash $w at $p: dump exit $ea, run exit $ra" >> "$REPORT"
            compare_text "$d/dump-a.txt" "$d/dump-b.txt" "crash $w at $p, dumps"
            compare_text "$d/run-a.txt" "$d/run-b.txt" "crash $w at $p, runs after"
            compare_db "$OUT/wl/$w.wl" "$d/a" "$d/b" "$(decided_cut "$d/run-a.txt")" \
                "crash $w at $p, files" "$d/scan.txt"
            sa=$(exit_of "$d/scan.txt"); sb=$(exit_of "$d/scan-b.txt")
            [ "$sa" = "$sb" ] || fail "crash $w at $p: scan exit $sa and $sb"
            compare_scan "$d/scan.txt" "$d/scan-b.txt" "crash $w at $p, scans"
        done
    done
    say "crash variants: $NCUTS cuts, $((FAILS - before)) differences, in $(( $(date +%s) - T0 )) s"
fi

# ---- Corrupt variants (012-06) ----
# Copies (APFS clones) of side A's views with one bit flipped, at positions taken from
# its scan: the fields of the records, the nodes and the meta blocks, and random ones;
# and with a file cut by a byte, removed or renamed. Both scanners scan each copy, and
# must give the same exit status and the same text but for the text of the error lines:
# C refuses what Java refuses, where Java refuses it, and never crashes (with C= the
# test build, under the sanitizers).
corrupt_specs() {   # SCAN N SEED: N specs "flip:POS:BIT", and a few for the files
    awk -v n="$2" -v seed="$3" '
        function add(p) { if (p >= first && p < len) cand[++nc] = p }
        /^stream / { for (i = 2; i <= NF; i++) { split($i, a, "="); f[a[1]] = a[2] }
                     first = f["first"]; len = f["length"] }
        /^file / { nf++ }
        /^(record|top|key|value|delete|meta|nodes-end|gotdirty|padding|last) pos=/ {
            split($2, a, "="); p = a[2] + 0; k = $1
            if (k == "record") { split("0 1 2 3 4 5 8 15 16 23 24 31", o, " ") }
            else if (k == "top") { split("0 3 4 5 6 7 8 9 10 15 16 24 31 32 39 40 47 48 55", o, " ") }
            else if (k == "key") { split("0 3 4 5 6 7 8 15 16 17 18 19 24 32 39 40 47", o, " ") }
            else if (k == "value" || k == "delete") { split("0 3 4 5 6 7 8 16 17 19 20 23 24 27 28 31", o, " ") }
            else if (k == "meta") { split("0 3 4 5 6 8 15 16 23 40 44 46 127", o, " ") }
            else { split("0 1 3", o, " ") }
            for (j in o) add(p + o[j])
        }
        END {
            srand(seed)
            for (i = 1; i <= n && nc > 0; i++) {
                p = (i % 4 == 0) ? first + int(rand() * (len - first)) : cand[1 + int(rand() * nc)]
                if (!seen[p]++) print "flip:" p ":" int(rand() * 8)
            }
            if (nf > 1) { print "cutfirst:0:0"; print "renamelast:0:0" }
            if (nf > 2) print "dropsecond:0:0"
        }' "$1"
}

make_corrupt() {    # VIEW SPEC DEST: a copy of VIEW changed as SPEC says
    rm -rf "$3"
    mkdir -p "$(dirname "$3")"
    copy -R "$1" "$3"
    kind=${2%%:*}; rest=${2#*:}; pos=${rest%%:*}; bit=${rest#*:}
    case "$kind" in
    flip)
        start=$(cut_file_start "$3" "$pos")
        name=$(files_of "$3" | awk -v s="$start" '$1 == s { print $2 }')
        off=$((pos - start))
        old=$(dd if="$3/$name" bs=1 skip=$off count=1 2>/dev/null | od -An -tu1 | tr -d ' ')
        new=$(( old ^ (1 << bit) ))
        printf "\\$(printf '%03o' $new)" | dd of="$3/$name" bs=1 seek=$off conv=notrunc 2>/dev/null ;;
    cutfirst)
        name=$(files_of "$3" | awk 'NR == 1 { print $2 }')
        size=$(files_of "$3" | awk 'NR == 1 { print $3 }')
        truncate -s $((size - 1)) "$3/$name" ;;
    dropsecond)
        name=$(files_of "$3" | awk 'NR == 2 { print $2 }')
        rm -f "$3/$name" ;;
    renamelast)
        name=$(files_of "$3" | awk 'END { print $2 }')
        mv "$3/$name" "$3/${name#0}" ;;
    esac
}

NCORRUPT=0
if [ -n "$CORRUPT" ]; then
    : > "$OUT/corrupt-scan-a.jobs"; : > "$OUT/corrupt-scan-b.jobs"
    seed=1
    for w in $CORRUPT; do
        [ -d "$OUT/a/$w/view" ] || { fail "corrupt: no workload $w"; continue; }
        for spec in $(corrupt_specs "$OUT/a/$w/scan-by-a.txt" "$FLIPS" "$seed"); do
            d=$OUT/corrupt/$w/$(echo "$spec" | tr ':' '-')
            make_corrupt "$OUT/a/$w/view" "$spec" "$d/src"
            echo "scan $d/scan-a.txt $d/src" >> "$OUT/corrupt-scan-a.jobs"
            echo "scan $d/scan-b.txt $d/src" >> "$OUT/corrupt-scan-b.jobs"
            NCORRUPT=$((NCORRUPT + 1))
        done
        seed=$((seed + 1))
    done
    both_sides "$OUT/corrupt-scan-a.jobs" "$OUT/corrupt-scan-b.jobs"
    before=$FAILS
    nerr=0
    for w in $CORRUPT; do
        [ -d "$OUT/corrupt/$w" ] || continue
        for d in "$OUT/corrupt/$w"/*; do
            v=$(basename "$d")
            sa=$(exit_of "$d/scan-a.txt"); sb=$(exit_of "$d/scan-b.txt")
            [ "$sa" = "$sb" ] || fail "corrupt $w $v: scan exit $sa and $sb"
            [ "$sa" = 0 ] || nerr=$((nerr + 1))
            compare_scan "$d/scan-a.txt" "$d/scan-b.txt" "corrupt $w $v, scans"
        done
    done
    say "corrupt variants: $NCORRUPT, $nerr refused or with error lines, $((FAILS - before)) differences, in $(( $(date +%s) - T0 )) s"
fi

# ---- Runs in turns ----
NTURNS=0
if [ -n "$TURNS" ]; then
    max=0
    for w in $TURNS; do
        n=$(segments_of "$OUT/wl/$w.wl")
        [ "$n" -gt "$max" ] && max=$n
        rm -rf "$OUT/turns/$w"; mkdir -p "$OUT/turns/$w"
        NTURNS=$((NTURNS + 1))
    done
    k=0
    while [ $k -lt $max ]; do
        side=a; [ $((k % 2)) = 1 ] && side=b
        : > "$OUT/turns-$k.jobs"
        for w in $TURNS; do
            [ "$k" -lt "$(segments_of "$OUT/wl/$w.wl")" ] || continue
            echo "run $OUT/turns/$w/run-$k.txt -segments $k $OUT/wl/$w.wl $OUT/turns/$w/db" >> "$OUT/turns-$k.jobs"
            # Side B's segments: C's since 012-11 (c_runs).
            if [ "$side" = b ] && [ "$(c_runs "$OUT/wl/$w.wl")" = 0 ]; then
                echo "$OUT/turns/$w/run-$k.txt" >> "$OUT/java-only.txt"
            fi
        done
        side_jobs $side "$OUT/turns-$k.jobs"
        k=$((k + 1))
    done
    before=$FAILS
    for w in $TURNS; do
        n=$(segments_of "$OUT/wl/$w.wl")
        k=0
        echo "bergdb-run 1" > "$OUT/turns/$w/run.txt"
        while [ $k -lt "$n" ]; do
            expect_exit "$OUT/turns/$w/run-$k.txt" 0 "turns $w segment $k"
            tail -n +2 "$OUT/turns/$w/run-$k.txt" >> "$OUT/turns/$w/run.txt"
            k=$((k + 1))
        done
        compare_text "$OUT/a/$w/run.txt" "$OUT/turns/$w/run.txt" "turns $w, run outputs"
        cut=$(decided_cut "$OUT/a/$w/run.txt")
        compare_db "$OUT/wl/$w.wl" "$OUT/a/$w/db" "$OUT/turns/$w/db" "$cut" "turns $w, files (A alone)" "$OUT/a/$w/scan-by-a.txt"
        compare_db "$OUT/wl/$w.wl" "$OUT/b/$w/db" "$OUT/turns/$w/db" "$cut" "turns $w, files (B alone)" "$OUT/b/$w/scan-by-b.txt"
    done
    say "runs in turns: $NTURNS workloads, $((FAILS - before)) differences, in $(( $(date +%s) - T0 )) s"
fi

# ---- A planted difference: one byte flipped in a copy must be found and explained ----
PLANTED=""
if [ "$SET" != scale ]; then
    w=$(echo $WORKLOADS | awk '{ print $1 }')
    cut=$(decided_cut "$OUT/a/$w/run.txt")
    p=$(awk -v c="$cut" '/^value pos=/ { split($2, a, "="); if (a[2] + 0 >= c + 1000) { print a[2] + 20; exit } }' "$OUT/a/$w/scan-by-a.txt")
    rm -rf "$OUT/planted"; copy -R "$OUT/b/$w/db" "$OUT/planted"
    start=$(cut_file_start "$OUT/planted" "$p")
    name=$(files_of "$OUT/planted" | awk -v s="$start" '$1 == s { print $2 }')
    off=$((p - start))
    old=$(dd if="$OUT/planted/$name" bs=1 skip=$off count=1 2>/dev/null | od -An -tu1 | tr -d ' ')
    new=$(( (old + 1) % 256 ))
    printf "\\$(printf '%03o' $new)" | dd of="$OUT/planted/$name" bs=1 seek=$off conv=notrunc 2>/dev/null
    keep=$FAILS; saved=$REPORT; REPORT=$OUT/planted.txt; : > "$REPORT"
    compare_db "$OUT/wl/$w.wl" "$OUT/a/$w/db" "$OUT/planted" "$cut" "planted, $w byte $p" "$OUT/a/$w/scan-by-a.txt" > /dev/null
    FAILS=$keep; REPORT=$saved
    echo "scan $OUT/planted.scan $OUT/planted" > "$OUT/planted.jobs"
    side_jobs a "$OUT/planted.jobs"
    { echo "    the planted copy's scan around $p:"; scan_around "$OUT/planted.scan" "$p"; } >> "$OUT/planted.txt"
    if [ "$LAST_FIRSTDIFF" = "$p" ] && grep -q "value pos=" "$OUT/planted.txt"; then
        PLANTED="the planted difference at $p was found and explained"
        echo "planted: $(cat "$OUT/planted.txt")" >> "$REPORT"
    else
        fail "the planted difference at $p was not found (found: ${LAST_FIRSTDIFF:-none})"
        cat "$OUT/planted.txt"
    fi
fi

# ---- The result ----
if [ "$FAILS" = 0 ] && [ "$KEEP" != 1 ]; then
    rm -rf "$OUT/a" "$OUT/b" "$OUT/crash" "$OUT/corrupt" "$OUT/turns" "$OUT/planted"
fi
T=$(( $(date +%s) - T0 ))
SUMMARY="$NW workloads, $NCUTS crash cuts, $NCORRUPT corrupt variants, $NTURNS in turns${PLANTED:+, $PLANTED}; side B: ${CTOOLS:-Java}; $T s"
if [ "$FAILS" = 0 ]; then
    say "CROSS $SET OK: $SUMMARY"
    exit 0
fi
say "CROSS $SET FAILED: $FAILS differences; $SUMMARY (report: $REPORT)"
exit 1
}
