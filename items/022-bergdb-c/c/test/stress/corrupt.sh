#!/bin/sh
# Corrupt input at the start (bergdb 012-14, done item 3): copies of finished databases
# changed in ways that cross.sh's corrupt variants (012-06: the scanners only) do not
# cover, each started by both dumpers (Java's Dump, C's bergdb-dump of the test build,
# under AddressSanitizer and UndefinedBehaviorSanitizer): garbage and zeroed meta blocks
# (the first, the last, a middle one), files cut short, made longer, emptied, removed,
# renamed (a gap, a wrong name, a wrong length), an extra file of garbage, a directory in
# place of a file, bergdb.lock as garbage, missing or a directory, and bit flips near the
# stream's end (where a start reads). Checked per variant: both dumpers give the same
# exit status and the same text (a refused start prints "start error=NAME", Java's
# exception's name); C never crashes (no sanitizer report, no signal); and when C
# refuses the start, C's copy is as it was, every file and byte (C never writes into a
# database it refuses). Java writing into a database that it refuses is reported, not
# counted.
#
# Usage: test/stress/corrupt.sh
#   OUT     (environment) /Users/f/fl/bench/012/14-out/corrupt by default
#   CBUILD  (environment) C's builds, build/ by default
#   BASES   (environment) the bases, "SEED:K=V,..." each (Gen's), in place of the four
#   HEADERS (environment) N: also a bit flipped in each header byte (32) of the last N
#           committed records of each base
# Needs C's test build and build/java/classes. Prints CORRUPT OK or CORRUPT FAILED.
# The script is one compound command, read whole before it runs.

{
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
CDIR=$(cd "$HERE/../.." && pwd)
OUT=${OUT:-/Users/f/fl/bench/012/14-out/corrupt}
CBUILD=${CBUILD:-$CDIR/build}
[ -n "${JAVA_HOME:-}" ] || JAVA_HOME=/opt/homebrew/opt/openjdk
JAVA=$JAVA_HOME/bin/java
CLASSES=$CDIR/build/java/classes
export ASAN_OPTIONS=exitcode=86
FAILS=0
fail() { FAILS=$((FAILS + 1)); echo "DIFFERENCE $*"; }
T0=$(date +%s)

rm -rf "$OUT"; mkdir -p "$OUT/wl"
# The bases: no reclaim, several files (large values), node size 8, reclaim.
BASES=${BASES:-"501:n=600,maxnode=8,sd=100,restarts=2,retain=0
502:n=800,restarts=3,retain=0,huge=40,valmax=3000
503:n=900,maxnode=14,sd=1000,retain=2,restarts=2
504:n=1500,valmax=2000,big=20,retain=0,restarts=1"}
: > "$OUT/base.jobs"
for b in $BASES; do
    seed=${b%%:*}
    # shellcheck disable=SC2046
    "$JAVA" -cp "$CLASSES" bergdb.cross.Gen "$seed" $(echo "${b#*:}" | tr , ' ') > "$OUT/wl/$seed.wl"
    mkdir -p "$OUT/base/$seed"
    echo "run $OUT/base/$seed/run.txt $OUT/wl/$seed.wl $OUT/base/$seed/db" >> "$OUT/base.jobs"
done
"$JAVA" -ea -Xmx2g -cp "$CLASSES" bergdb.core.Batch "$OUT/base.jobs" > "$OUT/base.log" 2>&1
: > "$OUT/scan.jobs"
for b in $BASES; do
    seed=${b%%:*}
    echo "scan $OUT/base/$seed/scan.txt $OUT/base/$seed/db" >> "$OUT/scan.jobs"
done
"$JAVA" -ea -Xmx2g -cp "$CLASSES" bergdb.core.Batch "$OUT/scan.jobs" > "$OUT/scan.log" 2>&1

files_of() {    # DIR: "START NAME SIZE" of its .bergdb files, by start
    ls -ln "$1" | awk '$1 ~ /^-/ && $NF ~ /^[0-9]+\.bergdb$/ && length($NF) == 21 {
        print substr($NF, 1, 14) * 100000, $NF, $5 }' | sort -n
}
put() {     # FILE OFFSET COUNT SEED MODE: garbage, zero or flip (one bit) bytes at OFFSET
    python3 -I -c '
import random, sys
f, off, n, seed, mode = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
r = random.Random(seed)
with open(f, "r+b") as h:
    h.seek(off)
    old = h.read(n)
    if mode == "garbage": new = bytes(r.randrange(256) for _ in range(n))
    elif mode == "zero": new = bytes(n)
    else: new = bytes([old[0] ^ (1 << r.randrange(8))]) + old[1:]
    h.seek(off); h.write(new)' "$@"
}
name_of() { printf '%014d.bergdb' $(( $1 / 100000 )); }

: > "$OUT/dump-a.jobs"; : > "$OUT/dump-b.jobs"
NV=0
for b in $BASES; do
    seed=${b%%:*}
    base=$OUT/base/$seed/db
    m=$(awk '$1 == "set" && $2 == "maxnode" { print $3 }' "$OUT/wl/$seed.wl")
    files=$(files_of "$base")
    nf=$(echo "$files" | wc -l | tr -d ' ')
    first=$(echo "$files" | awk 'NR == 1 { print $2 }')
    last=$(echo "$files" | awk 'END { print $2 }'); lastsize=$(echo "$files" | awk 'END { print $3 }')
    laststart=$(echo "$files" | awk 'END { print $1 }')
    mid=$(echo "$files" | awk -v n="$nf" 'NR == int((n + 1) / 2) { print $2 }')
    len=$(echo "$files" | awk 'END { print $1 + $3 }')
    fstart=$(echo "$files" | awk 'NR == 1 { print $1 }')    # after reclaim's cut, not 0
    lastmeta=$(( (len - 1) / 200000 * 200000 ))
    midmeta=$(( (fstart + len) / 2 / 200000 * 200000 ))
    [ "$midmeta" -lt "$fstart" ] && midmeta=$lastmeta
    window=$(( len - fstart - 1 )); [ "$window" -gt 400000 ] && window=400000
    variants="meta-first-garbage meta-first-zero meta-last-garbage meta-last-zero meta-mid-garbage
        meta-last-flip last-cut-1 last-cut-1000 last-longer last-empty first-missing first-empty
        mid-missing extra-garbage-file wrong-name-length wrong-name-odd last-as-dir
        lock-garbage lock-missing lock-dir all-empty"
    [ "$nf" -gt 1 ] && variants="$variants mid-cut-1 mid-longer gap-rename"
    i=0
    while [ $i -lt 12 ]; do variants="$variants flip-$i"; i=$((i + 1)); done
    if [ -n "${HEADERS:-}" ]; then
        # One bit flipped in each of the 32 header bytes of the last HEADERS records.
        for rp in $(awk '/^record pos=/ && / time=/ { split($2, a, "="); print a[2] }' \
                "$OUT/base/$seed/scan.txt" | tail -n "$HEADERS"); do
            o=0; while [ $o -lt 32 ]; do variants="$variants hdr-$rp-$o"; o=$((o + 1)); done
        done
    fi
    for v in $variants; do
        d=$OUT/v/$seed/$v
        mkdir -p "$d"
        cp -R "$base" "$d/src"
        s=$d/src
        case $v in
        meta-first-garbage) put "$s/$first" 0 128 1 garbage ;;
        meta-first-zero) put "$s/$first" 0 128 1 zero ;;
        meta-last-garbage|meta-last-zero|meta-last-flip|meta-mid-garbage)
            [ "${v#meta-mid}" != "$v" ] && p=$midmeta || p=$lastmeta
            fs=$(files_of "$s" | awk -v p="$p" '$1 <= p { s = $1; n = $2 } END { print s, n }')
            mode=${v##*-}
            if [ "$mode" = flip ]; then put "$s/${fs#* }" $(( p - ${fs%% *} + 60 )) 1 7 flip
            else put "$s/${fs#* }" $(( p - ${fs%% *} )) 128 2 "$mode"; fi ;;
        last-cut-1) truncate -s $((lastsize - 1)) "$s/$last" ;;
        last-cut-1000) truncate -s $((lastsize > 1000 ? lastsize - 1000 : 0)) "$s/$last" ;;
        last-longer) head -c 5000 /dev/urandom >> "$s/$last" ;;
        last-empty) : > "$s/$last" ;;
        first-missing) rm "$s/$first" ;;
        first-empty) : > "$s/$first" ;;
        mid-missing) rm "$s/$mid" ;;
        mid-cut-1) sz=$(wc -c < "$s/$mid" | tr -d ' '); truncate -s $((sz - 1)) "$s/$mid" ;;
        mid-longer) head -c 100 /dev/urandom >> "$s/$mid" ;;
        gap-rename) mv "$s/$last" "$s/$(name_of $((laststart + 400000)))" ;;
        extra-garbage-file) head -c 3000 /dev/urandom > "$s/$(name_of $((len / 200000 * 200000 + 2000000)))" ;;
        wrong-name-length) mv "$s/$last" "$s/0$last" ;;
        wrong-name-odd) mv "$s/$last" "$s/$(name_of $((laststart + 100000)))" ;;
        last-as-dir) rm "$s/$last"; mkdir "$s/$last" ;;
        lock-garbage) head -c 40 /dev/urandom > "$s/bergdb.lock" ;;
        lock-missing) rm -f "$s/bergdb.lock" ;;
        lock-dir) rm -f "$s/bergdb.lock"; mkdir "$s/bergdb.lock" ;;
        all-empty) for f in "$s"/*.bergdb; do : > "$f"; done ;;
        hdr-*) rp=${v#hdr-}; o=${rp#*-}; rp=${rp%-*}; p=$((rp + o))
            fs=$(files_of "$s" | awk -v p="$p" '$1 <= p { s = $1; n = $2 } END { print s, n }')
            put "$s/${fs#* }" $(( p - ${fs%% *} )) 1 "$o" flip ;;
        flip-*) k=${v#flip-}
            p=$(( len - 1 - (k * 7919 * 13) % window ))
            fs=$(files_of "$s" | awk -v p="$p" '$1 <= p { s = $1; n = $2 } END { print s, n }')
            put "$s/${fs#* }" $(( p - ${fs%% *} )) 1 "$k" flip ;;
        esac
        cp -R "$s" "$d/a"; cp -R "$s" "$d/b"
        (cd "$d/b" && find . | sort && find . -type f | sort | xargs shasum 2>/dev/null) > "$d/b.before"
        echo "dump $d/dump-a.txt -maxnode $m $d/a $OUT/base/$seed/scan.txt" >> "$OUT/dump-a.jobs"
        echo "dump $d/dump-b.txt -maxnode $m $d/b $OUT/base/$seed/scan.txt" >> "$OUT/dump-b.jobs"
        NV=$((NV + 1))
    done
done
echo "variants: $NV, made in $(( $(date +%s) - T0 )) s"

"$JAVA" -ea -Xmx2g -cp "$CLASSES" bergdb.core.Batch "$OUT/dump-a.jobs" > "$OUT/dump-a.log" 2>&1 &
pa=$!
while read -r kind out args; do
    # shellcheck disable=SC2086
    "$CBUILD/test/bergdb-dump" $args < /dev/null > "$out" 2> "$out.err"
    echo $? > "$out.exit"
done < "$OUT/dump-b.jobs"
wait $pa

NREF=0; NACC=0; JW=0; NREAD=0
for d in "$OUT"/v/*/*; do
    v=${d#$OUT/v/}
    ea=$(cat "$d/dump-a.txt.exit" 2> /dev/null || echo missing); eb=$(cat "$d/dump-b.txt.exit")
    if grep -q 'Sanitizer\|runtime error' "$d/dump-b.txt.err" 2> /dev/null || [ "$eb" -ge 86 ]; then
        fail "$v: C crashed (exit $eb): $(head -3 "$d/dump-b.txt.err")"
        continue
    fi
    if [ "$ea" = 3 ] && [ "$eb" = 5 ]; then
        # Both started, and a read after the start failed: Java's Dump threw (Batch's
        # status 3) where C's bergdb-dump stopped (5). C prints a getMany's pairs as it
        # walks, Java's getMany returns them all or throws: Java's text is a prefix of
        # C's, and both name the same position.
        NREAD=$((NREAD + 1))
        head -n "$(wc -l < "$d/dump-a.txt")" "$d/dump-b.txt" | cmp -s - "$d/dump-a.txt" \
            || fail "$v: a read failed after the start, and Java's text is not a prefix of C's"
        pa=$(grep -o 'spos:* [0-9]*' "$d/dump-a.txt.err" | head -1 | tr -dc 0-9)
        pb=$(grep -o 'spos:* [0-9]*' "$d/dump-b.txt.err" | head -1 | tr -dc 0-9)
        [ -n "$pa" ] && [ "$pa" = "$pb" ] || fail "$v: the failed reads' positions: Java ${pa:-none}, C ${pb:-none}"
        echo "read failed $v: spos $pb, $(grep -v '^bergdb-dump: start read' "$d/dump-b.txt.err" | head -1 | cut -c1-160)" >> "$OUT/refused.txt"
        continue
    fi
    [ "$ea" = "$eb" ] || fail "$v: exit status Java $ea, C $eb"
    if ! cmp -s "$d/dump-a.txt" "$d/dump-b.txt"; then
        fail "$v: the dumps differ: $(diff "$d/dump-a.txt" "$d/dump-b.txt" | head -4 | tr '\n' ' ')"
    fi
    if [ "$eb" != 0 ]; then
        NREF=$((NREF + 1))
        (cd "$d/b" && find . | sort && find . -type f | sort | xargs shasum 2>/dev/null) > "$d/b.after"
        cmp -s "$d/b.before" "$d/b.after" || fail "$v: C refused the start and changed the directory"
        (cd "$d/a" && find . | sort && find . -type f | sort | xargs shasum 2>/dev/null) > "$d/a.after"
        if ! cmp -s "$d/b.before" "$d/a.after"; then
            JW=$((JW + 1)); echo "note: $v: Java refused the start and changed the directory"
        fi
        echo "refused $v: exit $eb $(grep '^start error' "$d/dump-b.txt") $(grep -v '^bergdb-dump: start read' "$d/dump-b.txt.err" | head -1 | cut -c1-160)" >> "$OUT/refused.txt"
    else
        NACC=$((NACC + 1))
        # Started: both recovered their copies alike.
        diff -rq "$d/a" "$d/b" > /dev/null 2>&1 || fail "$v: the directories after the starts differ"
    fi
done
echo "starts: $NV variants, $NREF refused by both, $NACC started by both, $NREAD started by both with a read failing later; Java changed $JW directories it refused; $(( $(date +%s) - T0 )) s"
if [ $FAILS = 0 ]; then
    echo "CORRUPT OK: $NV variants"
    rm -rf "$OUT/v"
    exit 0
fi
echo "CORRUPT FAILED: $FAILS differences ($OUT)"
exit 1
}
