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
# exception's name); C never crashes (no sanitizer report, no signal); when C refuses
# the start, C's copy is as it was, every file and byte (C never writes into a database
# it refuses), but for 014-01's known case, as corruptset.sh counts it: recovery's zero
# fill of a damaged size written, then the start refused, by both, the two directories
# alike (a flip in a record size's low byte, HEADERS). And the messages (bergdb 022-02,
# D6): the exception's name and message of a refused start (status 1), of a refused
# directory (status 3: FileStream's exception leaves Java's Dump; C's bergdb-dump prints
# "the directory DIR: NAME, MESSAGE") and of a read that failed after the start (Java's
# from its stack trace, a DbFailedException with its cause's message; C's "A read
# failed: " and the cause's), Java's (standard error, each dump's own through CorruptSet's
# -dump) and C's, byte for byte, C's cut at its 239 bytes. Both dumpers run in OUT with
# paths from there, so that a path in a message (FileStream's texts name the directory
# or a file) is short; it names the dumper's own copy, v/SEED/VARIANT/a or .../b, the one
# difference allowed. The variants of random bytes (last-longer, mid-longer,
# extra-garbage-file, lock-garbage) differ from run to run: last-longer's record size is
# random, refused when negative, zero-filled (up to 2 GB a copy) and started when
# positive; each outcome is compared as it comes, and no class is counted by variant.
# Such a start reads the zero-filled record whole, one array of up to
# StoredTrans.MAX_RECORD_SIZE, 2^31 - 9 bytes, in either dumper: Java's runs with
# -Xmx4g (bergdb 022-02; with -Xmx2g it threw OutOfMemoryError at a record of
# 2,146,064,565 bytes, where C started it; with 4g a record of 2^31 - 9 bytes starts,
# a resident size of 2.3 GB, both dumps equal).
# Java writing into a database that it refuses is reported, not counted.
#
# Usage: test/stress/corrupt.sh
#   OUT     (environment) /Users/f/fl/bench/022/out/corrupt by default
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
OUT=${OUT:-/Users/f/fl/bench/022/out/corrupt}
CBUILD=$(cd "${CBUILD:-$CDIR/build}" 2> /dev/null && pwd)
[ -n "${JAVA_HOME:-}" ] || JAVA_HOME=/opt/homebrew/opt/openjdk
JAVA=$JAVA_HOME/bin/java
CLASSES=$CDIR/build/java/classes
export ASAN_OPTIONS=exitcode=86
[ -x "$CBUILD/test/bergdb-dump" ] || { echo "no bergdb-dump in C's test build"; echo "CORRUPT FAILED"; exit 1; }
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
        # Paths from OUT, where both dumpers run: the messages that name a file are short.
        r=v/$seed/$v
        echo "dump $r/dump-a.txt -maxnode $m $r/a base/$seed/scan.txt" >> "$OUT/dump-a.jobs"
        echo "dump $r/dump-b.txt -maxnode $m $r/b base/$seed/scan.txt" >> "$OUT/dump-b.jobs"
        NV=$((NV + 1))
    done
done
echo "variants: $NV, made in $(( $(date +%s) - T0 )) s"

# Both dumpers in OUT. Java's dumps one at a time, each with its standard error in
# OUT.err (CorruptSet's -dump), as C's; a heap for a record of 2^31 - 9 bytes (above).
(cd "$OUT" && exec "$JAVA" -ea -Xmx4g -cp "$CLASSES" bergdb.core.CorruptSet -dump 1 dump-a.jobs) \
    > "$OUT/dump-a.log" 2>&1 &
pa=$!
(cd "$OUT" && while read -r kind out args; do
    # shellcheck disable=SC2086
    "$CBUILD/test/bergdb-dump" $args < /dev/null > "$out" 2> "$out.err"
    echo $? > "$out.exit"
done < dump-b.jobs)
wait $pa

NREF=0; NACC=0; JW=0; NREAD=0; K014=0
: > "$OUT/texts.jobs"
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
        echo "$v read" >> "$OUT/texts.jobs"
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
        (cd "$d/a" && find . | sort && find . -type f | sort | xargs shasum 2>/dev/null) > "$d/a.after"
        if ! cmp -s "$d/b.before" "$d/b.after"; then
            # 014-01's known case, as corruptset.sh counts it: recovery's zero fill of a
            # damaged size written, then the start refused, by both, the directories alike.
            if [ "$ea" = "$eb" ] && cmp -s "$d/a.after" "$d/b.after"; then
                K014=$((K014 + 1)); echo "known 014-01: $v: both wrote the zero fill, then refused"
            else
                fail "$v: C refused the start and changed the directory"
            fi
        elif ! cmp -s "$d/b.before" "$d/a.after"; then
            JW=$((JW + 1)); echo "note: $v: Java refused the start and changed the directory"
        fi
        case $eb in 1) echo "$v start" ;; 3) echo "$v open" ;; esac >> "$OUT/texts.jobs"
        echo "refused $v: exit $eb $(grep '^start error' "$d/dump-b.txt") $(grep -v '^bergdb-dump: start read' "$d/dump-b.txt.err" | head -1 | cut -c1-160)" >> "$OUT/refused.txt"
    else
        NACC=$((NACC + 1))
        # Started: both recovered their copies alike.
        diff -rq "$d/a" "$d/b" > /dev/null 2>&1 || fail "$v: the directories after the starts differ"
    fi
done
# The messages: a refused start's, a refused directory's and a failed read's exception,
# its name and message (texts.txt: each, Java's and C's).
python3 -I - "$OUT" > "$OUT/texts.txt" <<'EOF2'
import os, re, sys
out = sys.argv[1]
TEXT = 239                      # C's text, cut at ERR_TEXT - 1 bytes (src/err.h)
UTF = ('utf-8', 'surrogateescape')

def read(p):
    try:
        with open(p, 'rb') as f:
            return f.read()
    except OSError:
        return b''

def text(b):                    # bytes as str, and back by .encode(*UTF): exact
    return b.decode(*UTF)

def java_error(err):
    """Java's exception: Dump's line of a refused start, or the stack trace's first line
    (an exception that left Dump: a directory refused, status 3; a read, status 3 with C's
    5) and a DbFailedException's cause: (simple name, message), or None."""
    lines = text(err).splitlines()
    for i, line in enumerate(lines):
        m = re.match(r'Dump: the start failed: (\w+), (.*)$', line)
        if m:
            return m.group(1), m.group(2)
        m = re.match(r'(?:[\w$]+\.)*(\w+(?:Exception|Error))(?:: (.*))?$', line)
        if m:
            name, msg = m.group(1), m.group(2) if m.group(2) is not None else 'null'
            for c in lines[i + 1:]:
                cm = re.match(r'Caused by: (?:[\w$]+\.)*(\w+)(?:: (.*))?$', c)
                if cm and name == 'DbFailedException':
                    return name, 'A read failed: ' + (cm.group(2) or 'null')
            return name, msg
    return None

def c_error(err):
    """C's: bergdb-dump's line of a refused start, a failed read or a refused directory."""
    for line in text(err).splitlines():
        m = re.match(r'bergdb-dump: (?:the start|a getMany|a getOne) failed: (\w+), (.*)$', line)
        if m:
            return m.group(1), m.group(2)
        m = re.match(r'bergdb-dump: the directory .*?: (\w+), (.*)$', line)
        if m:
            return m.group(1), m.group(2)
    return None

nd, n = 0, 0
for line in read(os.path.join(out, 'texts.jobs')).decode().splitlines():
    v, kind = line.split(' ')
    d = os.path.join(out, 'v', v)
    j = java_error(read(os.path.join(d, 'dump-a.txt.err')))
    c = c_error(read(os.path.join(d, 'dump-b.txt.err')))
    if j is not None:
        # A file's path names the dumper's own copy: Java's v/V/a, C's v/V/b.
        j = j[0], j[1].replace('v/%s/a' % v, 'v/%s/b' % v)
    n += 1
    same = j is not None and c is not None and j[0] == c[0]
    if same:
        jm, cm = j[1].encode(*UTF), c[1].encode(*UTF)
        same = jm == cm or (len(cm) == TEXT and jm[:TEXT] == cm)
    print('%s %s: Java %r, C %r%s' % (v, kind, j, c, '' if same else ' DIFFERENCE'))
    nd += not same
print('messages: %d compared, %d differ' % (n, nd))
EOF2
while read -r line; do
    case $line in *' DIFFERENCE') fail "the messages: ${line% DIFFERENCE}" ;; esac
done < "$OUT/texts.txt"
tail -1 "$OUT/texts.txt"
echo "starts: $NV variants, $NREF refused by both, $NACC started by both, $NREAD started by both with a read failing later; $K014 of 014-01's known case; Java changed $JW other directories it refused; $(( $(date +%s) - T0 )) s"
if [ $FAILS = 0 ]; then
    echo "CORRUPT OK: $NV variants"
    rm -rf "$OUT/v"
    exit 0
fi
echo "CORRUPT FAILED: $FAILS differences ($OUT)"
exit 1
}
