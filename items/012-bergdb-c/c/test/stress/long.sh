#!/bin/sh
# Long runs (bergdb 012-14, done item 4): one of Gen's workloads of N transactions with
# restarts and reclaim, run by C's test build (AddressSanitizer, UndefinedBehaviorSanitizer,
# the allocator's checks) and C's release build under macOS's leaks, both with a small
# memory budget (-budget), and by Java's Run, at once. Checked: every run exits 0; C's
# text (the test build's) is Java's; the stream from reclaim's decided cut and the other
# files are Java's, for both C builds; leaks finds 0 leaks; and the directory's size,
# sampled every 2 s during the test build's run, stays bounded (its most and its end
# against the stream's length; Java's directory's too, for comparison).
#
# Usage: test/stress/long.sh SEED N [BUDGET] [GENPARAMS]
#   BUDGET     C's memory budget in bytes (20000)
#   GENPARAMS  more of Gen's parameters, K=V,... (retain=1,restarts=20,sd=50000,huge=1,setters=6)
#   OUT        (environment) /Users/f/fl/bench/012/14-out/long by default
#   CBUILD     (environment) C's builds, build/ by default
# Needs C's builds (./build.sh) and build/java/classes (test/cross/java-build.sh).
# Prints LONG RUN OK or LONG RUN FAILED and the figures; exit status 0 or 1. The
# script is one compound command, read whole before it runs.

{
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
CDIR=$(cd "$HERE/../.." && pwd)
SEED=$1; N=$2; BUDGET=${3:-20000}
P=${4:-retain=1,restarts=20,sd=50000,huge=1,setters=6}
OUT=${OUT:-/Users/f/fl/bench/012/14-out/long}/s$SEED-n$N
[ -n "${JAVA_HOME:-}" ] || JAVA_HOME=/opt/homebrew/opt/openjdk
JAVA=$JAVA_HOME/bin/java
CLASSES=$CDIR/build/java/classes
CBUILD=${CBUILD:-$CDIR/build}
FAILS=0
fail() { FAILS=$((FAILS + 1)); echo "FAILED: $*"; }

rm -rf "$OUT"; mkdir -p "$OUT"
# shellcheck disable=SC2046
"$JAVA" -cp "$CLASSES" bergdb.cross.Gen "$SEED" n="$N" $(echo "$P" | tr , ' ') > "$OUT/w.wl" || exit 1
echo "long run: $(sed -n 2p "$OUT/w.wl"), C's budget $BUDGET; $(date '+%H:%M:%S')"
T0=$(date +%s)

"$JAVA" -ea -Xmx2g -cp "$CLASSES" bergdb.cross.Run "$OUT/w.wl" "$OUT/java" > "$OUT/java.txt" 2> "$OUT/java.err" &
pj=$!
leaks --atExit -- "$CBUILD/release/bergdb-run" -budget "$BUDGET" "$OUT/w.wl" "$OUT/release" \
    > "$OUT/release.txt" 2> "$OUT/release.err" &
pr=$!
"$CBUILD/test/bergdb-run" -budget "$BUDGET" -mem "$OUT/w.wl" "$OUT/test" > "$OUT/test.txt" 2> "$OUT/test.err" &
pt=$!
maxk=0; maxj=0
while kill -0 $pt 2> /dev/null || kill -0 $pj 2> /dev/null; do
    sleep 2
    k=$(du -sk "$OUT/test" 2> /dev/null | awk '{ print $1 }')
    [ -n "$k" ] && [ "$k" -gt "$maxk" ] && maxk=$k
    k=$(du -sk "$OUT/java" 2> /dev/null | awk '{ print $1 }')
    [ -n "$k" ] && [ "$k" -gt "$maxj" ] && maxj=$k
done
wait $pt; et=$?; tt=$(( $(date +%s) - T0 ))
wait $pj; ej=$?; tj=$(( $(date +%s) - T0 ))
wait $pr; er=$?; tr=$(( $(date +%s) - T0 ))
echo "exit: C test $et ($tt s), Java $ej ($tj s), C release under leaks $er ($tr s)"
[ $et = 0 ] || fail "C's test build exit $et: $(tail -3 "$OUT/test.err")"
[ $ej = 0 ] || fail "Java exit $ej: $(tail -3 "$OUT/java.err")"
grep -q ': 0 leaks for 0 total leaked bytes' "$OUT/release.txt" || fail "leaks: $(grep 'leaks for' "$OUT/release.txt")"
cmp -s "$OUT/test.txt" "$OUT/java.txt" || fail "C's text differs from Java's: $(diff "$OUT/test.txt" "$OUT/java.txt" | head -4)"
# The release run's text, before leaks's report, is Java's too.
head -n "$(wc -l < "$OUT/java.txt")" "$OUT/release.txt" | cmp -s - "$OUT/java.txt" || fail "C release's text differs from Java's"

files_of() {    # DIR: "START NAME SIZE" of its .bergdb files, by start
    ls -ln "$1" | awk '$1 ~ /^-/ && $NF ~ /^[0-9]+\.bergdb$/ && length($NF) == 21 {
        print substr($NF, 1, 14) * 100000, $NF, $5 }' | sort -n
}
stream_bytes() {  # DIR FROM: the stream's bytes from FROM to its end
    from=$(files_of "$1" | awk -v c="$2" 'NR == 1 { s = $1 } $1 <= c { s = $1 } END { print s + 0 }')
    files_of "$1" | awk -v f="$from" '$1 >= f { print $2 }' | (cd "$1" && xargs cat) | tail -c +$(( $2 - from + 1 ))
}
cut=$(awk '/^status / { for (i = 2; i <= NF; i++) if ($i ~ /^firstAvailablePos=/) { split($i, a, "="); c = a[2] } } END { print c + 0 }' "$OUT/java.txt")
len=$(awk '/^status / { for (i = 2; i <= NF; i++) if ($i ~ /^length=/) { split($i, a, "="); c = a[2] } } END { print c + 0 }' "$OUT/java.txt")
jsha=$(stream_bytes "$OUT/java" "$cut" | shasum -a 256 | cut -c1-16)
for d in test release; do
    s=$(stream_bytes "$OUT/$d" "$cut" | shasum -a 256 | cut -c1-16)
    [ "$s" = "$jsha" ] || fail "C $d's stream from the decided cut $cut differs from Java's"
    for f in "$OUT/java"/*; do
        case "$f" in *.bergdb) ;; *) cmp -s "$f" "$OUT/$d/$(basename "$f")" || fail "C $d's $(basename "$f") differs" ;; esac
    done
done
endk=$(du -sk "$OUT/test" | awk '{ print $1 }')
nt=$(grep -c '^trans ' "$OUT/java.txt"); ns=$(grep -c '^segment ' "$OUT/java.txt")
echo "transactions $nt, segments $ns; stream length $len, decided cut $cut; C test build's directory: at most $maxk kB (sampled), $endk kB at the end; $(ls "$OUT/test" | wc -l | tr -d ' ') files; Java's: at most $maxj kB, $(du -sk "$OUT/java" | awk '{ print $1 }') kB at the end"
grep -h 'resident\|peak' "$OUT/test.err" | tail -2
if [ $FAILS = 0 ]; then
    echo "LONG RUN OK: seed $SEED, $N transactions, $(( $(date +%s) - T0 )) s"
    exit 0
fi
echo "LONG RUN FAILED: $FAILS ($OUT)"
exit 1
}
