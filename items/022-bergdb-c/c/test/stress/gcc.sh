#!/bin/sh
# A second compiler, by hand (bergdb 012-14, done item 6; not in the gate, whose
# compiler is Apple clang with -Werror): Homebrew's gcc 16 builds both builds without
# -Werror into OUT/build, its warnings counted (the library's: none since 012-14; the
# tests' and the examples' -Wformat-truncation of paths into fixed buffers remain, as
# meant), then the unit and functional tests run in both builds (the test build under
# gcc's AddressSanitizer and UndefinedBehaviorSanitizer).
#
# Usage: test/stress/gcc.sh
#   GCC  (environment) the compiler, gcc-16 by default
#   OUT  (environment) /Users/f/fl/bench/022/out/gcc by default
# Prints GCC OK or GCC FAILED, with the warnings: in the library, and in all.
{
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
CDIR=$(cd "$HERE/../.." && pwd)
GCC=${GCC:-gcc-16}
OUT=${OUT:-/Users/f/fl/bench/022/out/gcc}
mkdir -p "$OUT"
T0=$(date +%s)
if ! CC=$GCC WERROR= BUILD="$OUT/build" sh "$CDIR/build.sh" > "$OUT/build.txt" 2>&1; then
    tail -20 "$OUT/build.txt"
    echo "GCC FAILED: the build"
    exit 1
fi
all=$(grep -c 'warning:' "$OUT/build.txt")
lib=$(grep 'warning:' "$OUT/build.txt" | grep -c '/src/\|^src/')
fails=0
for b in test release; do
    for p in unit func; do
        "$OUT/build/$b/$p" > "$OUT/$b-$p.txt" 2>&1 || fails=$((fails + 1))
        echo "$b $p: $(tail -1 "$OUT/$b-$p.txt")"
    done
done
if [ "$fails" = 0 ] && [ "$lib" = 0 ]; then
    echo "GCC OK: $GCC $($GCC -dumpfullversion), both builds without -Werror: $lib warnings in the library, $all in all (the tests' and the examples'); the unit and functional tests pass in both ($(( $(date +%s) - T0 )) s)"
    exit 0
fi
echo "GCC FAILED: $fails test programs failed, $lib warnings in the library ($OUT/build.txt)"
exit 1
}
