#!/bin/sh
# Builds the C clone of BergDB's Core (bergdb 012) into build/, two builds
# with the flags of 012-01, section 6.1:
#   build/release/  -O2
#   build/test/     -O1 -g, AddressSanitizer and UndefinedBehaviorSanitizer,
#                   BERGDB_TEST (the allocator's checks, mem.h)
# each with libbergdb.a (src/*.c), the tools (tools/*.c, one program each,
# bergdb-NAME), the unit tests (test/unit/*.c, one program: unit), the
# functional tests (test/func/*.c, one program: func, when there are any)
# the examples (examples/*.c, one program each, named as the file,
# with include/ only on their include path: bergdb.h's API alone; 012-13)
# and the benchmarks (bench/*.c, likewise, bench-NAME; 012-15); in the test
# build also bergdb-power (test/stress/power.c with tools/run.c; 012-14).
# Then checks that include/bergdb.h compiles alone.
#
# Usage: ./build.sh            (from any directory; a few seconds)
# Prints BUILD OK. Every warning is an error (-Werror).
#   CC=...      the compiler (cc, Apple clang, by default)
#   WERROR=     (empty) warnings are not errors: for another compiler, by hand
#               (test/stress/gcc.sh: Homebrew's gcc 16; the gate is clang's, with -Werror)
#   BUILD=DIR   the builds go to DIR/release and DIR/test instead of build/

set -e
C=$(cd "$(dirname "$0")" && pwd)
cd "$C"
CC=${CC:-cc}
WERROR=${WERROR--Werror}
BUILD=${BUILD:-$C/build}

WARN="-std=c17 -Wall -Wextra -Wpedantic -Wshadow -Wconversion $WERROR -fwrapv -ffp-contract=off"
INC="-I$C/src -I$C/include -ffile-prefix-map=$C/="

build() {    # build NAME FLAGS...
    name=$1
    shift
    out=$BUILD/$name
    rm -rf "$out"
    mkdir -p "$out/obj"
    # The library: one cc call for every module.
    (cd "$out/obj" && $CC $WARN $INC "$@" -c "$C"/src/*.c)
    ar rcs "$out/libbergdb.a" "$out"/obj/*.o
    for t in "$C"/tools/*.c; do
        [ -f "$t" ] || continue
        $CC $WARN $INC "$@" -o "$out/bergdb-$(basename "$t" .c)" "$t" "$out/libbergdb.a"
    done
    $CC $WARN $INC -I"$C/test/unit" "$@" -DVECTORS_DIR="\"$C/test/unit/vectors\"" \
        -o "$out/unit" "$C"/test/unit/*.c "$out/libbergdb.a"
    if ls "$C"/test/func/*.c > /dev/null 2>&1; then
        $CC $WARN $INC -I"$C/test/unit" "$@" -o "$out/func" "$C"/test/func/*.c "$out/libbergdb.a"
    fi
    # The power-loss runner (012-14, test/stress/power.c), in the test build only: the
    # I/O seam is BERGDB_TEST's. tools/run.c with its main, sync and close renamed.
    if [ "$name" = test ]; then
        $CC $WARN $INC "$@" -Dmain=run_main -Dbergdb_sync=power_sync -Dbergdb_close=power_close \
            -c "$C/tools/run.c" -o "$out/power-run.o"
        $CC $WARN $INC "$@" -o "$out/bergdb-power" "$C/test/stress/power.c" "$out/power-run.o" \
            "$out/libbergdb.a"
        # The allocation-failure runner (012-14, test/stress/allocfail.c): run.c's calls
        # renamed to its wrappers.
        AF=""
        for f in open close trans_new trans_put trans_delete execute read_new get_one get_many \
                sync current_time set_startup_distance set_cache_size_indicator \
                set_retain_duration set_reclaim_internal_fraction; do
            AF="$AF -Dbergdb_$f=af_$f"
        done
        $CC $WARN $INC "$@" -Dmain=run_main $AF -c "$C/tools/run.c" -o "$out/allocfail-run.o"
        $CC $WARN $INC "$@" -o "$out/bergdb-allocfail" "$C/test/stress/allocfail.c" \
            "$out/allocfail-run.o" "$out/libbergdb.a"
    fi
    # The examples (012-03), one program each, against bergdb.h only (012-13).
    for e in "$C"/examples/*.c; do
        [ -f "$e" ] || continue
        $CC $WARN -I"$C/include" "$@" -o "$out/$(basename "$e" .c)" "$e" "$out/libbergdb.a"
    done
    # The benchmarks (012-15), one program each, against bergdb.h only.
    for b in "$C"/bench/*.c; do
        [ -f "$b" ] || continue
        $CC $WARN -I"$C/include" "$@" -o "$out/bench-$(basename "$b" .c)" "$b" "$out/libbergdb.a"
    done
}

build release -O2
build test -O1 -g -fsanitize=address,undefined -fno-sanitize-recover=all -DBERGDB_TEST

# The API header alone (written by 012-03).
if [ -f include/bergdb.h ]; then
    echo '#include "bergdb.h"' | $CC $WARN $INC -fsyntax-only -x c -
fi

echo "BUILD OK: $BUILD/release and $BUILD/test"
