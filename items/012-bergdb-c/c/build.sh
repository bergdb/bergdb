#!/bin/sh
# Builds the C clone of BergDB's Core (bergdb 012) into build/, two builds
# with the flags of 012-01, section 6.1:
#   build/release/  -O2
#   build/test/     -O1 -g, AddressSanitizer and UndefinedBehaviorSanitizer,
#                   BERGDB_TEST (the allocator's checks, mem.h)
# each with libbergdb.a (src/*.c), the tools (tools/*.c, one program each,
# bergdb-NAME), the unit tests (test/unit/*.c, one program: unit), the
# functional tests (test/func/*.c, one program: func, when there are any)
# and the examples (examples/*.c, one program each, named as the file,
# with include/ only on their include path: bergdb.h's API alone; 012-13).
# Then checks that include/bergdb.h compiles alone.
#
# Usage: ./build.sh            (from any directory; a few seconds)
# Prints BUILD OK. Every warning is an error (-Werror).

set -e
C=$(cd "$(dirname "$0")" && pwd)
cd "$C"
CC=${CC:-cc}

WARN="-std=c17 -Wall -Wextra -Wpedantic -Wshadow -Wconversion -Werror -fwrapv -ffp-contract=off"
INC="-I$C/src -I$C/include -ffile-prefix-map=$C/="

build() {    # build NAME FLAGS...
    name=$1
    shift
    out=$C/build/$name
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
    # The examples (012-03), one program each, against bergdb.h only (012-13).
    for e in "$C"/examples/*.c; do
        [ -f "$e" ] || continue
        $CC $WARN -I"$C/include" "$@" -o "$out/$(basename "$e" .c)" "$e" "$out/libbergdb.a"
    done
}

build release -O2
build test -O1 -g -fsanitize=address,undefined -fno-sanitize-recover=all -DBERGDB_TEST

# The API header alone (written by 012-03).
if [ -f include/bergdb.h ]; then
    echo '#include "bergdb.h"' | $CC $WARN $INC -fsyntax-only -x c -
fi

echo "BUILD OK: build/release and build/test"
