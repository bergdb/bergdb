#!/bin/sh
# The C gate of BergDB's Core in C (bergdb 012-01, section 6.5): it must
# print C BEFORE COMMIT OK before C code is committed. Java's gate,
# java/before-commit.sh, stays as it is; this one does not touch java/.
#
# Usage: ./before-commit.sh      (from any directory; seconds while the
#                                 tests are few, a target of 2 minutes)
#
# The steps, in order; each writes its output to build/gate/STEP.txt and
# prints one line. The first that fails stops the gate: the tail of its
# output, then C BEFORE COMMIT FAILED: STEP.
#   build         build.sh: the release and the test builds, every warning
#                 an error (-Werror); include/bergdb.h alone and examples/*.c
#                 when they exist (012-03)
#   rules         the module rules of readme.md (section 4) that a tool can
#                 check: no malloc, free or the like outside src/mem.c; no
#                 writable global or static data in the library (P9); a .h
#                 for each .c of src/
#   unit          the unit tests in the test build (AddressSanitizer and
#                 UndefinedBehaviorSanitizer)
#   unit-release  the unit tests in the release build, under macOS's leaks
#   func          the functional tests in the test build, when there are any
#   func-release  the functional tests in the release build, under leaks
#   cross         test/cross/cross.sh quick, when it exists (012-05), with C's
#                 tools of the test build as side B (C=build/test: bergdb-scan
#                 since 012-06, under the sanitizers), Java's where C has none;
#                 KEEP=1, for the next step
#   write         test/cross/writecheck.sh on the quick set's Java directories
#                 (012-09, part 1): C's take replayed on every record, and the
#                 records re-appended through C's append path, the
#                 directories equal to Java's; C's tools of the test build
#   examples      examples/compare.sh with the test build (012-13): the
#                 examples run under the sanitizers, get_many_prefix prints
#                 Java's output, and core_demo and Java's CoreDemo print the
#                 same on each other's databases (the Java classes of the
#                 cross step)

C=$(cd "$(dirname "$0")" && pwd)
cd "$C" || exit 1
G=$C/build/gate
START=$(date +%s)
export UBSAN_OPTIONS=${UBSAN_OPTIONS:-print_stacktrace=1}
export ASAN_OPTIONS=${ASAN_OPTIONS:-detect_stack_use_after_return=1:strict_string_checks=1}

step() {        # step NAME COMMAND...
    name=$1
    shift
    t0=$(date +%s)
    mkdir -p "$G"
    if "$@" > "$G/$name.txt" 2>&1; then
        echo "  $name: ok ($(( $(date +%s) - t0 )) s) $(tail -1 "$G/$name.txt")"
    else
        echo "--- the tail of build/gate/$name.txt:"
        tail -40 "$G/$name.txt"
        echo "C BEFORE COMMIT FAILED: $name"
        exit 1
    fi
}

rules() {
    bad=0
    # Every allocation and free of the library through the allocator
    # (012-01, 4.5, point 1).
    if grep -nE '(^|[^A-Za-z0-9_])(malloc|calloc|realloc|reallocf|free|strdup|strndup|aligned_alloc|posix_memalign|valloc)[[:space:]]*\(' \
            $(ls src/*.c src/*.h | grep -v '^src/mem\.c$'); then
        echo "rules: an allocation or a free outside src/mem.c, above"
        bad=1
    fi
    # No global state (P9): nothing in the writable data of the release
    # build's objects (constants are in __TEXT,__const or __DATA,__const).
    if nm -m build/release/obj/*.o \
            | grep -E '\(__DATA,__(data|bss|common|thread_vars|thread_bss|thread_data)\)|\(common\)'; then
        echo "rules: writable global or static data in the library, above"
        bad=1
    fi
    for c in src/*.c; do
        if [ ! -f "${c%.c}.h" ]; then
            echo "rules: $c has no ${c%.c}.h"
            bad=1
        fi
    done
    [ $bad = 0 ] && echo "rules ok: $(ls src/*.c | wc -l | tr -d ' ') modules"
}

# A test program of the release build: its own result, then under leaks
# (a second run) no leak at its exit.
leaks_run() {   # leaks_run PROGRAM
    out=$G/$(basename "$1")-release
    if ! "$1" > "$out.txt" 2>&1; then
        cat "$out.txt"
        return 1
    fi
    leaks --atExit -- "$1" > "$out-leaks.txt" 2>&1
    if ! grep -q ': 0 leaks for 0 total leaked bytes' "$out-leaks.txt"; then
        cat "$out-leaks.txt"
        return 1
    fi
    echo "$(tail -1 "$out.txt"), and no leaks"
}

step build ./build.sh
step rules rules
step unit build/test/unit
step unit-release leaks_run build/release/unit
if [ -x build/test/func ]; then
    step func build/test/func
    step func-release leaks_run build/release/func
fi
if [ -f test/cross/cross.sh ]; then
    step cross sh test/cross/cross.sh quick C=build/test KEEP=1
    step write sh test/cross/writecheck.sh build/cross/quick C=build/test
fi
if [ -f examples/compare.sh ]; then
    step examples sh examples/compare.sh build/test
fi
echo "C BEFORE COMMIT OK ($(( $(date +%s) - START )) s)"
