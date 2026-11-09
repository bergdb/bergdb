#!/bin/sh
# The C clone's size (bergdb 012-15, item 5): code lines as 006-08 counts
# them (its lines.py: lines with code on them, not blank, not only a
# comment), and the library's machine code on arm64, text + data as
# llvm-size counts them (Berkeley), as 006-08's c-size.sh measured LMDB
# (52.7 kB at -Os). The library is src/*.c (and its headers) with
# include/bergdb.h; compiled with build.sh's flags but -Werror, at -O2, -Os,
# and -Os -DNDEBUG (asserts off; the builds keep them on, section 3, rule 12,
# of the C readme), and at -O2 -flto (the release build since 012-17): its
# objects are bitcode, so the library is linked as a dynamic library (every
# external function kept, as in the objects of the others) and the linker's
# native object of it (-object_path_lto) is measured. Then core_demo, linked
# with -dead_strip at -Os, -O2 and -O2 -flto: the library's bytes in it.
#
# Usage: sh bench/size.sh [OUT]      (from any directory; a few seconds)
#   OUT: a directory for the objects (default: a new temporary one).
# Needs clang as cc, xcrun llvm-size, python3.

set -e
C=$(cd "$(dirname "$0")/.." && pwd)
LINES=$C/../../006-2026-q4/08-core-layer/lines.py
OUT=${1:-$(mktemp -d "${TMPDIR:-/tmp}/bergdb-c-size.XXXXXX")}
mkdir -p "$OUT"
CC=${CC:-cc}
FLAGS="-std=c17 -fwrapv -ffp-contract=off -I$C/src -I$C/include"

code_lines() {    # code_lines FILE...: "LINES CODE"
    python3 -I "$LINES" "$@" | sed 's/^\([0-9]*\) lines, \([0-9]*\) code lines$/\1 \2/'
}

echo "== Lines (lines.py of 006-08: all lines, code lines)"
printf '%-40s %s\n' "library: src/*.c src/*.h include/bergdb.h" "$(code_lines "$C"/src/*.c "$C"/src/*.h "$C"/include/bergdb.h)"
printf '%-40s %s\n' "  of which src/*.c" "$(code_lines "$C"/src/*.c)"
printf '%-40s %s\n' "  of which src/*.h and bergdb.h" "$(code_lines "$C"/src/*.h "$C"/include/bergdb.h)"
printf '%-40s %s\n' "unit tests: test/unit/*.c *.h" "$(code_lines "$C"/test/unit/*.c "$C"/test/unit/*.h)"
printf '%-40s %s\n' "functional tests: test/func/*.c" "$(code_lines "$C"/test/func/*.c)"
printf '%-40s %s\n' "cross harness, Java: test/cross/java" "$(code_lines "$C"/test/cross/java/*.java)"
printf '%-40s %s\n' "tools: tools/*.c *.h" "$(code_lines "$C"/tools/*.c "$C"/tools/*.h)"
printf '%-40s %s\n' "examples: examples/*.c" "$(code_lines "$C"/examples/*.c)"
echo "== Code lines by module (src/NAME.c and .h)"
for f in "$C"/src/*.c; do
    m=$(basename "$f" .c)
    set -- $(code_lines "$f" "$C/src/$m.h")
    echo "$2 $m"
done | sort -rn > "$OUT/modules.txt"
cat "$OUT/modules.txt"

bytes() {    # text + data of the objects in directory $1
    xcrun llvm-size -B "$1"/*.o | awk 'NR > 1 { t += $1; d += $2 } END { printf "%d %d %d", t, d, t + d }'
}

echo "== Machine code, arm64 (text data text+data, bytes)"
for v in O2 Os Os-NDEBUG O2-flto; do
    rm -rf "$OUT/$v"
    mkdir -p "$OUT/$v"
    case $v in
    O2) opt="-O2" ;;
    Os) opt="-Os" ;;
    Os-NDEBUG) opt="-Os -DNDEBUG" ;;
    O2-flto) opt="-O2 -flto" ;;
    esac
    (cd "$OUT/$v" && $CC $FLAGS $opt -c "$C"/src/*.c)
    ar rcs "$OUT/$v/libbergdb.a" "$OUT/$v"/*.o
    if [ $v = O2-flto ]; then
        mkdir "$OUT/$v/native"
        $CC $opt -dynamiclib -o "$OUT/$v/libbergdb.dylib" -Wl,-all_load "$OUT/$v/libbergdb.a" \
            -Wl,-object_path_lto,"$OUT/$v/native/lto.o"
        printf '%-12s %s\n' "$v" "$(bytes "$OUT/$v/native")"
    else
        printf '%-12s %s\n' "$v" "$(bytes "$OUT/$v")"
    fi
done
echo "== By module at -Os (text + data)"
xcrun llvm-size -B "$OUT"/Os/*.o | awk 'NR > 1 { n = $NF; sub(".*/", "", n); print $1 + $2, n }' | sort -rn
echo "== Linked into an application: examples/core_demo.c, -dead_strip"
echo "   (by the linker's map: the bytes of the symbols from libbergdb.a's objects, and of all"
echo "   the program's symbols; with -flto the link's own object holds code and constants that"
echo "   the map does not give to a module, so only the program's total compares there)"
for v in Os O2 O2-flto; do
    case $v in
    O2) opt="-O2" ;;
    Os) opt="-Os" ;;
    O2-flto) opt="-O2 -flto" ;;
    esac
    $CC $FLAGS $opt -o "$OUT/core_demo-$v" "$C/examples/core_demo.c" "$OUT/$v/libbergdb.a" \
        -Wl,-dead_strip -Wl,-map,"$OUT/core_demo-$v.map"
    printf '%-12s ' "$v"
    python3 -I - "$OUT/core_demo-$v.map" <<'PY'
import re, sys
files, sizes, insyms = {}, {}, False
for line in open(sys.argv[1], errors="replace"):
    m = re.match(r"\[\s*(\d+)\] (.*)", line)
    if m and not insyms:
        files[int(m.group(1))] = m.group(2).strip()
        continue
    if line.startswith("# Symbols:"):
        insyms = True
        continue
    if line.startswith("# Dead Stripped Symbols:"):
        break
    m = re.match(r"0x[0-9A-F]+\s+0x([0-9A-F]+)\s+\[\s*(\d+)\]", line)
    if insyms and m:
        f = files.get(int(m.group(2)), "?")
        sizes[f] = sizes.get(f, 0) + int(m.group(1), 16)
lib = {f: n for f, n in sizes.items() if "libbergdb.a(" in f}
total = sum(lib.values())
print("library bytes in core_demo: %d, from %d of the archive's objects; the program's: %d"
      % (total, len(lib), sum(sizes.values())))
names = sorted(re.sub(r".*\((.*)\)", r"\1", f) for f in lib)
print("             objects linked: " + " ".join(names))
PY
done
echo "SIZE OK (objects: $OUT)"
