#!/bin/sh
# The C clone's size (bergdb 012-15, item 5): code lines as 006-08 counts
# them (its lines.py: lines with code on them, not blank, not only a
# comment), and the library's machine code on arm64, text + data as
# llvm-size counts them (Berkeley), as 006-08's c-size.sh measured LMDB
# (52.7 kB at -Os). The library is src/*.c (and its headers) with
# include/bergdb.h; compiled with build.sh's flags but -Werror, at -O2 (the
# release build), -Os, and -Os -DNDEBUG (asserts off; the builds keep them on,
# section 3, rule 12, of the C readme).
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
for v in O2 Os Os-NDEBUG; do
    rm -rf "$OUT/$v"
    mkdir -p "$OUT/$v"
    case $v in
    O2) opt="-O2" ;;
    Os) opt="-Os" ;;
    Os-NDEBUG) opt="-Os -DNDEBUG" ;;
    esac
    (cd "$OUT/$v" && $CC $FLAGS $opt -c "$C"/src/*.c)
    printf '%-12s %s\n' "$v" "$(bytes "$OUT/$v")"
done
echo "== By module at -Os (text + data)"
xcrun llvm-size -B "$OUT"/Os/*.o | awk 'NR > 1 { n = $NF; sub(".*/", "", n); print $1 + $2, n }' | sort -rn
echo "== Linked into an application at -Os: examples/core_demo.c, -dead_strip"
echo "   (the library's bytes in the program, by the linker's map: sections of libbergdb.a's objects)"
ar rcs "$OUT/Os/libbergdb.a" "$OUT"/Os/*.o
$CC $FLAGS -Os -o "$OUT/core_demo" "$C/examples/core_demo.c" "$OUT/Os/libbergdb.a" \
    -Wl,-dead_strip -Wl,-map,"$OUT/core_demo.map"
python3 -I - "$OUT/core_demo.map" <<'PY'
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
print("library bytes in core_demo: %d, from %d of the archive's objects" % (total, len(lib)))
names = sorted(re.sub(r".*\((.*)\)", r"\1", f) for f in lib)
print("objects linked: " + " ".join(names))
PY
echo "SIZE OK (objects: $OUT)"
