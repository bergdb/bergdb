#!/bin/sh
# Machine code per line of C, for the estimate of a C clone's size (bergdb
# 006-08, section 6.3). Downloads three C libraries, each into a directory of
# its own, counts their code lines (lines.py) and compiles them with -Os:
#   LMDB 0.9.33, mdb.c and midl.c: a copy-on-write B+tree database.
#   littlefs 2.9.3, lfs.c and lfs_util.c: a power-loss safe file system for
#     flash on microcontrollers; also for a Cortex-M4 (Thumb-2), freestanding,
#     with its debug output, asserts and malloc off (LFS_NO_*).
#   SQLite 3.49.1, the amalgamation, with its default options.
# Prints, for each: code lines, bytes of code and data (text + data, as
# llvm-size counts them), and bytes per code line.
#
# Usage: sh c-size.sh
#   Needs clang (Apple's has the Arm targets), xcrun llvm-size, curl, unzip
#   and python3. About 15 s. Output in $OUT (default: a new temporary
#   directory).

set -e
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/bergdb-c-size.XXXXXX")}
mkdir -p "$OUT/lmdb" "$OUT/littlefs" "$OUT/sqlite" "$OUT/obj" "$OUT/stub"

curl -sSfL -o "$OUT/lmdb/lmdb.tar.gz" \
    https://github.com/LMDB/lmdb/archive/refs/tags/LMDB_0.9.33.tar.gz
curl -sSfL -o "$OUT/littlefs/littlefs.tar.gz" \
    https://github.com/littlefs-project/littlefs/archive/refs/tags/v2.9.3.tar.gz
curl -sSfL -o "$OUT/sqlite/sqlite.zip" \
    https://www.sqlite.org/2025/sqlite-amalgamation-3490100.zip
tar xzf "$OUT/lmdb/lmdb.tar.gz" -C "$OUT/lmdb"
tar xzf "$OUT/littlefs/littlefs.tar.gz" -C "$OUT/littlefs"
unzip -q "$OUT/sqlite/sqlite.zip" -d "$OUT/sqlite"
M=$OUT/lmdb/lmdb-LMDB_0.9.33/libraries/liblmdb
L=$OUT/littlefs/littlefs-2.9.3
Q=$OUT/sqlite/sqlite-amalgamation-3490100

# The two headers of the C library that littlefs needs and a freestanding
# Thumb-2 build does not have.
cat > "$OUT/stub/string.h" <<'EOF'
#include <stddef.h>
void *memcpy(void *, const void *, size_t);
void *memset(void *, int, size_t);
int memcmp(const void *, const void *, size_t);
size_t strlen(const char *);
char *strcpy(char *, const char *);
char *strchr(const char *, int);
size_t strspn(const char *, const char *);
size_t strcspn(const char *, const char *);
EOF
printf '#include <stdint.h>\n' > "$OUT/stub/inttypes.h"

LFS_OFF="-DLFS_NO_DEBUG -DLFS_NO_WARN -DLFS_NO_ERROR -DLFS_NO_ASSERT -DLFS_NO_MALLOC"
THUMB="-target thumbv7em-none-eabi -mcpu=cortex-m4 -mthumb -ffreestanding"
cd "$OUT/obj"
clang -Os -w -c -I"$M" "$M/mdb.c" "$M/midl.c"
mkdir -p lfs-arm64 lfs-thumb
(cd lfs-arm64 && clang -Os -w -c -I"$L" $LFS_OFF "$L/lfs.c" "$L/lfs_util.c")
(cd lfs-thumb && clang $THUMB -Os -w -c -I"$L" -isystem "$OUT/stub" $LFS_OFF \
    "$L/lfs.c" "$L/lfs_util.c")
clang -Os -w -c -I"$Q" "$Q/sqlite3.c"

# text + data of the object files $@, as llvm-size prints them (Berkeley).
bytes() {
    xcrun llvm-size -B "$@" | awk 'NR > 1 { s += $1 + $2 } END { print s }'
}

code_lines() {
    python3 -I "$HERE/lines.py" "$@" | sed 's/.*, \([0-9]*\) code lines/\1/'
}

row() {
    name=$1 lines=$2 b=$3
    awk -v n="$name" -v l="$lines" -v b="$b" \
        'BEGIN { printf "%-28s %7d code lines %8d bytes %5.1f bytes a line\n", n, l, b, b / l }'
}

LM=$(code_lines "$M/mdb.c" "$M/midl.c" "$M/midl.h" "$M/lmdb.h")
LL=$(code_lines "$L/lfs.c" "$L/lfs_util.c" "$L/lfs.h" "$L/lfs_util.h")
LQ=$(code_lines "$Q/sqlite3.c")
row "LMDB, arm64" "$LM" "$(bytes mdb.o midl.o)"
row "littlefs, arm64" "$LL" "$(bytes lfs-arm64/lfs.o lfs-arm64/lfs_util.o)"
row "littlefs, Cortex-M4" "$LL" "$(bytes lfs-thumb/lfs.o lfs-thumb/lfs_util.o)"
row "SQLite, arm64" "$LQ" "$(bytes sqlite3.o)"
echo "C SIZE OK (output: $OUT)"
