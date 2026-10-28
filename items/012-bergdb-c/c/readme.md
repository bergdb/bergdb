BergDB's Core in C
==================

The C clone of BergDB's Core (bergdb item 012; the plan is 012-01): the
same database as Java's `bergdb.core`, with the same stream, byte for byte,
on F53 (macOS, Apple silicon). This directory is all of it (decision D1):
the library, its tests, the tools, and the Java side of the cross tests.
Its first parts, the build, the tests, the gate and the rules below, are
012-04's.


# 1. Build and test

    ./build.sh             the release and the test builds, into build/ (about 1 s)
    ./before-commit.sh     the C gate: must print C BEFORE COMMIT OK

Both are plain `sh`; Apple clang 21 as `cc` (or `CC=...`). `build.sh`
compiles every module with one `cc` call per build, with 012-01, 6.1's
flags (C17, every warning an error, `-fwrapv -ffp-contract=off`):

* `build/release/`: `-O2`;
* `build/test/`: `-O1 -g`, AddressSanitizer and UndefinedBehaviorSanitizer
  (`-fno-sanitize-recover=all`), and `BERGDB_TEST` (the allocator's checks).

Each has `libbergdb.a`, the tools (`bergdb-NAME` from `tools/NAME.c`), the
unit tests `unit` and the functional tests `func` (once `test/func/` has
any). `build.sh` also checks that `include/bergdb.h` compiles alone and
that `examples/*.c` compile, once 012-03 has written them.

`before-commit.sh` (012-01, 6.5) runs, in order, and stops at the first
failure with the tail of its output (all of it in `build/gate/`): the
build; the rules a tool can check (section 4); the unit tests in the test
build; the unit tests in the release build, then under macOS's `leaks`;
the functional tests likewise, when there are any; and
`test/cross/cross.sh quick`, when it exists (012-05). Java's gate,
`java/before-commit.sh`, is not touched.

The test programs run every test, or those whose names start with an
argument; `-l` lists them:

    build/test/unit                 all
    build/test/unit klong_ keys_    those of two modules

**Java's vectors.** `test/unit/vectors/*.txt` are what Java's own classes
give for fixed inputs (compare values, segments, hashes, checksums, the
byte codecs, and Java's arithmetic in `jsem.txt`). They are written by
`test/cross/java/Vectors.java` and committed, so that the unit tests run
without Java; `t_vectors.c` reads them. To write them again from Java, and
to check C against Java's latest without changing the committed ones:

    JAVA_HOME=/opt/homebrew/opt/openjdk test/cross/java-build.sh
    /opt/homebrew/opt/openjdk/bin/java -ea -cp build/java/classes bergdb.core.Vectors DIR
    BERGDB_VECTORS=DIR build/test/unit vectors_

012-05's cross tests do that and compare DIR with the committed files.
`records.txt` (012-06) holds a small stream that Java's `Db` wrote, its
records as `StoredTrans.parse` parses them, and records with one change
that Java refuses, with the exception; `t_records.c` reads it.


# 2. The layout

As 012-01, 6.3:

    readme.md            this file
    build.sh             the builds
    before-commit.sh     the C gate
    include/bergdb.h     the API (012-03)
    examples/            the API's examples (012-03)
    src/                 the library: one .c and .h per module
    test/unit/           unit tests, t_MODULE.c, and test.h, the framework
    test/unit/vectors/   Java's vectors
    test/func/           functional tests, through bergdb.h only
    test/cross/          the cross tests with Java: cross.sh, the Java harness
                         (java/, compiled by java-build.sh into build/java/)
    tools/               bergdb-scan, bergdb-dump, bergdb-run

The modules so far, each ported from its Java class:

| Module | Java | Prefix |
|---|---|---|
| `jsem.h` | Java's semantics (section 3) | `j_`, `J64` |
| `bytes` | `bergdb.common.Bytes` | `bytes_` |
| `checksum` | `bergdb.core.NodeChecksum` | `cks_` |
| `klong` | `bergdb.dag.Klong` | `kl_`, `KL_` |
| `keys` | `bergdb.dag.Keys` | `keys_` |
| `spos` | `bergdb.dag.Spos` | `spos_`, `SPOS_` |
| `mem` | the allocator (012-01, 4.5) | `mem_`, `MEM_` |
| `err` | errors: a code, Java's exception's name, a text (012-06) | `err_`, `ERR_` |
| `plat` | the platform: a directory's entries, files read (POSIX) | `plat_` |
| `stream` | `MemoryStream`; `FileStream`'s directory, read-only so far | `stream_` |
| `meta` | `bergdb.storage.MetaBlock` | `meta_`, `META_` |
| `rstream` | `RecoverableStream`'s reading side, and recovery's plan | `rs_`, `RS_` |
| `snode` | `NodeStream.bytesToNode`, the three `Stored*Node.parse` | `sn_`, `NODE_` |
| `strans` | `StoredTrans.Parser` | `st_`, `ST_` |
| `nstream` | `NodeStream`'s reads: the trans iterator, `readNode` | `ns_` |

The tools so far: `bergdb-scan PATH` (012-06), Java's `StreamScan` in C:
the same text, "streamscan 1", for every stream (`tools/scan.c`).


# 3. Java's semantics in C

Every task follows these rules (012-01, 6.2), so that C computes what Java
computes, bit for bit, where the bytes depend on it. The helpers are in
`src/jsem.h`; `jsem.txt` holds Java's own results for them, and
`t_jsem.c` checks the build flags they rely on.

1. **Types.** `long` is `int64_t`, `int` is `int32_t`, `short` is
   `int16_t`, `boolean` is `bool`. A `byte` is `int8_t` where its sign is
   used, and `uint8_t` for bytes in buffers. Java's array and offset are a
   pointer: `Bytes.bytesToLongLE(buf, off)` is
   `bytes_get_long_le(buf + off)`; an offset that is part of the result
   stays an offset (`NodeChecksum.sumWithZeroReplace`'s `replaceOffset`).
2. **Overflow wraps**, as Java's: the build's `-fwrapv` defines `+`, `-`,
   `*`, unary `-` and `<<` of negative values on `int64_t` and `int32_t`.
   `Keys.hash`'s `value = value * 37 + l` is the same line in C. Without
   `-fwrapv`, the test build stops in `t_jsem.c` (`jsem_wrapv`).
3. **Long literals with the high bit set** are `J64(...)`: Java's
   `0xc000000000000000L` is a negative long, C's `0xc000000000000000` an
   unsigned one, which would turn the whole expression unsigned.
   `Klong.getType`'s `value & 0xc000000000000000L` is
   `value & J64(0xc000000000000000)`; `TransSeq.dither`'s
   `pos * 0x9E3779B97F4A7C15L` is `pos * J64(0x9E3779B97F4A7C15)`.
4. **Shifts.** `>>>` is `j_ushr64` or `j_ushr32` (a shift of the unsigned
   type). A shift whose count is not a constant in 0 to 63 (0 to 31 for an
   int) is `j_shl64`, `j_shr64` and so on, which mask the count as Java
   does (`& 63`, `& 31`); in C a count of 64 is undefined, and UBSan stops
   on it. `Klong.createKey`'s `(0x00ffL & key[i]) << shift` is
   `j_shl64(0x00ff & key[i], shift)`; `Bytes.longToBytesLE`'s
   `(byte) (value >>> 8)` is `(uint8_t) j_ushr64(value, 8)`.
5. **Narrowing casts.** Java's `(int)`, `(short)` and `(byte)` of a wider
   integer keep the low bits: `j_l2i`, `j_l2s`, `j_l2b`; a store into a
   byte buffer is `(uint8_t)`. `Klong.getLength`'s
   `(int) ((value & 0x38L) >>> 3)` is `j_l2i(j_ushr64(value & 0x38, 3))`.
   Every narrowing is written, as Java requires (section 6).
6. **Signed bytes.** Java's bytes are -128 to 127, C's buffer bytes 0 to
   255. Java's `data[i] & 0xff` (`NodeChecksum.sum`) and
   `if (b0 < 0) b0 += 256` (`Bytes.bytesToUShortLE`) are the `uint8_t`
   itself. Where Java uses a byte's sign, C takes `j_l2b(p[i])`. Arithmetic
   on a byte wraps modulo 256 in both: `Keys.toBytes`'s `b++; b++` on a
   Java byte is the same on a `uint8_t`.
7. **Division.** `/` and `%` truncate toward 0 in both languages, and
   `Spos.addToAlign`'s `(mod - (a % mod)) % mod` is the same line in C.
   Where Java would throw `ArithmeticException` (a divisor 0), C checks
   first and returns the error that the exception becomes; C's division by
   0 is undefined. Where the divisor can be -1, `j_div64`, `j_rem64`,
   `j_div32`, `j_rem32` give Java's `MIN / -1 == MIN`. `Math.floorDiv` is
   `j_floor_div64` (`MemoryStream`).
8. **Doubles.** IEEE doubles in both, rounded to the nearest. Write Java's
   expression as it is, in its order and with its parentheses: C groups
   `a * b / c * d / e` as Java does, left to right. A `long` in a double
   expression needs a written `(double)` in C (Java widens it silently;
   section 6). No fused multiply-add: `-ffp-contract=off`, checked by
   `t_jsem.c` (`jsem_no_fma`); never `-ffast-math`. `TransSeq.take`'s share,
   `(double) dirtyCount * recordOwnBytes / ownBytes * (streamLength -
   currentSp) / startupDistance`, is
   `(double) dirtyCount * (double) recordOwnBytes / (double) ownBytes *
   (double) (streamLength - currentSp) / startupDistance`, and `jsem.txt`
   has Java's bits of it. A double divided by 0 gives infinity or NaN in
   both, not an error. Java's `Math` functions beyond the exact ones
   (`log`, `pow`, `exp`) may differ from C's in the last bit; on
   2026-10-28 the Core used them only in tests and in `StringUtil`'s text.
9. **Double to integer** is `j_d2l` or `j_d2i`: NaN gives 0, values out of
   range give the limits, others are truncated, as Java's cast; C's cast
   is undefined out of range. `StoredTrans`'s
   `(long) (totalSize * 1.20)` is `j_d2l(totalSize * 1.20)`.
10. **Comparisons** are the Java code's own: signed where it uses `<` or
    `Long.compare` (`j_cmp64`), unsigned where it uses
    `Long.compareUnsigned` (`j_cmpu64`) or masks. `Keys.compareKeys`
    compares signed and `Keys.compareArrays` unsigned, and each port does
    the same. Never compare an `int64_t` with a `size_t`.
11. **Text** that reaches the stream is formatted as Java's: `"" + long`
    is `"%" PRId64` (the same digits, `Long.MIN_VALUE` too), as in
    `Reclaim`'s table (`m.put("pStart", "" + pStart)`, 012-11).
12. **Asserts and exceptions.** Java's `assert` is C's `assert`, on in both
    builds (`NDEBUG` is never set), as Java's tests and gates run with
    `-ea`. An exception that Java throws for a caller's input becomes a
    return code: `Keys.toBytes` throws for the empty key, and
    `keys_ikey_to_bkey` returns false.
13. **Order.** Where Java's order reaches the bytes (a `HashMap`'s
    iteration, a sort), C reproduces it; 012-02 lists where.


# 4. Module rules

* **One `.c` and `.h` per module** in `src/` (header-only, like `jsem.h`,
  where it is only inline helpers). The header says which Java class the
  module ports and what it leaves out, and compiles alone.
* **Names.** `bergdb_` for the API (`include/bergdb.h`) only; inside, a
  short prefix per module (`kl_`, `keys_`, `cks_`), constants in capitals
  (`KL_MAX_TIME`). A ported function keeps Java's local names and order,
  line for line, so that it can be read beside the Java.
* **No global state** (P9): no writable global or static data in `src/`;
  everything hangs off the database handle. Constants are fine.
* **Errors are return codes**: the API's error codes (`bergdb.h`, 012-03),
  or `bool` for a refusal, with results through pointers. The library
  never exits or aborts but for a failed `assert`.
* **Memory through the allocator** (section 5): no `malloc`, `free` or the
  like outside `src/mem.c`. No large buffers on the stack and no recursion
  deeper than the tree (012-01, 4.5, point 8).
* **The platform in one place**: files, forces and the clock go through
  one module (from 012-06); the rest is ISO C17, without compiler
  extensions.

`before-commit.sh` checks three of these: no allocation or free outside
`src/mem.c` (a `grep` of `src/`), no writable data in the library (`nm -m`
of the release build's objects: nothing in `__DATA,__data`, `__bss`,
`__common` or thread-local sections), and a `.h` for each `.c`.


# 5. The allocator

`src/mem.h` (012-01, 4.5, point 1): every allocation and free of the
library goes through `mem_alloc`, `mem_zalloc`, `mem_realloc` and
`mem_free`, with the `struct mem` of its database, which counts the live
bytes in all and by kind (`MEM_INDEX`, `MEM_VALUE`, `MEM_HANDLE`,
`MEM_TABLE`, `MEM_BUFFER`, `MEM_CALLER`, `MEM_STATE`), the peak, the live
blocks, the allocations and the failed ones. The memory budget (012-12)
compares with these counts, and the tests check that nothing is live after
a close: `CHECK_MEM_ZERO(&m)` in `test/unit/test.h` prints the live bytes
by kind when it fails.

* **Sized free.** `mem_free` and `mem_realloc` take the block's size and
  kind, as allocated; the release build has no header. The test build puts
  16 bytes before each block and aborts on a free whose size or kind does
  not match.
* **NOMEM.** A failed allocation returns NULL; the caller frees what it
  built and returns NOMEM (012-01, 4.5, point 7).
* **The Nth allocation fails** when `fail_at` is N (both builds; one
  comparison). The allocation-failure runs set `fail_at` to 1, 2, 3, ...
  until a run makes fewer allocations than `fail_at`; every other run must
  give NOMEM and leave nothing live. `t_mem.c`'s `mem_failure_runs` is the
  pattern.


# 6. `-Wconversion`: kept

Decided in 012-04 (012-01, 6.1 left it open). `-Wconversion` (with
clang's sign conversions) warns on every implicit conversion that may
change a value: a narrowing, a change of sign, an integer to a double that
may round. **It stays**, for this reason: Java requires a written cast for
every narrowing and has no unsigned types, while C narrows and mixes signs
silently. With `-Wconversion`, C asks for exactly the casts that Java's
code already has, so a line-for-line port keeps them, and a forgotten one,
a silent truncation from `int64_t` to `int32_t` or a sign change, is a
compile error. The first modules show it: without their casts, the 6
modules give 32 warnings, 29 of them at Java's own `(byte)` casts in
`Bytes` and `Klong`, the other 3 where the allocator counts a `size_t` in
an `int64_t`; no warning asks for a cast that Java does not have. The cost is small and
clear: a written `(double)` for a `long` in a double expression, which Java
widens silently (rule 8, and it may round in both), and `(size_t)` for
lengths given to `memcpy` and `memset`, mostly in tests.


# 7. The tests

`test/unit/test.h` is the framework, one header: a test is
`TEST(name) { ... }`, listed in its file's table
(`const struct test MODULE_tests[]`, `TEST_ENTRY(name)`, `TEST_END`), and
`test/unit/main.c` lists the tables. `CHECK`, `REQUIRE` (returns from the
test), `CHECK_EQ` (two integers, both printed), `CHECK_BYTES` and
`CHECK_MEM_ZERO`; a failure prints its file and line and the test goes
on; the summary is `UNIT OK: ...` or `UNIT FAILED: ...`, with exit status
1. `test_random` is a deterministic generator for tests where Java's
`java.util.Random` values do not matter; where they do, the vectors have
Java's.

Each module's `t_MODULE.c` ports Java's `@Nano` tests of its class and
adds the edge cases (012-04, section 4: empty keys refused, keys of 6, 7,
8, 13 and 14 bytes, the bytes 0, 1, 0x7f, 0x80 and 0xff, `Long.MIN_VALUE`
in `hash`); `t_vectors.c` checks every line of Java's vectors and fails on
a kind of line it does not know, so that a new kind in `Vectors.java`
shows.
