BergDB's Core in C
==================

The C clone of BergDB's Core (bergdb item 012; the plan is 012-01): the
same database as Java's `bergdb.core`, with the same stream, byte for byte,
on F53 (macOS, Apple silicon). This directory is all of it (decision D1):
the library, its tests, the tools, and the Java side of the cross tests.
Its first parts, the build, the tests, the gate and the rules below, are
012-04's.

**Which Java.** C is a port of **Java release 2026.2** (the tag
`release-2026.2`, `95bde62`, 2026-11-04; bergdb 015-02), not of the Java
of the day: it writes that release's bytes, opens its databases and
refuses what it refuses, and its API follows `Db`'s public methods there.
It does not follow Java's changes after the release, and it is meant to
stay as it is (Frans, 2026-11-05): a port of a later release would most
likely be done in another item or in another repository. The cross tests
compare with the release's Java: `test/cross/java-build.sh` compiles the
Core Layer from `releases/2026.2/bergdb-2026.2-src.zip`, checked against
its `SHA256SUMS` and extracted once into `build/java-src/`.
`JAVA_REF=tree` compiles the repository's `java/` instead, and
`JAVA_REF=DIR` another Java tree; both differ from C where Java changed
after the release. Until 2026-11-05 C followed `main` as of 2026-10-29
(`ae4aaf9`).


# 1. Build and test

    ./build.sh             the release and the test builds, into build/ (about 30 s)
    ./before-commit.sh     the C gate: must print C BEFORE COMMIT OK

Both are plain `sh`; Apple clang 21 as `cc` (or `CC=...`). `build.sh`
compiles every module with one `cc` call per build, with 012-01, 6.1's
flags (C17, every warning an error, `-fwrapv -ffp-contract=off`):

* `build/release/`: `-O2 -flto` (link-time optimization, 012-17, below);
* `build/test/`: `-O1 -g`, AddressSanitizer and UndefinedBehaviorSanitizer
  (`-fno-sanitize-recover=all`), and `BERGDB_TEST` (the allocator's checks).

**Link-time optimization** (012-17). The release build's objects in
`build/release/obj/` are LLVM bitcode, not machine code; each program's
link optimizes the library and the program as one, so the small helpers
that the hot paths call across modules (`klong`, `keys`, `node`) are
inlined, which `-O2` alone cannot do across files (012-15, 6.4: +15 to +34
percent). An application that links `libbergdb.a` therefore links with
clang and `-flto` too (`ld` reads the bitcode through Apple's
`libLTO.dylib`); `LTO= ./build.sh` builds the release without it, `-O2`
alone. The flags of Java's semantics (section 3) hold at the link without
anything more: `-fwrapv` and `-ffp-contract=off` act when clang turns C
into bitcode, and what they decide is in the bitcode, instruction by
instruction: signed arithmetic without `nsw` (so no optimization may
assume that it does not wrap), and multiplies and adds without the
`contract` flag and no `llvm.fmuladd` (so none may be fused). The link
keeps that; clang 21's driver gives the link step (`ld`) only `-O2` and
`-lto_library` (seen with `cc -###`), none of the two flags, and needs
none (`-Wl,-mllvm,...` would be for the optimizer's own options, none of
which is needed). Checked on 2026-10-29 with two files, a function in one
and its caller in the other, linked with `-flto`: `x + 1 > x` across them
stays false at `Long.MAX_VALUE` with `-fwrapv` and folds to true without
it; `a * b + c` across them gives Java's 0 with `-ffp-contract=off` and
`-0x1p-60` (an `fmadd`) only with `-ffp-contract=fast`. `t_jsem.c`'s
`jsem_wrapv` and `jsem_no_fma` run in the release build's `unit`, which is
linked with `-flto`. One test met the optimizer's wider view:
`mem_too_large` (`t_mem.c`) passes its results through a volatile, as a
`malloc` whose block is never used may be removed and taken as succeeded
once `mem_alloc` is inlined into the test. The gate's rule of no global
state (section 4) reads the bitcode's symbols (`nm` shows writable
variables as `(LTO,DATA)`).

Each has `libbergdb.a`, the tools (`bergdb-NAME` from `tools/NAME.c`), the
unit tests `unit`, the functional tests `func`, and the examples
(`core_demo`, `get_many_prefix`: one program each, built with `include/`
only on their include path), and the benchmarks against Java
(`bench-cbench`, 012-15; `bench/bench.sh` runs them); the test build also
has the robustness runners of 012-14, `bergdb-power` and
`bergdb-allocfail` (section 10). `build.sh` also checks that
`include/bergdb.h` compiles alone. `CC=` names another compiler, `WERROR=`
(empty) turns `-Werror` off, `BUILD=DIR` builds into DIR (section 10, gcc).

`before-commit.sh` (012-01, 6.5) runs, in order, and stops at the first
failure with the tail of its output (all of it in `build/gate/`): the
build; the rules a tool can check (section 4); the unit tests in the test
build; the unit tests in the release build, then under macOS's `leaks`;
the functional tests likewise; `test/cross/cross.sh quick` (012-05) and
`writecheck.sh`; the allocation failures in turn on a small workload
(`bergdb-allocfail`, 012-14, section 10); and `examples/compare.sh`
(012-13), which runs the examples under the sanitizers and compares them
with Java (section 8).
Java's gate, `java/before-commit.sh`, is not touched.

The test programs run every test, or those whose names start with an
argument; `-l` lists them:

    build/test/unit                 all
    build/test/unit klong_ keys_    those of two modules

**Java's vectors.** `test/unit/vectors/*.txt` are what Java's own classes
give for fixed inputs (compare values, segments, hashes, checksums, the
byte codecs, and Java's arithmetic in `jsem.txt`). They are written by
`test/cross/java/Vectors.java` and committed, so that the unit tests run
without Java; `t_vectors.c` reads them. They are release 2026.3's (written
again on 2026-11-09, 022-01, step 0). To write them again from Java, and to check
C against the Java that `JAVA_REF` chooses (above; the release by default)
without changing the committed ones:

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
    examples/            the API's examples (012-03), and compare.sh, which
                         checks them against Java (012-13)
    src/                 the library: one .c and .h per module
    test/unit/           unit tests, t_MODULE.c, and test.h, the framework
    test/unit/vectors/   Java's vectors
    test/func/           functional tests, through bergdb.h only; java/ holds
                         StatsProbe.java, Java's side of f_settings.c's status test
    test/cross/          the cross tests with Java: cross.sh, the Java harness
                         (java/, compiled by java-build.sh into build/java/)
    test/stress/         the robustness runs (012-14, section 10), by hand: random.sh,
                         long.sh, corrupt.sh, power.sh (power.c; java/PowerImages.java),
                         allocfail.sh (allocfail.c, allocfail.wl), gcc.sh
    tools/               bergdb-scan, bergdb-dump, bergdb-run
    bench/               the benchmarks against Java (012-15): bench-cbench (cbench.c),
                         JBench.java, bench.sh (the runs), summary.py, size.sh

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
| `plat` | the platform: a directory's entries, files read and written, forces (`F_FULLFSYNC`), the lock, the time, random bytes (POSIX, macOS); in the test build the I/O seam of the writes, forces and deletes (`plat_io_set`, 012-14) | `plat_` |
| `stream` | `MemoryStream`; `FileStream`'s directory, read-only or for writing (the lock, the files' names and sizes, the write buffer) | `stream_` |
| `meta` | `bergdb.storage.MetaBlock` | `meta_`, `META_` |
| `rstream` | `RecoverableStream`'s reading side, and recovery's plan | `rs_`, `RS_` |
| `snode` | `NodeStream.bytesToNode`, the three `Stored*Node.parse` | `sn_`, `NODE_` |
| `strans` | `StoredTrans.Parser` | `st_`, `ST_` |
| `nstream` | `NodeStream`'s reads: the trans iterator, `readNode` | `ns_` |
| `obj` | the counted objects of the index, the pending list, safe points, the recount, close's walk (012-07, 6.4) | `obj_`, `OBJ_` |
| `node` | `bergdb.dag.Node`, `Pointer`, `KlongWithPointer`, `AccessData`'s constants | `node_`, `ptr_`, `kwp_` |
| `handle` | `bergdb.dag.Handle`, and `Cache3`'s changes of a handle | `hd_` |
| `knode` | `bergdb.dag.KeyNode`, and `StoredKeyNode.parse`'s object | `kn_` |
| `tnode` | `bergdb.dag.TopNode`, and `StoredTopNode.parse`'s object | `tn_`, `TN_` |
| `vnode` | `bergdb.dag.ValueNode`, and `StoredValueNode.parse`'s object | `vn_` |
| `topds` | `bergdb.dag.TopDs` | `tds_` |
| `opdata` | `bergdb.dag.OpData`, and the Dag's interfaces (follower, listeners, cache policy) | `op_`, `OP_` |
| `nwrite` | the writers: `StoredKeyNode.toLongs`, `StoredTopNode.toLongs`, `StoredValueNode.toBytes` | `nw_` |
| `dag` | `bergdb.dag.Dag` (putKv, getOne, dirtyNodeBound), `PutData`, `GetData`, `KeyAccessPath` (012-08) | `dag_`, `pd_`, `kap_`, `DAG_` |
| `getmany` | `bergdb.dag.GetMany`: the chain, the stop conditions, `Dag.getMany` | `gm_`, `GM_` |
| `mdb` | a database of Level 0 in memory: Db's creation, puts and deletes at a transaction's time, reads with `DbClock.lookupTime` | `mdb_` |
| `replay` | Java's databases read by a full replay of the stream (Level 1): `Db.start`'s checks and reports, `getTrans` | `replay_` |
| `clock` | `DbClock`, `SystemClock`, `CoreTestClock` (012-09, part 1) | `clk_`, `dbclock_` |
| `keymod` | `KeyModSet`, the STM's conflict set (012-09, part 1) | `kms_` |
| `transseq` | `TransSeq` (D and the paced take), `TransInfo`, `StartupPos` (012-09, part 1) | `ts_` |
| `strmap` | `StringMap`, reclaim's table text (012-09, part 1) | `sm_` |
| `reclaim` | `Reclaim`: iterations, steps, the table, the cut (012-11, part 1) | `rc_` |
| `trans` | `Trans` and `Trans.Builder`, with `Kv` (012-09) | `tr_` |
| `transnodes` | `TransNodes`, a record's nodes (012-09) | `tns_` |
| `serial` | `StoredTrans.Serializer` and `NodeStream.appendNodes`, the record writer (012-09) | `ser_` |
| `db` | `Db`: the creation and the start (012-10: through `starter`), `execute` with its checks, the marking, `store` with the take, `setStartupDistance`, reads, sync, close (012-09) | `db_`, `DB_` |
| `api` | `include/bergdb.h`'s functions, and the structs of its handles (012-09) | `api_` |
| `lmap` | a map from a long to a long, `HashMap<Long, Long>` where its order does not matter (012-10) | `lmap_` |
| `ntable` | the node table, `Cache3` in part: register, install, makeCanonical, the live handles (012-10); evict, its bytes and shrink (012-12) | `nt_` |
| `ncoll` | `NodeCollection`: the followers that load with Rule R and the cut back, `resolvePointers`, `linkToCanonical` (012-10) | `nc_` |
| `recover` | `RecoverableStream.recover` with its fill (012-10) | `rcv_` |
| `starter` | `Db.startInner`'s checks, recovery and start, and `DbStarter`: the bounded startup with its rerun (012-10) | `sr_`, `SR_` |
| `sdb` | a database opened by the bounded startup, for reads: `bergdb-dump`'s and the tests' (012-10) | `sdb_` |
| `evict` | `Eviction` (the capacity controller, made deterministic: CLOCK over the node table at the ends of calls, the pins, the admission of large values) and `Cache3.clockStep`, Level 4 (012-12) | `ev_`, `EV_` |

The tools so far: `bergdb-scan PATH` (012-06), Java's `StreamScan` in C:
the same text, "streamscan 1", for every stream (`tools/scan.c`);
`bergdb-dump [-maxnode N] [-large] [-replay] [-check] DIR SCAN` (012-08,
012-10), Java's `Dump` in C: the same text, "bergdb-dump 1", the database
opened by the bounded startup (or by a full replay of the stream with
`-replay`), for a database without reclaim's table or cut (exit status 3
for one that has them; `cross.sh` gives those to Java's dumper); and
`bergdb-dump -probe [-maxnode N] [-check] DIR`, one line of what a start
rebuilt and read (012-10, 6.2) (`tools/dump.c`);
`bergdb-run [-v] [-segments A[-B]] [-budget N] [-mem] WORKLOAD DIR` (012-09,
012-10), Java's `Run` in C through `bergdb.h` only: the same text,
"bergdb-run 1", and Java's bytes, for every workload, restarts and reclaim
included (012-11), and under any memory budget (`-budget`, `-mem`'s report
of the resident and pinned bytes, 012-12) (`tools/run.c`). Part 1 of 012-09
added `bergdb-takecheck`, `bergdb-reappend` and `bergdb-clockcheck`
(`tools/readme.md`).


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
   `value & J64(0xc000000000000000)`; `TransSeq.ditherFp`'s
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
8. **No doubles decide** (bergdb 005-79, as Java's Core since release
   2026.2): the stream's bytes and the memory are decided in integers.
   The take's share and dither are in units of 2^-16 (`ts_share_fp`, with
   Java's 128-bit product `j_mulhi64` and its division `ts_divlu`, and
   `ts_dither_fp`), reclaim's fraction is an integer in units of 2^-16
   (`rc_fraction_of`), its spacing `retainDuration / 4`, and eviction's low
   watermark `ev_low_of`. A double is left only at the API, converted at
   once (`bergdb_set_reclaim_internal_fraction`), or as a statistic
   (`bergdb_stats`' `internal_fraction`), and in `jsem.h`'s conversions and
   `bytes`' codecs of a user's value. The gate's rules step refuses any
   other (`test/doubles.py`, the counterpart of `java/doubles.py`).
   Where a double remains: IEEE doubles in both, rounded to the nearest;
   Java's expression as it is, in its order and with its parentheses; a
   `long` in a double expression with a written `(double)` (section 6); no
   fused multiply-add (`-ffp-contract=off`, checked by `t_jsem.c`'s
   `jsem_no_fma`); never `-ffast-math`. Until 005-79 the take's share was
   such an expression, `(double) dirtyCount * (double) recordOwnBytes /
   (double) ownBytes * (double) (streamLength - currentSp) /
   startupDistance`.
9. **Double to integer** is `j_d2l` or `j_d2i`: NaN gives 0, values out of
   range give the limits, others are truncated, as Java's cast; C's cast
   is undefined out of range. `Math.round` is `j_round`, line for line as
   the JDK's: `Db.setReclaimInternalFraction`'s
   `(int) Math.round(internalFraction * 65536)` is
   `j_l2i(j_round(f * (double) RC_FRACTION_ONE))`. `jsem.txt` has Java's
   results of each.
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
`__common` or thread-local sections), and a `.h` for each `.c`. And
section 3, rule 8: no double or float in `src/` outside the allowed places
of `test/doubles.py`, each with its reason (005-79), with a self-test.


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


# 8. The API in short

To see it run, from this directory (a JDK for the last line):

    ./build.sh                              # about 20 s
    build/release/core_demo /tmp/fruit      # C's CoreDemo: a new database, a restart
    build/release/get_many_prefix           # getMany with a prefix, in memory
    build/release/func durable_             # kill -9 and restarts (section 9)
    sh examples/compare.sh                  # the examples against Java's, both ways

`include/bergdb.h` is the API (012-03); its top comment has the rules, and
each declaration its errors and who owns what. In short:

```c
#include "bergdb.h"

char err[BERGDB_ERRBUF_SIZE];
bergdb_db *db;
if (bergdb_open("mydb", NULL, &db, NULL, err) != BERGDB_OK) {     /* defaults */
    fprintf(stderr, "open: %s\n", err);         /* "DirectoryInUseException: ..." */
    exit(1);
}

uint8_t key[64];                                /* keys are bkeys: bytes */
size_t len = strlen("/fruit/apple");
bergdb_ikey_to_bkey((const uint8_t *) "/fruit/apple", len, key);

bergdb_trans *t;                                /* a transaction: Java's Trans.Builder */
bergdb_trans_new(db, &t);
bergdb_trans_put(t, key, len, (const uint8_t *) "red", 3);      /* copied */
struct bergdb_executed ex;
int rc = bergdb_execute(db, t, &ex);            /* ex.tt, ex.tpos, ex.last_pos */
if (rc != BERGDB_OK) {
    fprintf(stderr, "%s: %s\n", bergdb_errname(rc), bergdb_errmsg(db));
}
bergdb_trans_free(t);
bergdb_sync(db, 0, BERGDB_SYNC_ORDINARY);       /* durable now (section 9) */

bergdb_read *rd;                                /* a read context: GetData, GetMany */
bergdb_read_new(db, &rd);
struct bergdb_one one;
bergdb_get_one(db, rd, BERGDB_LATEST, key, len, &one);
/* one.value: NULL if none; else valid until rd's next call */
bergdb_read_free(rd);

bergdb_close(db);                               /* writes, forces, frees all */
```

* **Open.** `bergdb_open(dir, opt, &db, &info, errbuf)` creates the
  database in an empty directory and starts an existing one (Java's or
  C's) by the bounded startup; `dir` NULL is a database in memory, lost
  at the close. `bergdb_options_init` gives Java's defaults (node size
  30, startup distance 50 MB, cache budget 200 MB, retain forever, the
  system clock, a random id); the test clock (`struct
  bergdb_test_clock`) and `bergdb_test_id` make times and bytes
  deterministic. A failed open leaves nothing open, and its text is in
  `errbuf`.
* **Write.** A transaction holds puts, deletes and a read set
  (`bergdb_trans_key_read`, `bergdb_trans_lookup_time`: the STM's
  conflict gives `BERGDB_RERUN`); `bergdb_execute` commits it at one new
  time, atomically, and it can be executed again. Key and value
  transformations (`bergdb_trans_put_transformed`) compute a key or a
  value at the transaction's time.
* **Read.** `bergdb_get_one` (a key at a time), `bergdb_get_many` (a range
  in key order, forward or backward, with Java's stop conditions: an end
  key, a count, a prefix, or a function), `bergdb_get_trans` (the
  transaction at a position, as `bergdb_one.tpos` gives it). Results
  point into the read context: copy what must outlive its next call.
* **Close.** `bergdb_close` writes and forces what is buffered, releases
  the directory's lock and frees every byte, the transactions and read
  contexts not yet freed with it; after it the handle is gone, as a
  `FILE` after `fclose` (012-13, Q2). Its `BERGDB_IO` says that the last
  write or force failed.
* **Errors.** Every call returns `BERGDB_OK` or a code; `bergdb_errmsg(db)`
  is the text, which begins with the name of Java's exception for the
  same case. A *refusal* (`BERGDB_RERUN`, `BERGDB_LIMIT`, `BERGDB_ARG`,
  `BERGDB_NOT_AVAILABLE`, `BERGDB_NOMEM`, `BERGDB_STATE`) leaves the
  database as it was. `BERGDB_FAILED` means that the database has failed
  (the storage, memory after a transaction's go point, corrupt data):
  every later transaction and read gets it too; close the database and
  open it again, which rebuilds it from the stream as after a crash (P7).
* **One caller at a time.** A database, with its transactions and read
  contexts, is used by one thread at a time, as a `FILE`; different
  databases may be used by different threads. The library has no threads,
  no locks and no global state: what Java's threads do happens in the
  calls, and a database that is not called does nothing (P3). A callback
  (the clock, a stop condition, a transformation) must not call its
  database: such a call gets `BERGDB_STATE`. A directory is opened by one
  database at a time: another process's open, C's or Java's, gets
  `BERGDB_IN_USE`; within one process, open a directory once (section 9).
* **Examples.** `examples/core_demo.c` (Java's `CoreDemo`: execute,
  getOne, getMany, getTrans, a restart) and `examples/get_many_prefix.c`
  (getMany with a prefix, a count and a stop function), built into
  `build/release/`. `examples/compare.sh` runs them and checks them
  against Java: `get_many_prefix` prints Java's output, which its comment
  holds, and `core_demo` and Java's `CoreDemo` print the same on each
  other's databases.


# 9. Durability

What a C database keeps when its process dies, as written in 012-13 and
tested by `test/func/f_durable.c` (a child process killed with `SIGKILL`
after `bergdb_execute`, after `bergdb_sync`, with a record partly written,
and at random moments; a write that fails). Power loss: `test/stress/power.sh`
(012-14, section 10).

1. **The write buffer.** `bergdb_execute` appends the transaction's record
   to the stream's write buffer, in memory: 10 MB, Java's
   `StorageManager.DEFAULT_BUFFER_SIZE`, fixed. The buffer is written to
   the files (with `write`, not forced) when it is full, which can be in
   the middle of a record, at `bergdb_sync` and at `bergdb_close`, and it
   is written and forced by a transaction that decides a reclaim cut
   (point 9). Nothing writes it between calls: the library has no thread
   (012-01, 4.3).
   Java's `BufferedStream` writes it within 20 ms from a thread of its
   own, and `FileStream` forces each write; the bytes are the same, and
   only when they reach the disk differs.
2. **After `bergdb_execute`**, the transaction is committed: reads see it
   and the stream's length counts it, but it is not durable. A process
   that dies (a crash, `kill -9`, `abort`) loses what the buffer holds;
   what a full buffer wrote stays. The one exception is a transaction
   whose call decides a reclaim cut (point 9): that call forces the stream,
   so it and every transaction before it are durable when it returns.
3. **After `bergdb_sync`** at `BERGDB_SYNC_ORDINARY` or `STRONG` (the same
   with one stream; `NONE` does nothing), every transaction committed
   before it is durable: the buffer is written, and the files written
   since the last force, and the directory after a new file, are forced
   with `F_FULLFSYNC`, as Java's `force(true)` on macOS. With one stream,
   a sync to any position before the end makes all of it durable; a
   position at or past the end is `BERGDB_ARG` (012-03, D11).
4. **After `bergdb_close`**, as after a sync: the close writes and forces
   the buffer before it closes the files and releases the lock.
5. **The creation** is in the buffer too: the first meta block and the
   primordial transaction (264 bytes) become durable at the first sync or
   close. A process that dies before leaves an empty file, and the next
   open creates the database again (a new random id, unless the options
   give one). Java's start does not wait for its creation to be durable
   either; its buffer thread writes and forces it within 20 ms.
6. **What a start finds** after a process died: whole transactions only,
   a prefix of those committed: every synced one, and later ones as far as
   a full buffer's write took whole records, never one without those
   before it. A record that a write left torn at the end of the stream is
   cut off by the start's recovery (Java's: the zero fill), and the next
   transaction follows the last whole one.
7. **The durable length** (`bergdb_stats.durable_length`, Java's
   `getDurableLength`) is the stream's length at the last force: the
   open's (0 after a creation, as Java's), each sync's, each reclaim
   cut's force (point 9), the close's.
8. **A write or a force that fails** (an I/O error, a full disk, a file
   size limit) fails the database (P7): the call returns `BERGDB_FAILED`
   (`bergdb_sync`, or `bergdb_execute` when its record filled the buffer),
   and so does every later transaction, read and sync, as the stream takes
   no write after an error (Java's `FileStream.checkIOException`);
   `bergdb_stats` and the setters of the cache size indicator, the retain
   duration and the internal fraction still work, and `bergdb_close` gives
   `BERGDB_IO` and frees everything. The next open finds a prefix, as in
   point 6. A database that failed for another reason (memory after a
   transaction's go point, corrupt data in a read) still syncs and closes
   the records before the failure, while the storage works.
9. **Reclaim's cut** frees the disk only when the stream is durable up to
   the cut's decision (the table that marks the cut, the meta block that
   recovery starts from), as Java's `Reclaim.cutIfDurable`. Java's buffer
   thread forces the stream within about 20 ms, so Java cuts at one of the
   next transactions. C has no thread, so the `bergdb_execute` call whose
   transaction lets reclaim decide a cut forces the stream itself (as a
   `bergdb_sync` does: the buffer written, the files written since the
   last force and a new file's directory forced, `F_FULLFSYNC`) and then
   deletes the front files, in that call (11-reclaim.md, 6.4, Q1: option
   B, decided by Frans on 2026-10-29; 6.9). That is one force per cut
   decided: at most one per quarter of the retain duration, and only when
   the stream has grown by twice the startup distance since the last
   iteration began. The force comes whether the application syncs or not,
   so the directory stays within what the retention needs, as Java's does;
   the bytes are the same either way (only when the front files are
   deleted differs, 012-01, 3.2 point 8). A force that fails fails the
   database (point 8). A cut that the table marks and the files do not
   show (a process that died between the force and the deletes; a
   directory that Java's cut thread had not cut yet) is made by the next
   open.
10. **One database per directory.** The open locks `bergdb.lock` as
    Java's `FileStream` does (an `fcntl` lock of the byte at 2^62), so
    that another process's open, C's or Java's, gets `BERGDB_IN_USE`
    until the close. The lock belongs to the process (POSIX): within one
    process, open a directory once. A second open in the same process is
    not refused, and its close would release the first one's lock. Java
    checks a set of the JVM's locked directories; C has no global state
    (P9), so it leaves this to its one caller (012-13's decision on
    09-write-path.md, 6.4: option A).


# 10. Robustness runs (012-14)

By hand, not in the gate (but for the short allocation-failure run); each
script's header has its usage, and 14-robustness.md the results. Raw
output goes to `/Users/f/fl/bench/012/14-out/` by default (`OUT=`).

* `test/stress/random.sh FROM TO`: Gen's seeds by the thousand, Java
  against C, in batches of `cross.sh random`.
* `test/stress/long.sh SEED N`: a long run with restarts, reclaim and a
  small budget, in both builds and under `leaks`.
* `test/stress/corrupt.sh`: corrupt databases started by both dumpers.
* `test/stress/power.sh`: **power loss**. `bergdb-power` (`power.c`, the
  test build) is `tools/run.c` under a model of the disk behind the test
  build's I/O seam (`plat.h`, `struct plat_io`: open, write, force, force of
  the directory, delete and close, replaced for the process by
  `plat_io_set`; the release build has no seam): Java's `ModelIo` of
  `FileStreamPowerLossTester` in C, the bytes written, the bytes forced and
  the durable names apart. At each write, tear, force and delete it writes
  the image that a power loss leaves, and checks that the image holds the
  stream up to the length that the last `bergdb_sync` or `bergdb_close`
  acknowledged. The script starts every image with both dumpers and runs
  on it with both runners: the same exits, dumps and files. `JAVAIMG=1`
  does the other way, Java's images (`java/PowerImages.java`) started by
  both; `OMIT=file` or `OMIT=dir` is the negative control (forces not
  modelled: acknowledged bytes are lost, and found).
* `test/stress/allocfail.sh`: **allocation failures in turn**.
  `bergdb-allocfail WORKLOAD OUT` (`allocfail.c`, the test build) runs the
  workload once, then once for each allocation number N in a child process
  with allocation N failing (`bergdb_options.mem`'s `fail_at`): the call
  gives `BERGDB_NOMEM` and the run, making the call again, ends with the
  reference's text and bytes; or the call gives `BERGDB_FAILED` (after the
  go point, P7), and the closed stream is a prefix of the reference's and
  opens again; the live bytes are 0 after every close. The gate runs it on
  `test/stress/allocfail.wl` (Gen 31: 4 transactions, a restart, reclaim,
  a budget of 1,000 bytes; 379 runs, about 15 s).
* `test/stress/gcc.sh`: **a second compiler**, Homebrew's gcc 16, by hand:
  both builds without `-Werror` (`CC=gcc-16 WERROR= BUILD=DIR ./build.sh`),
  then the unit and functional tests in both. The gate keeps clang and
  `-Werror`. The library has no gcc warning (012-14 silenced its four, none
  a bug); the tests and the examples have about 15 of
  `-Wformat-truncation`, paths into fixed buffers, as meant.
