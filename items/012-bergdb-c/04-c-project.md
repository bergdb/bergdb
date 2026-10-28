012-04. Task: the C project, its build, tests and first modules
===============================================================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: done 2026-10-28 14:17, in the clone; for the
conductor's check and commit** (started 13:47; `cross.sh full` does not
exist yet, 012-05). Approved with 012-01 by Frans's go (012-01, 9.1).
Phase A (012-01, section 8). Effort: high. After: nothing.


# 1. The goal

The C directory, `items/012-bergdb-c/c/` (012-01, decision D1), ready
for the tasks that follow: the layout, the build, the test framework, the
gate, the rules for Java's semantics in C, and the first modules, those
every other module uses, checked against Java's own output.

Done when:

1. The layout of 012-01, 6.3 exists, with `readme.md` saying what the
   directory is, how to build and test, and the rules of section 3, step
   4.
2. `build.sh` builds, with the flags of 012-01, 6.1, a release build and a
   test build (AddressSanitizer and UndefinedBehaviorSanitizer) into
   `build/`: the library `libbergdb.a`, the tools and the test programs.
   It checks that `include/bergdb.h` compiles alone, once 012-03 has
   written it.
3. `test/unit/test.h`, a test framework of one header: a test is a
   function, registered in a table; the runner runs all or those named,
   prints each failure with its file and line and a summary, and exits
   non-zero on a failure.
4. `before-commit.sh` builds both builds with `-Werror`, runs the unit
   tests and the functional tests in the test build, runs the quick cross
   set when it exists, and prints `C BEFORE COMMIT OK`.
5. The first modules, with unit tests: little-endian bytes; Fletcher-16
   as `NodeChecksum` (`sum` and `sumWithZeroReplace`); the parts of
   `Klong` that make and read compare values; `Keys` (ikey to bkey, bkey
   to segments and back, comparison, `hash`); `jsem.h`, the helpers of
   Java's semantics (unsigned shift, masked shifts, Java's cast from
   double to long); and the allocator of 012-01, 4.5, point 1: every
   allocation and free of the library through it, the live bytes counted
   per database and by kind, NOMEM on a failure, and in the test build the
   Nth allocation made to fail, with a helper for tests that checks the
   count is 0 after a close.
6. Java's vectors: `Vectors.java` writes, for a fixed set of inputs, what
   Java's classes give (compare values, segments, hashes, checksums),
   into small files under `test/unit/vectors/`, which are committed; C's
   unit tests read them and agree. 012-05's cross tests regenerate them
   and compare, so that a change in Java shows.


# 2. Read first

* 012-01, sections 4.2, 4.5, 6.1 to 6.5.
* Java: `Bytes` (153 code lines), `NodeChecksum` (46), `Klong` (191),
  `Keys` (197), `Spos` (26); `java/build.sh`, `java/before-commit.sh`,
  006-08's `core-build.sh` (compiling the Core Layer alone).
* The memory notes on F53's toolchain: Apple clang 21 as `cc`, JDK 27 at
  `/opt/homebrew/opt/openjdk`.


# 3. The work

1. The layout and `readme.md`. `build/` is ignored by the repository's
   `.gitignore` already (`build/`).
2. `build.sh`: one `cc` call per build for the library's sources, then the
   tools and the tests; a few seconds. Plain `sh`, `set -e`, no make.
3. `test.h` and the runner; a first test that fails on purpose, run once
   to see the output, then removed.
4. **The rules of Java's semantics**, in `readme.md`, each with an example
   from the Java code: `long` as `int64_t` and wrapping (`-fwrapv`), `>>>`,
   shift counts, signed bytes, `%` and `/`, double to long, no fused
   multiply-add, comparisons as Java's (signed or unsigned), text as
   Java's `"" + long`. Also the module rules: no global state, errors as
   return codes, one `.c` and `.h` per module, names `bergdb_` for the API
   and a short prefix per module inside.
5. **Decide `-Wconversion`.** Build the first modules with it; keep it if
   the casts it asks for are few and clear, else drop it and say why in
   `readme.md`.
6. The first modules and their tests (done item 5), each ported from its
   Java class, line for line where the bytes depend on it.
7. `Vectors.java` (in `test/cross/java/`, compiled against the Core Layer
   as 012-01, 6.3 says) and the vector files.
8. `before-commit.sh`. Then run it, and time it.


# 4. Tests

The unit tests of the first modules: Java's vectors, Java's own `@Nano`
tests of `Klong` and `Keys` where they apply, and edge cases (empty keys
refused, keys of 6, 7, 8, 13 and 14 bytes, bytes 0, 1, 0x7f, 0x80 and
0xff, `Long.MIN_VALUE` in `hash`).


# 5. Notes

* Keep the build boring: a reader should see in a minute what it does.
* The test build's sanitizers make the tests slower; the gate's target is
  still about 2 minutes once all tests exist.


# 6. Progress

* **Java reference**: `main` at 404d2ee (`java/` last changed at
  fd8f513).
* **Clone**: `/Users/f/fl/bench/012/04-c-project/` (a git clone of
  bergdb at 404d2ee); the conductor copies the files in.
* 13:47: started.
* 13:56: **stopped at a safe point** at the conductor's request (Frans
  raised 012's effort to xhigh); a new agent continues from this clone.
  Done so far (committed in the clone, not in main):
  * Layout of 012-01, 6.3: `src/`, `test/unit/`, `test/unit/vectors/`
    (empty), `test/func/`, `test/cross/java/`, `tools/` (empty dirs are
    not in Git until they get files).
  * `build.sh` (step 2): release (`-O2`) and test (`-O1 -g`, ASan, UBSan,
    `-DBERGDB_TEST`) builds with 6.1's flags incl. `-Wconversion -Werror`,
    `libbergdb.a`, tools, the `unit` program (`-DVECTORS_DIR`), `func`
    when `test/func/*.c` exist; checks `include/bergdb.h` alone and
    `examples/*.c` with `-fsyntax-only` when they exist. Prints
    `BUILD OK`, about 1 s.
  * `test/unit/test.h` (step 3): TEST, per-file tables, TEST_MAIN with
    `test_main`, CHECK, REQUIRE, CHECK_EQ, CHECK_BYTES, CHECK_MEM_ZERO;
    name-prefix selection, `-l`. A failing demo test was run once (file,
    line, values, `UNIT FAILED` and exit 1 seen) and removed.
    `test/unit/main.c` has an empty table list now: `unit` prints
    `UNIT FAILED` (no test run) until test files are added.
  * Modules written, ported line for line, all build with `-Wconversion`
    without a warning: `jsem.h` (masked shifts, `>>>`, narrowing casts,
    `j_d2l`/`j_d2i`, `j_div64`/`j_rem64`/`j_floor_div64`, `j_cmp64`,
    `j_cmpu64`, `j_nlz64`, double/float bits), `bytes` (Bytes),
    `checksum` (NodeChecksum, incl. the long[] sum), `klong` (Klong, all
    but toString), `keys` (Keys, without the display functions), `spos`
    (Spos), `mem` (the allocator: counts by kind, peak, blocks, `fail_at`
    for the Nth allocation, sized free with a 16-byte checked header in
    the test build).
  * `test/cross/java/Vectors.java` written, **not yet compiled or run**.
  * Checked: with `-fwrapv`, clang 21's UBSan flags no signed overflow,
    no left shift of a negative value, no `MIN / -1`; it does flag shift
    counts >= 64 (so `jsem.h`'s masks matter).
  * `-Wconversion` (step 5): so far zero warnings in the first modules
    with the casts that Java has anyway; keep it unless the tests change
    that. Not yet written in `readme.md`.
  Next steps (as the first agent left them): compile and run `Vectors.java` (`test/cross/java-build.sh`,
  then `java -ea -cp build/java/classes bergdb.core.Vectors
  test/unit/vectors`), check the files are small; the unit tests
  `t_jsem.c`, `t_bytes.c`, `t_checksum.c`, `t_klong.c`, `t_keys.c`,
  `t_spos.c`, `t_mem.c` (Java's @Nano tests, the edge cases of section
  4) and `t_vectors.c` with a small vector reader; `readme.md` (step 1
  and the rules of step 4, the `-Wconversion` decision); empty-dir
  readmes for `test/func/` and `tools/`; `before-commit.sh` (step 8),
  timed.
* 13:57: a second agent (effort high, by the conductor's brief) took over
  from the clone at 75c6802, reviewed what was written (build.sh, test.h,
  the modules against their Java classes: no difference found) and went
  on. Commits in the clone: 15ca478, 364c4c3, 633b13d (the gate),
  e7b079f, and the last of this entry.
  * **Java's vectors** (step 7): `Vectors.java` compiled with
    `java-build.sh` (unchanged; 178 source files, about 3 s) and run.
    Changed before the first commit of the files: the zero-replace edge
    data were all 0xff, which Fletcher-16 sums to 0 whatever is replaced,
    so a ramp now; a fifth file, `jsem.txt`, with Java's own results for
    the rules of `jsem.h`: casts from double (NaN, infinities, 2^63 and
    its neighbours), long to double rounding, narrowing, shifts with
    counts -64 to 127, division and `floorDiv` with `MIN / -1`,
    `compare` and `compareUnsigned`, `numberOfLeadingZeros`, the take's
    share expression (`TransSeq.take`) and `TransSeq.dither`; no
    `Math.pow` in the inputs, so that the files do not depend on the JDK.
    Five files, 64 KB, 957 cases, committed in `test/unit/vectors/`.
    `t_vectors.c` checks every line (4,762 checks), fails on a kind of
    line it does not know and on a kind without lines, prints the vector's
    file and line under a failed check, and reads `BERGDB_VECTORS` in
    place of the committed directory when set (for 012-05). Seen to fail
    on a changed line, an unknown kind and a missing kind.
  * **Unit tests** (step 6, section 4): `t_jsem.c`, `t_bytes.c`,
    `t_checksum.c`, `t_klong.c`, `t_keys.c`, `t_spos.c`, `t_mem.c`: every
    `@Nano` test of `Bytes`, `NodeChecksum`, `Klong`, `Keys` and `Spos`
    ported (Java's `java.util.Random` values replaced by `test_random`
    where only round trips depend on them), and the edge cases of section
    4: empty keys refused (and 0xfe, 0xff), keys of 6, 7, 8, 13, 14 and
    more bytes (segment counts and last lengths), the bytes 0, 1, 0x7f,
    0x80, 0xff at each position, `Long.MIN_VALUE` in `hash` (005-21); a
    property test that segments order 3,000 random keys as their bytes do
    (`compareKeys`, `compareArrays`, `isPrefix`). `t_jsem.c` has two
    tripwires, seen to fire: without `-fwrapv` UBSan stops in
    `jsem_wrapv`, and with `-ffp-contract=on` `jsem_no_fma` fails.
    81 tests, 23,341 checks, 0.4 s in the test build.
  * **The allocator** (`mem`): now counts failed allocations too
    (`failed`), for the failure runs. `t_mem.c`: counts by kind, peak and
    blocks; one `struct mem` per database; zalloc, size 0, realloc
    (counts, contents, from NULL, to 0); `fail_at` for an alloc and a
    realloc (the block kept); too large; the allocation-failure runs as
    012-14 will make them (each allocation of a small workload made to
    fail, NOMEM and nothing live each time, then a run that succeeds);
    in the test build, a free with the wrong size or kind aborts (in a
    child process). The helper for tests: `CHECK_MEM_ZERO` (test.h).
  * `test.h`: `TEST(name)` now defines `test_name`, so that a test may
    bear its module's names; `test_random` and `test_random_below`.
  * `jsem.h`: `J64(hex)` for Java's long literals with the high bit set
    (a `static_assert` checks the cast), `j_div32`, `j_rem32`; `klong`
    writes Java's `0xc000000000000000L` as `J64(0xc000000000000000)`.
    `keys_byte_size` asserts a segment, where Java would throw.
  * **`readme.md`** (steps 1, 4, 5): build and test, the layout, the 13
    rules of Java's semantics with an example from the Java code each,
    the module rules, the allocator, the tests, and the `-Wconversion`
    decision. `test/func/readme.md` and `tools/readme.md` keep the empty
    directories of the layout.
  * **`-Wconversion` kept** (step 5; reason in `readme.md`, section 6):
    Java requires a written cast for every narrowing, and `-Wconversion`
    makes C ask for the same casts, so a forgotten one is an error. With
    the casts removed, the six modules give 32 warnings: 29 at Java's own
    `(byte)` casts, 3 where the allocator counts a `size_t` in an
    `int64_t`; none asks for a cast that Java lacks. The cost: a written
    `(double)` for a long in a double expression, and `(size_t)` for
    lengths, mostly in tests.
  * **`before-commit.sh`** (step 8): build; rules (no `malloc`/`free`
    and the like outside `src/mem.c`, by `grep`; no writable global or
    static data, by `nm -m` of the release objects; a `.h` per `.c`); the
    unit tests in the test build; in the release build, then under
    `leaks --atExit`; `func` likewise when it exists; `cross.sh quick`
    when it exists. Each step's output in `build/gate/`; the first failure
    prints its tail and `C BEFORE COMMIT FAILED: STEP` (seen for a rules
    violation and a build warning). **`C BEFORE COMMIT OK (3 s)`**, about
    3 s by `time`.
  * **Findings in Java** (no bug, comments only; nothing in 005):
    `Klong`'s format comment gives a TIME klong 58 bits and its closing
    note `MAX_TIME = 2^58-1 = 0x03ffffffffffffffL`, while the code's
    `MAX_TIME` and `getTime` use 56 bits (`0x00ffffffffffffffL`), which
    005-18's range check follows; `Klong.getIntType`'s comment says "0, 1,
    or 2", and it returns 3 for a delete bitmap. Fletcher-16 modulo 255
    sums a byte 0xff as 0, so nodes that differ only in 0x00 against
    0xff bytes have the same checksum: by design, noted for 012-14's
    corruption tests.
  * For the conductor: `test/cross/java-build.sh` needs no change.
    `Vectors.java` is in `bergdb.core` and calls `TransSeq.dither`
    (package-private). The files to copy in are everything under
    `items/012-bergdb-c/c/` but `build/`, and this file.
  Next: nothing in this task; 012-05 regenerates the vectors in
  `cross.sh` and compares them (`BERGDB_VECTORS=DIR build/test/unit
  vectors_`, then a diff with `test/unit/vectors/`).
