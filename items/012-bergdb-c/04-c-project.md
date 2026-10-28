012-04. Task: the C project, its build, tests and first modules
===============================================================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: not started**; approved with 012-01 by Frans's
go (012-01, 9.1).
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

Not started.
