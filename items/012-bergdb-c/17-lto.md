012-17. Task: link-time optimization in the release build
=========================================================

Created 2026-10-29 by Claude (Opus 5.5, Claude Code), the conductor of
012, at Frans's request (2026-10-29, 12:47, on 012-15's first proposal:
"build with -flto. Yes, why not? Tell me more."; 12:51: "Just add subitem
17 for now."). **Status: done** (2026-10-29, 15:27; Frans's go 13:59;
the coder: Claude, Opus 5.5, Claude Code, in a scratch clone of main at
`0935005`).
After: 012-15. Effort: high (Frans, 2026-10-29: agents at high).


# 1. The goal

The C clone's release build with link-time optimization (`-flto`), so
that the small helpers that the hot paths call across modules (`klong`,
`keys`, `node`, the byte reads) are inlined, with every byte unchanged.

012-15 measured it on a side build (15-performance.md, section 6.4: 1M
keys, three runs each in turns): +15 to +34 percent on every figure
(load 1.34, batch 1.25, single puts 1.24, `getOne` 1.15 to 1.17, `getMany`
1.23, under a 16 MB budget 1.24), the stream lengths equal. The profile
put C's reads in the key node's search, calling small helpers in other
modules that `-O2` alone cannot inline.

Done when:

1. `build.sh`'s release build compiles and links with `-flto`, and with
   the flags that keep Java's semantics (012-01, 6.1 and 6.2:
   `-fwrapv -ffp-contract=off`, and the rest) given at the link too, so
   that the link-time optimizer keeps Java's arithmetic; the reason is
   written in `c/readme.md`. The test build (the sanitizers) stays as it
   is.
2. The C gate prints `C BEFORE COMMIT OK`.
3. `cross.sh full` passes with the release build's tools as side B
   (`C=build/release`), not only the test build's: the bytes of every
   workload equal Java's with the optimized code. The take decides with
   doubles (012-01, 3.2 point 4), so a contraction or a reordering at the
   link would show here.
4. 012-15's timed figures again, `-O2` and `-O2 -flto`, C and Java in
   turns, medians of three, on a quiet machine (`bench/bench.sh`): the
   table in this file.
5. The code size with `-flto` (`bench/size.sh`), against 012-15's 196.3 kB
   at `-O2` and 170.4 kB at `-Os`.


# 2. Read first

* 15-performance.md, sections 6.4 to 6.8, and its scripts in `c/bench/`.
* `c/build.sh`, `c/readme.md` (the rules of Java's semantics in C, and
  why `-ffp-contract=off`).
* 012-01, 6.1 and 6.2.


# 3. The work

1. The flags in `build.sh`, release only; a check that the link gets
   them (`-Wl,-mllvm` or the driver's own forwarding, whichever Apple
   clang 21 needs; written down).
2. The gate, then `cross.sh full C=build/release`.
3. The timed runs, in a quiet window, the session idle meanwhile.
4. The size.


# 4. Notes

* The alternative of 15-performance.md, proposal 1: move the hot helpers
  into their headers as `static inline`, which gains much of the same
  without link-time optimization and works with any compiler. Compare if
  `-flto` gives trouble.
* C is a separate project (Frans, 2026-10-29, 12:36): its tests and
  scripts stay in 012 and run by hand.


# 5. Progress

All times 2026-10-29, from `date`.

* 13:59 Started. Read the plan, 15-performance.md 6.4 to 6.8,
  `build.sh`, the C readme, 012-01 6.1 and 6.2.
* 14:01 What the link needs, on two small files (a function in one, its
  caller in the other, `-O2 -flto`): `cc -###` shows that clang 21's
  driver gives `ld` only `-O2`, `-lto_library` and
  `-mllvm -enable-linkonceodr-outlining`, none of the semantic flags. They
  need not reach the link: their effect is in the bitcode (no `nsw` with
  `-fwrapv`; no `contract` flag and no `llvm.fmuladd` with
  `-ffp-contract=off`, seen in the `-S -emit-llvm` output). Across the two
  files, after the link's inlining: `x + 1 > x` at `Long.MAX_VALUE` stays
  false with `-fwrapv`, true without; `a * b + c` gives 0 (Java's) with
  `-ffp-contract=off` and `on`, and `-0x1p-60` with one `fmadd` only with
  `fast`. `ld` passes `-Wl,-mllvm,...` on (it refuses an unknown option),
  but `-Wl,-mllvm,-fp-contract=fast` fused nothing in bitcode compiled
  with `off`: the link's optimizer follows the bitcode. So no link flag
  is added; the reason is in `c/readme.md`, section 1.
* 14:03 `build.sh`: `LTO=${LTO--flto}`, the release build `-O2 $LTO`
  (every compile and link of the build, as all its flags); `LTO=` builds
  without. The build: 29 s (20 s with `LTO=`; the test build is most of
  it). `before-commit.sh`'s rule of no global state read `nm -m` of the
  release objects, which are bitcode now: `nm` shows their symbols as
  `(LTO,CODE)`, `(LTO,RODATA)` or `(LTO,DATA)`, so the rule would have
  passed anything. It now also refuses `(LTO,DATA)` (checked on a
  planted global, static and common variable: all three shown as
  `(LTO,DATA)`; a constant table of pointers is `RODATA`). On the build:
  646 `CODE`, 13 `RODATA`, no `DATA`.
* 14:04 The gate with macOS's own `leaks` (it runs: `leaks --atExit` on
  `core_demo` ended in a second, 0 leaks; no stand-in needed):
  **failed** in `unit-release`, `mem_too_large`:
  `mem_alloc(&m, SIZE_MAX - 8, ...)` returned a block. With `-flto`,
  `mem_alloc` is inlined into the test, whose block is only compared with
  NULL, and the optimizer removed the `malloc` and took it as succeeded,
  which C allows (the disassembly had no call of `malloc`). The library's
  own calls use their blocks, so this is the test's: its results now go
  through a `void *volatile`, and `malloc` is called again. Fused
  multiply-adds: none in any release program but `unit`, whose one
  `fmadd` is `jsem_no_fma`'s own `fma()`; a scratch build with
  `-ffp-contract=fast` given after the others makes `jsem_no_fma` fail,
  so the test sees a contraction in a `-flto` build.
* 14:06 The gate again: **C BEFORE COMMIT OK (176 s)**, with macOS's
  `leaks`.
* 14:07 `bench/size.sh` gets `-O2 -flto` (the library linked as a
  dynamic library, every external function kept, measured in the
  linker's native object, `-object_path_lto`) and `core_demo` at `-Os`,
  `-O2` and `-O2 -flto`; `bench/bench.sh` gets mode `lto` (timed's runs
  with C's release build as built, `c`, and without `-flto`, `co2`, built
  with `LTO=` into `build/nolto`, in turns with Java); `summary.py` its
  table.
* 14:10 `cross.sh full C=build/release` started (in the background).
* 14:12 `test/stress/gcc.sh` by hand (output in the session's scratch
  directory): GCC OK, gcc 16 builds and links the release with `-flto`
  too (its objects carry GCC's LTO sections), the unit and functional
  tests pass in both builds.
* 14:43 **CROSS full OK** with the release build's tools as side B: 446
  workloads, 1357 crash cuts, 498 corrupt variants, 6 in turns, 1784
  budget runs, the planted difference found and explained; side B
  `build/release`; 2018 s.
* 14:44 The machine: no JVM, compiler, gate or timing of another session;
  Spotlight (`mds`) busy after the cross run, 76 to 84 percent idle.
  14:45 to 15:23 `bench.sh lto` (40 runs, every one started quiet, at 85.5
  to 97 percent idle; twice it waited a few seconds for quiet, 14:50 and
  15:21); this session idle meanwhile. Section 6.
* 15:24 The tables (section 6; the size from `bench/size.sh`'s run at
  14:09, the same `src/`), this file, `c/readme.md` (section 1), 012's
  log.
* 15:24 The gate on the final tree: **C BEFORE COMMIT OK (177 s)**, with
  macOS's `leaks`. Done at 15:27.


# 6. Results

The library's code is `0935005`'s; this task changes `build.sh`, the gate's
rule, one unit test, the benchmark scripts and documents, nothing in
`src/`. F53 (M1 Pro), Apple clang 21, OpenJDK 27 (G1, `-Xms12g -Xmx12g`),
as 012-15, 6.1. Raw output: `/Users/f/fl/bench/012/17-out/lto/` (its
`log.txt` and `summary.txt`; ranges there).

**Timed** (`bench.sh lto`: C with `-O2 -flto` (the release build now), C
with `-O2` alone (`LTO=`), Java, in turns, each a fresh process; medians
of 3 runs, a run's read figure its best of 3 rounds; rates a second, times
in seconds; one thread; no eviction but the 16 MB budget; sd 50 MB). The
stream's length after every phase equal in all three, in every run.

| | 1M: `-O2 -flto` | 1M: `-O2` | Gain | 1M: Java | C/Java | 10M: `-O2 -flto` | 10M: `-O2` | Gain | 10M: Java | C/Java |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| load (puts/s) | 449,582 | 325,892 | 1.38 | 339,104 | 1.33 | 194,477 | 150,877 | 1.29 | 137,292 | 1.42 |
| batch (puts/s) | 299,255 | 239,198 | 1.25 | 234,748 | 1.27 | 137,670 | 108,877 | 1.26 | 99,804 | 1.38 |
| single (/s) | 236,136 | 189,825 | 1.24 | 146,762 | 1.61 | 123,031 | 98,914 | 1.24 | 79,812 | 1.54 |
| syncone (/s) | 154 | 147 | 1.05 | 205 | 0.75 | 206 | 205 | 1.00 | 212 | 0.97 |
| syncbatch (/s) | 120 | 112 | 1.08 | 104 | 1.16 | 98.8 | 86.0 | 1.15 | 74.6 | 1.32 |
| getOne latest | 844,453 | 703,944 | 1.20 | 967,563 | 0.87 | 527,429 | 479,343 | 1.10 | 602,146 | 0.88 |
| getOne historical | 932,346 | 789,835 | 1.18 | 802,242 | 1.16 | 531,198 | 492,773 | 1.08 | 630,456 | 0.84 |
| getMany (keys/s) | 6,748,686 | 5,497,483 | 1.23 | 6,421,894 | 1.05 | 6,847,814 | 5,609,123 | 1.22 | 6,982,454 | 0.98 |
| close (s) | 0.519 | 0.502 | 0.97 | 0.001 | | 3.481 | 3.478 | 1.00 | 0.002 | |
| lowopen, budget 16 MB (s) | 0.921 | 1.085 | 1.18 | 1.827 | 0.50 | 0.991 | 1.133 | 1.14 | 1.972 | 0.50 |
| getOne, budget 16 MB | 145,587 | 117,581 | 1.24 | 218,778 | 0.67 | 44,310 | 35,944 | 1.23 | 109,314 | 0.41 |

Gain: `-O2 -flto` over `-O2` (for times, `-O2`'s over `-O2 -flto`'s).
C/Java: `-O2 -flto` against Java. 10M keys at sd 200 MB (one run each,
C only): load 264,612 against 212,029 puts/s (1.25), batch 184,566
against 151,562 (1.22). Startup, warm (3 runs each): the 10M database at
sd 50 MB 0.912 s with `-flto`, 1.002 s without (1.10), Java 2.485 s (C/Java
0.37); at sd 200 MB 4.107 s, 4.611 s (1.12), Java 10.5 s (0.39).

So `-flto` gains what 012-15's side build measured: writes 1.24 to 1.38,
reads in memory 1.08 to 1.23, under the 16 MB budget 1.23 to 1.24, the
opens 1.10 to 1.18; the syncs and the close (the device's flush, `free`)
about none. C against Java now: writes 1.27 to 1.61; getOne 0.84 to 0.88
(1.16 for the historical at 1M), getMany 0.98 to 1.05; under the budget
still 0.41 to 0.67 (012-15's proposal 2, the sweep, not this task's).
This window was a little noisier than 012-15's (85 to 97 percent idle
against 96 to 98): Java's and C `-O2`'s 1M reads came out 1 to 10 percent
below 012-15's; the gains are measured within the same window, in turns.

**Size** (`bench/size.sh`, text + data as `llvm-size` counts them):

| | The library (every module, every external function) | `core_demo` with `-dead_strip`: the program |
|---|---:|---:|
| `-O2` | 197.1 kB (012-15: 196.3 kB at `de7613d`) | 169.5 kB |
| `-O2 -flto` | 235.7 kB (1.20 times `-O2`) | 178.3 kB (1.05 times) |
| `-Os` | 170.9 kB (012-15: 170.4 kB) | 151.4 kB |

The library with `-flto` is the linker's native object of the library
linked as a dynamic library (`-object_path_lto`), every external function
kept, as the objects of the other rows keep them: 20 percent larger, from
the helpers inlined into their callers. In an application that uses the
API (`core_demo`, dead code stripped), the program grows 5 percent; the
linker's map gives most of it to the library's modules (144.6 kB) and the
rest to the link's own object (merged constants and strings) and to
`core_demo`'s own object (library code inlined into `main`), so only the
program's total compares with `-O2`'s 163.4 kB of library and 6.1 kB of
program.
