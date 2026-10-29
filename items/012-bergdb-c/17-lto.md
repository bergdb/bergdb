012-17. Task: link-time optimization in the release build
=========================================================

Created 2026-10-29 by Claude (Opus 5.5, Claude Code), the conductor of
012, at Frans's request (2026-10-29, 12:47, on 012-15's first proposal:
"build with -flto. Yes, why not? Tell me more."; 12:51: "Just add subitem
17 for now."). **Status: not started**; a plan, to start when Frans says
so.
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

Not started.
