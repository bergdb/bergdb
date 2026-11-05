015-19. Fix: tools in items still use what 005-79 removed
=========================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2. 005-79 (`f04cefe`) removed `Eviction.LOW` and
`TransSeq.dither`. Some tools in items, outside `java/` and so outside
`before-commit.sh`, still use them and no longer compile against `main`:

* `items/005-todo/65-gets-with-8-readers/night/ScaleBench-065.diff`
  (005-65's `night/prep.sh`) uses `Eviction.LOW`. 016-10's
  `prep-tools.sh` (`/Users/f/fl/bench/016/numbers/`) puts
  `Eviction.lowOf` in that line for a jar without it.
* `items/007-bounds/08-step4-take-in-lean/TakeCheck.java` calls
  `TransSeq.dither` (Lean's side: 015-03).
* `items/012-bergdb-c/c/test/cross/java/Vectors.java` calls
  `TransSeq.dither` (C's side: 015-02).

Done when: each tool compiles against `main` and gives the values of
005-79's integer take, or its item says that it is kept for the code
before 005-79 only.

First step: give `ScaleBench-065.diff` the line of `prep-tools.sh`.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05, in 015-02's work: `items/012-bergdb-c/c/test/cross/java/Vectors.java`
writes `TransSeq.ditherFp` and `shareFp` (and `Math.multiplyHigh` and
`Math.round`) in place of `dither`, and compiles against release 2026.2,
whose Java the cross harness now compiles by default (015-02). The other two
tools are as they were.
