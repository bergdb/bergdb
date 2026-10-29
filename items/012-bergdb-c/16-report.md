012-16. Task: the report
========================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: in progress.** Section 0 is an interim report,
written by the conductor (session f1-0f) on 2026-10-29 at 05:08, after
the first unattended run (2026-10-28 13:43 to 2026-10-29 07:00); the final
report follows 012-14. Approved with 012-01 by Frans's go (012-01, 9.1).
Phase E (012-01, section 8). Effort: high. After: 012-14, 012-15.


# 0. Interim report, 2026-10-29

**In short.** BergDB's Core runs in C: Levels 0 to 4, every byte equal
to Java's. 012-02 to 012-13 and 012-15 are done, in 15 hours of
unattended work (two to four subagents at a time, xhigh and max effort);
012-14 (robustness) has had a first pass; this report is 012-16's draft.
The C code is in `c/` (21,080 lines of C in `src/`, 16,146 code lines by
006-08's count; 17,049 lines of tests), built and gated by
`c/before-commit.sh` (`C BEFORE COMMIT OK`, about 150 s); `c/readme.md`
has the guide.

## 0.1 012-01's "Done when", item by item

1. **Java to C.** Every database of the cross sets opens in C and reads
   as in Java: in `cross.sh full` all 892 side-B dumps are C's (latest
   state, `getMany` both ways, `getOne` at sampled times, `getTrans` of
   every transaction), equal to Java's (012-13's final run, on the merged
   tree of 012-12 and 012-13: 446 workloads, 1,368 crash cuts, 498 corrupt
   variants, 6 runs in turns, 1,784 budget runs, 0 differences, 2,240 s).
   C's startup equals Java's read for read (012-10: a probe compared D,
   the node table, the objects, the loads and every file read on 482
   directories and 1,262 crash cuts).
2. **C to Java.** Java starts each of C's databases with assertions and
   its audit on (`Dump -audit 1`), and its dump equals C's: every
   workload of the sets, and the 10M-key database.
3. **The same bytes.** C runs every workload of the sets (side B's 446
   runs all C's since 012-11), and its files equal Java's: restarts
   (`l2-every1`: 399 restarts), runs in turns between Java and C,
   continuing after crash cuts, eviction budgets, and reclaim, compared
   from the decided cut (012-01, 3.2 point 8). Beyond the sets: 300 seeds
   and a million keys (012-09), 416 reclaim workloads (012-11). No byte
   difference was met at any step of 012-09; the mutations tried in
   012-09 and 012-11 were all found.
4. **The API.** `bergdb.h` (012-03): 35 of `Db`'s 45 public methods have
   their C counterpart in 33 functions, the other 10 are left out with
   reasons; each function has a functional test (012-13). C's `CoreDemo`
   prints what Java's prints, on its own and on Java's databases; the
   gate runs it.
5. **The levels.** 0 and 1 (012-07, 012-08), 2 (012-09, 012-10), 3
   (012-11), 4 (012-12).
6. **Quality.** The C gate: both builds with `-Werror` (C17, Apple clang
   21, `-Wconversion`), 345 unit tests, 23 functional tests, the
   examples, the quick cross set, under AddressSanitizer and
   UndefinedBehaviorSanitizer, `leaks` on the release build, the
   allocator's count 0 after every test, allocation failures in turn. The
   deep set passes (item 1).
7. **Scale.** `cross.sh scale` (10M keys) with C writing side B
   (2026-10-29, 05:02): the same bytes as Java's, each side's dumps of
   both databases equal, Java's with its audit (257 s). C at a 4 MB
   budget on a million keys (1.2 GB on disk): Java's bytes and reads,
   resident at most 3,999,972 bytes (012-12).
8. **Measured** (012-15, medians of three, quiet machine): C writes at
   1.01 to 1.31 of Java's rate, reads at 0.73 to 0.97 (in memory) and 0.33
   to 0.68 (small budgets), starts 1.9 to 2.4 times faster (10M keys,
   warm, 50 MB: 0.99 s against 2.42 s), needs 3 to 7 percent less memory
   per key; 196 kB of machine code at `-O2` (LMDB: 53 kB).
9. **Reported**: this section, the draft.

## 0.2 The milestones

| Milestone | When | Commit |
|---|---|---|
| M1, phase A: format, API, project, harness | 2026-10-28 16:25; 012-02's review 17:06 | `3421e91`, `c1479b7` |
| M2: C reads Java's databases | 21:40 | `dabaa50` |
| M3: Levels 0 to 2, C writes and restarts as Java | 23:26 | `e0d5e15`, `e1507b9` |
| M4: Levels 3 and 4 | 2026-10-29 03:17 | `ca9e583`, `afb47e5` |
| Phase E so far: API and durability, measurements | 04:00, 05:06 | `0c910bc`, `9104af2` |

## 0.3 Departures from Java

Each with its reason in the task files: one caller at a time, no threads
(012-01, 4.2); a transaction is durable at `sync` or close, the buffer
written when full (012-13, `c/readme.md` section 9); a decided cut frees
disk at the next sync or open (012-11, Q1 below); a handle ends at its
close (012-13, Q2 below); a directory opened once per process (012-09
part 1's question, decided in 012-13 as recommended); replicas,
encryption and the upper layers left out (012-01, section 1).

## 0.4 What the port found in Java

All registered in 005 (decision D5), none fixed in 012; C does as Java:

* **005-70, a correctness bug**: the STM's `KeyModSet` is empty after a
  start, so a transaction that read before a restart can commit where it
  is refused without the restart (012-02's audit, C4, with a probe).
* 005-71 (`DbClock`'s last read time not kept across a start), 005-72
  (the files after a physical cut depend on timing; the cross tests
  compare from the decided cut, its option A), 005-69 (`SystemClock`'s
  promise), 005-73 (seven small API findings), 005-74 (a negative node
  size makes the parser loop until the heap is gone), 005-75 (dead checks
  such as `checkIncreasingTime` and `validateTransactions`, and comments).

## 0.5 For Frans to decide

1. **005-70**, the STM after a start: fix Java soon (its option A, the
   new set's first time at the last transaction's)? Recommended: yes.
2. **012-02, Q1 and Q2** (section 13): the comparison from the decided
   cut (done so, as 012-01 meant) and the restart findings registered
   (done); confirm. Recommended: confirm.
3. **012-11, Q1** (section 6.4): C forces the stream itself when a cut is
   pending, so that the disk is freed without a sync. Recommended: yes.
4. **012-13, Q2** (section 6.5): a closed handle ends at the close, as a
   `FILE` after `fclose` (implemented). Recommended: confirm.
5. **D6b**: the format document to `docs/stream-format.md` is due now
   that 012-10 is done (012-01, section 11). Proposed: copy sections 1 to
   12 of 012-02 to `docs/stream-format.md`, kept up to date with the code
   from then on; 012-02 stays as the history (its review and questions);
   `core/doc-files/stream-format.txt` becomes a pointer.
6. **012-15's proposals** (all keep the bytes): `-flto` (+15 to +34
   percent on every figure), a bounded eviction sweep when D is over the
   budget. Recommended: a small task after 012-14.
7. **005-69, 005-71 to 005-75**: when to fix, each entry has a
   recommendation.
8. **012-14's open points** (14-robustness.md, section 6): one flipped
   bit of a record's time makes Java's start throw an `Error` and C's
   process abort (005-75); C could refuse it first as a format error (a
   prototype exists), or keep Java's behaviour until Java is fixed.
   Recommended: fix Java (005-75) and C together. Also: `-Werror` under
   gcc 16 (40 warnings, the library's 4 false positives), and the names
   of the exceptions C reports for read errors.

## 0.6 Left

* **012-14**, robustness: a first pass ran 05:00 to 06:20. 1,800 random
  workloads over wide parameters (916 with reclaim, 2,652 crash cuts,
  3,600 budget runs): all byte for byte equal to Java's. Long runs up to
  1M transactions with 50 restarts (2.49 GB written): Java's bytes, no
  sanitizer report, flat memory; one leak in the `bergdb-run` tool found
  and fixed. gcc 16: the tests pass without `-Werror`. 2,199 starts of
  corrupt variants: C refuses as Java but for the flipped-time case
  above. Left: power loss through an I/O seam (designed, not built),
  allocation failures in turn as a set, the open points above, a small
  eviction lag (20 kB over budget plus pinned in one run).
* **012-16**, this report's final version, after 012-14, with 012-01's
  next steps (section 1, item 7 below) and the log's entry in
  `docs/log.md`.



# 1. The goal

012's outcome, for Frans to decide what comes next, and the item closed.

Done when this file has, and 012 is set done:

1. **What works**: 012-01's "Done when", item by item, with its evidence
   (the sets, the seeds, the counts, the commits).
2. **The departures from Java**, each with its reason: one caller at a
   time, when bytes become durable, what is left out.
3. **What the port found in Java**: the 005 entries it registered, and
   their state.
4. **Speed, memory and size**, from 012-15.
5. **The format's document**: where it lives (012-01, D6).
6. **The code's place**: it stays in `items/012-bergdb-c/c/` (012-01,
   D1: "indefinitely for now"), and the report moves nothing. It says what
   that means once 012 is done, as a done item is history
   (`items/readme.md`), so that Frans can decide whether the C code is
   kept in step with Java, and where.
7. **Next steps**, with options and costs: Linux; an embedded target and
   006-08's open questions (memory and writes at small startup distances,
   raw flash, 005-60's block storage); readers in other threads; the C
   trace exporter for the Lean checker; keeping C in step with Java
   (`night.sh`, or the C gate in Java's).
8. **The log** of 012, and `docs/log.md`'s entry.


# 2. Read first

* 012-01 and every task file's outcome; 006-08, section 6; 005-60.


# 3. The work

Write it; review it against the task files; the news entry.


# 4. Tests

None.


# 5. Notes

Short: the evidence is in the task files, and the report points to it.


# 6. Progress

Not started.
