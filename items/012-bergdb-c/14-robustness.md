012-14. Task: robustness and scale
==================================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: not started**; approved with 012-01 by Frans's
go (012-01, 9.1).
Phase E (012-01, section 8). Effort: high; max to diagnose a failure.
After: 012-13.


# 1. The goal

Confidence beyond the standard sets: many random workloads, crashes and
power loss, corrupt input, long runs and a large database.

Done when:

1. **Random runs by the thousand**: `Gen.java`'s workloads over a wide
   range of parameters (node sizes, startup distances, retain durations,
   value sizes, transaction sizes, restarts, setter calls), Java against
   C: the same files and dumps. A failing seed is kept as a workload in the
   full set once fixed.
2. **Power loss**, through an I/O seam in C as Java's `FileStreamIo`
   (011-07, `PowerLossTest`): writes that were not forced are lost or
   torn at chosen points; C recovers to a state that Java also recovers
   to from the same files, and no committed and synced transaction is
   lost.
3. **Corrupt input**: bit flips, cut and missing files, files with wrong
   names or sizes, garbage meta blocks: C refuses them with an error code
   as Java does, never crashes, never writes into a database it refuses
   (under the sanitizers).
4. **Long runs**: 100,000 transactions and more with restarts, reclaim and
   a small budget, under the sanitizers and `leaks`: no failure, no leak,
   and the directory's size bounded.
5. **Scale**: the 10M-key workload (`cross.sh scale`), at a startup
   distance of 50 MB and of 200 MB: C and Java write the same bytes; C
   starts Java's database and reads it; Java starts C's.
6. **A second compiler**, if cheap: the code builds and the tests pass
   with Homebrew's gcc 16, as a check of portable C.
7. **Allocation failures** (012-01, 4.5), through 012-04's allocator: for
   small workloads, each allocation made to fail in turn, one run each.
   The call gives NOMEM; before the go point the database is as it was,
   and the run goes on to the same bytes as without the failure; after it
   the database has failed (P7); close frees everything, the allocator's
   count is 0, under the sanitizers. A short version runs in the gate.


# 2. Read first

* `java/stress/PowerLossTest.java`, `CrashTest.java`, `DagFuzz.java`,
  `RestartStress.java`, `Soak.java`; 011-07 (durability and the fault
  model); 005-46 (the file stream's reads and the cut).
* The memory notes on F53's timing etiquette (other sessions' timed runs,
  quiet blocks) before the long and the large runs.


# 3. The work

1. The I/O seam in C's platform module, and the power-loss runs.
2. The corrupt-input runs.
3. The random runs, in batches, in the background, outside other
   sessions' timed blocks.
4. The long runs and the large one, the same.
5. The allocation-failure runs (done item 7), and their short version in
   `before-commit.sh`.
6. Each failure: a minimal workload, the cause, the fix (in C), or a 005
   entry (in Java).


# 4. Tests

This task is tests. Its new workloads join the full set when they are
cheap enough, or a `cross.sh night` set if Frans wants one in `night.sh`.


# 5. Notes

* The large runs take minutes and all cores for a while: not while
  another session times anything (012-01, section 9).
* Startup distances of 50 MB or more for large runs, as for Java's
  measurements; small ones are for the small workloads.


# 6. Progress

Not started.
