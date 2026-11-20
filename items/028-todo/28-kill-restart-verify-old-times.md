028-28. Investigate: the kill-and-restart harness's check at old times
======================================================================

Status: in progress. Kind: Investigate. Frans: none.
Created 2026-11-19 by Frans Lundberg.

What: `KillRestartHarness.verify()` reads the database at old times on the
real clock, with a retention of 20 seconds. A lookup whose time has
passed out of the retention is refused, and verify() does not tell such
a refusal from a lost or wrong value: a slow check on a loaded machine
could read too late and fail, or a check could be skipped. Noted while
sorting the test scripts by kind (028-23); not seen to fail.

Why: The harness must fail only for the database's faults (020-15), on loaded
machines too: night.sh and week.sh run under load.

Frans: none.

Done when: Either verify() reads only times inside the retention at the moment of
the read and says how it ensures it, or a refusal at a time that has
left the retention is counted as expected; a test that shows the case;
`java/before-commit.sh` BEFORE COMMIT OK; `kill-restart.sh 1000` KILL
RESTART OK.

First step: Read verify() (java/src/bergdb/pubimp/KillRestartHarness.java, around
line 942) and the lookups it makes; find whether a refusal can reach its
comparison.


Findings
--------

**When a refusal can reach the checks.** A lookup is refused
(LookupTimeNotAvailableException) only at a time before the first
available lookup time, and that moves only when reclaim cuts, to the end
time of an iteration older than the retain duration (`Reclaim`, bergdb
027-13): a refused time t is always t < first <= now - retain. The
harness reads at old times in four places:

- `verify()`, right after the start: the killed run's resolution at tsj,
  the time of the first start after its kill (several runs earlier when
  the runs after the kill were killed during their start or their
  checks), and `checkAtStart()` at ts, this start's time. A refusal
  escaped as an exception: the child printed FAIL, and the harness failed.
  For it, a cut past tsj must come after tsj, from the commits of the
  resumed builds and cleanups alone (no user transaction is committed
  after the kill until the next schedule), and at least 20 s after the
  iteration's end: rare, but possible on a loaded machine or after a chain
  of short runs. The information of the transaction in flight
  (`transactionInfo()`) is refused in the same way when reclaim has
  rewritten its stamp and cut the transaction.
- `checkNow()` in the schedule and `settle()`: a fresh time, but the reads
  that follow may take more than the 20 s on a loaded machine; a refusal
  failed the run in the same way.
- `checkPast()`: skipped a time before the first available one, and
  caught a refusal silently.

No failure of this kind is known.

**The fix** (`KillRestartHarness`, the harness only): option two of the
Done when, a refusal at a time that has left the retention is expected.

- `refused(t, e)` decides it: expected only if the database has a retain
  duration and t < first <= now - retain (first, the first available
  lookup time read after the refusal). A refusal at a time inside the
  retention, with none set, or not explained by the first available
  time fails the run as before. Counted as `cutSkipped`.
- `checkNow()`, `settle()` and `checkPast()`: an expected refusal skips
  the check at that time.
- `verify()`: the time each read needs is kept (tsj, ts, and for the
  transaction in flight's information a time after the last committed
  one before it, a bound at or before its own). After an expected
  refusal the run cannot check the database, and its model cannot be
  made: verify() throws Abandon, the child prints ABANDON with the reason,
  its counts and "P abandon" and ends with status 0, and the parent
  counts `abandoned`, says "Database N abandoned in run R: ..." and
  begins a new database. Nothing is checked at a later time instead:
  the checks keep their meaning.

**The test.** `KillRestartHarness.testRefusalOutsideRetention` (unit, about
2 s): a database with a retain duration of 1 s and the Core's startup
distance of 10 bytes is written until its first available lookup time is
past the start's time ts; verify() then meets the refusal at ts, which
refused() accepts, and throws Abandon (on the old code the refusal escaped
and the child would print FAIL); a refusal claimed at the current time
fails refused()'s check. The parent's path was tried once with a refusal
forced in verify() (not committed): "Database 0 abandoned in run 3", then
the next databases, KILL RESTART OK.


Log
---

2026-11-19. Registered by coord-1118 from a report of the day's work.

2026-11-20. Taken by hf of coord-1120, on the branch `028-29-28-harness`.
