005-70. Fix: the STM forgets the writes before a start (`KeyModSet` is empty after a start)
=========================================================================================

Status: done. Kind: fix. Created 2026-10-28. Done 2026-10-30.

Registered by Claude (Opus 5.5, Claude Code), the conductor of 012, from
012-02's determinism audit (012-02, section 10.3, finding C4; question Q2
in its section 13), as 012-01's decision D5 says: a Java bug that the C
clone's work finds is registered here and not fixed in 012.


The issue before the fix
------------------------

A transaction with a read set is refused (`RerunException`) when a key it
read was written after its read time: `Db.stmCheckConflicts` asks
`KeyModSet.modifiedAfter(readTime, hash)`. `KeyModSet` is kept in memory
only. A start makes a new one (`Db`, `keyModSet = new KeyModSet()`), whose
first bin has `firstTime` −1 (`KeyModSet.Bin`). So after a start every read
time counts as covered, and no write before the start is seen:

* a transaction whose read time is before the start, and whose read key
  was written between its read time and the start, **commits** where
  without the start it is refused. That is a gap in the STM's
  serializability: the transaction read a value that was no longer the
  latest, and still commits;
* and a restart changes the bytes of the stream (against P2, 010-01): the
  committed transaction writes a record that the run without the restart
  does not.

Probe (012-02, `/Users/f/fl/bench/012/02-out/audit/` and `02-out/verify/`,
`RestartStateProbe stm`): put `/k` at T1; put `/k` at T2; [restart]; at
T3 a transaction with `lookupTime(T1)`, `keyRead("/k")` and a put of
`/j`. Without the restart it is refused (stream 472 bytes); with it, it
commits (560 bytes).

`KeyModSet.modifiedAfter` already answers "modified" for a read time older
than what it holds ("Too old time, not enough information, we must be on
the safe side"); it lacks only the knowledge that, after a start, it holds
nothing before the start.


Options
-------

* **A.** At a start, give the new `KeyModSet` a first time equal to the
  last transaction's time (or the first transaction after the start), so
  that a read time before it is "too old" and refused, as for a read time
  older than the set's bins. Small; a test with the probe's case.
* **B.** The same through `Db`: refuse a transaction whose read time is
  before the start's last transaction time.
* **C.** Nothing; document that a read set does not reach across a start.

Recommended: A, as the existing "too old" path then covers it. This is a
Core API case: application code retains read results, their actual lookup
time and their read dependencies, closes the old `Db`, and submits a
transaction to a new `Db` on the same stream. `Db.start()` is called once
per object; an ordinary Pub API transaction stays attached to its old
connection and cannot migrate to the new object. The original probe
supplies a read time and read dependency directly, without performing a
read. There is no current practical use case for carrying reads across
objects (Frans, 2026-10-30), but accepting an unchecked read set is unsafe.

For 012, the original decision was to port `KeyModSet` as Java had it;
comparisons at the same restart points were not affected, as both forgot
the same. C now follows this fix (012-01, section 9.2).


Done when
---------

The decision is taken; for A or B, the change with a test that fails
before it (the probe's case), `before-commit.sh` and `level2.sh` (the
STM), StreamDigest's note, and 012's C port brought in line.


Decision and implementation, 2026-10-30
--------------------------------------

Frans accepted option A after discussing the lifecycle and the Core API's
read sets. The boundary is the **last recovered commit's time**, including
an empty commit, not the wall clock and not the first write after startup.
A read time equal to that boundary is covered; an older time with a read
dependency is refused with `RerunException`. A transaction without read
dependencies needs no STM validation.

`Db.startInner` initializes the new `KeyModSet` with that time, before
publishing the active database. `KeyModSet.setFirstTime` initializes the
empty first bin. Its first add preserves the initialized boundary, so an
unrelated write does not unnecessarily invalidate a snapshot taken just
after startup. The existing "too old" path does the refusal; bin turnover
and conflict detection otherwise work as before. The C port follows in
`kms_set_first_time` and `db_open`, and both APIs document the refusal.

The regression `DbTesterRestart.testStmAfterRestart` reads `/k` and saves
`GetData.actualLookupTime`, changes `/k`, makes an empty commit, closes the
database, and opens a new object. On the code before the fix it failed
with "committed a stale read set at 10". It passes after the fix, with
startup distances of 100 and 1,000,000 bytes. It also checks that refusal
changes neither the stream length nor `/j`, an empty commit after startup
does not lose the boundary, equality is accepted, the first unrelated
write preserves coverage, later conflicting writes are detected, fresh
reads can commit, and a transaction without read dependencies still works.
`KeyModSet.testStartupBoundary` checks the boundary and its eventual
replacement by normal bin turnover. C has the matching boundary unit test
and `api_stm_after_restart`, using real read times and close/open on files.

The original `RestartStateProbe stm` also now refuses both runs, with and
without the restart (`RerunException`, 472 bytes each); their stream files
are byte-for-byte identical.

StreamDigest's scope: its workloads exercise ordinary writes, reads and
restarts, but do not submit read sets from before a restart. They must keep
their bytes. The probe's stale transaction intentionally changes from a
commit to a refusal. This does not promise identical STM decisions for
every read set across restarts: an older snapshot is conservatively
refused even when its keys happened not to change.

Validation on 2026-10-30:

* The new Java integration test fails before the fix and passes after it;
  both new Java tests pass, and C's boundary and API regressions pass.
* `java/before-commit.sh`: `BEFORE COMMIT OK` (1,073 unit tests and 78
  f-tests).
* StreamDigest against the build before the fix: `DIGESTS IDENTICAL`
  (36 of 36), using the same compiled harness for both builds.
* C's `before-commit.sh`: `C BEFORE COMMIT OK`, including the sanitizer
  and release tests, macOS leak checks, Java/C cross-tests (22 workloads,
  82 crash cuts, 85 corrupt variants and 44 budget runs), write checks,
  allocation failures and examples. The first sandboxed attempt could not
  obtain a task port for `leaks`; the complete run outside the sandbox
  passed.
* `java/stress/level2.sh` (full): `LEVEL 2 OK`; the Lean build passed
  (148 jobs), and all 70 conformance traces passed.

The command outputs, including the regression failure before the fix, are
in [validation.txt](70-keymodset-after-start/validation.txt).
