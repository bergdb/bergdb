021-17. Fix: transactionInfo() refuses a value that reclaim has rewritten
========================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-09 by Frans Lundberg.

What: with any finite retain duration, `Connection.transactionInfo()`
throws `LookupTimeNotAvailableException` ("reclaim has rewritten the
value, and the transaction that wrote it is no longer available") for a
value whose transaction nothing has cut, from reclaim's first iteration
on: for a value 10 ms old with a minute retained, while
`getFirstAvailableLookupTime()` is still 1970. Reclaim rewrites every
live value stored before its cut point, the first iteration all of them,
and `ConnectionImp.transactionInfo()` threw for any record with a KV under
reclaim's prefix. The Javadoc's advice, a later lookup time, cannot help.
Found by a new-user application, 020-24-06, U6-1 (medium); the
reproduction `TiRepro.java` in `/Users/f/fl/bench/2026-11-09/app-u6/probe/`.
With it, the Javadoc of 020-24-06's U6-2, U6-3, U6-4, U6-6 and U6-7
(changes of Javadoc only, as 020-24's commits).

Why: the method's promise is the transaction that wrote the value read;
the transaction is there, and a get at its own time finds it. A metrics
service cannot ask when an idle sensor last reported, and a walk back
through a key's versions stops inside the retain duration.

Frans: none, unless the fix needs a format change (he approves any such
change; not to be made here).

Done when: TiRepro as a unit test that fails before; a fix within
today's stream format that resolves a reclaim copy to the transaction that
wrote the value while it is available, else a refusal with a true
message; or, if none is small and safe, Javadoc and message that say
exactly what happens, and the alternatives here for Frans; the Javadoc of
U6-2, U6-3, U6-4, U6-6 and U6-7 made true (what 020-24's x24 wrote today,
67b9e2b..381d26a, not repeated); `BEFORE COMMIT OK` and `JAVADOC PUB OK`
under the gate lock; lines in `releases/next.md`.

First step: what a reclaim step's record keeps of the copied value.


Log
---

2026-11-09. Registered by coord-1109 from 020-24-06's U6-1 (and the
Javadoc findings U6-2 to U6-4, U6-6, U6-7), and taken by its agent r17
(clone `clone-r17`, on main's 772e09b).

2026-11-09. Done by r17: commits 579f7d9 (021-17, U6-1) and 6e336b6
(020-24, U6-2 to U6-4, U6-6, U6-7) in `clone-r17`, on main's 772e09b, to
land. Severity: medium, as 020-24-06 gave it. In 2026.1 to 2026.3
(005-42; before it the call gave reclaim's step, its time and its row).

* Why it threw. A step (`Reclaim.step`) rewrites each value live at the
  iteration's start and stored before its cut point, the first iteration
  every one, in an internal transaction that also stores the iteration's
  row under reclaim's prefix; the copy is a new version of the key at the
  step's time. A get at any later time reads the copy, and
  `ConnectionImp.transactionInfo()` threw for any record with a KV under
  reclaim's prefix. The cut comes much later: when the iteration's end is
  older than the retain duration.
* What the record keeps: the step's time and the copied key and value,
  not the original transaction's time or position. But the copy is the
  value of the key one unit before the step's time: the step reads at the
  latest state and puts the value with the key as read (`keyRead`,
  `readTime`), so a write of the key between them makes it run again
  (`RerunException`); transaction times increase strictly.
* Fix, in the Pub layer, within today's format: the connection keeps the
  key of its last read that found a value (`infoKey`, set with
  `getData.tpos` by `get()` and `exists()`); `transactionInfo()`, for a
  record of reclaim's, reads the key at the step's time less one unit,
  which gives the original or an older copy, followed back the same way,
  each record before the one it came from (else a `Bug`, which fails the
  database: cannot happen), and gives the transaction found, its time and
  its KVs. A read before the first available lookup time is refused, and
  then the transaction is before that time and reclaim has removed it or
  may at any time: `LookupTimeNotAvailableException`, "No available
  transaction info: reclaim has rewritten the value, at time S (UTC), and
  the transaction that wrote it is before the first available lookup
  time, F (UTC), and no longer available." So a transaction at or after
  the first available lookup time is always given (a refusal by a cut
  that overtakes the call also means a transaction before the new first
  time); one before it until reclaim removes it, as for a value never
  rewritten. A get of a copy costs one get and one record read more per
  level of copy. `Reclaim.step`'s comment states the property it relies
  on; no Core code changed.
* Not taken, nothing to decide: a format change in which the copy names
  its original transaction (in the step's value node or row) would save
  those reads; not needed.
* Left as it is, a note: the Core's `GetData.tpos` and `Db.getTrans` give
  a Core user reclaim's step for a copy, as before (`GetData.tpos`'s
  comment says "the transaction that wrote the value"); a line for the
  Core's Javadoc if wanted.
* Tests, each failing before the fix: `PubTester`'s
  `testTransactionInfoOfReclaimsCopy` (TiRepro with a test clock, 60 s
  retained, puts 20 ms apart: one copy, then a copy of a copy, nothing
  cut, the put's time and both KVs; after the cut passes the put, the
  refusal and its message) and `testTransactionInfoAgainstOracle` (2,500
  puts at 40 keys 10 ms apart, 1 s retained, gets at the latest state and
  at past times: 45 cuts, 63 reads of a copy, 18 refusals, each of a
  transaction before the first available lookup time, the rest right).
* Probes on the fixed build: TiRepro gives the put's time; u6's
  `TiAgeProbe`, 10 s each (3 s retained and 5 MB, 60 s and 5 MB, 3 s and
  50 MB): 0 refusals in 1.4 to 1.7 million calls, every time right
  (before: 79 to 170, all before any cut). u6's application, phases 1
  and 2 (60 s, 7.0 million writes, its own oracle): both phases OK, 0
  notes of a refusal before any cut or inside the retain duration, 0
  refusals of a transaction after the first available lookup time
  (the report's run: 45 such notes, 2,153 refusals before any cut in
  phase 1, 283 to 558 per step after the first available time); every
  refusal now of a transaction before it, the idle sensors' too (written
  40 s before, first available 4 s before now).
* Javadoc (commit 6e336b6, 020-24): U6-3, `setRetainDuration()` and
  `setStartupDistanceInMb()` can be undone by a crash before `sync()`;
  U6-2, what stays on disk, beside x24's when the first cut comes (U3-9),
  and that the startup distance paces reclaim (`DatabaseBuilder` too);
  U6-7, `getFirstAvailableLookupTime()` is `Time.units(0)` before the
  first cut and moves only when reclaim decides a cut, at a commit; U6-4,
  it only moves forward within a run, and a restart after a crash between
  a cut's decision and its durable record gives the time before, on a
  stream not cut; U6-6, `get()`, `exists()` and `ReadInterface` list
  `LookupTimeNotAvailableException`. Test
  `PubTesterJavadoc.testSettingsUndoneByACrashBeforeSync`. Not done here:
  U6-5, U6-8 to U6-10 (not asked).
* `releases/next.md`: Pub API (021-17) and Documentation (020-24).

Runs, under the gate lock (2026-11-09, 15:11 to 15:14), on the tree of
both commits: `BEFORE COMMIT OK (153 s)` (unit 1554, f 86, demos);
`JAVADOC PUB OK`. No Core code changed, so no `level1.sh`.
