005-70. Fix: the STM forgets the writes before a start (`KeyModSet` is empty after a start)
=========================================================================================

Status: open. Kind: fix. Created 2026-10-28.

Registered by Claude (Opus 5.5, Claude Code), the conductor of 012, from
012-02's determinism audit (012-02, section 10.3, finding C4; question Q2
in its section 13), as 012-01's decision D5 says: a Java bug that the C
clone's work finds is registered here and not fixed in 012.


The issue
---------

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

Recommended: A, as the existing "too old" path then covers it. A
transaction that read before a restart and commits after it is rare in
practice (an application that keeps a read set across `stop()` and
`start()`), but the result is a wrong commit, not a performance issue.

For 012: the C clone ports `KeyModSet` as Java has it now; a comparison of
Java with C at the same restart points is not affected, as both forget
the same. After the fix C follows (012-01, section 9.2).


Done when
---------

The decision is taken; for A or B, the change with a test that fails
before it (the probe's case), `before-commit.sh` and `level2.sh` (the
STM), StreamDigest's note, and 012's C port brought in line.
