021-13. Fix: transactionInfo() while another thread writes fails the database
==============================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-09 by Frans Lundberg.

What: a reader that gets a value and calls `Connection.transactionInfo()`
while another thread writes can fail the whole database:
`DbFailedException`, the cause a `StreamFormatException` "Bad item byte
size ... beyond the stream's record bytes"; every later call, the
writer's too, throws until a restart, which loses nothing. A variant
throws `IllegalArgumentException` "Not a position of a transaction ...:
at or past the end of the stream", which the Javadoc does not name (it
names `IllegalStateException`, "call get() again"). Found by a new-user
application, 020-24-01, findings U1-1 (high) and U1-2 (medium); the
probes `InfoRace4.java` (fails in 46 to 169 ms, in memory and in a
directory) and `InfoRace3.java` in
`/Users/f/fl/bench/2026-11-09/app-u1/probe/`.

Why: both calls are legal, and the Javadoc foresees the case (a get right
after the put, in another thread). A database fails when its environment
has failed or on a bug (010-01, P7): here a record not yet appended in
whole was taken for corrupt data.

Frans: none.

Done when: the interleaving explained; a test that fails before the fix
(deterministic if a hook can order it); the fix, so that the read waits
for the record, reads it from memory or answers as the Javadoc allows;
every other API that reads a record by position looked at; the probes
pass; `BEFORE COMMIT OK` and, if the Core changes, `java/stress/level1.sh`
under the gate lock; a line in `releases/next.md`.

First step: who sets a value's transaction position, and when its record
becomes readable.


Log
---

2026-11-09. Registered by coord-1109 from 020-24-01's U1-1 and U1-2, and
taken by its agent f13 (clone `clone-f13`, on main's 82edabf).

2026-11-09. Done by f13: commit f98ac76 in `clone-f13`, on main's
82edabf, to land.

* The interleaving. The writer, under `writeLock`, puts the values in
  memory with a vpos (`putKvs`), makes the transaction's time a lookup
  time (`DbClock.transactionEnd`), and only then stores the record
  (`Db.store`, `NodeStream.appendNodes`): `StoredTrans.Serializer` sets
  every node's position, a value node's real `spos` and
  `offsetFromTrans` included, and then `RecoverableStream.append` appends
  the record, in one append to the storage, or in three when a meta
  block falls in the record (the part before it, the meta block, the
  rest); each can wait for room in the storage's buffer. A get after
  `transactionEnd` reads the value: while its `spos` is a vpos,
  `ValueNode.getTpos()` gives `Spos.NULL` and `transactionInfo()` throws
  the documented `IllegalStateException`; from the serializer on it gives
  the record's real position. `transactionInfo()` calls `Db.getTrans`,
  which reads the record at that position through
  `NodeStream.TransIterator` (its size, then `checkReadSize` against the
  storage's length, then the record): with none of the record in the
  storage the iterator finds the end of the stream, and `getTrans` throws
  `IllegalArgumentException` (U1-2); with the part before a meta block
  appended, the size goes past the storage's length (always a multiple
  of 200,000 in the reports: 600,000), a `StreamFormatException`, which
  `getTrans` takes for corrupt data and fails the database with
  (`failOnStorage`, U1-1).
* Other reads of a record by a position from memory: none. `getTrans` is
  the only reader of a record by a get's position; its only caller is
  `ConnectionImp.transactionInfo()` (020-22's change left the read as it
  was, it filters the KVs after it); `TransactionInfo`, `Kv` and the
  primary and index scans read no record; the other users of a
  transaction iterator (start, recovery, reclaim) run under `writeLock`,
  after the appends; a node is reached by a stream pointer only after
  `store` has appended its record (eviction's admission comes after it).
* Fix, in the Core, small: `NodeStream` keeps a volatile `appendedEnd`,
  the end of the records appended in whole (set after the append in
  `appendNodes`, and to the stream's length by `recover()`), and
  `Db.getTrans` waits for the writer, `synchronized (writeLock) {}`, when
  the position is at or after it. The writer appends the record under
  `writeLock`, so after the lock the record is in the stream in whole, or
  the database has failed, which the state check after it finds. Only a
  position of a record not yet appended in whole waits, for the rest of
  that transaction (a bad position past the end too, refused as before);
  every other call takes no lock, as before. The vpos window keeps the
  documented `IllegalStateException`; the Pub API's Javadoc is
  unchanged, `Db.getTrans`'s says that it waits.
* Test `DbTesterFailure.testGetTransOfARecordBeingAppended`,
  deterministic: the storage's flush held (`FaultStream.holdAppends`) so
  that its buffer fills and the writer waits for room in the middle of
  its record, before any of it (case none) or after its part before a
  meta block (case part, a buffer that is full just there). Before the
  fix: case none, `IllegalArgumentException` ("at or past the end of the
  stream"); case part, `DbFailedException`, the database failed. Now
  `getTrans` waits for the write lock, and gives the transaction once the
  flush goes on. About 30 ms.
* Probes after the fix, 3 s each: `InfoRace4` in memory and in a
  directory, values of 1,000 and 10 bytes: no failure, no
  `IllegalArgumentException`, 70,266 to 1,122,600 reads, and 1,125 to
  32,887 documented `IllegalStateException`s (the vpos window);
  `InfoRace3`: 0 of 10 rounds threw another exception. Before the fix,
  on this build and on the 2026.2 and 2026.3 jars, `InfoRace4` failed the
  database within 59 to 115 ms; 2026.1's `getTrans` reads the same way.
* `releases/next.md`, Pub API, a line.

Runs, under the gate lock (2026-11-09, 13:24 to 13:37):
`BEFORE COMMIT OK (227 s)` (unit 1507, f 86, demos);
`java/stress/level1.sh`: `LEVEL 1 OK`.
