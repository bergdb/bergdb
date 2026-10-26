005-todo
========

Created 2026-10-19 by Frans Lundberg. Status: open.

A list of things to do on BergDB: issues to fix, things to investigate,
decisions to make. Each entry is a subitem with its own ID and a short
definition: what, why, the questions, when it is done, the first step. An
entry that grows into real work gets an item of its own, linked from here.


The list
========

Two tables: what is left to do, and what is closed. A subitem's own
`Status:` line is the source. When an entry closes (done, dropped or
moved), its row moves from Open to Closed in the same edit, with the date
it closed; Closed is newest first. Files stay where they are, so links to
them keep working.


Open
----

| ID | Kind | What | Status |
|---|---|---|---|
| [005-03](03-sweep-cost.md) | Investigate | The sweep's cost under read churn (item 001, finding 10) | open |
| [005-05](05-bergdb-future.md) | Decide | What to do with BergDB: publish it, when, money, paid work | open |
| [005-06](06-publication-literature.md) | Investigate | The literature and the options for a publication | open |
| [005-07](07-transaction-synchronization.md) | Investigate | Synchronization of transactions: how it is today, how it may need to change | open |
| [005-11](11-replication.md) | Decide | Replication: study the implementation and its tests; remove it, complete it, or change its design (005-10). For release 2026.1: kept, documented as experimental | open |
| [005-46](46-stream-file-lock.md) | Fix | A read of the stream's last file waits for the writer's append and its `fsync` (`FileStream.DbFile`, one monitor for both): seconds on s1's disk, the longest waits left there with handles (009-03) | open |
| [005-47](47-written-not-forced.md) | Decide | A durability of "written, not forced": a sync that returns when the bytes have left the process (`write()`), not when they are forced to the device; Frans's question. Options: a property of the storage (`FileStream` without per-append forces), a new sync level, or nothing. Forces stay at new files, cuts and deletes; holes in an unforced tail are untested (after 005-46) | open |
| [005-48](48-group-commit.md) | Investigate | Group commit: a sync that waits starts the flush, instead of waiting for `BufferedStream`'s timer; one thread's durable commit from 35 ms to about one force (005-13's question 5) | open |
| [005-49](49-smooth-index-writes.md) | Investigate | Smooth index writes: at large startup distances the index is written in bursts (10M keys, 1000 MB: windows of 70 to 1,100 bytes a put); a commit's index writes should follow its own size. Before 007-03's step 3 (005-38) | open |
| [005-50](50-fix-node-size-start.md) | Fix | A start with another node size than the stream was written with fails with what looks like a corrupt stream (`StreamFormatException: startup error, node ... not found`); it should fail with a clear error. Only that (005-38) | open |
| [005-51](51-eviction-on-calls.md) | Fix | Eviction only in response to the calls: the eviction thread wakes once a second while the database is open, also when idle (`evictorLock.wait(1000)`), against 010-P3, calm when not used | open |
| [005-52](52-cache-size-while-running.md) | Fix | Change the cache size while the database runs: the Pub API sets it only at start (`cacheSizeInMb`), against 010-P6; the core has `Eviction.setBudget` (also through JMX). The cache should converge gradually to the new size, with no disruption | open |
| [005-53](53-startup-distance-on-the-fly.md) | Investigate | The startup distance on the fly: the Pub API cannot change it for an existing database (against 010-P6); the core can since 2013-04, through JMX only. A decrease in steps (007-03's D4), measured; options A to D for the Pub API; `Reclaim.initialStartupDistance`. First study, from 010-03, in its directory | open |
| [005-54](54-open-bounds.md) | Investigate | The bounds still open in the problem statement, 011-01: Q1 the lookup bound, Q2 long keys, Q3 the cost model, Q5 write overhead, Q8 the space bound with reclaim; carried forward when it left `docs/` (006-07) | open |


Closed
------

| ID | Kind | What | Status | Closed |
|---|---|---|---|---|
| [005-38](38-writes-at-scale.md) | Investigate | Writes at scale: the stream grew to about 1.1 KB per key at 100M random keys (004-02); the cause was its startup distance of 10 MB. At 200 to 1000 MB a put costs 180 to 670 bytes at 10M and 50M keys; the fix is a startup distance that suits the database. Node size 30 stays. Bursts of index writes at large startup distances found | done | 2026-10-26 |
| [005-45](45-fix-two-leftovers.md) | Fix | Two faults found on the way in 005-40 and 005-41: `SalsaStream.getLength()` did not count what it appended (BergDB's own stack did not meet it), and `WTransaction.sync(SyncLevel)` waited for the database's last transaction, not for its own; now the length is the underlying stream's, and the sync waits for its own transaction, as `sync()` does | done | 2026-10-25 |
| [005-42](42-transaction-info.md) | Decide | `Connection.transactionInfo()` gave internal KVs, whose `key()` threw (an index entry, reclaim's row), and for a value that reclaim had rewritten, reclaim's transaction and its time; from a TODO of 2016 (006-05). Decided A1 and B2: the internal KVs are left out, and a value that reclaim has rewritten gives `LookupTimeNotAvailableException` | done | 2026-10-25 |
| [005-33](33-crashed-creation.md) | Decide | A database whose creation crashed (a power loss in the first write of its stream) never started: one of three `StreamFormatException`s that did not say why, after recovery had zero-filled its first transaction. Decided A, one clear error: a start refuses it with a `DatabaseNotCreatedException` that says what happened and what to do, and writes nothing (005-28) | done | 2026-10-25 |
| [005-44](44-fix-sync-commit-byte.md) | Fix | A sync returned when every byte of the transaction but its last, the commit byte, was durable, so that a crash could then lose a transaction that the sync had reported durable, with a write buffer whose size is not a multiple of 4 (through the core API); now it waits until the commit byte is durable too (005-41) | done | 2026-10-25 |
| [005-41](41-is-durable.md) | Decide | `isDurable()`, whether a transaction is durable, answered at once, beside `sync()`; Frans's idea of 2026-10-13, from comments in the Pub API (006-05): not now (option C) | done | 2026-10-25 |
| [005-43](43-fix-from-todos.md) | Fix | Two leftovers of TODO markers (006-05): `Db.getTrans` threw a `DbException` for a position at or past the end of the stream, and the Pub API's `IndexBuilder.dir` and `UsePrimaryBuilder.dir` a `BadFormatException` for a bad directory; now both throw `IllegalArgumentException`, as for the other positions that cannot start a transaction and for a bad key | done | 2026-10-25 |
| [005-40](40-fix-refused-start-writes.md) | Fix | A start wrote to the stream before it checked the crypto key and the format: after a crash that ended the stream at or just inside a meta block, a start with a wrong key, or none, left a database that the right key could not start either; a newer record format was refused as corrupt data, with format 2's message. Now recovery reads the meta blocks first, and the versions of records and nodes are refused with a `VersioningStreamException` that says which BergDB wrote the stream. The format check that `DbStarter`'s TODO asked for had been made by the parsers since 2015 | done | 2026-10-25 |
| [005-39](39-fix-trans-completed-before.md) | Fix | `RecoverableStream.getPosOfTransCompletedBefore`, where the iterators that do not start at an exact position start: its Javadoc promised the last transaction completed before the position, which it never searched for (a TODO said so), and in a stream cut by reclaim it threw `NullPointerException` or gave a transaction before the cut; now the Javadoc says what it gives, and in a cut stream it gives the first transaction after the cut that a meta block names | done | 2026-10-25 |
| [005-31](31-fix-take-blocked.md) | Fix | A transaction whose dirty index nodes did not fit in one record stopped the startup pos for good; now one whose index nodes, by a bound at the largest node size, could take more than 15/16 of the record limit is refused before its go point (007-02, 007-03 step 1) | done | 2026-10-24 |
| [005-35](35-fix-stop-and-close.md) | Fix | `stop()` lost the transactions still in the write buffer; `close()` returned at once after `stop()` or beside another `close()`; a writer that waited for room in the buffer waited for ever; now `stop()` starts one close that writes everything, in a thread that is not a daemon, and `close()` waits for it | done | 2026-10-24 |
| [005-32](32-fix-failed-start-storage.md) | Fix | A start that threw left its storage running: its threads, its open files, and writes of what it appended, also into a database started after it; `BufferedStream.close()` hung when the last flush failed; now a start that throws closes its storage before the exception leaves (005-28) | done | 2026-10-24 |
| [005-34](34-fix-transaction-info-position.md) | Fix | `Connection.transactionInfo()` read at a wrong position for a value after a meta block in its record, and, after a restart, for a value rerun at startup; now a get gives its transaction's position, `getTrans` refuses a position that cannot start one, and a format error there fails the database (005-30) | done | 2026-10-24 |
| [005-37](37-fix-memory-stream-checks.md) | Fix | `MemoryStream` took a negative length to `append` and a `pretruncate` past its length, after some of which it took no more appends; now it refuses both, and `AppendOnlyStream`'s Javadoc says what the streams do (005-29) | done | 2026-10-24 |
| [005-36](36-fix-test-crash3.md) | Fix | `DbTester.testCrash3` never tested a truncation: it truncated a copy and started on the original; now it starts on the copy, after a sync that writes the creation (005-29) | done | 2026-10-24 |
| [005-30](30-fix-read-failure.md) | Fix | A read or a sync that failed on the storage (an I/O error, corrupt data) left the database running half dead; now it fails the database, as a transaction does since 005-01 | done | 2026-10-23 |
| [005-27](27-fix-meta-block-edge.md) | Fix | A crash that ended the stream exactly at a meta block's position, after a transaction that ended there, left a database that did not start; now recovery fills out that meta block too, as one partly written (005-11, P11) | done | 2026-10-23 |
| [005-29](29-fix-memory-stream-assert.md) | Fix | `MemoryStream.copy` failed an assertion when the stream was empty or its length a multiple of 1,000,000 bytes (test code; 005-11); now its arrays are exactly those that hold bytes, also after `truncate` and an append of 0 bytes | done | 2026-10-23 |
| [005-28](28-fix-trans-iterator-loop.md) | Fix | Startup looped for ever when the transaction at its start position was a failed one (a damaged or mixed stream, 005-11's P9, or a crash in a new database's first transaction); now it throws a `StreamFormatException` that names it | done | 2026-10-23 |
| [005-01](01-fix-m49-exception-safety.md) | Fix | M49: a transaction that threw after its go point was half committed; now it fails the database, which refuses every transaction and read until it is restarted (item 003) | done | 2026-10-22 |
| [005-12](12-transaction-outputs.md) | Decide | Transaction outputs (`setOutput`, `getOutput`) stay, with a consistent API: typed, null for a missing output, the same checks; an environment refuses calls after its action (005-10) | done | 2026-10-22 |
| [005-26](26-fix-lone-surrogates.md) | Fix | A string with a lone surrogate cannot be stored in an array: `utf8Size` | done | 2026-10-21 |
| [005-25](25-fix-buffered-read-past-end.md) | Fix | A `BufferedStream` read one byte past the end returns a stale byte | done | 2026-10-21 |
| [005-24](24-fix-file-read-at-end.md) | Fix | A `FileStream` read at the end of the stream loops forever | done | 2026-10-21 |
| [005-23](23-fix-deep-objects.md) | Fix | `StackOverflowError` for a cyclic or deeply nested object at a put | done | 2026-10-21 |
| [005-22](22-fix-narrowing.md) | Fix | A stored value too large for its Java field is truncated silently | done | 2026-10-21 |
| [005-21](21-fix-small-overflows.md) | Fix | Smaller overflows: `Time.millis`, `TimeResolver` seconds, `TransSeq.take`, negative key hashes, `DbObject` shorts, corrupt counts | done | 2026-10-21 |
| [005-20](20-fix-jmx-retain-days.md) | Fix | `Jmx` `setRetainDurationInDays` in `int`: 99,999 days becomes 578.5 | done | 2026-10-21 |
| [005-19](19-fix-file-names.md) | Fix | `FileStream` cannot reopen a stream past 214.7 TB: file names parsed as `int` | done | 2026-10-21 |
| [005-18](18-fix-clock-range.md) | Fix | A clock time of 2^56 or more is not checked; the database cannot restart ("Time too large") | done | 2026-10-21 |
| [005-17](17-fix-transaction-size.md) | Fix | A transaction of 1.79 GB or more is half committed and blocks the writer: the record's sizes in `int`, no size limit (M49) | done | 2026-10-21 |
| [005-16](16-fix-memory-stream-first-pos.md) | Fix | An in-memory database with a retain duration fails after 2^31 bytes: `MemoryStream`'s first position in `int` | done | 2026-10-21 |
| [005-15](15-fix-index-scan-carry.md) | Fix | Long-index range scans skip or add entries: `plusOne` does not clear the `0xff` bytes it carries past (startAt(255) exclusive misses 256 to 510) | done | 2026-10-21 |
| [005-14](14-calm-when-idle.md) | Decide | Calm when idle: an idle database woke 163 times a second at 20 ms; now the consumer sleeps when nothing is buffered; also the wake count's overflow and a close that appended the whole buffer (005-13) | done | 2026-10-21 |
| [005-10](10-unused-code.md) | Investigate | Unused code in `java/` and `lean/`: find it and propose what to remove; nothing is removed without Frans's approval | done | 2026-10-20 |
| [005-09](09-fix-node-table-snapshot-race.md) | Fix | A race between a reader and a sweep lets the node table name a released object (INV-CAN); a unit test fails now and then (005-02) | done | 2026-10-20 |
| [005-13](13-buffer-time.md) | Investigate | The buffer time (100 ms, from the hard-drive era): sweep it on SSD, then decide the default and group commit; now 20 ms | done | 2026-10-20 |
| [005-08](08-fix-node-table-tree-bins.md) | Fix | The node table's 256 maps make every bin a tree (`Cache3.mapIndex`): 61 bytes per KV, a slower `set` (006-02) | done | 2026-10-19 |
| [005-04](04-a6-failures.md) | Decide | A6 fails in 5 Java transactions: is anything to be done? | done | 2026-10-19 |
| [005-02](02-fix-m46-ordinal-bound.md) | Fix | M46: the top node ordinal bound, 2^30 − 1 over a database's life (item 002) | done | 2026-10-19 |

Status values: open, in progress, done, dropped, moved (to an item of its
own). Kinds: Fix (a known fault), Investigate (find out, then propose),
Decide (a question for Frans, prepared by an investigation).

Order, as proposed, of what is open: 005-03 next among what changes Java,
as it changes the same part of it as 005-01 and 005-02, which are done;
005-05 and 005-06 beside the rest, as they are mostly reading and thinking,
and 005-06 feeds 005-05. 005-07 is best before 005-03's fix; the go point
it asks about is in `Db.executeInner` since 005-01. 005-09 is done. What is left of 005-10 waits for Frans; a removal is best made
when no other change to `java/` is under way. 005-11 can go any time, best
before 005-05's decision on publishing, as it concerns the Pub API; 005-12
is done. 005-27, 005-28 and 005-29, the fixes found in 005-11, are done.
005-30 is done, and so is 005-34, found in it. 005-31 is done, which item
007's deadline for `TransSeq.take` (007-01, D1) needed. 005-32
is done, which 005-33's change needed; 005-33 is decided, A, and done. 005-35,
005-36 and 005-37 are done, and so are 005-39, 005-40, 005-43 and 005-44.
005-41 is decided: not now. 005-42 is decided, A1 and B2, and done, and so
is 005-45. 005-11 is kept as it is for release 2026.1, documented as
experimental; its decision waits for Frans.


Files
=====

* [01-fix-m49-exception-safety.md](01-fix-m49-exception-safety.md). 005-01,
  fix M49; done, with its probe, checks and runs in
  [01-fix-m49-exception-safety/](01-fix-m49-exception-safety/).
* [02-fix-m46-ordinal-bound.md](02-fix-m46-ordinal-bound.md). 005-02, fix
  M46.
* [03-sweep-cost.md](03-sweep-cost.md). 005-03, investigate the sweep's
  cost.
* [04-a6-failures.md](04-a6-failures.md). 005-04, the A6 failures: decide
  whether anything is to be done; done, with its tools and runs in
  [04-a6-failures/](04-a6-failures/).
* [05-bergdb-future.md](05-bergdb-future.md). 005-05, what to do with
  BergDB.
* [06-publication-literature.md](06-publication-literature.md). 005-06, the
  literature and the options for a publication.
* [07-transaction-synchronization.md](07-transaction-synchronization.md).
  005-07, synchronization of transactions: today's design, from the code and
  F1-007's notes, and what may need to change.
* [08-fix-node-table-tree-bins.md](08-fix-node-table-tree-bins.md). 005-08,
  fix the node table's tree bins, found and measured in 006-02; done, with
  its runs and tools in
  [08-fix-node-table-tree-bins/](08-fix-node-table-tree-bins/).
* [09-fix-node-table-snapshot-race.md](09-fix-node-table-snapshot-race.md).
  005-09, fix the race that lets the node table name a released object,
  found in 005-02; done, with its probe, runs and checks in
  [09-fix-node-table-snapshot-race/](09-fix-node-table-snapshot-race/).
* [10-unused-code.md](10-unused-code.md). 005-10, find unused code and
  propose what to remove, for Frans to approve; the proposal, with its
  tables, plan, tools and runs, in [10-unused-code/](10-unused-code/), and
  the removal as Frans decided it in
  [10-unused-code/applied/](10-unused-code/applied/).
* [11-replication.md](11-replication.md). 005-11, replication: the
  decision material for Frans; the study, with its probes and runs, in
  [11-replication/](11-replication/).
* [12-transaction-outputs.md](12-transaction-outputs.md). 005-12,
  transaction outputs: they stay; the API made consistent, with unit
  tests; done.
* [13-buffer-time.md](13-buffer-time.md). 005-13, the buffer time: the
  sweep, and the default changed to 20 ms; done, with its table, tools
  and runs in [13-buffer-time/](13-buffer-time/).
* [14-calm-when-idle.md](14-calm-when-idle.md). 005-14, the idle cost of
  the storage thread's timer, by buffer time, and the fix: the consumer
  sleeps when idle, with two faults of `BufferedStream` fixed; done, with
  its table, tools and runs in [14-calm-when-idle/](14-calm-when-idle/).

* [15-fix-index-scan-carry.md](15-fix-index-scan-carry.md) to
  [26-fix-lone-surrogates.md](26-fix-lone-surrogates.md). 005-15 to 005-26,
  the findings of the review of the Java code for overflow: 15
  [index scan carry](15-fix-index-scan-carry.md), 16
  [MemoryStream first position](16-fix-memory-stream-first-pos.md), 17
  [transaction size](17-fix-transaction-size.md), 18
  [clock range](18-fix-clock-range.md), 19
  [file names](19-fix-file-names.md), 20
  [Jmx retain days](20-fix-jmx-retain-days.md), 21
  [smaller overflows](21-fix-small-overflows.md), 22
  [narrowing](22-fix-narrowing.md), 23
  [deep objects](23-fix-deep-objects.md), 24
  [FileStream read at the end](24-fix-file-read-at-end.md), 25
  [BufferedStream read past the end](25-fix-buffered-read-past-end.md), 26
  [lone surrogates](26-fix-lone-surrogates.md).
* [27-fix-meta-block-edge.md](27-fix-meta-block-edge.md),
  [28-fix-trans-iterator-loop.md](28-fix-trans-iterator-loop.md),
  [29-fix-memory-stream-assert.md](29-fix-memory-stream-assert.md). 005-27
  to 005-29, faults found in 005-11 outside replication: a crash at a meta
  block's position, the startup's loop on a failed transaction, and
  `MemoryStream.copy`'s assertion. 005-28 is done, with its runs in
  [28-fix-trans-iterator-loop/](28-fix-trans-iterator-loop/); 005-29 is
  done; 005-27 is done, with its runs, gates and probe in
  [27-fix-meta-block-edge/](27-fix-meta-block-edge/).
* [30-fix-read-failure.md](30-fix-read-failure.md). 005-30, a read that
  fails on the storage fails the database (005-01's follow-up); done, with
  its checks and runs in [30-fix-read-failure/](30-fix-read-failure/).
* [31-fix-take-blocked.md](31-fix-take-blocked.md). 005-31, a transaction
  whose dirty index nodes do not fit in one record stops the startup pos
  for good; found in item 007, with the probe in
  [../007-bounds/02-take-blocked/](../007-bounds/02-take-blocked/); done;
  the measurements of the bound in
  [31-fix-take-blocked/](31-fix-take-blocked/).
* [32-fix-failed-start-storage.md](32-fix-failed-start-storage.md). 005-32,
  a start that throws leaves its storage running; found in 005-28; done;
  the probe and its runs, before and after the fix, in
  [32-fix-failed-start-storage/](32-fix-failed-start-storage/).
* [33-crashed-creation.md](33-crashed-creation.md). 005-33, a database
  whose creation crashed: the study, the options and Frans's decision, A;
  done; found in 005-28, with the probe and its runs, before and after the
  change, in [33-crashed-creation/](33-crashed-creation/).
* [34-fix-transaction-info-position.md](34-fix-transaction-info-position.md).
  005-34, `transactionInfo()`'s wrong position after a meta block, found in
  005-30; done; its probe and runs in
  [34-fix-transaction-info-position/](34-fix-transaction-info-position/).
* [35-fix-stop-and-close.md](35-fix-stop-and-close.md). 005-35, `stop()`
  and `close()` do not close the database as their Javadoc says, from
  Frans's note in `Db.close()`; done; its probes, the survey of the calls
  and their runs, before and after the fix, in
  [35-fix-stop-and-close/](35-fix-stop-and-close/).
* [36-fix-test-crash3.md](36-fix-test-crash3.md) and
  [37-fix-memory-stream-checks.md](37-fix-memory-stream-checks.md).
  005-36 and 005-37, found in 005-29: `DbTester.testCrash3`, which tests
  no truncation, and `MemoryStream`, which takes a negative length and a
  cut past its end. Both are done.
* [38-writes-at-scale.md](38-writes-at-scale.md). 005-38, investigate
  writes at scale: the stream's growth per key and loads beyond the
  budget, found in 004-02; done; the report, the tool (WriteBench), the
  node-size runs and every output in
  [38-writes-at-scale/](38-writes-at-scale/).
* [39-fix-trans-completed-before.md](39-fix-trans-completed-before.md).
  005-39, `RecoverableStream.getPosOfTransCompletedBefore`: a wrong
  Javadoc, from the TODO under it, and a cut stream; done; the probe and
  its output, before and after the fix, in
  [39-fix-trans-completed-before/](39-fix-trans-completed-before/).
* [40-fix-refused-start-writes.md](40-fix-refused-start-writes.md).
  005-40, a start writes to the stream before it checks the crypto key
  and the format; found from the TODO on the format version in
  `DbStarter`; done; the probes, their runs before and after the fix, and
  the prototype in
  [40-fix-refused-start-writes/](40-fix-refused-start-writes/).
* [41-is-durable.md](41-is-durable.md). 005-41, `isDurable()`: Frans's
  idea, the options, and two findings on the syncs; decided: not now.
* [42-transaction-info.md](42-transaction-info.md). 005-42, what
  `transactionInfo()` gives; decided A1 and B2, and done; the probe and its
  output, before and after the change, in
  [42-transaction-info/](42-transaction-info/).
* [43-fix-from-todos.md](43-fix-from-todos.md). 005-43, two fixes from the
  TODO markers of 006-05; done.
* [44-fix-sync-commit-byte.md](44-fix-sync-commit-byte.md). 005-44, a sync
  one byte short of the commit byte, found in 005-41; done; the probe and
  its output, before and after the fix, in
  [44-fix-sync-commit-byte/](44-fix-sync-commit-byte/).
* [45-fix-two-leftovers.md](45-fix-two-leftovers.md). 005-45, two faults
  found on the way in 005-40 and 005-41: `SalsaStream.getLength()` and
  `WTransaction.sync(SyncLevel)`; done.
* [46-stream-file-lock.md](46-stream-file-lock.md). 005-46, a read of the
  stream's last file waits for the writer's append and its `fsync`; found
  in 009's measurements; open.
* [47-written-not-forced.md](47-written-not-forced.md). 005-47, a
  durability of "written, not forced": Frans's question, the options and
  the constraints; open.
* [48-group-commit.md](48-group-commit.md). 005-48, group commit: a
  waiting sync starts the flush; the change, the questions; open.
* [49-smooth-index-writes.md](49-smooth-index-writes.md). 005-49, smooth
  index writes: the bursts found in 005-38, the cause, the questions; open.
* [50-fix-node-size-start.md](50-fix-node-size-start.md). 005-50, a start
  with another node size fails with a clear error; found in 005-38; open.
* [54-open-bounds.md](54-open-bounds.md). 005-54, the bounds still open in
  the problem statement (011-01): Q1, Q2, Q3, Q5 and Q8; open.

Log
===

2026-10-19. Created the item, at Frans's request, with subitems 01 to 06.
Defined, not started.

2026-10-19. Added 005-07, synchronization of transactions, at Frans's
request, with the design notes found in F1-007.

2026-10-19. Added 005-08, the node table's tree bins, at Frans's request,
from 006-02's finding and its experimental patch.

2026-10-19. 005-02 done, at Frans's request ("Fix 005-02"), by Claude (Opus
5.5, Claude Code): the top node ordinal is a `long` below 2^48 without a
format change, and a user transaction is refused before it changes anything
near the end. M46 and item 002 closed. Its outcome is in the subitem.

2026-10-19. 005-08 done, at Frans's request ("Fix bergdb 005-08"), by
Claude (Opus 5.5, Claude Code): `Cache3.mapIndex` by Fibonacci hashing, and
a unit test that the node table's bins stay small; MEM 227 to 191 bytes per
KV, `set` 10 to 13 percent faster, the streams unchanged, the four gates and
the quick performance suite passed. The change in `java/` is left for Frans
to commit. Found on the way, for 005-03: a sweep breaks ties of age by the
node table's order, not by depth (005-08, "The table's order").

2026-10-19. Added 005-09, the race that lets the node table name a released
object, at Frans's request, from 005-02's finding (a unit test that fails now
and then).

2026-10-19. Added 005-10, unused code: find it and propose what to remove,
at Frans's request. For an AI to do; nothing is removed without Frans's
approval.

2026-10-19. 005-04 done, at Frans's request ("Do as proposed"), by Claude
(Opus 5.5, Claude Code): A6 is not a target, the assumption stays A6'. Option
4's look found one kind of A6 failure only, the in-place split of a segment
root made by the same transaction, which keeps A6'; 61 Java-tier failures at
node sizes 8 to 62 are all that kind, and 21 new traces with it pass the
checker, with eviction too. No change to `java/` or `lean/`. Proposed, not
done: TREE, A6' and A-COPY as gate checks, and A6' as the checker's
diagnostic.

2026-10-19. 005-10 in progress, at Frans's request ("Do the 005-10 todo
item"), by Claude (Opus 5.5, Claude Code): the proposal is written, in
10-unused-code/proposal.md. About 11,700 lines can go in recommended groups
(A1 to F1); a patch with all of them passes the build, the unit and
f-tests, the four gates and `lake build` on a clone. Found on the way:
tests that never ran, as their classes are in no pack (one fails today),
and night tests that nothing runs (they pass). Nothing is removed; Frans
decides by ID.

2026-10-20. 005-10: Frans decided ("remove all recommended; C1 keep; C2
keep; C3 keep; D1 keep; D2 keep; D3 keep; E1 keep; G1 remove", and a
script for the night tests). Removed by Claude (Opus 5.5, Claude Code): A1
to A3, B1 to B3, F1 and part of G1, 3,071 lines in 103 files; added
`java/stress/night.sh`. The build, the unit and f-tests, the four gates,
`lake build` and `night.sh` pass on a clone; the change is in the main
tree, for Frans to commit. The rest of G1 waits: the proposal's G1 was
wrong for part of it (code behind those API methods is used), see the
subitem.

2026-10-20. 005-04's two proposals done, at Frans's request ("Yes"), by
Claude (Opus 5.5, Claude Code): TREE, A6' and A-COPY are gate checks, in
`A2A3Check2` (`level2.sh`, step 7) and in the checker's C-A, where A6'
replaces the diagnostic A6; the small and evict sets have a configuration
with A6's kind, whose traces must contain it. The four gates pass, also with
005-10's removal (`c6ca623`). See 005-04, "Follow-up".

2026-10-20. Added 005-11, replication, and 005-12, transaction outputs, at
Frans's request, from 005-10's G1 (the Pub API's methods that nothing in
the repository calls).

2026-10-20. The list split into Open and Closed, at Frans's request, by
Claude (Opus 5.5, Claude Code), so that what is done shows at a glance; the
files stay where they are. 005-08's own status said open: its outcome and
its files, written on 2026-10-19 in a clone and never copied here, are now
in the subitem and in
[08-fix-node-table-tree-bins/](08-fix-node-table-tree-bins/).

2026-10-20. 005-10 done, at Frans's request, by Claude (Opus 5.5, Claude
Code): the Pub API's `getFirstAvailableLookupTime` returned the current
time; fixed, with two unit tests. `Connection.put(Object)`, the repeated
`RwEnvironment.exists` and `NoFieldsSetException` removed; replication and
transaction outputs are 005-11 and 005-12. The four gates pass.

2026-10-20. Added 005-13, the buffer time, at Frans's request, by Claude
(Opus 5.5, Claude Code): a sweep of the buffer time on today's source
first, with the proposal of group commit (a waiting sync starts the
flush). Defined, not started.

2026-10-20. 005-13 done, at Frans's request ("Just set the default to 20
ms unless you find a good reason for not to"), by Claude (Opus 5.5, Claude
Code): the sweep of 10 to 200 ms, three rounds; a sync after a commit
waits for the timer (122 ms at 100 ms), and writers that do not sync are
as fast from 10 to 100 ms (about 100,000 puts of 1 KB a second).
`StorageManager.DEFAULT_BUFFER_TIME` is 20: one syncing thread gets 29
commits a second instead of 8, p50 35 ms. Group commit and the Pub API's
buffer time are not done; a storage design for SSD and flash is out of
scope. `before-commit.sh` passes.

2026-10-20. 005-09 done, at Frans's request ("Fix 005-09"), by Claude (Opus
5.5, Claude Code): `Cache3.pointerCreated` reads the canonical flag again
under the node table's lock, and `Cache3.released` clears it under the same
lock, so a reader no longer enters an object that a sweep has just
released. A deterministic test fails without the fix; the flaky test, under
load, failed 1 in 2,000 runs before and 0 in 8,000 after. The stream
unchanged (StreamDigest as R8's), Props and the quick performance suite
unchanged. The change in `java/` is left for Frans to commit.

2026-10-21. Added 005-14, calm when idle, at Frans's request ("I would
like the database to be calm when not used ... have a look at how 20 vs 50
vs 100 ms affects this"), by Claude (Opus 5.5, Claude Code), with the
measurements on F53: an idle database wakes 56, 85 and 163 times a second
at 100, 50 and 20 ms, against the JVM's own 25 (0.3 percent of a core and
0.14 mW at 20 ms). A prototype consumer that sleeps when nothing is
buffered makes it 25, as the JVM alone, at any buffer time. Found on the
way: the wake count overflows after 190 days without a write at 20 ms.
For Frans to decide; no change to `java/`.

2026-10-21. 005-14 done, at Frans's request ("OK, do 005-14 as proposed.
Also fix the overflow problem."), by Claude (Opus 5.5, Claude Code), in
`BufferedStream`: the consumer sleeps when nothing has been buffered for
a buffer time (an idle database wakes 26 times a second, as the JVM
alone, instead of 187); the wake count stops at 4 (it overflowed after
2^31 wakes without a write); and nothing is flushed when nothing is
buffered, also when closing: a close could append the whole buffer, 10 MB
of stale bytes, and the database then failed to start (34 of 24,000
closes in a test before the fix, 0 of 12,000 after). Four unit tests that
fail without the change; `before-commit.sh` passes; no change under load.
The change in `java/` is left for Frans to commit.

2026-10-21. Added 005-15 to 005-26, at Frans's request ("Go through it and
search for overflow issues", then "Write the findings up as 005 entries.
Then fix each one."), by Claude (Opus 5.5, Claude Code): a review of the
Java code for overflow. Six faults checked with probes (wrong index scan
results, an in-memory database that fails after 2^31 bytes, a large
transaction half committed, an unchecked clock, file names in `int`, Jmx
retain days in `int`), smaller overflows, and three faults found on the
way. Frans decided: a value that does not fit its Java field throws, and
cyclic or too deep objects get clear exceptions.

2026-10-21. 005-15 done, by Claude (Opus 5.5, Claude Code): a long index
scan's start key (`UseIndexBuilderImp.plusOne`) kept the `0xff` bytes it
carried past, so a scan after a value whose low byte is `0xff` (255, -1)
skipped or added entries: `startAt(255).inclusive(false)` missed 256 to
510. Now they become 0. Two tests; `before-commit.sh` passes.

2026-10-21. 005-16 done, by Claude (Opus 5.5, Claude Code):
`MemoryStream`'s first position was a product of two `int`s and went
negative after a cut past 2^31 bytes, so an in-memory database with a
retain duration treated a read below the cut as a storage failure and
stopped taking transactions. Now in `long`; an f-test; `before-commit.sh`
passes.

2026-10-21. 005-17 done, by Claude (Opus 5.5, Claude Code): a transaction of
1.79 GB or more was half committed and blocked the writer, since the
record's size was added up in an `int` after the go point. Now a
transaction whose value nodes pass 7/8 of the record limit (2^31 − 9
bytes) is refused before it changes anything, `TransSeq.take` keeps the
index nodes within the limit, and the serializer computes in `long`. Four
tests; streams unchanged (StreamDigest), Props unchanged;
`before-commit.sh` passes.

2026-10-21. 005-18 done, by Claude (Opus 5.5, Claude Code): a clock time of
2^56 or more (a clock in nanoseconds, say) was taken, and the database
then could not start again ("Time too large"). Now `DbClock` refuses it
with a `DbException` before the transaction begins. Two tests; streams
unchanged; `before-commit.sh` passes.

2026-10-21. 005-19 done, by Claude (Opus 5.5, Claude Code): `FileStream`
parsed its file names as `int`s, so a stream past 214.7 TB of positions
could not be opened again. Now `long`; a test; `before-commit.sh` passes.

2026-10-21. 005-20 done, by Claude (Opus 5.5, Claude Code): Jmx's
`setRetainDurationInDays` computed in `int`, so 99,999 days set a retention
of 578.5 days. Now in `long`; a test; `before-commit.sh` passes.

2026-10-21. 005-21 done, by Claude (Opus 5.5, Claude Code): smaller
overflows fixed: `Time.millis` (unchecked product), `TimeResolver`
(seconds cast to `int`, NaN), `TransSeq.take`'s node count limit, negative
key hashes (`Keys.hash` for `Long.MIN_VALUE`, `KeyModSet`'s index,
`Trans.Builder`), a `DbObject` field name over 32,767 UTF-8 bytes, and
corrupt counts that gave `NegativeArraySizeException`. Seven tests;
streams unchanged; `before-commit.sh` passes.

2026-10-21. 005-22 done, by Claude (Opus 5.5, Claude Code), as Frans
decided: reading an object into its class, a stored value that does not fit
its Java field (a long of 3,000,000,000 into an `int`, a NaN into a `long`)
was cast silently; now it is a `DataFormatException` that names the field.
Two tests; `before-commit.sh` passes.

2026-10-21. 005-23 done, by Claude (Opus 5.5, Claude Code), as Frans
decided: a put of an object with a reference cycle, or nested 20,000 deep,
threw `StackOverflowError`. Now `DbObject.toDbObject` refuses a cycle, and
nesting deeper than 1,000 objects, with an `IllegalArgumentException` that
names the field path. Three tests, one changed; `before-commit.sh` passes.

2026-10-21. 005-24 done, by Claude (Opus 5.5, Claude Code): a `FileStream`
read at the end of the stream looped forever, since a bound check compared
`spos` with `spos + fileLength`; one past it threw
`IndexOutOfBoundsException`. Now both throw `EOFException` and the stream
stays usable. A test; `before-commit.sh` passes.

2026-10-21. 005-25 done, by Claude (Opus 5.5, Claude Code):
`BufferedStream.read` let a read end one byte past the end of the stream,
and gave a stale byte of the ring buffer; now it throws. A test;
`before-commit.sh` passes.

2026-10-21. 005-26 done, by Claude (Opus 5.5, Claude Code):
`StringUtil.utf8Size` counted a lone surrogate as 3 or 4 bytes, where the
encoder writes 1, so an object with such a string in an array could not be
stored ("Bad type"). Now it counts as the encoder writes. Tests;
`before-commit.sh` passes. With it, 005-15 to 005-26, the findings of the
review of the Java code for overflow, are done.

2026-10-22. 005-12 changed, at Frans's request, by Claude (Opus 5.5,
Claude Code): the outputs stay ("Deleting the feature is not an option any
more"), a feature of their own, not transaction metadata. Now a decision:
an API that makes them consistent with `put` and `get` is proposed (null
for a missing output, typed by a class, the same checks in both methods,
the rules in the Javadoc; `NoSuchObjectException` goes), then the tests.
No change to `java/`.

2026-10-22. 005-12 done, at Frans's request ("The proposal for 005-12 is
good, implement it."), by Claude (Opus 5.5, Claude Code), as proposed:
`Transaction.getOutput(name, clazz)` is typed and gives null for a missing
output and for a w-transaction; both methods check the name the same way;
`NoSuchObjectException` is removed; an rw-transaction's environment
refuses calls after its action has run (`IllegalStateException`); the
rules are in the Javadoc; `GetStarted4` shows an output. Seven unit tests
in `PubTesterOutput`; `before-commit.sh` passes.

2026-10-22. 005-11 studied, at Frans's request ("Do 005-11. Replication:
study it, for Frans to decide."), by Claude (Opus 5.5, Claude Code), with
probes P1 to P11 on today's code. Replication works without cuts and
failures: replicas are byte copies, one can be added while the database
writes, a crash in its copy is harmless. It fails with reclaim (a crash
leaves the replica unusable while it is behind the cut's decision: 943 of
943 such images broken), after a start without the replica (the main hung
at startup, or the replica held another history), when a replica fails
(`NullPointerException` from later transactions), and with encryption (the
replica in plain text). Proposed: remove it, and leave mirroring to the OS
and backups to copying the files. Found on the way, outside replication: a
crash that ends the stream where a meta block starts leaves a database
that does not start. For Frans to decide; no change to `java/`.

2026-10-22. 005-01 done, at Frans's request ("Do as proposed /
Recommanded. Implement this and commit it. Refuse both reads and writes
after failure. Use the wrapper as recommanded. Task 2, as you
recommend."), by Claude (Opus 5.5, Claude Code): `Db.executeInner` has a
go point, after the checks and before the first change. A `Throwable`
after it fails the database (`DbState.FAILED`), which refuses every later
transaction and read with a `DbFailedException` (the first failure as the
cause; an `Error` is thrown as it is) until it is restarted. The
transaction's time does not become readable when its puts throw, and the
state is checked again under the write lock. No rollback; transformations
stay after the go point and must not throw. M49 and item 003 closed; no
model change. Seven tests in `DbTesterFailure`, and
`DbTesterStream.testReadOnlyStream2` changed; streams unchanged
(StreamDigest); `before-commit.sh` and the four gates pass.

2026-10-23. Added 005-27 to 005-29, at Frans's request ("For now, add 005
entries for the bugs."), by Claude (Opus 5.5, Claude Code): the faults that
005-11's probes found outside replication. 005-11 stays open (Frans: "I
need to think carefully about this one. Replication is linked to
durability and it affects the public API."); its options A, B, C1, C2 and
C3 are now described in the entry itself, with what each means for the
syncs of the API, and Frans's earlier design of durability levels from
F1-007 is summarized there. The probes ran again on `78cc5f3`: since
005-01, a replica that fails, or `addReplica` during cuts, fails the whole
database at the next cut (a `NullPointerException` after the go point),
where before some transactions threw. No change to `java/`.

2026-10-23. Added 005-30, at Frans's request ("Write it up in a new entry.
I like your proposal."), by Claude (Opus 5.5, Claude Code), from 005-01's
follow-up: a read that fails on the storage leaves the database running
half dead, as the storage below refuses all I/O after the first error;
proposed, to fail the database as a transaction does since 005-01,
corrupt data included, but not for reads that a cut has overtaken or that
run while the database stops. No change to `java/`.

2026-10-23. 005-28 done, at Frans's request ("Fix bergdb 005-28."), by
Claude (Opus 5.5, Claude Code), as proposed: `NodeStream.TransIterator`
went back to its start position after a failed transaction there and read
it again, for ever. Now a failed transaction at an exact start position
(startup, `Db.getTrans`) throws a `StreamFormatException` that names it,
and the other iterator steps on to the next transaction. P9's first case
fails at startup with it. Found on the way: it also happened in one
history, after a crash in a new database's first transaction; such a
database now fails to start with that exception. Three tests;
`before-commit.sh` passes. The change in `java/` is left for Frans to
commit.

2026-10-23. Added 005-31, at Frans's request ("Register the bug in 005."),
by Claude (Opus 5.5, Claude Code), from item 007's finding 007-02: a
transaction whose got-dirty index nodes need more bytes than one record
can hold is never taken, so the startup pos stays before it for good.
Proposed: refuse such a transaction before its go point (option A). No
change to `java/`.

2026-10-23. 005-29 done, at Frans's request ("Fix bergdb 005-29."), by
Claude (Opus 5.5, Claude Code): `MemoryStream.assertOk` expected one array
too many for an empty stream and at a length that is a multiple of
1,000,000 bytes, so `copy()` failed its assertion. The one-line fix
proposed was not enough, as `truncate` and an append of 0 bytes made that
extra array; now all three keep exactly the arrays that hold bytes. A
unit test; `before-commit.sh` passes. Found on the way:
`DbTester.testCrash3` has never started on its truncated copies; on them
it meets 005-28's case, as it takes its first length before the new
database is written. The change in `java/` is left for Frans to commit.

2026-10-23. Added 005-32 and 005-33, at Frans's request, by Claude (Opus
5.5, Claude Code), from 005-28's findings. 005-32 ("Yes, make a new 005
entry."): a start that throws leaves its storage running until the
garbage collector finalizes the `Db`; in a probe, a failed start's thread
wrote into a database started after it on the same files, which then lost
a synced transaction 4 times in 20 (assertions off); and
`BufferedStream.close()` hangs when the last flush fails. Proposed: close
the storage when a start throws. 005-33 ("Study the options and propose
something in the entry. Do not implement anything."): a crash in a
database's creation leaves a stream that never starts, with one of three
messages; in 300 kills of a creating process none left one (the creation
is one write), but a power loss can. Options: a clear error (A), create
it again at start (B), create it whole or not at all (C), no change (D);
proposed: A, then B in the Pub API, after 005-32. No change to `java/`.

2026-10-23. 005-27 done, at Frans's request ("bergdb 005-27, fix it."), by
Claude (Opus 5.5, Claude Code), as proposed first: when the stream ends at
a meta block's position, `RecoverableStream.fixMetaBlockIfNeeded` fills
out that meta block too, as one partly written; the block is invalid, and
recovery takes the one before it. Two unit tests that fail without the fix;
`CrashTest` also cuts at and next to meta block positions, and at the end
of each transaction that ends at one (three in `level2.sh`'s full run,
which fail without the fix); P11 again: none of its 13 images fails.
Streams unchanged (StreamDigest); `before-commit.sh` and the four gates
pass, on `e2c0dc0` with the change. The change in `java/` is left for
Frans to commit.

2026-10-23. 005-30 done, at Frans's request ("Fix bergdb 005-30. As
proposed. Commit when done."), by Claude (Opus 5.5, Claude Code), as
proposed: a read that fails on the storage (`getOne`, `getMany`, the
warm-up of a transaction, `getTrans`), or a sync that does, fails the
database as a transaction does since 005-01: the call throws a
`DbFailedException` with the failure as the cause, and every later
transaction and read is refused with it until a restart. A read that a cut
has overtaken still expires, and a read or a sync while the database
stops, or an interrupted sync, throws as before. The state changes under
`readSync`, in `stop()` and `close()` too. In `getTrans` a format error is
thrown as it is, because of 005-34. Ten tests in `DbTesterFailure`, three
changed; streams unchanged (StreamDigest); `before-commit.sh`, `level3.sh`
and `level4.sh` pass; Props unchanged.

2026-10-23. Added 005-34, by Claude (Opus 5.5, Claude Code), found in
005-30 with a probe: a get gives a transaction position 128 bytes too far
for a value after a meta block in its record, so `transactionInfo()` reads
the middle of a record; on the code before 005-30, one such call could
leave the database half dead. Proposed: keep the value node's offset in
stream bytes. No change to `java/` for it.

2026-10-24. 005-31 decided, by Frans ("005-31, it has my 'go'. But don't
start the implementation now."): option A, refuse such a transaction before
its go point. Not started; it is step 1 of item 007's plan (007-03).

2026-10-24. Added 005-35, at Frans's request ("Investigate this further,
then write this down as a fix item in 005."), by Claude (Opus 5.5, Claude
Code), from Frans's note in `Db.close()`: both methods are meant to close
the database properly, stop() without waiting. Probes on `685e895`: stop()
loses what is still buffered (after 2,000 puts and a stop, a restart found
0 of them in two runs of three; close() kept all); close() returns at once
after stop() or beside another close(); a writer that waits for room in
the buffer waits for ever when the stream stops or fails, so a failing
disk hangs the database. Proposed: stop() starts the close in a thread of
its own and close() waits for it; two questions for Frans. No change to
`java/`.

2026-10-24. 005-35, Frans's answers: no `Database.close()` in the Pub API
for now ("Not now."); a transaction that runs when stop() is called
completes and is written ("As you propose."). Not started.

2026-10-24. Added 005-36 and 005-37, at Frans's request ("Add to 005."),
by Claude (Opus 5.5, Claude Code), from 005-29's findings, checked again
on `685e895`: `DbTester.testCrash3` has never tested a truncation, and on
its copies it fails in the database's creation (005-33's case) unless it
syncs first, a two-line fix; `MemoryStream` takes a negative length to
`append` and a `pretruncate` past its length, after some of which it takes
no more appends, where the interface says otherwise. No change to `java/`.

2026-10-24. Added 005-38, at Frans's request ("Register the write problem
as a todo in 005 of type Investigate."), by Claude (Opus 5.5, Claude
Code), from 004-02's results: the stream grows to about 1.1 KB per key at
100M random keys, and loads into an index larger than the budget slow to
under 100 puts a second on s1. To follow incremental eviction (004-03),
before the Lean physical layer is redone.

2026-10-24. 005-36 done, at Frans's request ("fix all todo items of type
Fix", "do what is proposed"), by Claude (Opus 5.5, Claude Code), as
proposed: `DbTester.testCrash3` syncs the new database before it takes its
first length, and starts on each truncated copy, at eleven lengths after
the creation; it passes. Test code only; `before-commit.sh` passes.

2026-10-24. 005-37 done, at Frans's request, by Claude (Opus 5.5, Claude
Code), as proposed: `MemoryStream` refuses a negative length or offset to
`append`, and a `pretruncate` past its length, with an
`IllegalArgumentException`, before it changes anything; the Javadoc of
`AppendOnlyStream.pretruncate` says what the streams do. A unit test;
`before-commit.sh` passes. The other streams' checks are not done, as
decided.

2026-10-24. 005-34 done, at Frans's request, by Claude (Opus 5.5, Claude
Code), as proposed: a value node keeps the distance in the stream from its
transaction's start, so a get gives the transaction's position also for a
value after a meta block in its record; `getTrans` refuses a position that
cannot start a transaction, and a format error there fails the database.
Found on the way and fixed: after a restart, a value that startup had
rerun gave its own position, and `transactionInfo()` threw. Tests;
StreamDigest identical; `before-commit.sh` passes.

2026-10-24. 005-32 done, at Frans's request, by Claude (Opus 5.5, Claude
Code), as proposed: a start that throws closes its storage before the
exception leaves (what it appended is written, the streams closed, the
threads ended) and stops the database; the Pub API closes the `Db`, or the
builder's streams, when it throws after or before the `Db` is built; and
`BufferedStream.close()` returns, and throws the failure, after a failed
flush, where an `Error` in a flush now fails the stream as an
`IOException` does. Tests; the probe's cases again: no thread or file is
left. Its race now ends the same way every time, but not as "Done when"
expected: the failed start writes the replica's copy to the main, which
then holds two histories (005-11). `before-commit.sh` passes.

2026-10-24. 005-35 done, at Frans's request, by Claude (Opus 5.5, Claude
Code), as proposed and with his answers: `stop()` starts one close of the
database, in a thread of its own that is not a daemon, and `close()` waits
for it, also after `stop()` or beside another `close()`. The close takes
the write lock, so a transaction that runs completes and is written, then
writes what is buffered and closes the streams. A writer that waits for
room in the buffer gets an `IOException` when the stream stops or fails.
The probes again: every key after `stop()`, also when the program returns
from `main` after it. Tests; `before-commit.sh` and the four level scripts
pass.

2026-10-24. 005-31 done, at Frans's request ("fix all todo items of type
Fix"), by Claude (Opus 5.5, Claude Code), option A as decided: a
transaction whose index nodes, those it makes dirty or creates, could take
more than 15/16 of the record limit, by a bound at the largest node size,
is refused before its go point. A cheap test from the keys first; a walk of
the paths of a large transaction's keys under the write lock
(`Dag.dirtyNodeBound`). The bound is 1.0 to 2.6 times the actual nodes on
007-02's database at the four node sizes. A test; StreamDigest identical;
`before-commit.sh` passes. Step 1 of 007-03.

2026-10-24. The final checks of the six fixes of the day (005-31, 005-32,
005-34 to 005-37), on `43d85f9`: the four level scripts pass, and Props in
ABBA order against `7f08273`, the commit before them, shows no difference
(MEM 191, SS 1.50, CORE 0.27 to 0.29). See 005-31's outcome. With them, no
entry of kind Fix is open.

2026-10-25. Added 005-39 and done, at Frans's request ("Investigate
RecoverableStream.java:516. The TODO there.", then "Yes" to a Fix
entry), by Claude (Opus 5.5, Claude Code). The TODO was right: the
Javadoc promised the last transaction completed before the position,
which the method never searched for; and in a stream whose front
reclaim had cut, it threw `NullPointerException` or gave a transaction
before the cut, so `NodeStream.createTransIterator` and `print()` failed
on such a database. Startup does not use it; it reads from an exact
position. Now the Javadoc says what the method gives, and in a cut
stream it gives the first transaction after the cut that a meta block
names. Tests; `before-commit.sh` passes.

2026-10-25. Added 005-40, at Frans's request ("Investigate this and
propose what to do. If you find it appropriate, add an item to 005."), by
Claude (Opus 5.5, Claude Code), from another session's remark that the
stream format version is not checked at start (`DbStarter.java:590`). It
is: since 2015-07-24 the parsers check the format byte of each record and
node they read, and recovery the meta blocks' version; the TODO there is
from 2014. Probes on `425d7a7` found instead that recovery writes before
it checks: after a crash that ends the stream at or just inside a meta
block, a start with a wrong crypto key, or with none, appends the rest of
the block, and then the right key fails at every start (at 0, 3 and 5
bytes into the block; at 6, for 5 of 2,560 wrong keys). And a record of
another format is refused as corrupt data, with the message for format 2.
Proposed: read the meta blocks before that fill (a prototype passes
`before-commit.sh` and `CrashTest`), `VersioningStreamException` for the
versions of records and nodes, a rule for the next format change, and
the stale TODO and constant gone. No change to `java/`.

2026-10-25. 005-40 done, at Frans's request ("fix 005-40"), by Claude
(Opus 5.5, Claude Code), as proposed: `RecoverableStream.recover()` reads
the meta blocks before it fills out one that a crash has cut, so a start
with a wrong crypto key, with none, or on a stream of another meta block
version writes nothing, and the right key then starts the database. The
versions of records and nodes are refused with a
`VersioningStreamException`, now a `StreamFormatException`, whose message
says whether an older or a newer BergDB wrote the stream. The rule for the
next format change is in the Javadoc of `MetaBlock` and
`StoredTrans.RECORD_FORMAT`, with one change: a node's new layout changes
`RECORD_FORMAT` too. The TODO in `DbStarter` and
`StoredTrans.CURRENT_FORMAT_VERSION` are gone. Tests; `before-commit.sh`
and `level2.sh` pass, StreamDigest identical, the probes again. Found on
the way, not fixed: `SalsaStream.getLength()` does not count what it
appends, which BergDB's own stack does not meet.

2026-10-25. Added 005-41 to 005-43, at Frans's request ("as proposed"), by
Claude (Opus 5.5, Claude Code), from the review of the TODO markers in
`java/` (006-05). 005-41: Frans's idea of `isDurable()`, from two comments
in the Pub API, which are gone. 005-42: `transactionInfo()`, from a TODO
of 2016 and a probe: a transaction that writes an index entry gives a KV
whose `key()` throws, and a value that reclaim has rewritten gives
reclaim's step, at 14,078 s for a put at 1 s. 005-43: two small fixes.
005-11's option B names the unit tests of `addReplica`, from a TODO of
2014 in `DbHelper`, which is gone. Found on the way, in 005-41: a sync
waits for every byte of a transaction but its last, the commit byte; it
is right because the buffer sizes in use are multiples of 4, and a core
API caller can choose another.

2026-10-25. 005-43 done, by Claude (Opus 5.5, Claude Code), as proposed:
`Db.getTrans` refuses a position at or past the end of the stream with an
`IllegalArgumentException`, where it threw a `DbException`, and
`PubKeys.udir2idir`, which the Pub API's `IndexBuilder.dir` and
`UsePrimaryBuilder.dir` use, refuses a bad directory with one, where it
threw a `BadFormatException`. Two tests, which fail without the change;
`before-commit.sh` passes.

2026-10-25. 005-41 decided, by Frans ("my decision: C, not now."): no
`isDurable()` for now. Its first finding, the sync one byte short, added
as 005-44, at his request ("Yes, register as an 005 item, fix it, then
commit the fix."), by Claude (Opus 5.5, Claude Code).

2026-10-25. 005-44 done, by Claude (Opus 5.5, Claude Code): a sync waited
until the durable length reached the transaction's last byte, the commit
byte, so it returned while that byte could still be in the write buffer;
with a buffer whose size is not a multiple of 4, which the core API
allows, a crash right after the sync lost the transaction, in 10 runs of
10 of a probe. Now `Db.sync` waits for the position after that byte, and
`Db` keeps the end of the last transaction instead of its last byte. An
f-test that fails without the fix; `before-commit.sh` passes.

2026-10-25. 005-33 decided, by Frans ("bergdb 005-33. Decision: A. Note
the decision in the readme. Implement it. Then commit if successful."):
option A, one clear error. Done, by Claude (Opus 5.5, Claude Code): a start
refuses a stream that holds a creation which did not complete, and no
committed transaction, with a `DatabaseNotCreatedException` (in
`bergdb.pub.util`, for the application to catch) that says what happened
and what to do; it does so before recovery, so it writes nothing. Before,
it threw one of three `StreamFormatException`s, after recovery had
zero-filled a cut first transaction. Without a crypto key, a stream whose
magic bytes are wrong is no longer called a wrong key. Tests;
`before-commit.sh` and `level2.sh quick` pass. Found on the way, for
005-11: with a replica, a stream that ends inside its first meta block
fails the start earlier, in the check of the streams' IDs.

2026-10-25. Before release 2026.1 (item 008), at Frans's request ("Are
there any known bugs in BergDB? If so, we should fix them before the
release."), by Claude (Opus 5.5, Claude Code): the known faults that were
left are those of the open entries 005-11, 005-33 (done meanwhile, in
another session) and 005-42, and two found on the way and not fixed, in
005-40 and 005-41. Frans's answers: 005-11, "Keep it, document as
experimental"; 005-42, "A1 + B2 as proposed"; 007-03's steps 2 to 5,
"After the release".

2026-10-25. 005-42 done, by Claude (Opus 5.5, Claude Code), A1 and B2 as
decided: `transactionInfo()` leaves out the KVs under the internal prefix,
so every `key()` works, and throws `LookupTimeNotAvailableException` for a
value that reclaim has rewritten, where it gave reclaim's step. Added
005-45, the two faults found on the way, and done: `SalsaStream.getLength()`
counts what it appends, and `WTransaction.sync(SyncLevel)` waits for its own
transaction. 005-11: the Javadoc of the Pub API's replica methods,
README.md and docs/levels.md say that replication is experimental, with
its faults. Tests that fail without the changes; `before-commit.sh`
passes.

2026-10-26. Added 005-46, found in item 009's measurements (009-03) by
Claude (Opus 5.5, Claude Code), during Frans's unattended run of 009: a
read of the stream's last file waits for the writer's append and its
`fsync`. And 005-38 got 009's answer to its question 4 for the 10M load on
s1 (009-03, section 7): 2026.1's eviction made most of its time.

2026-10-26. Added 005-47, at Frans's request, by Claude (Opus 5.5, Claude
Code): a durability of "written, not forced", Frans's question of the day
("Would the middle-ground be good to support too? That is, ensuring the
write left the process."). Three options, A recommended: a property of
the storage, `FileStream` without a force per append. Found on the way,
from the code: records have no checksum, so recovery cannot tell a hole in
an unforced tail from data; `FileStreamPowerLossTester` models a lost tail
and a prefix of it, not a hole. That holds today too, for one chunk
between its write and its force.

2026-10-26. Added 005-48, at Frans's request ("Yes, group commit as
005-48."), by Claude (Opus 5.5, Claude Code): group commit, proposed in
005-13 and not done there. A sync that waits asks `BufferedStream` for a
flush instead of waiting for its timer; the force paces the groups.

2026-10-26. 005-38 done, by Claude (Opus 5.5, Claude Code), with Frans:
the stream's growth per key at scale was 004-02's startup distance of 10
MB; at 200 to 1000 MB a put costs 180 to 670 bytes of stream at 10M and
50M keys (random updates, in memory). Node size 30 stays. Found: the index
is written in bursts at large startup distances, and a database starts
only with the node size it was written with.

2026-10-26. Added 005-49 and 005-50, at Frans's request ("Yes, register
the burst entry. Yes to node-size fix entry."), by Claude (Opus 5.5, Claude
Code), both found in 005-38: smooth index writes (the bursts at large
startup distances; 007-03's step 3 waits for it), and a start with another
node size, which should fail with a clear error, only that.

2026-10-26. Added 005-54, by Claude (Opus 5.5, Claude Code), in the docs/
cleanup (006-07), as Frans approved ("Everything as recommended"): the
open questions of the problem statement, now 011-01, that had no other
home (Q1, Q2, Q3, Q5, Q8).
