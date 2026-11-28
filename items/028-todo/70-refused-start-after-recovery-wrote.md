028-70. Investigate: a start refused after its recovery has written changes the stream
======================================================================================

Status: done (2026-11-28): every refusal of a start comes before the
recovery's first write (below). Kind: Investigate. Frans: none.
Created 2026-11-27 by Frans Lundberg.

What: a start can be refused after its recovery has already written to
the stream. The case found: the stream's last committed record has a
format version that this release does not read. The recovery runs
first and may append (it completes the stream's tail), and since
028-60's part 2 (`ac33aa93`) the first append also cuts a tail of zeros;
then the start is refused for the version. `main` before 028-60's part 2
behaved the same way for the recovery's own appends.

Why: a refused start should leave the storage as it found it, as the
other refusals do (015-05; `testRefusedStartsKeepZeroTail` for the
refusals before the recovery). The message of this refusal does not say
that nothing was written, and 027-11 says that the recovery may append
first, so no document is wrong; it is the behaviour that is uneven.
Found by Codex's third review of 028-60's part 2 (2026-11-27), not
fixed there: the fix changes the order of the start.

Frans: none.

Done when: every refusal of a start that can be decided from what is
read comes before the recovery's first write, with a test for the
unreadable format version (the files unchanged after the refused
start); or the cases that cannot be moved are listed in 027-11 with the
reason.

First step: list the checks of `DbStarter` and `Db.startInner` that
come after the recovery's first append, and for each what it reads.


The checks after the recovery's first write
-------------------------------------------

The entry's first step, read from `main` at `ee8a8165` (2026-11-28),
after 028-67 (C1, C3, T1), 028-66 (option C) and 028-76. The recovery
writes in `RecoverableStream.recover()`, after its walk (`walkTail`):
the rest of a meta block that the end of the stream cuts
(`fixMetaBlockIfNeeded`), then the completion of a torn last record
(`fixLastTransactionIfNeeded`). It writes only when the stream ends at
or in a meta block's place, or inside a record.

Before the first write on `main`, and so done before this entry, by
005-33, 005-40, 005-50, 019-34, 028-66, 028-67 and 028-76: an incomplete
creation (`refuseIncompleteCreation`); the node size
(`refuseOtherNodeSize`); the magic and the version of the blocks read,
and the last valid block (`readFirstMetaBlock`,
`readLastValidMetaBlock`); its lastTrans (`checkLastTransSpos`); the
files before a gap (`checkLeftovers`); and the walk: each record's size
and last byte, each header's check, the first walked record's format,
and the parse of the last committed record when it ends the stream.
Their tests: `testRefusedStartsKeepZeroTail`,
`testRecoverUnreadableWritesNothing`,
`testRecoverOtherVersionWritesNothing`, `DbTesterTail`,
`testStartRefusesFormat8` and `FileStreamPowerLossTester`.

After the first write on `main`, each a refusal of what the start reads,
none of it the bytes that the recovery writes, which every later read
takes as the end of an aborted record:

1. `Db.readStartupPos`, `MetaBlock.checkFormat`: the last valid meta
   block's time negative (SFE). Reads that block, which the recovery
   read before it wrote.
2. `Db.getStartupPosFromLastTransaction`, from the record that the
   block names to the end: each header (`NodeStream.readRecordHeader`:
   the size, the record limit, the stream's end, the last byte, the
   first record committed, the format byte of a committed record, a
   `VersioningStreamException`); each committed record's parse
   (`StoredTrans.parse`: the header's check, the nodes and their
   checksums); `checkStartupPos`. Reads the records that the walk read,
   which took all but the last committed one by their headers only. The
   found case is here: a committed record of another format whose header
   holds its check, not the first that the walk reads, followed by a
   torn record; without the torn record the walk refused it, as a tail
   to cut (`BadTailException`), the last record of the stream parsed.
3. `Db.readTransactions`, from s: the same checks for R(s) to R(k), and
   the record at s committed (005-28). Reads the section, most of it
   before the record that the block names, which the recovery does not
   read.
4. `DbStarter.start`: the section's validation (005-75); the cut back's
   stream pointers; the memory pointers' types (019-32); the super root
   (015-75; a read at topPos); the rerun's order of the puts and D's ids
   (015-75); rule 4's types (021-11); `postStartupCheck` (an
   `AssertionError`); a read below the first position
   (`Db.refusalOfMissingBytes`). Reads the section and the nodes that
   its pointers name, before the section too.
5. `Db.readStartupDistanceKv`: the KV's bytes
   (`InternalDataException`), or no KV (SFE). Reads the key tree.
6. `Reclaim.initFromDb`: the settings, the table and the current row
   (`InternalDataException`); a first position after the cut
   (`StreamAfterCutException`). Reads reclaim's KVs and the storage's
   first position; then it makes a pending cut.

What comes after 6 is not refused by what the start reads:
`created.txt` (a file of its own), eviction, the audit of BergDB's tests
(`DbBuilder.audit`, a check of the start's memory), and the creating
start's second record, on a stream that has nothing to complete. So
every refusal can be decided from what is read before the recovery
writes, and none had to stay after it.


The change
----------

On the branch `028-70-refuse-first` (2026-11-28):

* `RecoverableStream.recover(check, true)`, which `NodeStream.recover()`
  calls, holds the recovery's writes in memory: the storage is as it
  was, and the stream's length and reads are those of the stream with
  the writes made, so that the start reads what it read before. A run of
  zeros is held as its length; the meta blocks that the completion
  writes inside a record, 128 bytes each 200,000, as bytes. `Db.startInner`
  writes them (`NodeStream.writeRecovery()`) after check 6, before
  `created.txt`; the next append would write them first too. The bytes
  written are those that the recovery wrote before, in the same order.
* The walk refuses every committed record of another format whose
  header holds its check, as it refused the first: a
  `VersioningStreamException` before anything is written, also for the
  last record of the stream, which it refused before as a tail to cut
  at its start.
* `CorruptStreamTester`: a refused start that has written is a failure,
  no longer 014-01's known case (it keeps the fill that passes
  `MAX_APPENDED`).
* `DbTesterFailure.testFailedStartClosesStorage` (005-32) asserted that
  its refused start had written the fill; it asserts that nothing is
  written.
* 027-11 (sections 1, 1.2, 1.3, 1.9, 3, 6, 7 and 8) and 027-03 (G18, Q15
  and the gap table) say the order.

Tests, each failing on `main` and passing on the branch:
`DbTesterTail.testRefusalsAfterTheWalkWriteNothing` (MemoryStream: the
last committed record of format 10, a startupPos after its record, a
time not after the record before, the meta block's time negative, each
with a torn record after it: refused, the stream byte for byte as
before; restored, it starts and the completion is written) and
`DbTesterTail.testOtherFormatRefusedFilesUnchanged` (a file database:
format 10, the files byte for byte unchanged). And
`RecoverableStream.Tester.testRecoveryHeld`: the storage unchanged while
held, the reads and the length those of the stream with the writes, and
the bytes that `writeRecovery()`, or an append, writes those that
`recover()` writes, in three layouts.


Gates, on F53 beside `week.sh`, on the branch rebased on `main` at
`ee6c176e` (2026-11-28):

* `java/before-commit.sh`: BEFORE COMMIT OK (142 s; unit 1,760 tests, f
  96).
* `java/stress/level2.sh`: LEVEL 2 OK (conformance: 70 traces,
  TRACECHECK OK). `java/stress/level3.sh`: LEVEL 3 OK.
* 031-06's probes: `sweep.sh`, 0 different in each of its 63 lines (the
  torn records among them continued the same); `faults.sh`, bad 0 in
  each of its 42 lines.
* `PowerLossTest 1001 12 3000 3`: POWERLOSS OK, 12 seeds, 732 cold
  recoveries, without per-append forces 744; negative controls caught.
* The night tests of `DbTesterTail` (every cut of a completion, byte for
  byte) and `CorruptStreamTester` (the full set on the day's seed, a
  refusal after a write a failure): SUCCESS, 5 tests.


Log
---

2026-11-27. Registered by lead-1127.

2026-11-28. The list and the change, by an agent of lead-1127 on the
branch `028-70-refuse-first`, from `main` at `ee8a8165`. Done.
