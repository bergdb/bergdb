005-44. Fix: a sync could return before the commit byte was written
====================================================================

Status: done (2026-10-25). Kind: fix. Created 2026-10-25.

Found on 2026-10-25 by Claude (Opus 5.5, Claude Code), in 005-41, from the
code; added and fixed at Frans's request ("Yes, register as an 005 item,
fix it, then commit the fix."). The probe and its output, before and after
the fix, are in [44-fix-sync-commit-byte/](44-fix-sync-commit-byte/).


The issue
---------

A transaction is durable when its record's last byte, the commit byte
(`RecoverableStream.LAST_BYTE`), is; recovery drops a record without it.
`Trans.lastPos` is the position of that byte. A sync of a transaction
(`Transaction.sync()` and `Connection.sync()` in the Pub API, `Db.sync(pos,
level)` in the core API) passed that position to `StorageManager.sync`,
which waits while the durable length, the bytes from the start that are
durable, is below it. So it returned when every byte but the commit byte
was durable. A sync of the last transaction (`Database.sync()`,
`Db.sync(0, level)`) did the same: `Db` kept the position of the last
transaction's last byte.

It was right only while a durable length never ended just before a commit
byte. Records and meta blocks are multiples of 8 bytes, so a commit byte is
at 7 modulo 8, and a `BufferedStream` writes in parts that end at even
positions when its size is a multiple of 4: it writes at most half its
buffer at a time, and takes an append that does not fit in parts of the
room left. The Pub API's sizes are (10 MB for the main stream, 20 MB for a
replica), but the core API takes any size from 100 bytes
(`DbBuilder.stream`, `Db.addReplica`). With another size, a part can end
just before a commit byte.

The probe ([probe-before.txt](44-fix-sync-commit-byte/probe-before.txt)):
three puts of `/k` on a main stream with a buffer of 2 S − 2 bytes (366), S
the size of the third put's record (184 bytes), so that the buffer writes
S − 1 bytes of that record at once and its commit byte a buffer time (200
ms) later. After the third put, `sync(lastPos)`, and at once a crash image:
the stream cut at the durable length. In 10 runs of 10, the sync returned
with the durable length 847, the commit byte's position, and a database
started on the image gave the second put's value: the transaction that the
sync had reported durable was lost.


The fix
-------

* `Db.sync(pos, level)` waits until the durable length is at least
  pos + 1: every byte up to and including `pos` is durable. Its Javadoc
  says what `pos` is: the last byte to make durable, a transaction's
  `lastPos`, or 0 for the last transaction.
* `Db` keeps the end of the last transaction, its last byte + 1
  (`ExecuteData.endOfLastTrans`, which was `lastSposOfLastTrans`); at the
  start, the stream's length, as before.
* `StorageManager.sync(length)` and `syncStrong(length)` are unchanged but
  for the name of the parameter; their Javadoc says that they wait for a
  length. `syncStrong`'s message named D1; now D2.

The callers pass a transaction's `lastPos` or 0, as before: the Pub API's
`WTransaction`, `RwTransaction`, `ConnectionImp` and `DatabaseImp`, and
`DbHelper`'s `addReplica`. A sync now waits for the commit byte too, which
is at most one more write of the buffer, and only in the case above.


Done when
---------

* A test that fails without the fix.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.


Outcome
-------

2026-10-25, by Claude (Opus 5.5, Claude Code), as above:

* `DbTester.testSyncWaitsForTheCommitByte`, an f-test, has the probe's
  setup: the sync of the third put must leave the durable length past its
  `lastPos`. Without the fix it fails: "the commit byte is durable: 847 >
  847".
* The probe again ([probe-after.txt](44-fix-sync-commit-byte/probe-after.txt)):
  10 runs of 10 keep the transaction; the sync returns with the durable
  length 848.
* `before-commit.sh` passes, 1,018 unit tests and 68 f-tests.

Found in 005-41, not fixed: `WTransaction.sync(SyncLevel)` waits for the
database's last transaction, not for its own as its `sync()` does; longer
than it needs to, never too short.


The probe
---------

In [44-fix-sync-commit-byte/](44-fix-sync-commit-byte/):
`SyncCommitByteProbe.java`; `probe.sh JAR WORK_DIR [runs]` compiles it
against a build and runs it; its output on `cdb7861`, before and after the
fix, in `probe-before.txt` and `probe-after.txt`.
