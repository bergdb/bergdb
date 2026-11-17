005-34. Fix: transactionInfo() reads at a wrong position after a meta block
===========================================================================

Status: done (2026-10-24). Kind: fix. Created 2026-10-23.

Found on 2026-10-23 in 005-30, by Claude (Opus 5.5, Claude Code), when the
read of `Db.getTrans` (the Pub API's `Connection.transactionInfo()`) was
made to fail the database on a failure of the storage. The probe and its
runs: [34-fix-transaction-info-position/](34-fix-transaction-info-position/).


The issue
---------

`ValueNode.getTpos()` gives `spos - offsetFromTrans`: the value node's
stream position minus its offset in the record, as `StoredValueNode.toBytes`
writes it, an offset in the record's buffer. The two differ when the record
crosses a meta block (one every 200,000 bytes,
`RecoverableStream.META_BLOCK_DISTANCE`): the meta block's 128 bytes are in
the stream but not in the buffer. So for a value node after a meta block in
its record, the position is 128 bytes too far, per meta block in between.
`toBytes` says so: "Also, offset from start of transaction. Assumed to be
the same (easy to change if/when needed)."

`Dag.getOne` gives the position to `GetData.tpos`, and
`Connection.transactionInfo()` asks `Db.getTrans` for the transaction there:
it reads the middle of the record as a transaction.

The probe ([TposProbe.java](34-fix-transaction-info-position/TposProbe.java),
[probe.sh](34-fix-transaction-info-position/probe.sh)) writes transactions
of 20 values of 500 bytes until three records have crossed a meta block.
In each, the values after the meta block, 10 to 14 of the 20, get a
position 128 bytes too far. On the code before 005-30
([probe-before.txt](34-fix-transaction-info-position/probe-before.txt)):

* With zero bytes in the values, `getTrans` throws a
  `StreamFormatException` ("Bad transaction size, 0").
* With random bytes, it read a size of 199,872 bytes and then that many
  bytes, past the end of the stream: `BufferedStream` throws,
  `StorageManager` closes the main stream, and every later read that needs
  the stream fails ("Main storage not active"); the next transaction failed
  the database after its go point (005-01). One call of
  `transactionInfo()` left the database half dead. A larger size would
  allocate up to 2 GB for the read.

Since 005-30 ([probe-after.txt](34-fix-transaction-info-position/probe-after.txt))
the read past the end fails the database at once, as the storage has
failed; a format error in `getTrans` is thrown as it is and the database
goes on, because of this fault (005-30, Outcome).

How often: a record crosses a meta block with a probability of about its
size over 200,000 bytes, and about half of its values come after the meta
block. For records of 10 KB, about one value in 40; of 1 KB, one in 400.

Not hit: reclaim, which compares `GetData.tpos` with a cut position
(`Reclaim.step`, `gd.tpos < it.pCut`). The position is too far by less than
the rest of its record, and a cut position is a boundary between records,
so the comparison gives the same answer.

Also, rarer: a reader that reads a value of the transaction that the writer
is storing, after `dbClock.transactionEnd()`, gets a vpos (an odd number;
the node is not written yet), or, between the serializer's setting of the
node's spos and of its offset, the node's own position. A
`transactionInfo()` after the append then reads there too.


The fix, proposed
-----------------

Make the value node's in-memory offset the distance in the stream, `spos -
tpos`; the stream does not change:

* `RecoverableStream.getStartSpos(spos, size)`, the inverse of `getSpos`:
  the start of a transaction whose byte at offset `size` is at `spos`.
* `StoredValueNode.parse` converts the stored offset with it.
* The serializer (`StoredTrans.Serializer.prepareToSerialize`) sets the
  offset as it sets the node's spos, and before it, so that a reader that
  sees the new spos (a volatile field) sees its offset.
* `ValueNode.getTpos()` gives `Spos.NULL` for a vpos, and `Db.getTrans`
  refuses a position that cannot start a transaction (negative, or not a
  multiple of `TRANS_ALIGNMENT`) before it reads.

Then a format error in `getTrans` can fail the database, as 005-30 does for
the other reads.


Done when
---------

* A unit test with records that cross a meta block, with random values:
  `getTrans` of every value's position, from a get, gives its transaction,
  in memory and after a restart (the values then read from the stream).
* StreamDigest identical; `java/before-commit.sh` prints `BEFORE COMMIT OK`.


Size and order
--------------

S, any time.


Outcome
-------

2026-10-24, by Claude (Opus 5.5, Claude Code), as proposed, at Frans's
request ("fix all todo items of type Fix", "do what is proposed"), with a
second fault of the same position, found on the way, fixed too:

* `RecoverableStream.getStartSpos(spos, size)`, the inverse of `getSpos`:
  the start of a transaction whose byte at offset `size`, in the record's
  bytes, is at `spos`. It refuses an `spos` in a meta block, and a start
  before the stream's first transaction byte.
* The value node's offset in memory, `ValueNode.offsetFromTrans`, is the
  distance in the stream, spos - tpos. The stream does not change: its
  field is still the offset in the record's bytes. `StoredValueNode.parse`
  converts the stored offset with `getStartSpos` (one that cannot be is a
  `StreamFormatException`); the serializer
  (`StoredTrans.Serializer.prepareToSerialize`) sets it as it sets the
  node's spos, and before it; `toBytes` no longer sets it. The int is read
  as unsigned: a record of up to 2^31 - 9 bytes spans, with its meta
  blocks, up to about 1.4 MB more than 2^31 - 1 bytes in the stream, which
  a signed int would have wrapped. No field is added, so no memory.
* `ValueNode.getTpos()` reads the spos once, and gives `Spos.NULL` for a
  vpos, a value whose transaction is still being stored, as for
  `Spos.NULL`.
* Found on the way, and fixed: after a restart, a value that startup had
  rerun, which is every value of the startup section (the last 50 MB by
  default), had its own position as its transaction's.
  `DbStarter.rerunTransaction` set the new node's spos from the stored node
  but not its offset, which stayed 0. A get then gave the value node's
  position, and `transactionInfo()` threw: "Transaction at start pos 336 is
  not committed (its last byte is 0).", in a probe on `b2fa8b8` with two
  values in one transaction. Now the rerun copies the offset too. With the
  next point and without this fix, `transactionInfo()` after a restart
  would have failed the database.
* `Db.getTrans` refuses a position that cannot start a transaction
  (negative, as `Spos.NULL`; not a multiple of 8; in a meta block) with an
  `IllegalArgumentException`, before it reads; and a format error there
  now fails the database, as 005-30 made the other reads do for corrupt
  data. `Connection.transactionInfo()` throws an `IllegalStateException`,
  which says to get the value again, when its get read a value whose
  transaction was still being stored. `Reclaim.step` takes a value without
  a position as one after the cut, as it took its vpos before; its reads
  run after the transaction's `store()`, so it does not meet one.

Tests:

* `DbTester.testGetTransOfEveryValue`: transactions of 20 random values of
  500 bytes until three records have crossed a meta block. Every value's
  tpos from a get is its transaction's, and `getTrans` of it gives that
  transaction, in memory and after a restart: with the default startup
  distance, where the restart reruns them all, and with a startup distance
  of 20,000 bytes, where most values are then read from the stream. It
  fails without each of the three parts: the rerun's offset (value 0/0,
  296 for 264), the conversion in `parse` and the serializer's offset
  (value 18/2, 196952 for 196824).
* `DbTester.testGetTransRefusesBadPositions`: -1, `Long.MIN_VALUE`, a
  position 1 and 4 bytes into a transaction, 0, 64, and 200,000 and
  200,120 (in a meta block) are refused, and the database goes on.
* `DbTesterFailure.testGetTrans`: a corrupt read in `getTrans` now fails
  the database, as a read error does.
* `PubTester.testTransactionInfoAfterRestart`: `transactionInfo()` after a
  restart. Without the rerun's fix it fails the database.
* `StoredValueNode.testOffsetFromTransAcrossMetaBlock` (the offset across
  a meta block, an offset past 2^31, a vpos, a bad offset) and
  `RecoverableStream.testGetStartSpos` (100,000 random starts and sizes,
  and the refusals); the other `StoredValueNode` tests parse at valid
  positions now.

The probe again ([probe-fixed.txt](34-fix-transaction-info-position/probe-fixed.txt)):
0 of 20 values with a wrong tpos in each of the three records that cross a
meta block, with zeros and with random values.

`StoredTrans.testSerializeAndCheckKey2` serialized a transaction at
position 0, in the first meta block, where none starts; `parse` now refuses
its value node there, so the test uses position 128.

Streams unchanged: StreamDigest `all`, the build of `b2fa8b8` against the
one with the change, DIGESTS IDENTICAL (36 of 36)
([digest-compare.txt](34-fix-transaction-info-position/digest-compare.txt)).

`before-commit.sh`: BEFORE COMMIT OK (996 unit tests, 63 f-tests).
