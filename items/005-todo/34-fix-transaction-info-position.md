005-34. Fix: transactionInfo() reads at a wrong position after a meta block
===========================================================================

Status: open. Kind: fix. Created 2026-10-23.

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
