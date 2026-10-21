005-17. Fix: a transaction of 1.79 GB or more is half committed and blocks the writer
====================================================================================

Status: done (2026-10-21). Kind: fix. Created 2026-10-21.

Found on 2026-10-21 in a review of the Java code for overflow, by Claude
(Opus 5.5, Claude Code), at Frans's request; checked with a probe.


The issue
---------

Nothing limits the size of a transaction. `StoredTrans.Serializer` adds the
node sizes in an `int` (`totalSize`), `StoredValueNode.getByteSize` is an
`int`, and the buffer grows to `(int) (totalSize * 1.20)`. All of it runs in
`Db.store()`, after the puts are in memory and the transaction time is
readable: after the go point.

* Two values of 1.1 GB in one transaction: the sum wraps, and `store()`
  throws `ArrayIndexOutOfBoundsException`. A get returns the 1.1 GB value;
  the stream is unchanged. The next transaction, 4 bytes, throws the same,
  and so does every later one until a restart (`x.transNodes` still holds
  the nodes).
* Two values of 0.925 GB (1.85 GB, which the record format allows):
  `(int) (totalSize * 1.20)` is `Integer.MAX_VALUE`, and `store()` throws
  "OutOfMemoryError: Requested array size exceeds VM limit", with an 8 GB
  heap; the same blocked writer.

It is a trigger of M49 (005-01), but one that can be tested before the go
point, as Frans's note in 005-01 asks. The record's size field is 4 bytes
(`RecoverableStream`), so a record is at most 2^31 − 1 bytes.


The fix
-------

* A record is at most `Integer.MAX_VALUE - 8` bytes, the largest array
  (the record limit).
* Before the go point, `Db.executeInner` adds up the value nodes of the
  transaction in `long` and refuses a transaction whose value nodes need more
  than 7/8 of the record limit, with a `DbException`, before it changes
  anything. The last eighth, 256 MB, is for the index nodes and the
  got-dirty list.
* `TransSeq.take` gets a byte budget, so that the index nodes it adds to
  the record cannot pass the limit; it takes fewer only for records near
  it, so streams do not change.
* The serializer computes its sizes in `long`, grows its buffer at most to
  the record limit, and throws a clear `DbException` if a record would still
  pass it (an extreme case: more than 16 million index nodes made dirty).


Done when
---------

* A unit test: a transaction above the limit is refused, nothing changed,
  and the next transaction runs. The limit is a constant the test can lower
  so that it needs no 2 GB of heap.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`; the streams are
  unchanged (`StreamDigest` against `3a82968`).


Outcome
-------

2026-10-21, by Claude (Opus 5.5, Claude Code), as the fix above says:

* `StoredTrans.MAX_RECORD_SIZE` (`Integer.MAX_VALUE - 8`) and
  `StoredTrans.recordLimit`, which tests lower.
* `Db.checkSize`, before the warm-up and the write lock: the value nodes of
  the transaction (`StoredValueNode.getByteSizeLong`) may take at most 7/8
  of the limit; above it, a `DbException` ("The transaction is too large")
  and nothing has changed. Value transformations run later and are not
  counted; only reclaim's internal transactions use them, with small values.
* `TransSeq.take` has a byte budget (`Db.store` passes the limit minus the
  rest of the record); a taken node counts its size and 16 bytes.
* `Serializer.prepareToSerialize` adds up in `long`, refuses a record above
  the limit with a `DbException`, and grows its buffer at most to
  `MAX_RECORD_SIZE`. `RecoverableStream.getSpos` takes a `long` size.

Tests: `DbTester.testTransactionTooLarge` (refused, nothing changed, the
next transaction runs), `DbTester.testRecordsWithinLimit` (f-test: 300
records near a limit of 200,000 bytes, and a restart gives the same
checksum; without the budget a record took 201,176 bytes and was
refused), `StoredTrans.testRecordAboveLimit`, `TransSeq.testTakeWithBudget`.

Checks: the streams are unchanged, StreamDigest `all` against the build
before the change: `DIGESTS IDENTICAL (36 of 36)`
([digest-compare.txt](17-fix-transaction-size/digest-compare.txt)). Props
in ABBA order, 4 runs each: MEM 191, CORE 0.30 to 0.31 for both
([props-ab.txt](17-fix-transaction-size/props-ab.txt)). `before-commit.sh`:
BEFORE COMMIT OK (943 unit tests, 61 f-tests).

Left: an exception in `store()` is still possible for a record with more
than about 16 million index nodes made dirty, and M49 itself is 005-01.
