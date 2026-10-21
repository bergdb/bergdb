005-17. Fix: a transaction of 1.79 GB or more is half committed and blocks the writer
====================================================================================

Status: open. Kind: fix. Created 2026-10-21.

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
