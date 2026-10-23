005-27. Fix: a stream that ends at a meta block's position does not start
=========================================================================

Status: open. Kind: fix. Created 2026-10-23.

Found on 2026-10-22 in 005-11, by Claude (Opus 5.5, Claude Code): the
probe P2 met it in a replica's crash image, and the probe P11 made it on
the main stream ([11-replication/report.md](11-replication/report.md),
"P11"). Added at Frans's request ("add 005 entries for the bugs").


The issue
---------

A database whose stream ends exactly at a meta block's position (a
positive multiple of `RecoverableStream.META_BLOCK_DISTANCE`, 200,000),
right after a transaction that ends there, does not start. Recovery throws
`IllegalArgumentException: spos >= streamSize, 14400128, 14400000`, and
nothing gets the database going again short of editing its files.

* P11 (`11-replication/tools/ReplicaProbe.java`, probe `metaedge`): in two
  runs without reclaim, 30,000 and 150,000 transactions, 13 transactions
  ended exactly at a meta block's position. A copy of the stream cut at the
  end of each did not start, 13 of 13. Cut 8 bytes earlier, in the
  transaction, or just after the meta block, all 26 started and checked
  right (005-11's
  [runs/p11-metaedge.txt](11-replication/runs/p11-metaedge.txt) and
  [p11-metaedge-small.txt](11-replication/runs/p11-metaedge-small.txt);
  the same on `78cc5f3`).
* Such a stream comes from a crash, not only from a test's cut: P2 met one,
  a replica's image of exactly 14,400,000 bytes that a flush of its
  `BufferedStream` had left. The main stream is written the same way.


The cause
---------

* `RecoverableStream.append` (RecoverableStream.java:408 to 411) writes a
  transaction's bytes up to a meta block's position, and then the meta
  block, in two appends (`aos.append`, then `writeMetaBlock`). A
  `BufferedStream` flush can come between the two, so the forced stream can
  end exactly at the position; a crash before the next flush (20 ms) leaves
  it so.
* At startup, `recover` (:115) calls `fixMetaBlockIfNeeded` (:297). It
  fills out a meta block that is partly written, 1 to 127 of its 128
  bytes, with `MetaBlock.FILL_OUT_TEMPLATE`; not one of which no byte is
  written (`blockPos == 0`).
* `fixLastTransactionIfNeeded` (:150) then walks the transactions from the
  one the last valid meta block names. The last one is complete;
  `getSpos` gives the next position after the meta block that should follow
  it, 128 bytes past the end, and `getRemainingTransBytes` (:285) throws.
* A transaction that crosses the position, cut there, is fine: its zero
  fill appends the meta block first (`append` with `blockPos == 0`).


How likely
----------

Rare. A flush must come between the two appends, the transaction must end
exactly at the position (1 of 337 and 12 of 1,635 positions in P11's
runs), and the crash must come before the next flush. But then the database
does not start at all. `CrashTest` cuts at random positions and at, just
before and just after the ends of transactions; it is unlikely ever to try
one of these.


The fix, proposed
-----------------

In `fixMetaBlockIfNeeded`, fill out also a meta block that has not begun:
when the stream's length is a positive multiple of the distance, append the
whole `FILL_OUT_TEMPLATE`, as it appends the rest of it for a partly written
block. To check: that the filled-out block is read as invalid, so that
recovery takes the meta block before it, as it does now after a partly
written one. Or, in `fixLastTransactionIfNeeded`, write the meta block when
the next position is past the end. Recovery then goes on as after any
crash.


Done when
---------

* A unit test: a database's stream cut exactly after a transaction that
  ends at a meta block's position starts, with the state after that
  transaction, and goes on (a transaction, a restart). It fails on today's
  code.
* `CrashTest` also cuts at and next to meta block positions, so that the
  gates sample the case.
* P11 again: none of the images fails.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`; `level2.sh` and
  `level3.sh`, whose crash tests exercise recovery, print `LEVEL 2 OK` and
  `LEVEL 3 OK`.


Size and order
--------------

S. Independent of 005-11's decision: it concerns the main stream, Levels 2
and 3, as much as a replica.
