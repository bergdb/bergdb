005-27. Fix: a stream that ends at a meta block's position does not start
=========================================================================

Status: done (2026-10-23; see Outcome). Kind: fix. Created 2026-10-23.

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
  the same on `63fa5de`).
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


Outcome
-------

2026-10-23, by Claude (Opus 5.5, Claude Code), at Frans's request ("bergdb
005-27, fix it."): the first of the two proposed fixes.

**The change.** `RecoverableStream.fixMetaBlockIfNeeded` fills out a meta
block that has not begun, as it fills out one that is partly written: when
the stream's length is a positive multiple of the distance, it appends the
whole `FILL_OUT_TEMPLATE`. The condition is `size > 0 && blockPos <
META_BLOCK_SIZE`; it was `blockPos > 0 && blockPos < META_BLOCK_SIZE`. The
template's last byte is 0, so the block is invalid: `readLastValidMetaBlock`
passes it and takes the one before it, and the walk of
`fixLastTransactionIfNeeded` from the transaction that block names ends
exactly at the new end of the stream, after the filled-out block. Recovery
then goes on as after any crash. The block stays invalid, as a partly
written one does; the next valid one is written at the next position.

The same now happens when a transaction that crosses the position is cut
there: its meta block is the template, where the zero fill used to write a
copy of the last valid block (valid, and naming the same transaction).
Recovery starts from the same transaction either way, and so does
reclaim's condition on the cut (the transaction that the last valid meta
block names).

The first proposal, not the second (to write the meta block in
`fixLastTransactionIfNeeded`): it settles the end of the stream at the meta
block layer, before any transaction is read, in the same way for a block
not begun as for one partly written, as Frans's design of 2012 has it ("The
stream recovery algorithm fills out both streams with zeros at the end",
F1-007, `bergdb/doc/2012/2012-04-stream-format.txt`); and it writes no
valid block with stale contents.

No stream changes when nothing crashes there: StreamDigest `all` against
the build before the change gives `DIGESTS IDENTICAL (36 of 36)`
([digest-compare.txt](27-fix-meta-block-edge/digest-compare.txt)), and
P11's streams are as long as before.

**Tests.**

* `DbTester.testCrash7AtMetaBlockPosition` (unit, about 85 ms): a put,
  sized by the put before it, ends exactly at 200,000. The stream cut there
  starts with the state after that put, takes another put, and restarts
  right; so does the stream cut just after the meta block (200,128), and
  the one cut at 400,000, in a put that crosses that position. On `faa4269`
  it fails: `IllegalArgumentException: spos >= streamSize, 200128, 200000`.
* `RecoverableStream.Tester.crashAtMetaBlockPosition` (unit): the same at
  the storage layer. After recovery the stream is 200,128 bytes, the last
  valid meta block is the first one, and a transaction appended after
  recovery is read back after another recovery. On `faa4269` it fails the
  same way.
* `CrashTest`: after its 100 cuts per round, a cut at the end of each
  transaction that ends at a meta block's position, and 20 cuts
  (`metacuts`) at or next to random meta block positions: at it, 1 byte
  before, 1 and 127 bytes into the block, 128 and 129 bytes after. The Done
  line counts the first kind. Such transactions are rare: in `level2.sh`'s
  full run, seeds 5, 11 and 1004 have one each (at 2,200,000, 2,400,000
  and 4,000,000), and on `faa4269` those three cuts fail with the same
  exception
  ([runs/crashtest-edges.txt](27-fix-meta-block-edge/runs/crashtest-edges.txt)).
  The quick run's seeds have none, nor have Levels 3 and 4, which cut only
  after reclaim's last front cut, near the end of the stream (one meta
  block position or none in the rounds counted); there the metacuts reach
  the new code with transactions that cross the position.
* P11 again (005-11's probe `metaedge`, both runs): 0 of 1 and 0 of 12
  images fail, and none of the 2 and 24 cut before or after
  ([runs/](27-fix-meta-block-edge/runs/)).
* On disk, not asked for:
  [tools/FileBoundaryProbe.java](27-fix-meta-block-edge/tools/FileBoundaryProbe.java),
  a put that ends at 1,200,000, the end of FileStream's sixth file of
  200,000 bytes. The images without the next file and with it empty start,
  read right, take a put (the new file holds the 128 bytes of the invalid
  block and the put) and restart right; on `faa4269` both fail to start
  ([runs/file-boundary.txt](27-fix-meta-block-edge/runs/file-boundary.txt)).

**Gates**, one after the other, on a clone of `a10ebf9` (HEAD, with 005-28
and 005-29) with this change
([gates.txt](27-fix-meta-block-edge/gates.txt)): `before-commit.sh`, BEFORE
COMMIT OK (980 unit tests, 63 f-tests); `level1.sh` to `level4.sh`, full:
LEVEL 1 OK (129 s), LEVEL 2 OK (768 s; 70 of 70 traces `TRACECHECK OK`),
LEVEL 3 OK (499 s; 25 of 25 traces with cuts) and LEVEL 4 OK (871 s; 33 of
33 traces; 149,711 audits in its crash tests, none failed). Earlier, the
same and StreamDigest on `1a329d1` with 005-28's change and this one.
`CrashTest`'s steps took 10 to 15 s in Levels 2 and 3 and 37 s in Level 4,
against 8 to 13 s and 34 s in 005-01's run, for the 20 more cuts a round.

**Done when**, point by point: the unit test, `CrashTest`'s cuts, P11 and
the scripts, above. Not done: P2 was not run again; the replica images it
finds broken, shorter than their cut's decision, are 005-11's matter.
