005-31. Fix: a transaction whose dirty index nodes do not fit in one record stops the startup pos for good
==========================================================================================================

Status: open. Kind: fix. Created 2026-10-23.

Found on 2026-10-23 in bergdb item 007, by Claude (Opus 5.5, Claude Code),
and checked with a probe: [007-02](../007-bounds/02-take-blocked.md), with
the probe and its output in
[../007-bounds/02-take-blocked/](../007-bounds/02-take-blocked/). Added at
Frans's request ("Register the bug in 005.").


The issue
---------

Startup is bounded only while the startup pos moves. One transaction can
stop it for good: one whose got-dirty index nodes need more bytes than one
record can hold. From then on:

* the startup section grows with every transaction, and so does startup,
  which reruns everything after the stopped startup pos;
* D keeps the transaction's nodes for good, memory that eviction cannot
  free;
* reclaim cannot cut, since the cut waits for the startup pos;
* a restart does not help: startup rebuilds the same D, and the take meets
  the same transaction.

Nothing fails or warns. The probe, with the record limit lowered to 200 KB
as `DbTester.testRecordsWithinLimit` does: a transaction that updates 400
keys spread over the key nodes of 40,000 keys has a record of 34 KB, a
sixth of the limit, and stops the startup pos; 4,000 transactions later the
section is 20 times the startup distance and still growing.


The cause
---------

* `TransSeq.take` takes whole transactions. Since 005-17 it counts the
  bytes the nodes it takes add to the record (`recordBytes`: each node's
  size in the stream and 16 bytes) and does not take the first transaction
  that does not fit in the record limit (`StoredTrans.recordLimit`, 2^31 −
  9 bytes), "also when fewer than two are". If that transaction's nodes do
  not fit even in a record of their own, no later take ever takes it.
* The transaction's own record passed: it holds its value nodes and a
  16-byte got-dirty id per node, while writing a key node takes up to 528
  bytes at the default node size, about 360 on average. So a record can be
  well within the limit, and its nodes not.
* The take cannot take part of a transaction: the startup pos passes a
  transaction only when all the nodes that got dirty in it are written,
  since a node left in D keeps its got-dirty index (INV-1, INV-3 of
  docs/sis-model.md).

With the real limit it takes some millions of keys updated in one
transaction, spread over as many key nodes: a database of about a hundred
million keys or more. A load of new keys does not do it: its new key nodes
are full of its keys and take fewer bytes to write than the keys took in
its record.


The fix, options
----------------

A, proposed: refuse such a transaction before its go point, with a
`DbException`, as `Db.checkSize` refuses one whose value nodes pass 7/8 of
the limit (005-17).

* A cheap test first, for every transaction: if its keys times (the
  length of a key's path + 2) times the largest key node (528 bytes and 16)
  is within the limit, it passes; with a path of 8 that is every
  transaction of fewer than about 400,000 keys.
* Only for a transaction that fails the cheap test, under the write lock
  before the go point: count the distinct index nodes on the paths of its
  keys, as the warm-up walks them, add the new nodes its splits can make
  (its new key entries divided by half a node, plus a node per level), and
  refuse it if they would take more than the limit at the largest size.
* No change to the format, the model or the streams: only transactions that
  would stop the startup pos are refused. A large update must then be split
  by the application, as a very large transaction must since 005-17.

B: let one record of the model be several records of the stream
(continuation records), the last one with the startup pos, gd and topPos;
recovery drops an incomplete group as a torn record. Nothing is refused and
the model does not change, but the stream's format and recovery do.

C: write a transaction's nodes over several records before the startup pos
passes it, each record listing the nodes it took out of D, so that startup
can rebuild D. Nothing is refused, but it is a change to the model (step 6,
INV-1, startup's D) with its proofs, and to the format.


Done when
---------

* A unit test with the record limit lowered, as the probe: the transaction
  that stopped the startup pos is refused before it changes anything, and
  the database goes on with its startup pos moving; a transaction under the
  bound, and a large load of new keys, are taken.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`; StreamDigest
  identical.
* Docs: the refusal in `Db.checkSize`'s Javadoc and the Pub API's
  `DbException` docs, and docs/levels.md (Level 2, "Bounds").


First step
----------

On the probe and on a large load, compare the precise count of option A
with the bytes the transaction's got-dirty nodes take when they are
written, to see how much it overestimates.


Size and order
--------------

S for option A: a check before the go point and its tests. Before the
deadline that 007-01 proposes for `TransSeq.take` (its decision D1): the
deadline needs every transaction's nodes to fit in a record.
