005-31. Fix: a transaction whose dirty index nodes do not fit in one record stops the startup pos for good
==========================================================================================================

Status: done (2026-10-24). Kind: fix. Created 2026-10-23.

Found on 2026-10-23 in bergdb item 007, by Claude (Opus 5.5, Claude Code),
and checked with a probe: [007-02](../007-bounds/02-take-blocked.md), with
the probe and its output in
[../007-bounds/02-take-blocked/](../007-bounds/02-take-blocked/). Added at
Frans's request ("Register the bug in 005.").

Decided 2026-10-24, Frans: "005-31, it has my 'go'. But don't start the
implementation now." So option A, the proposed fix; not started. It is step
1 of item 007's plan, [007-03](../007-bounds/03-plan.md).


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

A, proposed, and decided on 2026-10-24: refuse such a transaction before
its go point, with a `DbException`, as `Db.checkSize` refuses one whose
value nodes pass 7/8 of the limit (005-17).

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


Outcome
-------

2026-10-24, by Claude (Opus 5.5, Claude Code), option A as decided, at
Frans's request ("fix all todo items of type Fix", "do what is proposed";
it lifted the hold of 2026-10-24). Step 1 of 007-03.

The check, `Db.checkDirtyNodes`, runs in `executeInner` under the write
lock, before the go point, after the check of the top node ordinals; not
for reclaim's internal transactions, whose steps have their own reserve
(`Reclaim.setStepReserve`), and which run after a user transaction's go
point, where a refusal would fail the database. It refuses with a
`DbException` ("The transaction is too large: the index nodes it can make
dirty or create, up to N, could take B bytes in a record, more than L
(bergdb 005-31). ...") when a bound on those nodes, each at the largest
size (32 + 16 (M + 1) bytes, 528 at the default node size M = 30, and 16
for its got-dirty entry) and two top nodes, passes
`StoredTrans.dirtyLimit()`: 15/16 of the record limit. So a later
transaction whose own part of its record (values, got-dirty ids, header)
is below 1/16 of the limit, 134 MB, can take them all. "The limit" of the
proposal, taken as the record limit less that room: a bound of the whole
limit could never be taken, as every record has a header.

* The cheap test, for every transaction: each key counts 3 h s + 3 nodes,
  s its segments and h = log2(the stream's length / 48) + 2, a height that
  no segment tree of the stream can pass (a tree of n nodes with two
  children or more is at most log2(n) + 1 high). At the real limit and a
  stream of 1 GB it passes every transaction of up to 23,000 keys of two
  segments (7 to 13 bytes), 45,000 of one; no walk, a sum over the keys.
* The bound, for a transaction that fails it: `Dag.dirtyNodeBound` walks
  the paths of its keys at the latest time, as a get, and counts the
  distinct key nodes on them (a put makes dirty its leaf and every node
  above it), the nodes that the splits of the klongs it appends can make,
  from each node's actual size (its room, then a split every
  max(2, M/2 - 3) klongs; a node that existed is replaced by up to two),
  new roots, and the new segment trees of keys whose segment is missing. A
  key with a key transformation (known only at the put) counts as in the
  cheap test.
* No change to the format, the model or the streams.

The first step, the bound against what the got-dirty nodes take when the
transaction has run (`TransSeq.recordBytes`, as `take()` counts them), with
[BoundProbe.java](31-fix-take-blocked/BoundProbe.java), on 007-02's
database (40,000 keys) at the real limit, at the four node sizes
([bound-m8.txt](31-fix-take-blocked/bound-m8.txt),
[bound-m14.txt](31-fix-take-blocked/bound-m14.txt),
[bound-m30.txt](31-fix-take-blocked/bound-m30.txt),
[bound-m62.txt](31-fix-take-blocked/bound-m62.txt)). The bound is above
the actual in every case. At the default node size:

| Transaction | Its record | Bound | Actual | Bound / actual, bytes (nodes) |
|---|---|---|---|---|
| update of every 20th key | 138 KB | 2,935 nodes, 1.60 MB | 2,571 nodes, 0.90 MB | 1.78 (1.14) |
| update of every 100th key | 34 KB | 949 nodes, 516 KB | 870 nodes, 305 KB | 1.69 (1.09) |
| update of every 1000th key | 5 KB | 123 nodes, 67 KB | 120 nodes, 44 KB | 1.53 (1.03) |
| load of 20,000 new keys, new prefix | 986 KB | 1,819 nodes, 990 KB | 1,539 nodes, 444 KB | 2.23 (1.18) |
| load of 20,000 new keys among them | 1.49 MB | 24,431 nodes, 13.3 MB | 23,264 nodes, 3.0 MB | 4.41 (1.05) |

The bound is close in nodes (1.03 to 1.19 at node size 30; 1.01 to 1.67 at
14 and 62; 2.0 to 2.6 at 8, where splits come every klong or two); the
bytes overestimate by 1.5 to 8, as every node counts at the largest size.
With the first version, a split every M/2 - 3 klongs also at node size 8,
the bound was 9 to 2,500 times too large there; hence the floor of 2. So
at the real limit a transaction is refused when its bound passes about 2
GB: an update of about 3 million keys spread over as many key nodes, or a
load of about 3 million new keys at random among existing ones (at the
default node size); for a load into a new key range the value limit (005-17)
comes first. Found on the way:
a load of new keys at random among existing ones dirties more index nodes
than it has keys (23,264 for 20,000), so it can stop the startup pos as an
update can; "A load of new keys does not do it" above holds for a load into
a new database or a new key range.

Tests: `DbTester.testTooManyDirtyNodes` (f), with the record limit lowered
to 200 KB: 10,000 keys, then an update of every 10th key, a record of about
70 KB, is refused before it changes anything (the stream's length and the
values as before), and the database goes on: an update of every 1000th
key, and a load of 1,000 new keys under a new prefix, are taken, and after
500 more transactions the startup section is below 3 startup distances.
Without the check the update is taken, and the section is then 16
startup distances, 163 KB, and growing (the stall of 007-02).
`DbTester.testRecordsWithinLimit` (005-17), at node size 8 with records of
170 KB of values, passes with the floor of 2, not without it.

Not done, as not part of the proposal: a transaction is taken by the record
of a later one that leaves room for it, so a transaction refused by
nothing can still wait if every later record is nearly full. A stream of
transactions each near the value limit, as in `testRecordsWithinLimit`,
does it; a dirty limit of 1/8 of the record limit, the room that every
record leaves after its values (005-17), would make one transaction always
fit, and refuse eight times smaller updates. For Frans: see the note at
step 1 of [007-03](../007-bounds/03-plan.md).

Streams unchanged: StreamDigest `all`, the build of `10bc36b` against the
one with the change, DIGESTS IDENTICAL (36 of 36)
([digest-compare.txt](31-fix-take-blocked/digest-compare.txt)): nothing of
the standard workloads is refused.

`before-commit.sh`: BEFORE COMMIT OK (1007 unit tests, 67 f-tests).
