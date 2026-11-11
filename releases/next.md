Notes for the next release
==========================

What the release notes of the next release after 2026.4 must say, collected
here as the changes are made, so that the release does not have to find them
again. The release folds them into its `releases/VERSION/readme.md`, as
[2026.4](2026.4/readme.md) has them under its changes, and
empties this file. A change of the stream's bytes, within the format,
names the StreamDigest configurations whose digests changed and the entry
that keeps its digests before and after (bergdb 018-01, section 2).

Emptied at release 2026.4 (2026-11-11), whose notes hold what was there.


### Core API

* **Merges at the delete; record format 7** (bergdb 024-21; 024-11, MG).
  A delete now merges an underfull key node with a sibling: after every
  transaction every key node that is not the root of a segment tree
  holds at least m live keys or children (m = 8 at node size 30; 024-11,
  BU1), so the index holds at most S + (n + S - 1) / (m - 1)
  key nodes for n live keys in S segment trees, whatever was deleted and
  with any retain duration. In 2026.4 a node went only when it emptied:
  after scattered deletes the index had 2 to 20 times the key nodes of a
  fresh database with the same keys (15.7 times at 10M keys, every 30th
  key kept; 024-03, section 5), and scans and gets paid for it. Readers
  at earlier times see the nodes as they were (a merge makes new nodes).
  A record of deletes means another tree, so the record format is 7, and
  **a start refuses a database of format 6, written by release 2026.4**,
  with a `VersioningStreamException` that names 2026.4 (format 5 of 2026.3
  and earlier, as before). The thresholds are 024-14's m8 (Frans,
  2026-11-11): at node size 30 m = 8, a merge's cap 17, and a split keeps
  a last version of up to 17 klongs (2026.4: 15), constants of format 7;
  so the put path changes too, at node sizes 30 and 62: about 1 % more
  bytes a put in a random fill at 10M keys and 6 to 13 % fewer key nodes
  (024-14, section 4.3). A transaction of
  deletes counts more index nodes before the go point (`Dag.
  dirtyNodeBound`, 024-11's CB2): at node size 30 and a path of 5 nodes
  about 120,000 deletes fit one transaction, and a larger one is refused
  before it changes anything.
  **One more rule of format 7: at most theta dead klongs a key node**
  (bergdb 024-23; 024-18's option 2, Frans's decision of 2026-11-11). A
  write to a key node that would leave it with more than theta dead
  entries (deleted or overwritten keys and children, which lookups before
  the write still read) replaces the node by its current version with the
  write applied, as a full node is replaced; theta is 7 at node size 30
  (1, 3 and 14 at 8, 14 and 62). In 2026.4 a node kept up to B such
  entries until it filled. Counted at 1M keys with a retain duration of
  1 s (bergdb 024-23, section 7; 024-18's probe): under random overwrites
  0.48 dead entries a live one with the merges alone, 0.31 with the rule;
  in a cold database that reclaim rewrites 0.83 down to 0.29; after
  scattered deletes, with a hot range, 0.85 down to 0.31; for -3 % to
  +8.5 % stream bytes, and 13 to 15 % fewer key nodes. Not yet measured:
  10M keys, memory, reads. Each written
  node and each lookup through it carries fewer stale entries; a node
  that is never written again keeps up to theta. A start's rerun applies
  the same rule (no new field).

* **A reclaim step makes dirty only the index nodes on the paths of its
  own puts** (bergdb 024-07, option A; on `main` in `a780b957`). The last
  step of each reclaim iteration made dirty every index node after its
  scan's last key (`Db.touchRange`, a key range with no end): with keys in
  time order (a queue, a log) the whole index, pinned in memory and then
  written in one record. At 10M keys in time order that was 772,454 nodes,
  a commit of 20.6 to 22.3 s under the write lock, 0.67 to 2.31 GB
  resident against a cache budget of 0.2 GB, and a record of 206 MB; at
  1M keys 1.6 s and 17 MB (024-07, sections 2 and 8). Two faults of 2026.4
  and before are gone with it (024-07, section 3; 2026.4's Known issues):
  * with a small heap the step ended in `OutOfMemoryError` inside a
    user's commit and failed the database (a queue of 1M keys, a heap of
    256 MB): it now runs its 40,000 transactions, the slowest commit 37
    ms;
  * from about 104M keys in time order the step's nodes passed the record
    limit, 2^31 - 9 bytes, the startup position stopped for good, no cut
    was made again, and the stream and the heap grew without end, without
    an exception (reproduced with the limit lowered,
    `Reclaim.Tester.testLastStepWithinRecordLimit`; not run at that
    size).

  Now a step follows the path of each key it puts (`Db.touchPaths`) and
  no key range. At 10M keys in time order the last step makes 5 to 15
  nodes dirty, the largest record is 29 kB, the slowest commit 78 ms, and
  a transaction writes 9.7 % fewer bytes (6 % at 100,000 to 1M keys);
  reclaim's iterations, steps and cuts are as before (024-07, section 8).
  The cut's correctness without the range: 024-07, section 4 (the Lean
  theorems T-COVER and T-LATEST; it rests on a delete's unlink, 023-07,
  section 5.1). The record format is unchanged; the stream's bytes of a
  database with reclaim on change. StreamDigest's configurations that
  change and the entry that keeps their digests before and after: not
  yet named (024-07, section 10).
* **In a transaction's builder the last call on a key wins, put or
  delete** (bergdb 024-10, R1; Frans, 2026-11-11, 07:08). Of the calls of
  `Trans.Builder` on one key as written, `build()` keeps the one made
  last, a put with its value or a delete; the earlier ones are gone. In
  2026.4 and before a put won over a delete whatever their order (015-40):
  `put(k, 1)` then `delete(k)` kept the put, and now deletes `k`. A
  transaction that names no key twice writes the bytes it wrote before
  (StreamDigest `all`, 48 of 48 digests identical; 024-10, section 8). The
  Pub API's `w()` and `rw()` already kept the last call on a key as
  written (015-40, 015-41).
* **A transaction whose key transformations make two of its keys one key
  is refused** (bergdb 024-16; Frans, 2026-11-11, 09:43: "One transaction
  must not set (put or delete) a value more than once! This is a strict
  rule."). At the commit, when the key transformations (the Core's; a key
  replace such as `${transactionTime}` in the Pub layer) make two
  different keys as written one key, nothing of the transaction is
  written and the caller gets a `DbException` that names both keys as
  written and the key they became; the database goes on. The check is
  made before the go point (`Db.transformKeys`), so every transaction
  that reaches the index holds one operation a key. In 2026.4 and before
  one of the two was kept (the last put in key order, or a delete). A
  transaction without such keys writes the bytes it wrote before.


### Known issues and limits

* **Fixed: reclaim with keys in time order** (bergdb 024-07; 2026.4's
  Known issues, its first entry): the heap that ran out in a user's commit
  and the record limit that stopped reclaim at about 104M keys (Core API,
  above).
