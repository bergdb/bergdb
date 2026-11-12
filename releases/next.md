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
  (2, 3 and 14 at 8, 14 and 62; at least 2, bergdb 024-19, Q4). In
  2026.4 a node kept up to B such entries until it filled. Counted at 1M keys with a retain duration of
  1 s (bergdb 024-23, section 7; 024-18's probe): under random overwrites
  0.48 dead entries a live one with the merges alone, 0.31 with the rule;
  in a cold database that reclaim rewrites 0.83 down to 0.29; after
  scattered deletes, with a hot range, 0.85 down to 0.31; for -3 % to
  +8.5 % stream bytes, and 13 to 16 % fewer key nodes. Not yet measured:
  10M keys, memory, reads. Each written
  node and each lookup through it carries fewer stale entries; a node
  that is never written again keeps up to theta. A start's rerun applies
  the same rule (no new field).
  **One more change of format 7: the node checksum is CRC32C** (bergdb
  024-25; 024-17, QL9, Frans's decision of 2026-11-11). Every node's
  checksum is a CRC-32C (`java.util.zip.CRC32C`) of 4 bytes in place of
  2026.4's Fletcher-16 of 2 bytes, in a node header of 12 bytes (8 in
  2026.4); the node formats are 3, 3 and 5 (top, key, value and delete
  nodes; 2, 2 and 4 in 2026.4). Key nodes keep their size (the fields
  moved into reserved bytes); a top node is 8 bytes longer, a value or
  delete node 4. The checksum of 8 MiB, a value at the limit L4, takes
  about 1 ms instead of 47 (0.12 ms a MB against 5.6; a key node of 544
  bytes 0.05 us against 3.0): a commit of an 8 MiB value about 2 to 10
  ms instead of 49 to 56, a get of it about 4 ms instead of 53, a
  restart with six such values about 0.2 s instead of 0.5 (rough
  figures, 024-25, section 6). It sees every change of up to 32 adjacent
  bits, so a byte changed between 0x00 and 0xff, which Fletcher-16 did
  not see (019-33), and passes about one random change in 2^32 (65,025
  before). A database written by `main` with format 7 before this change
  (no release wrote one) is refused at the start, for a checksum error.
  The stream grows by those bytes: Props' SS, stream bytes a user byte,
  from 1.51 to 1.53 (SS3, KVs of 100 bytes, from 1.64 to 1.69).
  StreamDigest: the digests of all 12 configurations change, in every
  mode (48 of 48; the digests before and after in 024-25, section 7).

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
  change: not isolated (024-07, section 10); every StreamDigest digest
  changes in 2026.5 anyway with record format 7 and CRC32C (all 48,
  024-25, section 7).
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
* **The node size is at most 62** (bergdb 024-19, Q6; 024-27; Frans,
  2026-11-12). The Core API's `DbBuilder` offers 8, 14, 30 and 62, as
  before, and the Pub API 30, the default (024-19, Q1); now the Dag and a
  start refuse a larger size too, a meta block that gives one with a
  clear message (in 2026.4 such a stream named a method that does not
  exist). Theta, the dead klongs a key node may hold, is at least 2:
  2 at node size 8 (was 1; 024-19, Q4).
* **A start checks a time klong's unused bits** (bergdb 024-25, section
  12; `0420c72e`). A key node whose time klong has any of bits 56 to 61
  set is refused at the start with a `StreamFormatException` ("Bad time
  klong") in place of an `AssertionError` with `-ea` (and a start that
  went on without it). No writer sets those bits, so every database that
  2026.5 writes opens as before. A damaged stream is caught as a best
  effort: BergDB relies on the storage for the integrity of its bytes
  (Frans, 2026-11-12).
* **`Db.getTrans` refuses a position that is not a transaction's**
  (bergdb 021-27; 010-04, R5). A multiple of 8 inside a record, not at
  its start, read the bytes there as a record and failed the database
  (`DbFailedException`; a database in memory was lost). Now any position
  whose bytes are not a committed transaction's record is refused with
  `IllegalArgumentException` (the read's `StreamFormatException` the
  cause), and the database goes on; only an I/O error fails it. A
  position inside a record whose bytes there happen to form a committed
  record still gives that record. The Pub API's `transactionInfo()`,
  whose position is a get's, still takes a bad record there for damage.
  A size over 1 MiB at the caller's position is believed only when a
  walk of the records' sizes from the meta block before it reaches the
  position (Q27-1): bytes inside a record that read as a size of up to
  2 GB are refused before an array of that size is made.
* **The Core refuses a caller's writes at its own keys** (bergdb 024-37;
  010-04, R5; CA3, 022-06-2's U2-8). The key `/#i/-dummy` and reclaim's
  directory `/#i/dreclaim/` with every key under it are written by the
  Core alone, and a start reads them: in 2026.4 seven bytes put through
  `Db` at `/#i/dreclaim/-settings.txt` were taken, and every later start
  failed with `InternalDataException`. Now a put or a delete there is
  refused before anything is written, and the database goes on: by the
  `Trans.Builder` call that takes the key, with
  `IllegalArgumentException` (it spoils the builder, as a key over the
  limit does), and by `Db.execute()` with a `DbException` for a key that
  a key transformation gives and for the internal calls `putLongKey()`
  and `deleteLongKey()`. The Pub API's keys under `/#i/` (its index
  definitions, entries and markers, `/#i/di...`) are written as before;
  reads of the Core's keys are allowed.


### Limits

* **Limits on keys, values and transactions** (bergdb 024-17, 024-24),
  fixed for every database; a later release may raise them, never lower
  them. A call over one throws and writes nothing; the database goes on.
  **A refused put or delete spoils its builder** (bergdb 024-26, U26-5,
  024-27; Frans, 2026-11-12): the Pub API's `WBuilder` and the Core's
  `Trans.Builder` then write nothing, and their `execute()` (Core:
  `build()`) and every later call throw `IllegalStateException`, also if
  the caller caught the refusal. In 2026.4 a caller that caught it and
  went on committed the other operations.
  **In an `rw()` action a refused call changes nothing and does not spoil
  the environment** (bergdb 024-27, QR1; Frans, 2026-11-12): an action
  that catches the refusal and returns commits its other writes, as
  before; the action is the application's code, and the database keeps
  its own indexes consistent either way (010-P14; 010-04, R1 and R3;
  `RwEnvironment`'s Javadoc, "Refused calls").
  * **A key is at most 111 bytes**; about 100 characters as a rule of
    thumb: ASCII letters and digits one byte each, each "/" of a Pub key
    two, letters such as å, ä and ö two bytes each (UTF-8). Refused with
    `IllegalArgumentException` by the call that takes the key. Until now a
    key had no limit.
  * **A value is at most 8 MiB** (8,388,608 bytes), refused at the put
    with `IllegalArgumentException`; larger data goes in chunks under keys
    of their own, with a key that lists them written last.
  * **A transaction is at most 500 operations** (the keys it puts or
    deletes; a Pub object put in a directory with k indexes counts up to 1
    + 2k) **and 32 MiB of keys and values**; its keys, its index entries
    among them, at most 56 KiB. Refused at the commit with
    `DbException`. Larger work goes in several transactions, with a key
    written last that readers look at first.
  * **An indexed value's levels are at most 111 bytes**, as a key: a put
    of an object with longer ones for an index of its directory is refused
    with `IllegalArgumentException` (until now it was taken with no entry,
    and the index's scans missed it); index such a value by a hash or a
    prefix. A build over objects put before the index gives them no entry.
  * A value transformation (Core API) whose result passes 8 MiB fails the
    database, as one that throws does. A start reads a record's header
    first, and refuses another format before reading the record.
  * Gates and tools changed with them: batches of 500 (were 1,000) in
    PayDemo, PayTest and LargerThanMemory, so bytes a put and time a
    commit there are not comparable with earlier runs; `performance.sh`'s
    long keys of 111 bytes (were 120), so its long-key results are not
    comparable with 2026.4's reference.

### Tests and gates

* **Count gates of aims 2 and 3** (bergdb 024-30): `stress/count-gates.sh`,
  a step of `night.sh` after level4 (about 2.5 minutes), at 1M keys and
  on counts, not times: the largest record (G1, at most 1 MB), key nodes
  against a twin built fresh (G2, at most 2 times), the stream kept beyond
  the history within the retain duration (G3, at most 6 times the live
  data) and back to empty (G4: 1M keys put and deleted, then within 2
  times a hello-world database's stream, key nodes, dead klongs, resident
  objects and heap). Release 2026.4 fails G1 and G2.

### Known issues and limits

* **Fixed: reclaim with keys in time order** (bergdb 024-07; 2026.4's
  Known issues, its first entry): the heap that ran out in a user's commit
  and the record limit that stopped reclaim at about 104M keys (Core API,
  above).
* **Fixed: a Core put under the Core's own keys** (CA3; bergdb 024-37;
  024-01, section 5.3): a database that never opened again after a put
  at `/#i/dreclaim/-settings.txt` through `Db` (Core API, above).
