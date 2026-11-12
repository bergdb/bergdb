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


### Pub API

* **`Database.maintain()`: the maintenance on request, a new method**
  (bergdb 024-32; Frans, 2026-11-12, 12:10 and 13:52; 023-04, Y10). With a
  finite retain duration, reclaim moves on only at the application's
  commits (010-01, P3), so a database that was emptied and is no longer
  written kept its stream. A call does a bounded part of the maintenance
  in the database's own transactions: at most one reclaim step, one write
  of index nodes by the take, one filler of at most 200 kB that is put and
  deleted at once to reach a meta block, the cut when it is due (after a
  sync, if needed), and a batch of the release from memory of what the cut
  ended; it returns true if more is due now. A call when nothing is due
  writes nothing; with the retain duration forever (the default) it
  returns false. Calling it is optional: the maintenance goes on at the
  commits as before, whether it is called or not. It writes records of
  kinds that exist only: no format, model or trace change (the
  conformance configurations `r-maint` and `e-r-maint` pass). G5 (Tests
  and gates): 1M keys put and deleted, then `maintain()` alone, no writes:
  the stream from 254 MB to 83 kB, at most 75 kB and 5 records a call.
  The Core's `Db.maintain()` is the same.


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
* **The take's pace is capped after a decrease of the startup distance**
  (bergdb 024-31; 015-84, 024-05's OP4; Frans, 2026-11-12, 13:09). Each
  record writes its share of the startup section's dirty index nodes (the
  take, 007-07), and the share grew with the section's span over the
  startup distance: right after a decrease from 1000 to 100 MB in one call
  a record took up to 10 times its usual share, and at 50M keys the
  catch-up's records were 13 to 15 MB (2026.4's Known issues, Limits). Now
  the share counts the span of the section's transactions as at most twice
  the startup distance (`TransSeq.SHARE_FACTOR_CAP`, 2). At 10M keys the
  catch-up's largest record from 1000 to 100 MB is 0.99 MB (was 1.90),
  from 200 to 50 MB 2.36 MB (was 4.12); the catch-up is longer: from 1000
  to 100 MB the section is below twice the new distance after 2.88M puts
  and 1,451 MB of stream (was 0.64M and 795 MB), and it shrinks at every
  record meanwhile. With a startup distance that was not lowered the span
  stays below twice it (T3), so the stream is the same, byte for byte
  (StreamDigest 48 of 48 identical before and after). The Lean model's
  pace mirrors it; `T3_take` holds for any pace.
* **`Db.maintain()`**: the Pub API's `Database.maintain()` (above) in the
  Core API (bergdb 024-32).
* **The cache's tables shrink after deletes** (bergdb 024-33, ST6; Frans,
  2026-11-12, 12:10). The node table, 4,096 hash maps, kept its largest
  size after a fill and a mass delete: at 1M keys put and deleted 226,400
  slots against a fresh database's 60,272 (3.76 times). Now a removal that
  leaves a map under 1/8 of its capacity copies it to a capacity of at
  least twice its entries, and at least 16 slots: 63,744 slots, 1.06 times
  (G4). A copy follows at least capacity / 8 removals, so the cost is
  constant a removal, amortized; `performance.sh ab` at 1M keys showed no
  change beyond the runs' spread. No byte of the stream changes. A floor
  is left (Known issues).
* **A reclaim step reads again only the values it may rewrite** (bergdb
  024-34, OP8; Frans, 2026-11-12, 12:10). A step read each live KV of its
  scan again at its time, also one whose value the scan found at pCut or
  later, which it never rewrites. That second read is now skipped: at 1M
  keys the second reads halve (4,208,912 to 2,063,799); with a cache of 20
  MB the loads fall 3.6 %, since the follower caches each version a step.
  The same puts and the same stream bytes (StreamDigest 48 of 48
  identical). The scan still loads every value it passes, as a step's size
  counts the values' lengths; a scan of keys only would change the bytes
  (024-34, Q34-1; not in 2026.5).


### Format

* **StreamDigest: all 48 digests change** (bergdb 018-01, section 2;
  024-38). Against release 2026.4's digests (its `baseline.zip`,
  `baseline/f53/digests.txt`), the decided digests of all 12
  configurations differ, the 8 of `l2-*` and the 4 of `l3-*`, in each of
  the four modes (48 of 48); in each configuration the four modes give the
  same stream. The causes are record format 7, with its merges, theta and
  CRC32C (024-21, 024-23, 024-25), and the last touch (024-07), whose
  configurations are not isolated (024-07, section 10). The take's cap
  (024-31), reclaim's reads (024-34), the cache's tables (024-33) and
  `maintain()` (024-32) change none: 48 of 48 identical before and after
  each. The digests before and after, and their comparison:
  `items/024-release-2026-5/38-release/` (`digests-base.txt`,
  `digests-new.txt`, `compare.txt`).


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
    database, as one that throws does (Known issues). A start reads a
    record's header first, and refuses another format before reading the
    record.
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
  objects and heap; since 024-33 also the cache's table slots, ST6). Release
  2026.4 fails G1 and G2.
* **G5, back to empty by `maintain()` alone** (bergdb 024-32, section 4),
  in `count-gates.sh` beside G1 to G4: 1M keys put and deleted, then
  20,000 calls of `maintain()` and no writes: the stream kept falls from
  254 MB to 83 kB (the limit: twice a fresh twin's plus 600 kB), quiet
  after call 6,130; resident objects 10 against the twin's 5; the cache's
  slots within the floor of ST6 (Known issues). Two new conformance
  configurations, `r-maint` and `e-r-maint`, trace databases driven by
  `maintain()` (`TraceExport` `maint=K`) and pass the Lean checker.

### Documentation

* **`docs/` moved into item 027** (bergdb 027; Frans, 2026-11-12, 14:17,
  14:27 and 14:32). `levels.md`, `sis-model.md`, `sources/` and the
  readme are 027-01, a snapshot of 2026-11-12, not updated; the trace
  format is 027-02, kept current with the code; `docs/` holds only
  `log.md`, the development log. Code comments, the level scripts and the
  repository's readme cite them by ID. 2026.4's notes link `docs/` at
  their release commit.


### Known issues and limits

* **Fixed: reclaim with keys in time order** (bergdb 024-07; 2026.4's
  Known issues, its first entry): the heap that ran out in a user's commit
  and the record limit that stopped reclaim at about 104M keys (Core API,
  above).
* **Fixed: on Linux, a new database in a new directory refused as in use**
  (bergdb 024-36, OT2; 2026.4's Known issues): `FileStream` now closes
  `bergdb.lock` and removes the directory from its set of locked
  directories in one step, under the monitor under which a start checks
  that set, so a start in the same JVM right after a close (as a background
  close after `stop()` of a database whose directory was deleted) no longer
  finds a new directory's reused inode still listed. Left: a start in
  another class loader of the same JVM can still, rarely, be refused in
  that moment; a retry works. Test
  `FileStream.testNoStartSeesAClosedLockStillListed`.
* **Fixed: a Core put under the Core's own keys** (CA3; bergdb 024-37;
  024-01, section 5.3): a database that never opened again after a put
  at `/#i/dreclaim/-settings.txt` through `Db` (Core API, above).
* **Fixed: `Db.getTrans` at a position inside a record** (bergdb 021-27;
  2026.4's Known issues, "Open at the release"): it is refused and the
  database goes on (Core API, above).
* **Fixed: a damaged time klong whose unused bits are set** (bergdb
  024-25, section 12; 2026.4's Known issues): a start refuses it (Core
  API, above).

**New in 2026.5:**

* **Aim 4, the model: proved in part, the rest checked by conformance**
  (bergdb 024-04, aim 4; 024-28, section 6; Frans, 2026-11-12, 12:22:
  2026.5 ships with conformance and the proofs that hold, the open ones
  named here). Proved: the tie of the model to the stream (`PhysStep`),
  the last touch's cut (T-COVER, T-LATEST), `T3_take`, the tree's spec
  (TP13, TP17, TP18), TP1 and TP9, the merge's local parts, and that the
  limits' nodes fit a record (`ReleaseFits`). Not proved: TP7 (the tree's
  invariants), TP10 (a get), TP30 (V1 kept, the large part of the
  B-tree's proof; reduced to TP7), TP31 (BU1, the fill of a key node), TP32
  (the merges of a transaction, restated for sorted transactions) and
  TP33 (CB3, a potential);
  TP11 (a scan) is refuted as stated, for keys that Java does not make,
  and its fix is decided: the model's `keyWf` is to say what
  `Keys.toSegments` makes (024-12; Frans, 2026-11-12, 13:38); and T4, the
  records at the startup section's ends, and a cold start's reads (007).
  What is not proved is checked by conformance: Java's traces are run
  against the model at every night's gate (`night.sh`'s level scripts
  and conformance steps; the large set in the release night) and hold on
  every traced state (024-12: 115 traces, with merges 260, with theta
  222).
* **An emptied database keeps the cache's tables at a floor of about
  256 kB** (bergdb 024-32, section 7; ST6 after 024-33). A map of the node
  table that was used keeps at least 16 slots, so a database brought back
  to empty keeps up to 4,096 maps of 16 slots, about 256 kB, whatever its
  size before (3,099 maps after 1M keys; a fresh database uses 5). G4 and
  G5 allow that floor.
* **Moved to 2026.6** (bergdb 024-05; 026): ST8, the 10 MB write buffer
  that every database allocates at its start, whatever its size; P8, the
  lag after a mass delete: an emptied database needs about 4.4 retain
  durations of further writes before its stream comes back near a fresh
  one's (G4: the first cut after the deletes at transaction 4,117, the
  twin's at 1,214; `maintain()` does it without writes).
* **A single put's record of about 0.25 MB now and then** (bergdb
  024-05, OP5, a named allowance; Frans, 2026-10-28; 010-01, P4). The
  take writes whole transactions: with single puts alone at 10M keys a
  record is at most 0.23 to 0.29 MB, the mean under 1 kB; with a batch of
  500 now and then among single puts a put's record reached 209 kB
  against a mean of 576 bytes (sd 1 MB, 20,000 keys; 007-07, section
  7.1). Large as a ratio, small in bytes; it grows with the batch.
* **A value transformation (Core API) that throws or passes 8 MiB fails
  the database** (bergdb 010-04, R5; 024-24, QL6; Limits, above), as
  in 2026.4; a restart has the state before its transaction. To change in
  2026.6 (Frans, 2026-11-12, 14:42: "I don't see it
  as a bug, but something to change anyhow.").
* **A put's stream bytes grow with the keys at a fixed startup distance**
  (bergdb 024-05, QF3, OP3 and BD5; 017-11, section 2.1; Frans,
  2026-11-12, 12:46). A put makes the index nodes on its path dirty, and
  the take writes each dirty node whole about once a startup distance of
  stream, so the puts in between share its write: a put's bytes are a
  function of the startup distance a key, sd / K, for a key shape, a
  value size and a node size. For 32-byte KVs (24-byte keys, 8-byte
  values), uniform updates and retention forever, bytes a put by sd a
  key: about 270 at 50 bytes (1M keys and 50 MB, the model), 190 at 100
  bytes (10M keys and 1000 MB), 524 at 20 bytes (10M keys and 200 MB),
  854 and 867 at 5 bytes (1M keys and 5 MB; 10M keys and 50 MB), 1,244
  at 1 byte (50M keys and 50 MB), about 1,380 at 0.5 bytes (100M keys and
  50 MB, the model); the rest measured, the law within about 15 %. So at
  the default 50 MB each tenfold growth of the keys adds about 400 to 650
  bytes a put, and a startup distance that grows with the keys keeps it
  constant, at the price of a start's time and heap (a warm start 2 to 5
  s at 50 MB, 8 to 20 s at 200 MB, 40 to 100 s at 1000 MB; 017-11,
  section 2.2). Reclaim adds at most about a third; larger values write
  fewer index bytes over the user's bytes. The default stays 50 MB, which
  suits up to about 10M keys; beyond that, 200 to 1000 MB. A default that
  follows the keys is studied in 017-11, not for 2026.5.
* **The stream kept under reclaim: about 4.5 to 6 times the live data
  beyond the history** (bergdb 024-05, QF1, decided by Frans, 2026-11-12,
  14:07; 024-30, G3; 024-29, section 9). With a finite retain duration,
  reclaim may rewrite a quarter of the stream's growth (its internal
  fraction, 1/4 since BergDB's first commit, kept for 2026.5). The stream
  then holds the records within the retain duration, the history, and
  beyond them up to about 6 times a fresh database of the same live keys:
  G3 measures 4.41 at 1M keys under uniform overwrites and fails above 6,
  in every `night.sh`. A larger fraction keeps less for more bytes written
  (at 1M keys 3/8 keeps 8 to 29 % less, for 15 to 27 % more bytes and 23
  % fewer puts a second). The fraction is no Pub API setting; three
  recommended fractions and a default, measured on larger databases, are
  for 2026.6 (026-04).

**From 2026.4's Known issues and limits** (`releases/2026.4/readme.md`),
each as it is in 2026.5:

* **Fixed**: reclaim with keys in time order (024-07), on Linux a new
  directory refused as in use (024-36), `Db.getTrans` inside a record
  (021-27), a damaged time klong (024-25), a Core put under the Core's own
  keys (024-37; part of "Writes through the Core that the rules leave
  undefined"), all above. 2026.4's two fixed entries (021-25's log keyed
  by time, the puts slowed after reclaim passed deleted keys) stay fixed.
* **Changed: a leaf keeps the entries of its deleted keys** (023-08, Q5):
  now underfull key nodes are merged at the delete (024-21), and a key
  node holds at most theta dead entries (024-23), so a node that is
  written keeps few; G2 holds the reachable key nodes within twice a fresh
  twin's (1.30 at 1M keys; 16.0 on 2026.4).
* **Changed: a decrease of the startup distance at 50M keys**, records of
  13 to 15 MB: the take's cap (024-31) halves the catch-up's largest
  records at 10M keys; not measured again at 50M.
* **Changed: a long key's still-dirty loop is quadratic** (021-16, Q1;
  024-05, OP6): a user's key is now at most 111 bytes (L2), so no user's
  key reaches it; the loop is as before for BergDB's own long keys.
* **Changed: other damage that a start does not detect** (019-30, 019-31,
  019-33): CRC32C sees every change of up to 32 adjacent bits (019-33's
  0x00 to 0xff is seen) and a start checks a time klong's unused bits;
  BergDB still assumes correct storage, and its checks are a best effort.
* **Changed: the documentation**: `docs/` is now a snapshot of 2026-11-12
  in item 027-01 (levels.md, sis-model.md, sources/), not kept current;
  the trace format is 027-02, kept current; `docs/` holds `log.md` only
  (Documentation, below).
* **Still so**: after a mass delete, more dirty top nodes for a while
  (023-03, section 10); a lost or cut last stream file (020-24-08, U8-1);
  a transaction larger than the startup distance (020-24-13, U13-7; now at
  most 32 MiB, L5); the user indexes' threads, a job's status that lags
  its index, a fair lock for builds (020-18, O1 and O2; 020-29, section
  7); the Core's other writes that the rules leave undefined (020-22,
  sections 5 and 6); the API's wishes (020-24-13, 020-24-14); a corrupt
  record header (015-73; no checksum covers it in format 7 either); at
  most as many busy readers as the cores less the collector's workers
  (015-86); the collectors; overload; a small commit after a large
  transaction (007-07, sections 7.1 and 7.2); D's loose bound (005-38);
  the default startup distance (above, the put's bytes); loads in memory
  8 to 20 % slower than before handles; bounded startup, T4 and a cold
  start not proved (above, aim 4); the files after a physical cut
  (005-72); concurrency outside the Lean model; power loss; the JDKs and
  systems tested: JDK 27 and 17, macOS and Linux, an Android emulator.
