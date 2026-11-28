# 024-17. The limits of BergDB

Created 2026-11-11 by Frans Lundberg. Status: decided (2026-11-11):
every question decided (section 8); made in 024-24 and 024-25.

The limits of a transaction (operations, bytes), of a key, of a value
and of a record: what they are today (main, `16759d36`, with 024-07
and 024-10 landed; the same as release 2026.4 in every limit this file
names), what they should be in
release 2026.5, and how each is stated, checked and proved. Frans,
2026-11-11, 10:03: "This is important. Setting limits. I suggest
creating a subitem of 024 to document this."

A study: facts from the code, from the item files and from
measurements; no product code. Limits proposed are L1 to L8 (section
6), alternatives A1 to A6 (section 7), questions QL1 to QL12 (section
8), findings F1 to F12; cite them as "024-17, L2". Reworked from 14:45
for Frans's QL2 (a key at most 112 bytes, 14:45): sections 0, 3, 5, 6,
7, 8 and 9. **Restated from 17:45 for the limits Frans decided at
17:41** (section 8): L1 = 500, L2 = 111, L3 = 56 KiB, L4 = 8 MiB, L5 =
32 MiB, L6 = 111; sections 0, 1, 3, 5.2a, 5.3, 6, 8 and 9. **L9 added
2026-11-28** (section 6.1): BergDB's own keys at most 1,024 bytes each,
decided by Frans that day (031-06, section 8, O1). **Corrected
2026-11-28 (028-72)**: the count with q needs 10 nodes a level at node
size 14 since 028-21, not 9; Java's counts of a delete are today's
(record format 8, since 028-21); and since 031-06 an action's index
nodes are admitted up to 7/8 of the record limit (5.2a, "The action's
7/8"); sections 5.2, 5.2a, 5.3, 8 and 9.


## 0. Summary

* **Today** (section 2) a key, a value and a transaction have no limit
  of their own, only the record's, 2^31 - 9 bytes (005-17): a
  transaction's KVs at most 7/8 of it, the index nodes it can dirty at
  most 15/16 (005-31), the latter decided by the tree it meets, so not
  the same on every database (F1). Our gates use at most 1,000
  operations a transaction but some unit tests (2,000) and perf tests
  (10,000); long keys and values over 16 MiB only in tests of size and
  in the AI-user apps (section 3).
* **Frans's frame** (section 1): user limits checked, internal bounds
  proved ("Yes, sure. Good."); the key's length the one limit a user
  remembers; the others large enough for nearly every use; "Ordinary
  photos should fit"; and at 17:41 "a bit more conservative, possibly
  increasing in a future version".
* **Decided** (Frans, 17:41; section 6): a key at most **111 bytes** as
  stored, 16 segments (a Pub key's UTF-8 with each "/" counted twice, a
  Core key's bytes; "about 100 characters"), and an indexed value's
  levels likewise (L6 = 111, a longer one refused); a transaction at
  most **500 operations** and **32 MiB** of keys and values; a value at
  most **8 MiB**; BergDB's own longer keys (index entries) within **56
  KiB** of key bytes a transaction (500 keys of 111 bytes, rounded up).
  Checked before the go point, the same whatever the database holds;
  nodes dirtied, records and heap are bounds derived from them; the
  record limit stays the format's.
* **At the decided limits** (5.2a): format 7's TP26 as stated today (20
  nodes a level) does **not** cover them: 481 operations of 111-byte
  keys at H = 22, 501 at H = 21, and at node size 62 only 330; with L3's
  index entries it fits only at H <= 19. The count with q (QL8 (a),
  decided) covers them at every node size: 1,199 operations at node size
  30 and H = 22 (2.4 times L1), 742 at 8, 822 at 62, and L3's sum 27 to
  57 % under the record's dirty limit. So the restatement is still
  needed, not only a margin; with it QL12 is gone. A worst record is
  then 0.95 GB at node size 30 (44 % of 2^31 - 9), 1.5 GB at node size
  8 (70 %).
* **F2, why 1,000 (the 14:45 version, for 112 bytes).** The count of
  dirtied nodes is operations x key segments x tree height: a 112-byte
  key is 17 segments (F10: not 16, a key of a multiple of 7 bytes ends
  in an empty segment), the height of any database at most 22 with
  024-11's merges, so a record of 2^31 - 9 bytes takes 1,133 operations
  by 2026.4's form of TP26, 1,128 by a form for format 7 that counts the
  room after a merge (8 nodes a level at node size 30), and **452 by
  format 7's TP26 as stated today** (20 nodes a level, 024-22, 3.4).
  **No form is proved** (F11): TP26 is stated and checked by the runs.
  So L1 = 1,000 rests on restating TP26 for format 7 (QL8): one line of
  `Bound.lean`, 13 % margin at H = 22.
* **F12, node sizes.** A node of size 62 takes 1,056 bytes in the bound,
  not 544, and at 8 a tree can be 61 levels high: at 8 and 62 not even
  Java's own count of one delete on a full path reaches 1,000
  operations (720 and 938 in a record); at 14 and 30 it does (5.2,
  QL12). At the decided L1 = 500 every node size is covered (5.2a).
* **Measured** (section 4, main, 1M and 10M keys): batching does not cut
  a put's bytes past about 100 operations, nor its time (2.7 to 5.3 us),
  F8; a commit of 1,000 operations takes 2 to 6 ms, of 10,000 27 to 90
  ms, of 100,000 0.3 to 1.2 s, so the pause guide's 20 ms is passed near
  4,000. A 16 MiB value's commit holds the write lock 135 to 250 ms and
  a get takes 106 ms, two thirds of both in the node checksum
  (Fletcher-16, 5.7 ms a MB; CRC32C 0.13: F6); a reclaim step moving it
  runs inside some user's commit (F7); a delete alone costs 20 times a
  put (F9).
* **8 MiB holds** every file of this repository but the three source
  zips of releases 2026.2 to 2026.4 (12.7 to 15.6 MB), phone photos of
  12 MP and most of 48 MP, most lossy songs and nearly all documents;
  not 200 MP photos, camera RAW, lossless audio or video (6.8). A commit
  of 8 MiB holds the write lock about 65 to 155 ms today (4.2's 10 MB
  row, scaled), about 25 ms with CRC32C (QL9, decided). Sizes S, M, L of
  databases (Frans, 10:38) are later; 2026.5 keeps the limits as named
  constants and hypotheses (6.9).
* **Questions** (section 8): QL1 to QL12 all decided (QL2 at 14:45,
  the rest at 17:41). None is left for the limits; a lower record limit
  (L7) is not possible with these bounds (1.5 GB at node size 8, 5.3).

## 1. The discussion

All times 2026-11-11.

* It began with 024-11's QU7: with merges at the delete, the simple,
  provable count of dirtied nodes (`dirtyNodeBound`) caps one
  transaction at about 250,000 deletes (024-11, CB2).
* Frans, 09:54: "It is reasonable to limit transactions. Actually, I see
  no reason for a transaction with 250,000 operations. Should we limit
  to 1000 operations? Or 100 operations? Atomic transactions are
  required for payments, other financial transactions (buying shares),
  adding index entries (secondary indexes). Tell me, is there ever a
  need for above 100 keys in a single transaction?"
* The coordinator's answer: yes. The Pub layer multiplies (an object
  with k indexes is up to 1 + 2k KVs); bulk load (in an append-only
  tree the puts of one transaction share the rewritten paths, so batch
  size is the main lever on the bytes a put); all-or-nothing batches (an
  import, a settlement run); deleting a group atomically; building an
  index over existing data. A limit is still right: it bounds per
  transaction the record, the memory, the nodes dirtied and the time the
  single writer is blocked, and it makes the model's cost bounds
  constants. Others, from memory, to be checked here (done in 6.6):
  DynamoDB 100 items a transaction, etcd 128 operations by default,
  Firestore 500 writes, Spanner tens of thousands of mutations,
  FoundationDB 10 MB a transaction with 10 kB keys and 100 kB values.
  Proposed: a limit between 1,000 and 10,000 chosen by measurement, and
  a byte limit.
* Frans, 10:03: "A limit on Core makes sense from an internal point of
  view. But not from the db user's point of view. Perhaps we should
  have both? Something like max 5,000 core operations (each node edited
  is one operation), and max 1000 user operations (KVs). Just
  discussing this for now. Yes, we also need to total transaction size
  limit and value size limit. Suggestions?"
* The coordinator's suggestions, 10:05, the draft that this file tests:
  1. Limits are stated in the user's terms and checked where the user
     can count: the number of operations (KVs put or deleted) and the
     bytes of keys and values of a transaction, a key's length, a
     value's length. They are refused deterministically: the same
     transaction is refused or accepted whatever the database holds.
  2. Internal quantities (nodes edited, the record's bytes, the
     transaction's heap) are not second limits that a user can hit:
     they are bounds derived from the user's limits, as theorems
     (`dirtyNodeBound`; a record's largest size), so that a transaction
     within the user's limits can never be refused for an internal
     reason. Frans's "5,000 core operations" would so be a proved
     consequence of "1,000 user operations", not a check that fails
     depending on the tree's shape.
  3. One invariant for every record, BergDB's own too: no record over
     R_max. Reclaim's steps and the touch are sized to it (the last
     touch's 206 MB record, 024-07, was the case against it; 024-05's
     BD1).
  4. Fixed constants, not settings: a limit can be raised in a later
     release without breaking a database, never lowered, so start low;
     and the format is to be stable in 2026.6 (026).
  5. First numbers, to be replaced by derived and measured ones: a key
     at most about 1 kB (the nodes a KV dirties grow with the key's
     segments of 7 bytes, so the key's limit sets the node bound;
     024-05's OP6 has long keys as quadratic); a value at most 1 MiB; a
     transaction at most 1,000 to 10,000 operations and 16 MiB of keys
     and values; so a record of a few tens of MiB at most, far under
     the 2 GB record limit. Users with more: chunks and a marker
     written last (a documented pattern), large values in chunks.
  6. Two layers: the Core's limit counts KVs; the Pub layer's counts
     what its user writes (objects), with index entries counted in a
     documented way (1 + 2k), or a limit on the indexes of a directory.
* Frans, about 10:20, asked by the coordinator whether "user limits
  checked, internal bounds proved" is what he meant with his two
  numbers: "Yes, sure. Good."
* Frans, 10:18: "About key size. BergDB intentially assumes short keys.
  This was an early tradeoff decision. It uses a variant of a prefix
  tree. At the Pub layers, it is a filesystem, string (filename) to
  bytes (raw bytes, no format required). Each 7 bytes of the key
  consumes a layer in the DAG data structure. Common prefix helps since
  the index nodes of the prefix are likely cached close to the
  processor (L2, L3, BergDB cache), but they still add to the access
  time. 256 is a reasonable limit to key size. I think this is the one
  limit that need to go into the db user's mind. We want to limit the
  cognitive load with things like this. But this is an exception. The
  other limits are typically large enough for nearly all use cases."
* The coordinator's brief from it (10:20): the key limit is 256 bytes
  and the one limit to remember; every other limit generous enough that
  nearly no use case meets it, while the internal bounds stay provable
  constants; lean towards the upper ends, and show what each choice
  implies. Work out what a 256-byte limit means below the user's key:
  the Pub layer's internal keys (index entries), key replace, the Core
  API's keys, the 7-byte segments, what our code uses, and Frans's
  design notes (section 6.2).
* Frans, 10:26: "One more thing about limits. I am thinking that most
  types of files in a filesystem should fit into BergDB. What would
  this mean, do you think? What are the largest files of this repo? I
  think 1 MB is too small for the limit. But 10 MB could work. Ordinary
  photos should fit." The coordinator's facts: the repository has 4,700
  tracked files, 116 MB; 13 over 1 MB, 3 over 10 MB (the source zips of
  releases 2026.2 to 2026.4: 12.7, 13.4 and 15.6 MB), none over 16 MiB.
  Its suggestion: 16 MiB (2^24 bytes), the transaction's byte limit a
  small multiple (64 MiB), R_max a little above; and the brief to work
  out and measure what a value of 10 MB, 16 MiB and 64 MiB means in
  BergDB as it is (section 6.8).
* Frans, 10:38, thinking aloud, "certainly not for 2026.5": "We will
  need a small version of the database if we want it ever fit a RP
  Pico 2. Limits like these would need to be lowered significantly. I
  have not figured this out exactly. But we may end up having databases
  that are S, M, L. Small, medium, large. Small is really tiny. Fits on
  a Pico. M is the default and L for 100M+ KVs and several gigabytes of
  data. Something like this. Different sizes have different
  requirements on the host computer. A computer like this can open
  databases of any size. Perhaps conversions from S to M, and from M to
  L are allowed. Just thinking out loud. Certainly not for 2026.5."
  The coordinator's remarks: see 6.9.
* Frans, 14:40 to 14:45, on the key's length: 150 bytes? 100? 120?
  "Let's make it 112 bytes then." The exchange is at the top of section
  8 (QL2, decided); sections 3, 5 and 6 are reworked for it.
* Frans, 17:41: "I want be a bit more conservative, possibly increasing
  in a future version. So, use: L1 = 500, L2 = 111, L4 = 8 MiB, L5 = 32
  MiB. The rest as recommended." (Section 8, "Decided, the limits";
  this file restated for them from 17:45.)


## 2. Today's limits

From the code of main, `16759d36`; release 2026.4 has the same in every
row (the record format moved to 6 since, not the limits). Paths are
under `java/src/bergdb/`.

### 2.1 The Core: what is refused

| What                  | Limit today                         | Where, how                      |
|-----------------------|-------------------------------------|---------------------------------|
| A record              | 2^31 - 9 = 2,147,483,639 bytes      | `StoredTrans.MAX_RECORD_SIZE`   |
| A transaction's KVs   | 7/8 of it: 1,879,048,178 bytes      | `Db.checkSize`, before go point |
| Its dirtied nodes     | 15/16 of it, at 544 bytes a node    | `Db.checkDirtyNodes` (005-31)   |
| A key                 | none; not null; String key nonempty | `Trans.Builder`                 |
| A value               | none of its own; not null           | `Trans.Builder`                 |
| Operations            | none of their own                   | (only through the two above)    |
| Node size             | 8, 14, 30 (default), 62 klongs      | `DbBuilder`, fixed per database |
| Startup distance      | builder >= 10; set: 400 kB to 1 GB  | `DbBuilder`, `Db.setStartup...` |
| Cache size indicator  | >= 1 byte, default 200 MB           | `DbBuilder`, `Db`               |
| Times                 | 56 bits of units (`Time.MAX`)       | `DbClock`, `StoredTopNode`      |

* **The record limit** (005-17). A record's size field is an int
  (`RecoverableStream`, `MAX_TRANS_SIZE = Integer.MAX_VALUE`), and a
  record is serialized to one `byte[]` (`StoredTrans`, buffer of 1.2
  times the record, at most `MAX_RECORD_SIZE`). `StoredTrans` throws
  "The record of the transaction would take N bytes, more than the
  limit, L (bergdb 005-17)" if a record would pass it; after the go
  point that fails the database, so the two checks below exist to
  refuse before it.
* **The size check** (`Db.checkSize`, 005-17). Sums
  `StoredValueNode.getByteSizeLong(value, key)` over the KVs: a put its
  value and 28 bytes, a delete 24, and each its key, 8 bytes for each
  whole 7 bytes and 8 more. Refused above `valueLimit()` = 7/8 of the
  record limit with `DbException` "The transaction is too large: its
  values and keys take N bytes in the stream, more than L." Before the
  go point, nothing written, the database goes on. A value
  transformation's input is counted; its result, made after the go
  point, must keep within the limit, or the database fails (015-51).
* **The dirty-node check** (`Db.checkDirtyNodes`, 005-31). A cheap
  count first: for each KV `(7 for a delete, 3 for a put) x height x
  segments + 3`, with height = 2 + log2(stream length / 48); only a
  transaction that fails it walks the paths of its keys at the current
  state (`Dag.dirtyNodeBound`, loading nodes). Refused if the nodes,
  each `32 + 16 x (M + 1) + 16` = 544 bytes at M = 30, and two top
  nodes, pass `dirtyLimit()` = 15/16 of the record limit, 2,013,265,912
  bytes: about 3.70 million nodes. `DbException` "The transaction is too
  large: the index nodes it can make dirty or create, up to N, could
  take B bytes in a record, more than L (bergdb 005-31). A larger update
  must be split into transactions." Under the write lock, before the go
  point. A key with a key transformation counts by the cheap rule.
* **Keys** (Db's Javadoc, "Keys and values", 020-24-09): "A key has no
  maximum length, and keys of 300 kB work in every call (bergdb
  021-16)"; it warns that a key costs in proportion to its length, many
  times a value's, and that a commit of a 1 MB key after one of 100 kB
  with the same start took 2.6 to 5.8 s (021-16, Q1; 024-05, OP6).
* **Nothing else.** No count of operations, no limit on a value but the
  transaction's, none on the keys of a transaction, none on the number
  of versions of a key (reclaim and the retain duration decide what is
  kept), none on a stream's length (a long position; files of
  `FileStream`), none on the keys a key transformation makes (024-16
  refuses two that become one).

**F1. The dirty-node refusal is not deterministic for the user.** It
walks the tree the transaction meets: the same 100,000 deletes can be
accepted on a small database and refused on a larger one, and the
cheap count's height grows with the stream's length. Nothing in our
code or tests hits it at real sizes (005-31's test lowers the record
limit); 024-11's merges make it reachable at about 250,000 deletes.

### 2.2 The Core: what is bounded, not refused

* **The startup section.** `TransSeq.take` keeps the startup position
  within `max(2 sd, span)` of the stream's end, and takes a
  transaction's dirty nodes whole, in a later record. A record larger
  than sd makes every start read all of it (024-05, OP7; 020-24-13,
  U13-7): with today's limits a start can read a 2 GB record.
* **The reader of a record.** `NodeStream`'s transaction iterator
  reads each record whole into one `byte[]` of its size, after
  `checkReadSize` checks the size against the stream (005-74). A start
  reads the records from the startup position to the end
  (`Db.readTransactions`) and keeps them in a list: its heap is the
  section, at most about 2 sd, plus the largest record. A reader of a
  2026.4 stream so needs heap of the largest record that stream holds,
  up to 2 GB.
* **The commit's heap.** The KVs as given, their value nodes, the
  record buffer (1.2 times the record, kept between commits:
  `resizeBuffersIfNeeded`), and the dirtied nodes (each in the cache).
  A large object in the Pub layer needs 4 to 5 times its stored size
  (`pub` package doc).
* **The cache budget** (cache size indicator, 200 MB by default) does
  not bound a transaction: the dirty nodes of a transaction stay
  resident until a later record takes them, whatever the budget.
* **Reclaim's steps** are within the value limit by construction
  (`Reclaim.step`, 16 kB of scanned KVs or one KV, `MAX_STEP_SIZE`,
  011-04) and are not checked by `checkSize` (015-50: a refusal inside
  a user transaction's go point would fail the database). Since 024-07
  a step's touch dirties the paths of its own puts only: largest
  record 29 kB at 10M keys, not 206 MB (024-07, section 2).

### 2.3 The Pub layer

* **Objects.** A stored value at most 2^31 - 9 bytes, the largest Java
  array (`ObjectFormat.MAX_ARRAY`; the format allows 2^31 - 1,
  `MAX_STORED`), counted before anything is copied, refused with
  `IllegalArgumentException` naming the place (021-23); a String's
  UTF-8 likewise (020-08). `MAX_FIELDS` 32,767, `MAX_LEVELS` 16,
  `MAX_NAME` 255 bytes (020-07). So one object fits a record only by
  the transaction's 7/8 limit: an object of 1.88 GB to 2 GB passes the
  object check and is refused by `checkSize` (`Connection`'s Javadoc).
* **Index entries.** An object put makes 1 KV, and for each index of
  its directory a delete of the old entry and a put of the new one when
  the levels change (`RwEnvironmentImp`, 494 to 509): up to 1 + 2k KVs
  for k indexes. An entry's key is `/#i/dient/d` + name (at most 255
  bytes) + 8 bytes of generation + levels (at most 4,096 bytes,
  `IndexKeys.MAX_LEVEL_BYTES`) + the object's key: up to about 4.4 kB
  plus the object's key. Above 4,096 bytes of levels a value has no
  entry: not a refusal (020-10, 3.3). At most 8 levels and 16 path
  parts an index (`IndexDefinition`).
* **Index jobs.** A build step reads at most 25 values or 1,000,000
  bytes (`IndexBuilderImp`), a cleanup step deletes at most 100 keys
  (`IndexManager`): BergDB's own transactions, small by construction.
* **020-14's refusals** are of other kinds (X1: a key replace that
  would put into a directory unknown before the transaction's time; X3:
  classes of other packages); none is a size.
* **No limit** on the objects of one `w()` or their bytes, beyond the
  Core's two refusals.

### 2.4 Tests of the limits today

`DbTester` (005-17's 900 kB refused and 800 kB taken, 2251; records near
the limit, 2424; 005-31's 1,000 puts refused, 2339), `StoredTrans`
(1030) and `Reclaim` (1906, 2891), all with `recordLimit` lowered to
100 kB to 1 MB; `LimitsTester` (018-01, 6.4), random transactions at
every limit with restarts; `DbTesterLongKeys` (keys of 100 kB to 1 MB);
`DbTesterStream.testLargeTransaction` (f, a 20 MB value); `PubTester`
(night, a string of 2^31 bytes refused); `DataObjectsTester` (2,100
arrays of 1 MiB refused, 021-23).


## 3. What our own code uses

From a survey of the repository, the C clone and the AI-user apps
(2026-11-11, 10:10). "Breaks" names the limits of 6.1 that it passes
(L1 1,000 operations, L2 a 112-byte key, L4 a 16 MiB value, L5 64 MiB a
transaction); "at L1": exactly 1,000. With 112 bytes (14:55),
`performance.sh`'s long keys of 120 bytes break L2 too (6.2 (e)).
**With the limits decided at 17:41** (L1 500, L2 111 bytes, L4 8 MiB,
L5 32 MiB) the last column is "Breaks, 17:41": every row of 1,000
operations a transaction now passes L1.

| Where                         | Ops a tx | Largest key | Largest value | Breaks, 17:41 |
|-------------------------------|---------:|------------:|--------------:|---------------|
| Unit tests (some)             |    2,000 |        1 MB |       1.5 MiB | L1 L2         |
| f group (`DbTesterStream`...) |      few |       small |         20 MB | L4            |
| Perf group (`Get`, `BigDb`)   |   10,000 |       small |         10 MB | L1 L4         |
| Night (`PayTest`)             |    1,000 |       small |        ~10 kB | L1            |
| Demos (`PayDemo` and others)  |    1,000 |       small |         small | L1            |
| `performance.sh` suites       |      100 |       120 B |      10,000 B | L2            |
| Level scripts                 |    1,000 |       small |       8,000 B | L1            |
| C clone's tests and bench     |    1,000 |       small |   1,000,000 B | L1            |
| AI apps 006-20 (u1 to u12)    |  400,000 |       59 kB |        100 MB | all           |
| AI apps 022-06 (C, u1 to u3)  |   30,000 |      16 MiB |         24 MB | all           |

Where: the unit tests' 2,000 a transaction in `DbTesterGetMany` (1360),
`DbTesterDelete` (137), `PubTesterPrimary` (67), `PubTesterThreads`
(313); values of 1.2 and 1.5 MiB in `Eviction` (2466) and
`CapacityTester` (398); 20 MB in `DbTesterStream.testLargeTransaction`
and `Crazy`; 10,000 a transaction in `Get` and `PerfGetMany`, 10 MB
values in `BigDb`. `PayDemo` (run by `before-commit.sh`) and `PayTest`
put 1,000 objects a `w()`, without indexes on them: 1,000 KVs.
`Perf.java` (`performance.sh`) loads 100 a transaction and no suite
changes it; `LargerThanMemory` (level 4) 1,000. The C clone's `cbench`
1,000 puts of 24-byte keys. Outside the gates: `ObjectBench` 1,000
objects with 100 kB blobs, `PauseProbe` 1,000, `Soak` and
`GoogleQueen` 100. The AI-user apps probed the edges on purpose:
006-20's u9 400,000 KVs and a 100 MB value, u1 a `w()` of about 95 MB,
u11 20,000 puts, u4 1,000 objects with indexes; 022-06's C u1 keys to
16 MiB and 30,000 operations.

**F3.** Every gate (`before-commit.sh`, the level scripts,
`performance.sh`) passes with 6.1's limits except the unit tests of
long keys and of 2,000 operations, `DbTesterStream`'s f test, the
perf group and, with 112 bytes, `performance.sh`'s read suites (keys of
120 bytes), which change; 1,000 operations is exactly what `PayDemo`, `PayTest`,
`LargerThanMemory` and `cbench` use, so the limit must be "at most",
and a Pub layer that counts index entries would refuse `PayTest` if
its objects had indexes. **With L1 = 500** (17:41) these four change
too: `PayDemo` (run by `before-commit.sh`), `PayTest` (night),
`LargerThanMemory` (level 4) and the C clone's `cbench` go to batches
of at most 500 (or 166 objects with one index), and the perf group's
10 MB values (`BigDb`) to at most 8 MiB. Their results stop being
comparable with earlier runs where the batch size shows (bytes a put
and time a commit, 4.1: little change from 500 to 1,000).


## 4. Measurements

On F53 (10 cores, 32 GB), JDK 27, ZGC, main `16759d36` built in the
clone. Probes in `17-limits/`: `LimitProbe.java` (4.1),
`ValueProbe.java` and `CsBench.java` (4.2); outputs `count-*.txt`
(one heavy-run slot, counts), `time-1000000.txt` and `value.txt` (both
slots, times).

### 4.1 Batch size

`LimitProbe`: keys "k" and 11 digits (12 bytes, 2 segments), values of 8
bytes; a database of n keys loaded in order, 1,000 a transaction, the
default builder but `noEvict`, sd 50 MB, a `FileStream` without forced
appends; 200,000 random updates to warm up; then for each batch size b
at least 200,000 updates (at least 3 transactions), of b random keys or
of b consecutive keys from a random start, then deletes (at least 20,000
a row). Columns: stream bytes an operation over the row; got-dirty
nodes an operation (index nodes that became dirty, which the take
writes once); the largest record (the stream's growth in one commit:
its own bytes and what the take wrote); the got-dirty list of that
commit; `Dag.dirtyNodeBound` of the row's first transaction, walked as
`Db.checkDirtyNodes` walks it. The counts ran 11:22 to 11:25 in one
slot (`count-*.txt`); the times are 4.1's second table.

At 10M keys (stream 741 MB after the load), random / consecutive keys:

| Op  | Batch   | B/op      | Dirty/op    | Largest rec kB    | Bound, first      |
|-----|--------:|-----------|-------------|-------------------|-------------------|
| put |       1 | 437 / 641 | 1.34 / 1.45 | 67 / 54           | 7 / 7             |
| put |      10 | 502 / 339 | 1.16 / 0.38 | 111 / 86          | 55 / 8            |
| put |     100 | 301 / 319 | 1.30 / 0.27 | 79 / 100          | 458 / 26          |
| put |   1,000 | 313 / 325 | 1.31 / 0.26 | 566 / 816         | 3,449 / 239       |
| put |  10,000 | 289 / 348 | 1.31 / 0.24 | 5,537 / 5,166     | 23,877 / 2,389    |
| put | 100,000 | 111 / 460 | 1.00 / 0.23 | 17,175 / 62,946   | 146,515 / 23,910  |
| del |       1 | 263 / 193 | 2.08 / 1.66 | 2,622 / 2         | 7 / 9             |
| del |      10 | 126 / 121 | 1.43 / 0.28 | 2 / 2             | 77 / 25           |
| del |     100 | 138 / 131 | 1.30 / 0.12 | 15 / 14           | 613 / 167         |
| del |   1,000 | 159 / 148 | 1.23 / 0.12 | 171 / 155         | 4,522 / 1,588     |
| del |  10,000 | 167 / 172 | 1.16 / 0.15 | 1,769 / 1,739     | 34,232 / 15,803   |
| del | 100,000 | 191 / 263 | 1.02 / 0.20 | 19,198 / 26,379   | 263,672 / 158,312 |

At 1M keys (stream 62 MB) the same shape: 110 to 190 bytes a put at
every batch size, 0.1 to 0.4 got-dirty nodes a put, the largest record
0.2 MB at 1,000 a transaction, 1.9 to 2.9 MB at 10,000, 17 to 24 MB at
100,000.

* **F8. Batching does not cut the bytes a put** past about 100: at 10M
  keys 290 to 350 bytes a put from 100 to 10,000, random or in order.
  The dirty set of the startup section is shared between transactions
  anyway (a node stays dirty until the take writes it, about sd later),
  so a batch adds little sharing: random keys dirty 1.0 to 1.3 nodes a
  put at every batch size; keys in order 1.45 alone and 0.25 from 100
  up. The coordinator's "batch size is the main lever on the bytes a
  put" holds for keys in order up to 100, not beyond.
* **The bound against the walk.** `dirtyNodeBound` walked is 1.5 to 4.5
  nodes an operation of 12-byte keys at 10M keys (deletes the most),
  2 to 3 times what the transaction dirties; TP26's formula (5.2) allows
  386. The got-dirty column also counts the still-dirty nodes that the
  take wrote in the same record and, when one ran last, a reclaim
  step's list (`x.transInfo` after `execute`), so it can pass the
  bound of the first transaction (keys in order, 100,000); it is not
  the bound's quantity.
* **Records.** 1,000 operations: at most 0.8 MB; 10,000: 1.7 to 5.5 MB;
  100,000: 17 to 63 MB. A single delete's record reached 2.6 to 5.8 MB
  when the take wrote a large share in it (BD1's ratio case).
* **Heap while built** (a GC before and after building, first
  transaction of a row): 60 to 90 bytes an operation beside the keys'
  and values' bytes, 8 MiB for 100,000 (ZGC's 2 MiB granularity makes
  the smaller rows noise).

The times, at 1M keys, with both slots (11:56, `time-1000000.txt`): the
build and the `execute` an operation, and the median and largest
`execute` of a row (no sync), random / consecutive keys:

| Op  | Batch   | us/op       | p50 ms          | max ms        |
|-----|--------:|-------------|-----------------|---------------|
| put |       1 | 3.7 / 3.7   | 0.00 / 0.00     | 0.5 / 0.3     |
| put |      10 | 3.4 / 2.7   | 0.02 / 0.02     | 8.7 / 0.6     |
| put |     100 | 4.2 / 2.7   | 0.37 / 0.25     | 7.9 / 0.7     |
| put |   1,000 | 4.5 / 3.1   | 4.09 / 2.96     | 11.4 / 4.2    |
| put |  10,000 | 5.3 / 4.3   | 48.25 / 43.91   | 55.2 / 71.4   |
| put | 100,000 | 5.3 / 4.8   | 521.65 / 448.07 | 528.2 / 502.7 |
| del |       1 | 77.9 / 82.3 | 0.07 / 0.07     | 92.5 / 108.0  |
| del |      10 | 12.6 / 10.7 | 0.13 / 0.10     | 1.1 / 1.1     |
| del |     100 | 5.8 / 2.7   | 0.49 / 0.23     | 7.6 / 1.4     |
| del |   1,000 | 5.4 / 2.8   | 4.07 / 2.36     | 22.7 / 3.3    |
| del |  10,000 | 4.8 / 3.7   | 43.17 / 27.30   | 43.3 / 57.3   |
| del | 100,000 | 5.0 / 3.7   | 429.73 / 323.63 | 429.7 / 323.6 |

* **Batching does not cut a put's time either**: 2.7 to 5.3 us an
  operation at every batch size (no sync; with a sync a commit, the
  sync's cost is shared by the batch, and `sync` is a group commit).
* **The pause guide** (about 20 ms of BergDB's own code; under 50 ms on
  F53 good) is passed between 1,000 and 10,000 operations: 1,000 take
  2.4 to 4.1 ms (the largest 23 ms), 10,000 take 27 to 48 ms (the
  largest 71 ms), 100,000 take 0.3 to 0.5 s. At 10M keys (the counts'
  run, one slot, other work beside it) 1,000 took 5 to 6 ms, 10,000 60
  to 90 ms, 100,000 up to 1.2 s. **So about 4,000 operations is where a
  commit passes 20 ms; L1 = 1,000 keeps every commit within the guide.**
* **F9. A delete alone is slow**: 78 to 82 us an operation at 1M keys
  in transactions of one delete, against 3.7 for a put, with commits up
  to 108 ms (a median of 0.07 ms); 13 us in tens, 3 to 6 from a
  hundred. At 10M keys 38 us. Not a limit's matter; for 024-05 and
  024-11 (the delete's upward unlink and the take of its record: one
  delete's record reached 4.9 MB).

### 4.2 One large value

`ValueProbe`: a database of 100,000 small keys, the default builder
(eviction by budget, cache 200 MB, sd 50 MB, `FileStream` with forced
appends); three puts of one value each, gets, a restart. Both slots,
11:56 (`value.txt`; a first run at 10:32 without the lock gave the same
within 15 %).

| Value  | Commit ms  | Sync ms   | Get ms | Get alloc | Heap after 3 | Restart ms |
|--------|-----------:|----------:|-------:|----------:|-------------:|-----------:|
| 10 MB  |  76 to 183 | 24 to 113 |     65 |     20 MB |        44 MB |        458 |
| 16 MiB | 135 to 250 | 58 to 106 |    106 |     34 MB |        59 MB |        557 |
| 64 MiB | 612 to 883 |  28 to 57 |    425 |    134 MB |       120 MB |        859 |

* **The checksum is most of it (F6).** `NodeChecksum.sum`, Fletcher-16
  with two `%` a byte, takes 96 ms for 16 MiB (`CsBench`, 5.7 ms a MB),
  against 2.1 ms for `java.util.zip.CRC32C` and 2.1 ms for a copy. A
  put checksums its value once (`StoredValueNode`), a get once
  (`NodeStream.readNode`): about 100 of a 16 MiB put's 150 ms and of a
  get's 105 ms. Every node pays it, key nodes too (about 3 us for a
  544-byte node at every write and load). A 16-bit sum also misses one
  corruption in 65,536.
* **A get allocates twice the value** (the node's bytes, then the value
  copied out, `StoredValueNode.parse`) and is never cached: values over
  1 MiB are unswizzled when their record is written and read with
  `CACHE_ALL_EXCEPT_LARGE_VALUE_NODES` (`Eviction`, `GetData`). Ten
  readers of one 64 MiB value at once allocate 1.3 GB.
* **The commit holds the write lock** for the copy into the record
  buffer, the checksum, and the append into `BufferedStream`'s 10 MB
  ring buffer, which waits for the writer thread to drain it when the
  record is larger (`BufferedStream`, 642 to 686): no other commit runs.
* **The record buffer stays** at 1.2 times the largest record until the
  97th commit after it shrinks it (`StoredTrans`, 865 to 897): 80 MB
  after a 64 MiB put.

## 5. The derivation

From the user's limits to every internal quantity, for a transaction
within L1 to L6 (section 6). Notation: n operations (n <= L1), key i of
k_i bytes, s_i = floor(k_i / 7) + 1 its segments (`Keys.toSegments`: a
key whose length is a multiple of 7 ends in an empty segment, so that a
klong of length 7 is always a key node's; k_i <= 112 gives s_i <= 17;
this file said max(1, ceil(k_i / 7)) until 14:55, F10), S the sum of
the s_i, values v_i, the sum of k_i and v_i at most L5. Reworked for
112-byte keys at 14:55; the arithmetic is `17-limits/bound112.py`, its
output `bound112.txt`.

### 5.1 The KVs that reach the tree

* **Key transformations** (Core) and key replace (Pub) change a key at
  the commit; 024-16 makes two that become one a refusal. The limits are
  checked on the keys after the transformation, in `Db.transformKeys`
  (024-16, S2), under the write lock and before the go point, where the
  key is known: still deterministic, as the result depends on the
  transaction's time, not on what the database holds.
* **Index entries** (Pub): an object put is at most 1 + 2k KVs for k
  indexes of its directory (2.3). The Pub layer builds them before it
  calls the Core, so the Core's check counts them, and the Pub layer
  states the rule in its terms (L1).
* **Value transformations** (Core): their result is made after the go
  point (015-51). The input is counted; a result over L4 is the
  caller's fault and fails the database, as a result over 7/8 of the
  record does today (the rule stays; QL6).

### 5.2 Nodes dirtied

* **The count.** 024-12's TP26 (stated, checked by the runs, not
  proved): `dirtyNodeBound` <= the sum over operations of (8 x s_i x (H
  + 2) + 2), H the largest height of a segment tree. So nodes <= 8 (H +
  2) S + 2n. **With merges** (record format 7, 024-21; 024-22, 3.4) it
  is restated as 20 x s_i x (H + 2) + 14 an operation: a delete's four
  klongs in every node of its path, the room q after a merge, and the
  merges' four nodes a level and two levels more. The Lean statement
  (`Limits.dirtyNodes`, `Bound.lean` on 024-22's branch) takes every
  operation at the longest key: maxOps x (20 x maxSegs x (H + 2) + 14).
* **H needs 024-11.** Today a segment tree's height is not bounded by
  its keys: deletes leave nodes nearly empty (024-11's underfill). With
  merges at the delete every node but a root holds at least m live
  klongs (024-11, V1; m = 8 at B = 30 since 14:34, 024-14's QT1; 7
  before), so a tree of K klongs has height at most 1 + log_m(K). A
  stream of under 2^63 bytes holds under 2^60 klongs: **H <= 22 for any
  database** at m = 7, 21 at m = 8. A constant, so the bound is a
  function of the user's limits alone; but it rests on V1, whose proof
  (024-22's TP30) is not made.
* **Format 7's count with q** (mine, 14:50; an argument as CB2's is).
  Java's format-7 `dirtyNodeBound` (024-21, 3.5) counts for a delete at
  each node of its path: the node, four nodes for the merges, and the
  node's overflows and one, at most 2 + k / q for the k klongs it gets
  (four of the delete, the overflows and one of the child below, the
  root collapses' klongs at a segment leaf), q the room after a
  replacement (`roomAfterReplacement`: 10 at B = 30 with 8/17/17, 12
  with 7/15/15). So x = 2 + (4 + x) / q a level, x = 2 (q + 2) / (q -
  1), 2.67 at q = 10: 7.67 nodes a level, and **8 x s_i x (H + 2) + 14**
  holds with the collapses (about H / (q - 1) a segment), the merges'
  two levels more and the new roots. A node shared by several operations
  overflows at most 1 + (their klongs) / q times, under the sum of their
  own counts, so the sum over operations bounds a transaction. TP26 as
  restated (20 a level) holds for every q >= 2, which is why it is loose
  at B = 30. Not in the model, not checked by its runs.
* **Numbers at node size 30.** At most 3,700,852 nodes fit a record's
  15/16 (2,013,265,912 bytes, less two top nodes, at 544 bytes a node,
  2.1). Nodes an operation, and the most operations whose bound fits
  (the last column: the nodes of 1,000 operations, in bytes):

| Count, a segment                  | Key           | H  | Nodes an op | Most ops | 1,000 ops |
|-----------------------------------|---------------|----|------------:|---------:|----------:|
| TP26 of 2026.4, 8 (H + 2) + 2     | 112 B, 17 seg | 22 |       3,266 |    1,133 |   1.78 GB |
| TP26 of 2026.4                    | 112 B         | 19 |       2,858 |    1,294 |   1.55 GB |
| TP26 of format 7, 20 (H + 2) + 14 | 112 B         | 22 |       8,174 |      452 |   4.45 GB |
| TP26 of format 7                  | 112 B         | 19 |       7,154 |      517 |   3.89 GB |
| format 7 with q, 8 (H + 2) + 14   | 112 B         | 22 |       3,278 |    1,128 |   1.78 GB |
| format 7 with q                   | 112 B         | 19 |       2,870 |    1,289 |   1.56 GB |
| Java's count, one delete (a)      | 112 B         | 22 |       2,778 |    1,332 |   1.51 GB |
| TP26 of 2026.4                    | 111 B, 16 seg | 22 |       3,074 |    1,203 |   1.67 GB |
| format 7 with q                   | 111 B         | 22 |       3,086 |    1,199 |   1.68 GB |
| TP26 of 2026.4 (before 14:45)     | 256 B, 37 seg | 22 |       7,106 |      520 |   3.87 GB |
| TP26 of format 7                  | 256 B         | 22 |      17,774 |      208 |   9.67 GB |
| walked, 10M keys (4.1)            | 12 B          | -  |  1.5 to 4.5 |        - |         - |

  (a) Java's format-7 count of one delete on a path of full nodes (no
  room), with the most root collapses, q = 10: the worst case of one
  operation, below which no per-operation count can go. H = 19 is the
  height the first version of this file gave for trees of at most 2^48
  klongs; at m = 8 that is 17. The put's and the delete's sharper counts
  of the first version (3 (H + 1) + 1 and 4 (H + 1) + 2) are dropped:
  format 7's own count of a delete is about 7.7 a level.
* **The coordinator's figures, checked.** "About 192 nodes a segment"
  is 2026.4's 8 (H + 2) at H = 22; 520, 880 and 1,280 operations at
  256, 150 and 100 bytes, and 1,070 at 120 bytes (18 segments), are
  right by that form. **"112 bytes are 16 segments, exactly; about
  1,200 operations" is not**: 112 bytes are 17 segments (F10), 1,133
  operations by 2026.4's form; 1,203 is 111 bytes'. And 2026.4's form
  is not format 7's: with merges as TP26 now states them, 452.
* **F10. 112 bytes are 17 segments.** A key of 7j bytes is j full
  segments and an empty one (`Keys.toSegments`); 111 bytes are the most
  in 16. So also 252 bytes were 37 segments, not 36 as 6.1 said; 251
  were 36.
* **F11. L1 = 1,000 with merges is not covered by a stated count, and
  by no proved one.** TP26 as stated for format 7 covers 452 operations
  of 112-byte keys at H = 22 (517 at 19), so 1,000 is over it by 2.2
  times; 2026.4's form (1,133) is not format 7's count. The count with q
  covers 1,128 (a margin of 12.8 % at H = 22; 1,177 at H = 21, m = 8;
  1,289 at H = 19). Proved is none of them: TP26 and TP23 are
  statements checked by `treetest` and by Java's traces (C-T8), and H
  rests on V1 (TP30). **What L1 = 1,000 needs**: (1) `Limits.dirtyNodes`
  for format 7 restated with q (8 a level at node sizes 30 and 62, 9 at
  14, 10 since 028-21; at 8, 14 a level, 5.2a), a line of `Bound.lean`, and `treetest` and
  `treeconf.sh` run against it, as they run TP26 today (024-22's agent
  or 024-12's); (2) a third field in `Limits`, the segments of a
  transaction (L3), with the sum form (5.6); (3) the proofs of TP23, TP26
  and TP30 for the internal checks to become `Bug`s (QL5): 024-22,
  section 6, puts them after 2026.5's change has settled. Without (1):
  L3 at most 45.7 KiB (5.3) or L1 at most 452 (A4).
* **F12. The node size changes the bound.** `Db.checkDirtyNodes` counts
  each node at its database's largest size, 32 + 16 (B + 1) + 16 bytes,
  and m, q and so H follow B (024-21's thresholds). The first version
  of this file took 544 bytes as the largest, true at B = 30 only. With
  112-byte keys (H = 1 + log_m(2^60)):

| B  | Bytes | m/h/c, q     | Nodes fit |  H | TP26 f7 | With q | Java (a) | Ops: f7, q, Java  |
|----|------:|--------------|----------:|---:|--------:|-------:|---------:|-------------------|
| 8  |   192 | 2/4/4, 2     |   10.49 M | 61 |  21,434 | 13,937 |   14,547 | 489, 752, 720     |
| 14 |   288 | 3/7/7, 4     |    6.99 M | 38 |  13,614 |  6,134 |    6,115 | 513, 1,139, 1,143 |
| 30 |   544 | 8/17/17, 10  |    3.70 M | 21 |   7,834 |  3,142 |    2,659 | 472, 1,177, 1,391 |
| 62 | 1,056 | 16/35/35, 24 |    1.91 M | 16 |   6,134 |  2,462 |    2,032 | 310, 774, 938     |

  "With q": c (H + 2) x 17 + 14 with c = 13, 9, 8, 8 (5 + x rounded
  up; 14 at B = 8 since 5.2a, and 10 at B = 14 since 028-21, so 6,814
  and 1,025 operations there; the column "Java (a)" is format 7's count,
  5.2a gives today's); at B = 8 it is below Java's own count (the collapses, H / q a
  segment, weigh at q = 2), so there the form needs more. **At B = 8
  and 62 no per-operation count reaches 1,000 operations**, not even
  Java's count of one delete (720 and 938); with trees of at most 2^48
  klongs (a stream under 2 PiB) the form with q gives 929 (too low at B
  = 8 itself) and 928. At B
  = 14 and 30 it does. A database of node size 8 or 62 can so meet
  005-31's refusal within L1 to L5 in the worst case, which needs a
  segment tree of 2^48 or more klongs built against the transaction:
  QL12.
* **The bound is loose.** Measured (4.1), a put of a 12-byte key at 10M
  keys dirties 0.25 to 1.45 nodes, and the walked `dirtyNodeBound` is
  1.5 to 4.5 an operation; the worst case
  needs a database of about 2^40 keys built against the transaction
  (each 7-byte level of its keys a full tree). The worst case is what a
  proof must cover; the measured case is what users see.
* **With the touch** (024-07): a reclaim step dirties the paths of its
  own puts only, so it is counted as a transaction of its KVs (5.5).

### 5.2a At the decided limits: 500 operations of 111 bytes

Frans's limits of 17:41 (section 8): L1 = 500, L2 = 111 bytes, 16
segments, and L3 = 56 KiB (6.1). Restated 17:45 from
`17-limits/bound500.py` (output `bound500.txt`; the functions are
`bound112.py`'s).

* **H at node size 30.** With m = 8, 5.2's rule 1 + log_m(K), K < 2^60,
  gives 21; 024-11's BU1 form, 1 + log_m(e / 2), gives 20. 22 (m = 7's)
  is kept as the safe figure, and 19 for comparison.
* **One operation of 111 bytes, node size 30** (3,700,852 nodes fit):

| Count, a level and an operation    | H  | Nodes an op | Most ops | Against L1 = 500 |
|------------------------------------|----|------------:|---------:|-----------------:|
| TP26 of format 7, 20 (H + 2) + 14  | 22 |       7,694 |      481 |           -3.8 % |
| TP26 of format 7                   | 21 |       7,374 |      501 |           +0.2 % |
| TP26 of format 7                   | 20 |       7,054 |      524 |           +4.8 % |
| TP26 of format 7                   | 19 |       6,734 |      549 |           +9.8 % |
| with q, 8 (H + 2) + 14             | 22 |       3,086 |    1,199 |           +140 % |
| with q                             | 19 |       2,702 |    1,369 |           +174 % |
| Java's count, one delete (5.2 (a)) | 22 |       2,983 |    1,240 |           +148 % |

* **Every node size** (H by 5.2's rule; "with q": the nodes a level of
  the count with q, then the most operations):

| B  |  H | TP26 of format 7 | With q   | Java, one delete |
|----|---:|-----------------:|----------|-----------------:|
| 8  | 61 |              519 | 14: 742   |              760 |
| 14 | 38 |              545 | 10: 1,089 |            1,205 |
| 30 | 21 |              501 | 8: 1,251  |            1,296 |
| 62 | 16 |              330 | 8: 822    |              866 |

  At node size 8 the count with q needs 14 a level, not 13 (5.2's
  F12 table): Java's count of one delete there is 13,789 nodes at 16
  segments (14,658 at 17), the root collapses' H / q weighing at q = 2;
  14 x 16 x 63 + 14 = 14,126 covers it (and 15,008 at 17 segments).
  At node size 14 it needs 10 a level since 028-21, which added the new
  roots above a cut segment root, 3 a tree there: Java's count of one
  delete of 16 segments is 5,797, above 9's 5,774; 10 x 16 x 40 + 14 =
  6,414 covers it.
* **Corrected 2026-11-28 (028-72).** Java's counts of one delete in the
  two tables above are today's, measured on the worst path (028-72's
  `ActionRoomProbe`: every segment tree on the path H + 1 key nodes
  high, every node full); until 2026-11-28 they were format 7's (2,615,
  and 766, 1,215, 1,478 and 996 operations), and the count with q at
  node size 14 was 9 a level (1,210 operations). On that path Java
  counts a middle segment 869 nodes at node size 8 (13.79 a level), 365
  at 14 (9.12), 186 at 30 (7.75) and 137 at 62 (7.61), within 14, 10, 8
  and 8 a level. `DagTester.testDirtyNodeBoundOfTheWorstPath` checks
  Java's count on that path against c (H + 2) S + 14 n with these c, so
  that a change that raises the count fails a unit test.
* **With L3** (BergDB's longer keys; S <= L3 / 7 + 500; per cent under
  the record's dirty limit, TP26 of format 7 / with q, H by the rule):

| L3     | Keys of 111 B |     S | B = 8     | B = 14    | B = 30    | B = 62    |
|--------|--------------:|------:|-----------|-----------|-----------|-----------|
| 48 KiB |           442 | 7,521 | +10 / +37 | +14 / +57 | +6 / +62  | -42 / +43 |
| 52 KiB |           479 | 8,106 | +3 / +32  | +7 / +54  | -1 / +60  | -53 / +38 |
| 54 KiB |           498 | 8,399 | -1 / +29  | +4 / +52  | -5 / +58  | -59 / +36 |
| 56 KiB |           516 | 8,692 | -5 / +27  | +0 / +50  | -8 / +57  | -64 / +34 |
| 64 KiB |           590 | 9,862 | -19 / +17 | -13 / +43 | -23 / +51 | -87 / +25 |

  (At B = 14 with 10 a level since 2026-11-28, 028-72; with 9, +61, +58,
  +57, +55 and +49.)

* **So TP26 as stated does not cover the decided limits.** At node size
  30 it covers 500 operations of 111-byte keys only if H <= 21 (0.2 %;
  4.8 % at BU1's H = 20), not at 22; at node size 62 nowhere (330); with
  BergDB's longer keys within L3 = 56 KiB at no node size but 14, with
  0 %. It would need L3 <= 49.2 KiB at H = 22, under L1 x L2 itself
  (55,500 bytes). **QL8's restatement (decided, (a)) is still needed,
  not only a margin.**
* **With q every node size is covered**: 1.5 (node size 8) to 2.5 (30)
  times L1 for one operation, and 27 to 57 % under the dirty limit with
  L3 = 56 KiB. One L1 for every node size (QL12 (a), decided) is so
  provable at 8, 14, 30 and 62 alike, and L8 can become a `Bug` at every
  node size once the count is proved (QL5). The restatement for format
  7 (F11's (1)) is then 14 a level at node size 8, 9 at 14 (10 since
  028-21), 8 at 30 and 62.
* **The action's 7/8** (since 031-06, 2026-11-27; 028-72, 2026-11-28).
  An action's index nodes are admitted up to 7/8 of the record limit
  (`StoredTrans.actionDirtyLimit()`, 1,879,048,185 bytes), not 15/16.
  `Db` compares Java's count (`Dag.dirtyNodeBound`) with it, not a
  formula. The worst transaction within L1 to L5 for that count is 500
  deletes of keys whose bytes sum to L3 (8,692 segments) on the worst
  path at H = 61: 7,488,343 nodes at node size 8, 76.5 % of the 7/8; at
  14, 30 and 62 (H = 38, 22, 16), 48.2, 46.8 and 66.9 %. So no
  transaction within L1 to L5 is refused by it. The count with q (14,
  10, 8, 8 a level) gives 78.4, 53.4, 48.5 and 70.7 %. The Lean's
  `Params.nodesALevel` (19, 13, 11, 11 since 028-21) is a looser bound
  of the same count, by which the worst action is 106.4 % of the 7/8 at
  node size 8, so `releaseFits8` shows only that it fits 15/16; its
  restatement from Java's count waits for the next change of
  `Bound.lean` (028-72, B).
* **L3 = 56 KiB** (57,344 bytes, 516 keys of 111 bytes): by the rule of
  6.1, L1 keys of L2 bytes never meet it (500 x 111 = 55,500 bytes,
  54.2 KiB); 54 KiB (55,296) would refuse 500 keys of 111 bytes, so 56
  KiB is the next round value.

### 5.3 A record's bytes

* **Own bytes**: the KVs, each its key, value, 28 bytes for a put (24
  for a delete) and 8 bytes for each whole 7 bytes of key and 8 more
  (`StoredValueNode`): at most L5 + n (8 + 44) + (key bytes) / 7, about
  67.2 MB at L5 = 64 MiB and n = 1,000.
* **Taken nodes**: `TransSeq.take` writes the dirty nodes of earlier
  transactions, each transaction's whole, into the record, up to the
  record limit less the own bytes. So a record must be able to hold one
  transaction's dirty set whole beside another's own bytes: R_max >=
  67.2 MB + 1.89 GB = 1.96 GB at n = 1,000 with the delete's sharper
  count: within 2^31 - 9 by 9 %. With L3's 256 KiB of BergDB's own
  longer keys, S <= 38,450 and 3.61 million nodes, 1.96 GB: within the
  dirty limit's 2.01 GB by 2.5 %. Tight: the proof has no room for a
  looser count. (The first version's numbers, for 256-byte keys.)
* **With 112-byte keys** (14:55, node size 30, H = 22). L3 = 112 KiB
  (6.1) gives S <= 114,688 / 7 + 1,000 = 17,384 segments. By the count
  with q (5.2), 8 x 24 x S + 14 n = 3,351,728 nodes, 1.82 GB: within the
  dirty limit by 9.4 % (20.7 % at H = 19); with the own bytes, 67.2 MB,
  a record of at most 1.89 GB, within 2^31 - 9 by 12.0 %. By 2026.4's
  form of TP26, 3,339,728 nodes (9.8 %). By format 7's TP26 as stated,
  8,358,320 nodes, 2.26 times the limit: with that count L3 can be at
  most 45.7 KiB at n = 1,000 (40 KiB: S <= 6,851, 3,302,480 nodes, 10.8
  % under), so 365 keys of 112 bytes a transaction.

| L3      |      S | TP26 of 2026.4 |    With q | TP26 of format 7 | Under the limit, with q |
|---------|-------:|---------------:|----------:|-----------------:|------------------------:|
| 40 KiB  |  6,851 |      1,317,392 | 1,329,392 |        3,302,480 |                  64.1 % |
| 64 KiB  | 10,362 |      1,991,504 | 2,003,504 |        4,987,760 |                  45.9 % |
| 112 KiB | 17,384 |      3,339,728 | 3,351,728 |        8,358,320 |                   9.4 % |
| 120 KiB | 18,554 |      3,564,368 | 3,576,368 |        8,919,920 |                   3.4 % |
| 128 KiB | 19,724 |      3,789,008 | 3,801,008 |        9,481,520 |                  -2.7 % |

  Nodes at H = 22 and n = 1,000; the limit is 3,700,852. The most L3
  that the count with q allows is 124.4 KiB (143.2 KiB at H = 19).
* **At the decided limits** (17:45; L1 500, L3 56 KiB, L5 32 MiB). Own
  bytes at most L5 + 500 x 52 + L3 / 7 = 33,588,624 (33.6 MB). One
  transaction's dirty set by the count with q (5.2a), each node at its
  largest, and the record with the own bytes:

| B  |     Nodes | Dirty set |  Record | Of 2^31 - 9 |
|----|----------:|----------:|--------:|------------:|
| 8  | 7,673,344 |   1.47 GB | 1.51 GB |      70.2 % |
| 14 | 3,483,800 |   1.00 GB | 1.04 GB |      48.3 % |
| 30 | 1,675,864 |   0.91 GB | 0.95 GB |      44.0 % |
| 62 | 1,258,648 |   1.33 GB | 1.36 GB |      63.5 % |

  By TP26 as stated, at node size 30, 2.31 GB: over the record limit.
  So the record limit stays the format's (F4): halving it to 2^30
  would not hold at node sizes 8 and 62.
* **F4: no provable record limit of "a few tens of MiB".** The record
  limit stays the format's 2^31 - 9 bytes, the bound proved under it.
  The guide for real records stays 024-05's BD1 (no record over the
  larger of 1 MB and 5 times the mean, own values apart), measured, not
  proved. A smaller R_max needs A3.

### 5.4 Heap

* **While built**: a `Kv` a operation with its key, its segments and
  its value: measured about 76 bytes an operation besides the bytes of
  keys and values (section 4); at the limits, 64 MiB and 76 kB.
* **While committed**: the record buffer, 1.2 times the record, kept
  between commits; the dirtied nodes, each resident until taken; the
  value nodes. At the limits, about 80 MiB and the nodes.
* **A reader** (a start, reclaim's scan of a record) holds one record
  whole: the largest record of the stream. A start holds the section,
  about 2 sd, and the largest record.

### 5.5 BergDB's own transactions

* **A reclaim step** scans at most 16 kB of KVs, or one KV
  (`MAX_STEP_SIZE`), and adds its row: at most about 455 KVs of the
  smallest size (36 bytes), key bytes under 16 kB: within L1 and L3; its
  one large KV within L4 since the user's was. So the same bound covers
  it, without a check of its own (and `checkSize` must not run inside a
  go point, 015-50).
* **Index jobs**: a build step at most 25 values or 1 MB, a cleanup
  step 100 deletes: within L1 to L5, entries within L3 and L6.
* **`setStartupDistance`**: one value of 200 kB: within L4.

### 5.6 What the Lean model can state

* **Today**: nothing of it. 024-06 lists `dirtyNodeBound` and the record
  limit as not modelled ("N").
* **With 024-12** (the tree): `Limits` (the most operations, the most
  segments) and `Tx.within`; TP26 bounds `dirtyNodeBound` by the limits;
  TP23 bounds the nodes marked by `dirtyNodeBound`. The tree needs S
  (or L3) in `Limits`, beside the most segments of a key: F2. Today
  `Limits.dirtyNodes` is maxOps x (20 x maxSegs x (H + 2) + 14) in
  format 7: every operation at the longest key. With L2 = 112, maxSegs
  = 17; with L3, a third field (the segments of a transaction, 17,384
  at 112 KiB) and the sum form, 8 (H + 2) S + 14 n with q (F11).
* **With 024-11**: V1 gives H <= 1 + log_m(K) (TH3's count).
* **Not the tree's**: L4 and L5 are counts of bytes in a record;
  `TransSeq.take`'s model (007-08's `T3_take`) leaves the record limit
  out, so "a record never passes R_max" is a Java check, tested.


## 6. Proposal

Third version, 2026-11-11, 10:45, after Frans's 10:18 on keys and
10:26 on files (section 1); checked against section 4 at 12:00. Fourth
version, 14:57, after Frans's QL2 of 14:45 (a key at most 112 bytes).
**Fifth version, 17:45: the limits Frans decided at 17:41** (section 8:
"a bit more conservative, possibly increasing in a future version");
L1, L2, L4 and L5 are his numbers, L3 and L6 follow by the rules of the
fourth version. The fourth version's reasons for 1,000 operations, 112
bytes, 16 MiB and 64 MiB are in Git (`562f6d22`).

### 6.1 The table

Each limit is a fixed constant of the release (6.3), checked before the
go point, so a refused transaction leaves nothing and the database goes
on, as today's two refusals do.

| ID | Limit                         | Value    | Checked where, refused with            |
|----|-------------------------------|----------|----------------------------------------|
| L1 | operations a transaction      | 500      | `Db.execute`, `DbException`            |
| L2 | a key's bytes, as stored      | 111      | at the put: Pub `u2i`, Core builder    |
| L3 | key bytes of a transaction    | 56 KiB   | `Db.execute`, `DbException`            |
| L4 | a value's bytes               | 8 MiB    | at the put, `IllegalArgumentException` |
| L5 | keys and values a transaction | 32 MiB   | `Db.execute`, `DbException`            |
| L6 | an indexed value's levels     | 111      | Pub, at the put of the object          |
| L7 | a record (internal)           | 2^31 - 9 | a theorem from L1 to L5; `Bug` if hit  |
| L8 | nodes dirtied (internal)      | derived  | a theorem; 005-31's check as `Bug`     |
| L9 | an own key's bytes (internal) | 1,024    | the internal calls, `Db.execute`       |

* **L1, operations.** At most 500 (Frans, 17:41). The KVs put or
  deleted, as the Core gets them: after the builder's rule (one
  operation a key as written, 024-10) and with the Pub layer's index
  entries (1 + 2k for an object put, k the indexes of its directory: so
  500 objects without indexes, 166 with one). Counted at
  `Trans.Builder.build`, refused by `Db.execute` before the write lock:
  "The transaction has N operations, more than 500 (bergdb 024-17, L1).
  Split it into transactions." The node bound with q fits a record at
  500 operations of 111-byte keys with 1.5 to 2.5 times to spare, at
  every node size (5.2a); TP26 as stated today does not (QL8's
  restatement, decided, is needed). A commit of 500 takes about 1 to 3
  ms (half 4.1's 1,000), well within the pause guide; batching gains
  little past 100 (F8); five times DynamoDB's and Cosmos DB's 100
  (6.6). The gates' batches of 1,000 change (F3).
* **L2, a key.** At most 111 bytes as stored (Frans, 17:41; 112 at
  14:45, QL11): 16 segments, the most a key of 16 has (F10: a key has
  floor(k / 7) + 1 segments, so 112 bytes would be 17, the last one
  empty). For a Pub key the UTF-8 of the key as the user writes it
  ("/dir/name") and one byte more for each part (its ikey,
  `PubKeys.u2i`: a "/" counts two), for a Core key its bytes
  (`put(byte[], ..)`, the UTF-8 of `put(String, ..)`, the bytes of
  `put(long[], ..)` as `Keys.toBytes` gives them). Refused at the call
  that takes the key, `IllegalArgumentException` ("The key has N bytes,
  more than 111 (bergdb 024-17, L2)"), so the place shows in the stack.
  **For users** (`Db`'s and the `pub` package's Javadoc, the release
  notes): "A key is at most 111 bytes; about 100 characters as a rule
  of thumb: ASCII letters and digits one byte each, each "/" of a Pub
  key two, letters such as å, ä and ö two bytes each (UTF-8)." The rule
  of thumb still holds: "/customers/12345678" is 21 bytes, a Pub key of
  100 ASCII characters with up to 11 "/" fits, a name of 50 Swedish
  letters, a quarter of them å, ä or ö, is about 63 bytes. The format
  stores no key length in a byte, so 111 is not tied to a byte's 255:
  it is 16 segments of 7 bytes less one (the fourth version's note on
  256 and 255, and on 252 bytes being 37 segments, not 36, stands).
* **L3, the key bytes of a transaction.** At most 56 KiB (57,344 bytes,
  516 keys of 111 bytes), the sum of the keys' bytes as the Core gets
  them. The rule (fourth version): L1 keys of L2 bytes never meet it;
  500 x 111 = 55,500 bytes (54.2 KiB), so 54 KiB would refuse them and
  56 KiB is the round value above. It binds only on BergDB's own longer
  keys, the index entries (6.2 (a)). It makes the node bound a sum (F2):
  S <= 57,344 / 7 + 500 = 8,692 segments, 1.68 million nodes at node
  size 30 and H = 22 by the count with q, 57 % under the record's dirty
  limit; 27 % at node size 8, 34 % at 62 (5.2a).
* **L4, a value.** At most 8 MiB (2^23 bytes; Frans, 17:41), at the put
  (Core builder; Pub: the stored value of an object or of raw bytes
  alike, counted before it is copied, as 021-23 counts it today against
  2^31 - 9). Every file of this repository but the three release source
  zips, phone photos of 12 MP and most of 48 MP, most lossy songs, most
  PDFs and office files fit (6.8). Half MongoDB's document, under
  Spanner's 10 MiB cell, over DynamoDB's 400 KB item and Firestore's 1
  MiB document (6.6). A value transformation's result over it fails the
  database as today (015-51; QL6). Costs at the limit (6.8): a commit
  about 65 to 155 ms today, about 25 ms with CRC32C (QL9, decided); the
  checksum alone 48 ms with Fletcher-16, 1.1 ms with CRC32C (F6).
* **L5, the bytes of a transaction.** At most 32 MiB of keys and values
  (Frans, 17:41; `checkSize`'s count, in the user's bytes instead of the
  stream's). Four values at the limit. A record's own bytes then at most
  33.6 MB (5.3).
* **L6, an indexed value.** At most 111 bytes of encoded levels (today
  4,096, `IndexKeys.MAX_LEVEL_BYTES`), a longer value's put refused
  (QL4, decided as recommended). **111, not 112:** the recommendation
  of 112 was "one number for everything that becomes a key", and the key
  is now 111; the byte makes no difference to the bound (an entry of
  497 or 498 bytes, 72 segments either way, 5.2a's `bound500.txt`). An
  index entry is a key, so the indexed value is limited as one. A
  string level is its UTF-8 and one byte (a terminating 00, each 00 or
  01 in it written as two, `IndexKeys`), a long or a double 8 bytes: one
  string level of up to 110 bytes, or a long and a string of up to 102.
  **The trade-off** (fourth version): e-mail addresses may have 254
  bytes (RFC 5321's 256 of a path less its brackets), nearly all are
  under 100, so a few cannot be indexed as they are; URLs often pass 111
  bytes (query strings, signed links). An application indexes such a
  value by a hash of it (a `bytes` level of 32) or by a prefix as a
  second, non-unique level, and checks the object it finds.
* **L7 and L8** are not limits a user can meet: Java keeps today's
  checks (`StoredTrans`'s record check, `Db.checkDirtyNodes`), but as a
  `Bug` (an internal error, a failure of BergDB) once the bound is
  proved, since a transaction within L1 to L5 cannot reach them.
  Until the proof, they stay refusals that tests show unreachable.
* **L9, one of BergDB's own keys** (added 2026-11-28; decided by Frans
  that day, option (b) of 031-06's O1, section 8). A key under "/#"
  longer than L2, which only Trans.Builder's internal calls
  `putLongKey` and `deleteLongKey` take, has at most 1,024 bytes, 147
  segments (`Db.MAX_OWN_KEY_BYTES`, package-private: no user can put
  such a key, and the Pub API does not change). Until then such a key
  was bounded only by L3, 57,344 bytes, 8,193 segments. Checked at the
  internal calls (`Trans.Builder.checkLongKey`,
  `IllegalArgumentException`: "The key, one of BergDB's own, has N
  bytes, more than 1024 (bergdb 024-17, L9)"), in `Db.checkLimits` for
  a KV set in `Trans.kvs` and in `Db.transformKeys` for a key that a key
  transformation gives (`DbException`), before the go point; not at
  reclaim's copies or at a start, which take a longer own key that a
  stream written before L9 holds. The longest own key BergDB writes is
  a Pub index entry, 275 + L6 + L2 - 1 = 496 bytes, 71 segments (11 +
  255 + 1 + 8 + 111 + 110; 6.2 (a) counted the file part as 111, 497
  bytes: the file part of an ikey of 111 bytes has at most 110, its
  first "/" being the root's), then a deletion's marker (284) and a
  definition (266). **The rule**: a raise of L2, L6 or the index name's
  255 bytes keeps 275 + L6 + L2 - 1 at most L9 (with L9 = 1,024, L2 and
  L6 can each go to 375); `PubTesterIndexJobs.testLongestOwnKeysWithinL9`
  puts such an entry and fails if the Core refuses it. With L9 one key's
  index nodes are bounded by 147 segments, a 56th of L3's 8,193 (at
  node size 8 about 25 MB in place of 1.39 GB, by 031-06's count), and
  031-06's bound on a step's last KV holds by the check (its section
  3). A transaction's segments stay L3's sum (5.2a; the Lean's
  `Limits.release.segments`), so the bounds of section 5 do not change.

### 6.2 A 111-byte key, below the user's key

* **(a) The Pub layer's own keys.** A Pub key "/a/b/name" becomes an
  ikey with one prefix byte a part ("d" for a directory, "-" for the
  file, `PubKeys.u2i`): L2 counts the ikey, so that the user's limit
  and the Core's are one number (the alternative, 111 bytes of UTF-8,
  makes Core keys of up to 166 bytes and breaks L3's sum, 5.3). The
  Pub's Javadoc says it as: at most 111 bytes of UTF-8, each "/"
  counted twice (L2's wording for users). An index entry (020-10, 4.1)
  is `/#i/dient/d` (11 bytes), the index name (at most 255), "/", the
  generation (8 bytes), the levels (at most 4,096 today) and the
  object's file part with its "-" (within the ikey's 111): today up to
  4,482 bytes. **So L2 is the user's limit, not every Core key's**: the
  Core takes BergDB's own keys longer, and L3 bounds what they add. With
  L6 at 111 (17:45) an entry is at most 11 + 255 + 1 + 8 + 111 + 110 =
  496 bytes, 71 segments (the object's file part is at most 110, as the
  ikey begins with "/"; 497 and 72 until 2026-11-28, 028-72; at 256: 642
  bytes, 92 segments), and an object with k indexes adds at most 2k x
  496 bytes to L3. Objects of one transaction, with entries all at the
  largest: 51 with one index (57,344 / (111 + 2 x 496)), 27 with two; with short entries L1 binds
  first, 500 / (1 + 2k) objects (166 with one index). (The fourth
  version, at L1 1,000 and L3 112 KiB: 103, 54 and 333.) The index
  name, up to 255 bytes, is the largest part of an entry: a limit of 64
  bytes on it would make the largest entry 306 bytes and 103 objects
  with one index; a later choice, not needed for the bound. The Core tells its own keys from the
  user's by the call: the Pub layer puts entries through an internal
  builder call that checks L3 but not L2.
* **(b) Key replace** (`${transactionTime}`, Pub) and Core key
  transformations. The Pub layer checks L2 at the put on the longest
  key the replace can give (the template with the time's 19 digits), so
  the refusal does not depend on the time; a Core key transformation's
  result is checked in `Db.transformKeys` (024-16, S2), before the go
  point.
* **(c) The Core API's keys.** L2 for every public put and delete;
  `long[]` keys are checked by their bytes.
* **(d) The 16 segments.** A key of 111 bytes crosses 16 segment trees
  (F10); every one on its path can be dirtied, with a split in each
  level: `dirtyNodeBound` an operation is up to 3,086 nodes at node size
  30 and H = 22 by the count with q, 7,694 by format 7's TP26 as stated
  (5.2a). These numbers, not the time of a get, are what makes L1
  small.
* **(e) What changes in code and tests** (a grep of main `a7a8f7e4`,
  14:50 to 14:54, for 112 bytes; restated 17:45 for the decided limits:
  111 bytes, 500 operations, 8 MiB; no edits; a full list comes with the
  implementation, when the checks fail every test that passes them):
  * **Long-key tests of the Core and Pub:** `DbTesterLongKeys` (119
    lines, 3 tests, keys of 100 kB to 1 MB), `PubTesterLongKeys` (a key
    of 200 kB), `DbTesterJavadoc` (434: a key of 3,000 bytes), and
    `Db`'s Javadoc (122: "A key has no maximum length, and keys of 300
    kB work"): to tests of the refusal at 112 bytes and of 111 at every
    node size. `DagTester.testLongKeyWalks` (462: 400 kB) is below the
    check (the Dag has no limit) and can stay.
  * **`LimitsTester`** (1,035 lines): `longKey()` (559, lengths 20 to
    3,006 bytes, used at 585 and 708) to 1 to 111 bytes, a 112 refused;
    its transactions and values to L1 and L4.
  * **Index tests at 4,095 and 4,096 bytes of levels**:
    `IndexDefinitionTester` (555 to 581, 729, 799: 12 lines),
    `IndexReference` (60, 334, 915, 916), `IndexHarness` (180, 181),
    `FormatFuzzer` (2101); the constant `IndexKeys.MAX_LEVEL_BYTES` (65)
    and `IndexBuilder`'s Javadoc (48): to L6 and, with QL4, a refusal.
  * **`performance.sh`**: its read suites put long keys of `longlen` =
    120 bytes, 18 segments (`Perf.java` 89; `read-100`, `read-1k`,
    `read-10k` in `performance.suite` 27 to 29, `read-1k` in
    `performance-quick.suite` 5, `read-s` in `performance-smoke.suite`
    5): L2 refuses them, so the default must become at most 111. **The
    long-key results (gets, scans, the mixed phase) then stop being
    comparable** with earlier runs, 2026.4's baseline included: 16
    segments a key, not 18. Recommended: 111, the longest key a user
    can make, and a line in the suite's history; the short-key suites
    are unchanged (they load 100 a transaction, within L1). `Soak` (94,
    `longlen` 120, outside the gates) the same.
  * **Batches of 1,000** (L1 = 500, F3): `PayDemo` (run by
    `before-commit.sh`), `PayTest` (night), `LargerThanMemory` (level
    4), the C clone's `cbench`; the unit tests of 2,000 a transaction
    (`DbTesterGetMany` 1360, `DbTesterDelete` 137, `PubTesterPrimary`
    67, `PubTesterThreads` 313) and the perf group's 10,000 (`Get`,
    `PerfGetMany`), as before; `ObjectBench`, `PauseProbe` (1,000,
    outside the gates).
  * **Values over 8 MiB** (L4): `BigDb`'s 10 MB (perf group),
    `DbTesterStream.testLargeTransaction` and `Crazy` (20 MB), as
    before for 20 MB.
  * **AI-user apps** (006-20, `/Users/f/fl/bench/2026-11-09/app-u1` to
    `u12`, outside the repository: keys up to 59 kB; 022-06's C apps:
    keys to 16 MiB): their next round expects the refusal.
  * **The C clone** (022): follows release 2026.4 (015-02); when it
    takes the limits, `src/db.c` (`check_size` 717, `check_dirty_nodes`
    791) and its long-key tests, 45 lines in 14 files of `c/test` (most
    in `t_klong.c` 8, `f_api.c` 7, `t_limits.c` 7).
  * **`docs/levels.md`**: no key length today; section 3's refusals
    (143, 403 to 405) gain L1 to L6 when they are built.
  * **Not affected:** the level scripts' and conformance sets' long
    keys (`/longer/key/` + i, `/long/` + i, `/longkey/number-` + i:
    under 30 bytes), `CapacityTester`'s "keys of 300 bytes" (300-byte
    values, keys "k" + k), `cbench` (24 bytes).
* **(f) The original trade-off.** Frans's note "Segmented keys" (F1-007
  notes, 2012-02): "We want to store keys that often have a prefix
  common with other keys, potentially long (10-100) prefixes. [...] The
  idea here is to segment the key into 7-byte "key segments"." His
  note of 2012-05 on lookups: "But the problem would be worse for long
  keys. For 40 byte longer keys, we would double the number of lookups
  and increase from 2.0 us to 3.6 us (still OK). For 80 byte keys, we
  get 4.4 us." Keys of tens of bytes, prefixes of 10 to 100, were the
  design point; 112 bytes keeps it with a little room (256 was well
  above it).

### 6.3 Fixed, not configurable

* **Fixed constants** in `Db` (and the C clone), documented in `Db`'s
  and the `pub` package's Javadoc, "Limits". Not settings: a setting
  that a database could raise would make the bounds of 5 depend on it
  and the model's constants parameters; one that lowers is a
  convenience an application can have by its own check.
* **Raise later, never lower.** A later release can raise a limit
  without breaking a database: every stream it reads was written
  within the old limits. Lowering would refuse to read, or to rerun,
  records of older transactions. So start at what the proof allows
  today, and raise when a sharper count is proved (A1).
* **The format** is to be stable in 2026.6 (026): the limits are not in
  the format, except that a reader may refuse a record over L7 (6.5).

### 6.4 BergDB's own records

Reclaim's steps, the touch (024-07) and the index jobs are within L1,
L3 and L5 by construction, and a step's one large KV within L4 (5.5):
the same bound covers them, with no check of their own (015-50); a
night test asserts it on the largest step. The take's record is within
L7 by its byte budget, and one transaction's dirty set fits it (5.3).

### 6.5 Databases and streams of 2026.4

* 2026.5 may refuse 2026.4's databases (Frans, 2026-11-11, 07:23), and
  a new record format does (024-13). So 2026.5 never reruns a 2026.4
  transaction that is over L1 to L5.
* **What a reader does with an old large record.** A start reads the
  record that the last meta block names whole, into one `byte[]`
  (`NodeStream`'s iterator), before it parses the format byte: a start
  of 2026.5 on a 2026.4 stream whose last record is 1.5 GB needs 1.5 GB
  of heap to refuse it. Recommended: read a record's header first
  (size, format byte), refuse another format before reading the rest,
  and refuse a size over L7 as corrupt (`checkReadSize`, 005-74, gains
  the bound). (F5.)
* The C clone (012) follows 2026.4 (015-02); it takes the limits with
  the format, later.

### 6.6 What other databases do

From each one's documentation, read 2026-11-11 (quotes in the agent's
notes; "-" where the documentation gives none).

| Database     | Ops a tx      | Bytes a tx     | Key max         | Value max       | Fixed? |
|--------------|---------------|----------------|-----------------|-----------------|--------|
| DynamoDB     | 100           | 4 MB           | 2,048 B (part.) | 400 KB item     | fixed  |
| Cosmos DB    | 100 (batch)   | 2 MB, 5 s      | 2,048 B (part.) | 2 MB item       | fixed  |
| etcd         | 128 (default) | 1.5 MiB        | -               | in the request  | config |
| Firestore    | none (500 to 2023) | 10 MiB    | 6 KiB name      | 1 MiB document  | fixed  |
| Spanner      | 80,000 mut.   | 100 MiB        | 8 KiB           | 10 MiB cell     | -      |
| FoundationDB | -             | 10 MB, 5 s     | 10,000 B        | 100,000 B       | lower only |
| TiDB         | none (300,000 to v4.0) | 100 MiB | -        | 6 MiB entry     | config |
| MongoDB      | -             | 16 MB an oplog entry, 60 s | - | 16 MiB document | config |
| LMDB         | dirty pages   | map size       | 511 B           | 4 GB            | compile |
| SQLite       | -             | -              | in the row      | 1e9 B           | lower only |

Sources: the limits pages of DynamoDB (Constraints), Cosmos DB
(concepts-limits), etcd (op-guide/configuration), Firestore (quotas;
release notes of March 2023: "Firestore no longer limits the number of
writes"), Spanner (quotas), FoundationDB (known-limitations: "Keys
cannot exceed 10,000 bytes in size"; its developer guide: "sizes above
1 kB should be avoided"), TiDB (tidb-configuration-file), MongoDB
(transactions-production-consideration), LMDB (mdb docs), SQLite
(limits.html: "Because the upper bounds were not well defined, they
were not tested, and bugs were often found when pushing SQLite to
extremes"). The proposal sits between the small fixed limits of the
cloud stores (100 operations, 2 to 4 MB) and the large configurable
ones of TiDB and Spanner. Its key limit, 111 bytes (256 in the first
version, 112 in the fourth), is the smallest in the table, under LMDB's 511 and
FoundationDB's advice of 1 kB: a store over a prefix tree, as LMDB over
pages, pays for long keys on every path.

### 6.7 The documented pattern for larger work

* **Larger than L1 or L5**: transactions of at most L1, each with a
  marker key in the last one (or a marker written last in its own),
  readers that look at the marker. Reads at one time see all or none
  of a committed transaction, so a reader that reads the marker first
  and then the data at the marker's time sees a whole batch.
* **Values over L4**: chunks under keys /x/0, /x/1, ..., a manifest
  written last (the same pattern), or a file outside BergDB.
* **Bulk loads**: batches of 100 to 1,000 (section 4: the bytes and the
  time a put stop falling before 1,000).


### 6.8 Files in BergDB: the value limit

Frans, 10:26: "most types of files in a filesystem should fit". Sizes
from vendors' pages and calculations from bit rates (a research agent's
notes, 10:35; "calc" where computed):

| File                               | Typical      | Large         | 10 MB | 16 MiB | 64 MiB |
|------------------------------------|--------------|---------------|-------|--------|--------|
| Phone photo, HEIC or JPEG (12 MP)  | 1.5 to 6 MB  | 48 MP: 5-10   | yes   | yes    | yes    |
| Phone photo, 200 MP JPEG           | 13 to 15 MB  | 21 to 37 MB   | no    | partly | yes    |
| Camera RAW, 45 MP (CR3, NEF)       | 21 to 52 MB  | 60 MB         | no    | no     | yes    |
| Camera RAW, 61 MP; ProRAW 48 MP    | 64 to 75 MB  | 139 MB        | no    | no     | no     |
| PDF                                | 0.15-0.4 MB  | 10 to 100 MB  | yes   | yes    | mostly |
| Office document                    | 20 kB-5 MB   | decks 100+ MB | yes   | yes    | mostly |
| Song, MP3 or AAC, 4 min            | 4 to 10 MB   | -             | yes   | yes    | yes    |
| Song, FLAC or CD WAV, 4 min        | 21 to 42 MB  | hi-res 138 MB | no    | no     | partly |
| Podcast, 1 h                       | 29 to 58 MB  | 115 MB        | no    | no     | partly |
| Video, 1080p30 HEVC, a minute      | 60 MB        | 4K60: 400 MB  | no    | no     | 1 min  |
| Web image, email, source file      | 12 kB-1 MB   | email 25 MB   | yes   | yes    | yes    |

Sources: support.apple.com/en-gb/119916 (ProRAW "approximately 25 MB
... 48MP is approximately 75 MB"); the Nikon Z8 manual's card capacity
page (lossless NEF 51.6 MB); dpreview's Canon R5 review; the HTTP
Archive's Web Almanac 2024, Media (median image 12 kB); Gmail's 25 MB
message limit (support.google.com/mail/answer/6584); song, podcast and
video sizes calc from their bit rates (Apple's podcast requirements,
128 to 256 kbps). File-system studies: "The median file size remains
4K" and "half of all bytes are in files larger than 30MB" (Meyer and
Bolosky, FAST 2011, 857 file systems); "most of the bytes in large
files are in video, database, and blob files" (Agrawal et al., FAST
2007). Precedents: MongoDB's 16 MiB document with GridFS's chunks of
255 KiB above it ("If your files are all smaller than the 16 MiB BSON
Document Size limit, consider storing each file in a single document");
SQLite: "For BLOBs smaller than 100KB, reads are faster when the BLOBs
are stored directly in the database file" (intern-v-extern-blob).

**So**: 16 MiB holds nearly every file by count, every ordinary photo
(Frans's test), every lossy song, nearly all documents; it does not
hold camera RAW, lossless audio, podcasts or video, which hold most of
a file system's bytes. 10 MB loses the 200 MP photos and the release
zips of this repository (12.7 to 15.6 MB); 64 MiB adds most RAW and
lossless songs and a minute of video, not video in general.

What a value of that size costs in BergDB as it is (4.2):

* **The commit** holds the write lock about 9 ms a MB: 135 to 250 ms
  for 16 MiB, 0.6 to 0.9 s for 64 MiB, against the pause guide of about
  20 ms for BergDB's own code; with CRC32C for Fletcher-16 (F6, a node
  format change, allowed in 2026.5) about 3 ms a MB, 50 ms for 16 MiB.
  The value's copy is the user's work; its checksum and the wait for a
  10 MB buffer to drain are BergDB's.
* **A get** reads the value from the stream every time (never cached
  over 1 MiB, outside the cache budget), allocates twice its size and
  checksums it: 106 ms and 34 MB for 16 MiB; per concurrent reader.
* **The stream**: a record crosses meta blocks (every 200,000 bytes)
  and `FileStream`'s files (200 kB, 1 MB, 5 MB, 20 MB, 100 MB, ...) as
  any record does: no limit there.
* **Reclaim moving one (F7).** A step takes at least one KV whatever
  its size and runs inside the commit of the user transaction that
  triggers it, under the write lock (`Reclaim.transactionCompleted`,
  `Db` 2531 to 2560): two reads and a put, about 360 ms for 16 MiB and
  1.4 s for 64 MiB added to an unrelated small commit. Its record holds
  one value, within R_max.
* **A restart** holds every value of the startup section in memory and
  checksums each: 0.46 to 0.86 s with three large values; the section
  is about sd (50 MB) and passes it by at most one record.
* **The Pub layer**: the same limit for an object and for raw bytes,
  on the stored value; a put of an object needs 4 to 5 times its stored
  size (`pub` package doc), 64 to 80 MiB at 16 MiB; a get of a Data
  Object 3 to 4 copies.

**Recommended: L4 = 16 MiB** (Frans's 10 MB rounded to the power of two
above it, which keeps the release zips and 200 MP photos), with F6
(CRC32C, 2026.5's format change) so that a 16 MiB commit is about 50
ms, and F7 noted (a reclaim step that moves a value over 1 MiB runs on
its own, not in a user's commit: a later change). L5 = 64 MiB, four
values at the limit. Larger files: chunks of at most 16 MiB under one
directory and a manifest written last (6.7), as GridFS does.

**Decided: L4 = 8 MiB, L5 = 32 MiB** (Frans, 17:41: "a bit more
conservative, possibly increasing in a future version"). What fits, by
the table above (8 MiB is 8.39 MB):

* **Fits:** phone photos of 12 MP (1.5 to 6 MB) and most of 48 MP (5 to
  10 MB), web images, source files, typical PDFs and office documents,
  most lossy songs (4 minutes at 256 kbps is 7.7 MB, at 320 kbps 9.6 MB:
  not). Of this repository's 4,970 tracked files (17:45) all but 3: the
  source zips of releases 2026.2 to 2026.4 (12.7, 13.4 and 15.6 MB); 7
  are over 4 MiB.
* **Does not fit:** 200 MP photos (13 to 37 MB), camera RAW, lossless
  songs, podcasts, video, large PDFs and decks, e-mails near Gmail's 25
  MB. Chunks of 8 MiB and a manifest (6.7) hold them.
* **Costs at 8 MiB** (4.2's rows scaled by size; not measured at 8 MiB):
  a commit holds the write lock about 65 to 155 ms today (the 10 MB
  row: 76 to 183), of which the node checksum is 48 ms (Fletcher-16,
  5.7 ms a MB, F6); with CRC32C (QL9, decided) the checksum is 1.1 ms
  and the commit about 25 ms, near the pause guide's 20. A get about 55
  ms and 17 MB allocated today, about 6 ms with CRC32C (its two copies
  remain). A reclaim step moving one value, inside a user's commit (F7):
  about 180 ms today, of which about 140 ms are three checksums; about
  40 ms with CRC32C. A Pub put of an 8 MiB object needs 32 to 40 MiB of
  heap.
* **L5 = 32 MiB**, four values at the limit: a record's own bytes at
  most 33.6 MB (5.3).


### 6.9 Later: sizes of databases

Not for 2026.5 (Frans, 10:38, section 1); only what 2026.5's choices
should leave open, from the coordinator's remarks of 10:40.

* **A class is a set of limits.** With S, M and L, the limits become a
  property of the database, its size class, written in the meta block
  as the node size is since 005-50, not of the release. 2026.5's limits
  are M's.
* **Raise, never lower** (6.3) becomes: a database can move to a larger
  class, never to a smaller one; a reader of a class can open every
  smaller one.
* **What 2026.5 does now:** the limits as named constants in one place
  (one class in Java, one header in C), read by every check, so that a
  class is a set of values; the bounds and theorems (5, 024-12's
  `Limits`) take them as hypotheses, not as literals, so that S's and
  L's values need no new proof. For S (a Pico 2: 520 kB of RAM) the
  node bound of 5.2 is what matters: a key of 111 bytes crosses 16
  segment trees, so S would lower L2 and L1 much more than L4.
* **The class's place in the format** is a question for the stable
  format (026; 024-02), with the node size beside it.


## 7. Alternatives

As of the fourth version (1,000 operations, 112-byte keys); Frans
decided at 17:41 (section 8). A4's 450 is the nearest to the decision.

* **A1. L1 = 10,000 and a smaller L3.** With 112-byte keys and the
  count with q (5.2), 10,000 operations fit a record only with S <=
  18,546, so L3 at most 58.4 KiB; at 48 KiB, S <= 17,021 and 3.41
  million nodes (7.9 % under): 10,000 keys of about 5 bytes, or 438 of
  112 bytes. (The first version: L3 = 128 KiB with 256-byte keys and
  the delete's count of then.) Costs: a second number users meet often
  (key bytes), the count restated and proved. Buys: bulk loads of very
  short keys in one transaction. Not worth it.
* **A2. L1 = 10,000 without L3 on user keys.** Not provable within a
  record: up to 32.8 million nodes, 17.8 GB, with 112-byte keys by the
  count with q (5.2; 71 million with 256-byte keys by the first
  version's TP26). Only with A3, and even then the heap a commit may
  need is about 18 GB in the worst case.
* **A3. The take writes one transaction's dirty nodes over several
  records.** Removes the record from the bound: a record is then
  bounded by its own bytes and the take's budget alone, and R_max could
  be tens of MiB. Costs: `TransSeq.take` and 007-08's `T3_take` change
  (the startup position must stay before a transaction until all of its
  nodes are written), a study of its own; the heap and the commit's time
  still follow the node bound. Buys: a small proved record limit.
* **A4. L1 = 450.** Covered by format 7's TP26 as stated today (452
  operations of 112-byte keys at H = 22, 5.2), with no restatement;
  still not proved, and at node size 62 that count gives 310. (The
  first version: 500, by 2026.4's TP26 with 256-byte keys.) Costs:
  PayDemo, PayTest, `LargerThanMemory` and `cbench` (1,000 a
  transaction) change. Buys: no new count.
* **A5. The value limit: 10 MB or 64 MiB against 16 MiB.** 10 MB
  (Frans's first number) loses 200 MP photos and this repository's
  release zips, and buys a commit a third shorter. 64 MiB keeps most
  camera RAW and lossless songs and a minute of video; it costs a
  commit of 0.6 to 1 s today (about 0.2 s with CRC32C), 134 MB
  allocated a get, a reclaim step of about 1.4 s inside a user's commit
  (F7), and L5 of 256 MiB to keep four values a transaction. A limit
  can be raised later, never lowered: 16 MiB first.
* **A6. The Pub layer counts objects.** "At most 1,000 objects a `w()`"
  with a limit on the indexes of a directory (say 8: 17 KVs an object)
  and L1 on Core KVs at 17,000: not provable (A2). So the Pub layer
  counts KVs, 1 + 2k an object, and says so.


## 8. Questions for Frans

**Decided, QL2: L2 = 112 bytes of the key as stored** (Frans,
2026-11-11), in place of 256. 14:40: "Should we limit key size to 150
bytes? Or even 100 bytes? Do you see any problem with that? After all,
this is a database, not a file system :-)." The coordinator: with
TP26's simple count (already proved; about 192 nodes a segment) a
record holds about 520 operations at 256 bytes, 880 at 150, 1,280 at
100, so 100 proves L1 = 1,000 without the sharper counts; limits can
be raised later and not lowered. 14:44: "How about 120 bytes. The user
can think "100 characters" as a rule of thumb." The coordinator: 120 is
18 segments, about 1,070 operations, a 7 % margin that the merges may
take; 112 (16 segments) the fallback. 14:45: "Let's make it 112 bytes
then." 112 bytes are 16 segments, exactly; about 1,200 operations by
TP26's count (the coordinator's arithmetic, to be checked). For the
user: "about 100 characters" (ASCII, each "/" of a Pub key counts two;
å, ä, ö two bytes each). The rest of the proposal (L3, L6, the bound's
arithmetic, the tests) is reworked for it (section 9).

**Checked, 14:55** (5.2, F10 to F12). Three corrections to the
exchange above: (1) TP26 is not proved: it is a statement that
`treetest` and Java's traces check (024-12, its table: "T"; 024-22:
"S"); (2) 112 bytes are 17 segments, not 16 (`Keys.toSegments`: a key
of a multiple of 7 bytes ends in an empty segment), so 2026.4's TP26
gives 1,133 operations, not about 1,200 (that is 111 bytes'); (3) with
merges (record format 7) TP26 is restated as 20 nodes a level, not 8
(024-22, 3.4), and gives 452 operations. A form for format 7 that
counts the room after a merge gives 1,128 at H = 22, 13 % over 1,000;
it is to be stated (QL8). The other figures (520, 880, 1,280, 1,070 at
256, 150, 100, 120 bytes) are right by 2026.4's form.

**Decided, the limits** (Frans, 2026-11-11, 17:41): "I want be a bit
more conservative, possibly increasing in a future version. So, use:
L1 = 500, L2 = 111, L4 = 8 MiB, L5 = 32 MiB. The rest as recommended."
So:

* **L1 = 500 operations** a transaction (QL1; was proposed 1,000).
* **L2 = 111 bytes** a key as stored, 16 segments (QL11; replaces the
  112 of 14:45).
* **L4 = 8 MiB** a value, **L5 = 32 MiB** a transaction (QL3; were
  proposed 16 and 64 MiB).
* **As recommended:** L6 with a refused put (QL4), the internal checks
  as `Bug` once proved (QL5), a value transformation's result over L4
  fails the database (QL6), the reader reads a record's header first
  (QL7), the count with q stated and run (QL8 (a)), CRC32C in place of
  Fletcher-16 (QL9), reclaim's step of a large value documented now
  (QL10), one L1 for every node size (QL12 (a)).
* **A precondition of QL5** (found 2026-11-11, 19:04, by 024-24's
  review, R3): a transaction within L1 to L5 can still meet 005-31's
  check (a probe at node size 62, 500 KVs of 111-byte keys, each with a
  key and a value transformation), because the check's count of
  transformed KVs is coarse. So 005-31's check becomes a `Bug` only
  after that count is made exact and the bound is proved; until then it
  stays a refusal (024-24, section 7).
* **To restate for the new values** (the coordinator's reading of "as
  recommended", for the rework to confirm): L3 by the same rule as
  proposed (L1 keys of L2 bytes: about 54 KiB); L6 as one number with
  the key (111 bytes); the bound's margins, and whether L1 = 500 is
  covered by TP26's form for format 7 (20 a level) at 16 segments, so
  that QL8's restatement is a margin and no longer a need; QL12 (Java's
  own counts at node sizes 8 and 62 were 720 and 938 operations).
* **Restated, 17:45** (lim2; 5.2a, 5.3, 6.1, 6.8):
  * **L3 = 56 KiB** (57,344 bytes): 500 keys of 111 bytes are 55,500
    bytes, 54.2 KiB, so 54 KiB would refuse them; 56 KiB is the round
    value above. S <= 8,692 segments; by the count with q 27 to 57 %
    under the record's dirty limit at the four node sizes.
  * **L6 = 111**, one number with the key: the recommendation's reason
    for 112 was "one number for everything that becomes a key"; the
    byte changes nothing in the bound (entries of 497 bytes, 72
    segments; 51 objects with one index at the largest a transaction).
  * **TP26 as stated (20 a level) does not cover L1 = 500** of 111-byte
    keys: at node size 30, 481 operations at H = 22 (-3.8 %), 501 at H
    = 21 (+0.2 %), 524 at BU1's H = 20 (+4.8 %), 549 at H = 19 (+9.8
    %); at node size 62, 330; with L3's index entries, at no node size
    but 14. **So QL8's restatement is still needed, not a margin.** With
    q (14 a level at node size 8, 9 at 14, 8 at 30 and 62): 742, 1,210,
    1,199 to 1,251 and 822 operations, 1.5 to 2.5 times L1 (at 14, 10 a
    level and 1,089 operations since 028-21, 5.2a, corrected 2026-11-28).
  * **QL12 is gone**: with the count with q every node size covers 500,
    so one L1 is provable at 8, 14, 30 and 62 alike; Java's own counts
    of one delete are 766, 1,215, 1,415 and 996 operations (format 7's;
    today's in 5.2a).
  * **The record** at the limits: at most 0.95 GB at node size 30, 1.51
    GB at node size 8 (70 % of 2^31 - 9), so the record limit stays.
  * **L4 = 8 MiB** holds every tracked file of the repository but the
    three release source zips, ordinary photos and most lossy songs; a
    commit of it about 25 ms with CRC32C, 65 to 155 ms today (6.8).
  * **Left for Frans: nothing** on the limits. The user wording ("about
    100 characters") holds for 111 bytes (6.1, L2).

The questions as they stood before 17:41, each now decided:

* **QL1. L1 = 1,000 operations and L3 = 112 KiB of key bytes** (6.1),
  resting on the count with q (QL8 (a)): 1,128 operations of 112-byte
  keys at H = 22, and with L3 3.35 million nodes, 9.4 % under the
  record's dirty limit; or A1's 10,000 with L3 at 48 KiB? **Recommended:
  1,000 and 112 KiB**; raise later when a count is proved. **Decided
  (17:41): L1 = 500; L3 = 56 KiB by the rule.**
* **QL2. Decided: L2 = 112 bytes** (above). Counted as stored: a Core
  key's bytes, a Pub key's ikey (its UTF-8 and a byte a part, so each
  "/" counts two), with BergDB's own longer keys (index entries) bounded
  by L3; 112 bytes of UTF-8 alone would make Core keys of up to 168
  bytes (6.2 (a)). **Replaced (17:41) by 111 bytes** (QL11).
* **QL3. Values 16 MiB, transactions 64 MiB** (L4, L5)? **Recommended:
  yes** (6.8); 10 MB or 64 MiB are A5. **Decided (17:41): 8 MiB and 32
  MiB.**
* **QL4. L6, an indexed value's encoded levels: 112 or 256 bytes, and
  above it no entry (as above 4,096 today) or a refused put?** 112: one
  number for all that becomes a key, entries of at most 499 bytes; 256:
  every e-mail address (up to 254 bytes) and most URLs, entries of up to
  643 bytes, 92 segments (6.1, L6). **Recommended: 112, and refuse the
  put**: a silent missing entry makes a lookup miss an object; long
  values are indexed by a hash or a prefix. **Decided (17:41): as
  recommended, refuse the put; L6 = 111 with the key.**
* **QL5. The internal checks** (005-31, the record check) as `Bug` once
  proved, refusals until then? **Recommended: yes.** **Decided: yes.**
* **QL6. A value transformation's result over L4** fails the database
  (015-51's rule kept)? **Recommended: yes**; the Core API is
  low-level. **Decided: yes.**
* **QL7. The reader** reads a record's header first and refuses a size
  over L7 (6.5)? **Recommended: yes, in 2026.5.** **Decided: yes.**
* **QL8. Which count L1 = 1,000 rests on** (F11)? (a) TP26 for format
  7 restated with q, the room after a merge: 8 nodes a level at node
  sizes 30 and 62, 9 at 14 (10 since 028-21, 028-72), the 20 kept at 8 (`Limits.dirtyNodes`, a
  line of `Bound.lean`; `treetest` and `treeconf.sh`, C-T8, run it as
  they run TP26 today), with the transaction's segments (L3) as a third
  field of `Limits` and the sum form; or (b) TP26 as stated (20 a
  level) with L3 = 40 KiB (365 keys of 112 bytes a transaction) or L1 =
  450 (A4). **Recommended: (a)**, stated and run in 2026.5; the proofs
  (TP23, TP26, and TP30 for H) after the merges have settled (024-22,
  section 6), so L7 and L8 stay refusals until then (QL5). **Decided:
  (a).** At L1 = 500 still needed (5.2a): TP26 as stated covers 481
  operations at H = 22.

* **QL9. The node checksum** CRC32C in place of Fletcher-16 with
  2026.5's format change (F6: 45 times faster, 32 bits)? **Recommended:
  yes**; it decides whether a 16 MiB commit is 135 to 250 ms or
  about 50. **Decided: yes** (at 8 MiB: about 25 ms against 65 to 155).
* **QL10. Reclaim's step of a large value** inside a user's commit (F7):
  accept for 2026.5 and document, or move such steps out? **Recommended:
  document now, change later**, with 024-05's BD7. **Decided: as
  recommended.**
* **QL11. 112 or 111 bytes** (F10)? 112 bytes are 17 segments, 111 the
  most in 16: 6 % more operations in the bound (1,199 against 1,128 by
  the count with q). The rule of thumb is the same. **Recommended: 112,
  as decided**: the bound fits with it, and a round number is easier to
  remember than 111. **Decided (17:41): 111**, 16 segments.
* **QL12. Node sizes 8 and 62** (F12): there no per-operation count
  reaches 1,000 operations of 112-byte keys in a record in the worst
  case (Java's own count of one delete: 720 and 938; at 62 a node is
  1,056 bytes, at 8 a tree up to 61 levels). (a) L1 = 1,000 for every
  node size; the bound stated and proved for 14 and 30; at 8 and 62
  005-31's check stays a refusal, documented ("a database of node size
  8 or 62 can refuse a transaction within the limits, in a tree of
  2^48 or more klongs built against it"); (b) L1 = 700 for every node
  size; (c) the builder offers 14 and 30 only in 2026.5 (024-19, the
  node size, is postponed). **Recommended: (a)**, and 024-19 takes the
  bound as one of its criteria (62 was its interim favourite with 30).
  **Decided: (a).** At L1 = 500 the count with q covers every node size
  (5.2a), so no node size keeps the refusal: L8 becomes a `Bug` at all
  four once the count is proved.

## 9. State

2026-11-11, 10:04 to 12:05, by the agent "limits" of coord-1111. A
study; in the main tree this file and `17-limits/` only.

* **Done.** Sections 0 to 8, after Frans's 10:18 (keys), 10:26 (files)
  and 10:38 (sizes of databases, 6.9). Section 4 measured on main
  `16759d36`: the counts at 1M and 10M keys in one slot (11:22 to
  11:25), the times at 1M keys and of large values with both slots
  (11:56 to 11:57).
* **Not done.** Times at 10M keys with both slots (the counts' run gives
  them with other work beside it); a reclaim step that moves a large
  value, measured (F7 is from the code and the put and get times); the
  sharper per-segment counts of 5.2 (mine, not proved).
* **Files** in `17-limits/`: `LimitProbe.java`, `ValueProbe.java`,
  `CsBench.java` (probes in package `bergdb.core`, compiled against the
  clone's `build/bergdb.jar`), `counts.sh` (one slot), `timing.sh` (both
  slots), `table.py` (4.1's tables), outputs `count-1000000.txt`,
  `count-10000000.txt`, `time-1000000.txt`, `value.txt`.
* **The clone** `/Users/f/fl/bench/2026-11-11/limits/clone`, main
  `16759d36`, no branch, no commit (probes only); probes compiled to
  `/Users/f/fl/bench/2026-11-11/limits/probe` and `.../limits/cs`.
* **To continue:** keep section 8 current with Frans's answers; the
  limits' implementation is a later subitem (checks in `Trans.Builder`
  and `Db.execute`, `Db`'s and the `pub` package's Javadoc "Limits",
  the tests of 2.4 and section 3 changed to assert the refusals).

**The rework for 112-byte keys**: 2026-11-11, 14:45 to 15:00, by the
agent "lim2" of coord-1111, for Frans's QL2 (14:45). Arithmetic,
reading and grep only; no clone, no run, no product code.

* **Done.** Sections 0, 1, 3, 5 (5 intro, 5.2 rewritten with F10 to
  F12, 5.3, 5.6), 6 (6.1's table, L1, L2 with the wording for users,
  L3 = 112 KiB, L6 = 112; 6.2 (a), (d), (e) with the list of code and
  tests that change; 6.6, 6.9), 7 (A1, A2, A4) and 8 (QL2 decided and
  checked; QL1, QL4, QL8 reworked; QL11, QL12 new). The numbers are
  `17-limits/bound112.py` (Java's constants as in 024-21's branch:
  `Db.checkDirtyNodes`, `Dag.dirtyNodeBound`, 8/17/17), its output
  `bound112.txt`; read 024-22 (2.1a, 2.6, 3.4, 6, 9) and 024-21 (2, 3.5)
  and the branch's `Bound.lean` (`Limits.dirtyNodes`).
* **Not done.** The count with q (5.2) is my argument and a one-path
  computation of Java's count, not stated in the model nor checked by
  `treetest`; a check of it on 024-22's runs is the next step (QL8 (a)).
  6.8's file table and section 4 are unchanged (no limit of theirs
  moved).
* **To continue:** Frans's answers to QL1, QL4, QL8, QL11, QL12; then
  024-22's agent (or 024-12's) restates `Limits.dirtyNodes` for format 7
  with q and runs it; the implementation subitem as above.

**The restatement for the decided limits**: 2026-11-11, 17:42 to 17:48,
by "lim2" again, for Frans's decision of 17:41 (L1 500, L2 111, L4 8
MiB, L5 32 MiB, the rest as recommended). Arithmetic and reading only.

* **Done.** `17-limits/bound500.py` and `bound500.txt`; section 5.2a
  (the bound at 500 operations of 111 bytes, every node size, L3's sum),
  5.3 (the record), 6.1 (the table and every limit's text, L3 = 56 KiB,
  L6 = 111, the user wording), 6.2 (a), (d), (e), 6.6, 6.8 (what 8 MiB
  holds and costs), 6.9, section 0, 1, 3 (F3: the batches of 1,000), 7's
  note, 8 (the restatement, every question marked decided).
* **Not done.** The count with q is still my argument (5.2, 5.2a), not
  in the model; 8 MiB's costs are 4.2's rows scaled, not measured.
* **To continue:** 024-22's agent (or 024-12's) restates
  `Limits.dirtyNodes` for format 7 with q (14, 9, 8, 8 nodes a level at
  node sizes 8, 14, 30, 62; 10 at 14 since 028-21, 028-72) and L3 as a field, and runs `treetest` and
  `treeconf.sh` against it; then the implementation subitem (checks in
  `Trans.Builder` and `Db.execute`, the Javadoc "Limits", the tests and
  harnesses of 6.2 (e) and F3).

2026-11-13. Status set after the release (coord-1113).
