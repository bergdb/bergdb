# 020-24-09 The Core API as an embedded key-value store

Created 2026-11-09 by Frans Lundberg.

An application written as a new user of 2026.4 would write it (u9, for coord-1109, round 3
of the common brief of 020-24): only the release jar on the class path, built from a clone
of main at `5d45478`, and only what a user reads: README.md, `releases/next.md`,
`java/src/overview-pub.html`, and the Javadoc of the Core's `Db` and of the types of its
signatures (`DbBuilder`, `Trans`, `Trans.Builder`, `GetData`, `GetMany` and its stop
conditions, `Kvt`, `Kv`, `Keys`, `StoredTrans`, `StoredValueNode`, `StartInfo`, `Clock`,
`SyncLevel`, `FileStream`, and `doc-files/key-encoding.md`), made with `javadoc` from the
sources, and the Pub API's package page for the cross-layer phase. The implementation was
read only afterwards, to explain U9-1 and U9-3; the item 021-16 only afterwards, to place
U9-2.


## 1. The application

A user of the Core API alone, as a C or Rust programmer would use an embedded store:
binary keys and values, `bergdb.core.Db` on a `FileStream`, transactions built with
`Trans.Builder`, reads with `getOne()` and `getMany()`. Every result is checked against
the application's own model, a sorted map of `byte[]` (unsigned order) with each key's
history (time to value), so that a read at any past time has an expected answer. The
application is `/Users/f/fl/bench/2026-11-09/app-u9/app/src/App.java`, with `run.sh`
(compiles it and runs `App all`; `sh run.sh PHASE` runs one phase). The reproductions are
beside it in `src/`: `Probe2.java` (U9-1, U9-2), `ReproTime2.java` and `ReproTime.java`
(U9-3), `Probe10.java` and `Probe11.java` (corner cases). The output of the last full
run is `/Users/f/fl/bench/2026-11-09/app-u9/last-run.txt`.

The phases:

* **edge**: one transaction of 292 keys of every kind: the empty key, runs of 00, FF and
  'a' of 1 to 64 bytes (around the 7-byte segments of `Keys.toSegments`), single bytes
  01 to FE with 00 and FF after them, prefix chains (`a`, `a 00`, `a 00 00`, `a FF`,
  `aaaaaaa 00`), the Pub API's prefixes 01 66 and 01 2f and the neighbours of BergDB's 01
  25, keys of 1,000 to 30,000 bytes that are prefixes of each other or differ in their
  last byte, 200 random keys; values of 0 bytes to 30 MB, and a 5 MB value at a 20 KB key.
  Then: full scans both ways, prefix scans, endpoint scans (inclusive and exclusive, both
  directions), GetN from every key (inclusive and exclusive, both directions), the
  application's own stop condition (CONTINUE as a filter, ADD_AND_STOP, STOP, and
  `eod()` called once only when the end is reached), a put and a delete of one key in one
  transaction in both orders, deletes of half the keys and then of all; every state again
  at every transaction's time; the listing of each transaction by `getTrans(Trans.tpos)`;
  all of it again after a restart.
* **longkey**: keys of 100 KB and 300 KB, under a cache of 500 KB, a startup distance of
  400 KB and a retain duration of 10 s with 1,500 transactions, then a restart (U9-2).
* **random**: 2,400 random transactions of 1 to 3,300 puts and deletes (keys from prefix
  families over 00 01 02 a b 7F 80 FE FF, runs of 00 and FF, random keys of up to 22 KB;
  values of 0 bytes to 104 KB; 1 in 30 operations on a key the transaction has already
  written), 99,070 keys; every 200 transactions 300 gets now, 200 gets at past times,
  60 scans now and 40 at past times with random start keys, directions, inclusiveness and
  stop conditions; three restarts, each followed by a full check now and 10 full scans at
  past times; a listing of every seventh transaction.
* **settings**: an application clock (one second per transaction); 2,000 transactions of
  about 40 MB under a cache of 1 MB, read in full; the cache set to 100 MB and to 200 KB
  while it runs; `setStartupDistance(100)` (clamped to 400,000), 2 MB; the refusals of
  each setter; `setReclaimInternalFraction(0.1)`, `setRetainDuration(60 s)`; a restart
  that keeps them; 3,000 transactions more until reclaim cuts the front; a read before
  the first available time refused, reads after it and the current state right, before
  and after a restart.
* **crash**: six rounds of a child JVM that writes deterministic transactions (a marker
  key with the transaction's number, 1 to 30 puts and deletes, every 40th a value of 3 to
  6 MB) and syncs every third, killed with `destroyForcibly()` (SIGKILL) after 0.3 to
  2.8 s; the parent starts the database, finds the last transaction by the marker, checks
  that it is at least the last synced and at most one past the last reported, and checks
  the whole state and 20 past states against the model; the next round goes on from there.
* **crashreclaim**: eight rounds as in crash, with an application clock (one second per
  transaction), a retain duration of 30 s and a cache of 5 MB: the child overwrites 300
  keys with values of 1 to 21 KB and syncs every second transaction, so that reclaim runs
  (0 to 3 iterations a round) and is killed in the middle of its work; the first
  available position reached 95 MB. The same checks, the past states from the first
  available time on.
* **threads**: four writers, each rewriting its 30 keys (and a key that comes and goes)
  in 1,500 transactions; three readers scanning a writer's keys at `currentTime()`, each
  scan one transaction's state, never older than the reader's last, and a `getOne()` at
  that time agreeing; four threads incrementing one counter with the STM (read at t,
  `lookupTime(t)`, `keyRead(key)`, retry on `RerunException`); a restart.
* **keyspace**: keys around 01 25, BergDB's keys in a new database, a put at a reserved
  key (01 25 41), the lifecycle's refusals (`start()` twice, a second `FileStream` on the
  directory, `getOne()` and `execute()` after `close()`).
* **pubmix**: a database of the Pub API (text, bytes, Data Objects at `/acc/`, an index
  on their balance), then the Core on its directory: a scan, nine keys of the user's own
  (00, FF FF, `k1`, 01, 01 24, 01 26 09, 01 2e, 01 67, 02), a copy of a Pub value at
  another Pub key, bytes that are not UTF-8 at a `.txt` key, a delete of a Pub key, a put
  at an indexed object key; the Pub API again, which reads each as Db's Javadoc says; then
  a retain of one second through the Core and 2,208 transactions of 100 KB until reclaim
  has cut 100 MB; the user's keys unchanged, the Pub API's data and index right.
* **large**: 957,784 keys (4 to 15 random bytes, one in ten from the random phase's
  generator) in 250 transactions of 4,000 puts, then 100 transactions of 2,000 overwrites
  and deletes, under a cache of 20 MB (a stream of 410 MB); 20,000 gets now, 2,000 at past
  times and 75 scans; a restart (5.7 s) and the same, cold; two full scans of the million
  KVs, both ways (11.7 s).
* **soak**: 25 s of three writers (20 keys of 2 to 10 KB each a transaction, a sync every
  tenth), three readers at random times from the first available time to now, each scan
  one transaction's state that holds every transaction committed before its time, under
  a cache of 3 MB and a retain of 3 s (reclaim cut 1.2 to 1.7 GB), and a thread that
  interrupts a reader or a writer every 2 ms; then `stop()` while they run, and a restart
  that must hold every transaction whose `execute()` returned.

Size: `App.java` 2,233 lines, `run.sh` 10, the probes and reproductions 712. A run of `App
all` checks 2,892 scans against the model, besides the readers' 7 million scans and the
gets, and takes 4 min 41 s on F53 (one JVM, and a child JVM at a time in the crash
phases); its directories take 2.0 GB afterwards.

The last run: every value of every get and scan was right, in every phase; it fails on
U9-1 (5 prefix scans of the edge phase), U9-2 (the longkey phase) and U9-3 (2.5 million
KV times), and so exits with 1.


## 2. The findings

Most severe first. A reproduction names a file in the application's `src/`, or a phase
of `App` (`sh run.sh PHASE`).

| ID | Kind | Severity | What | Reproduction |
|----|------|----------|------|--------------|
| U9-2  | bug | critical | a 90 KB key is stored; the next start overflows (U5-1)  | Probe2, longkey |
| U9-1  | bug | high     | `GetMany.Prefix` stops at the key equal to the prefix   | Probe2, edge    |
| U9-3  | bug | high     | a KV's time is a later transaction's, not its write's   | ReproTime2      |
| U9-4  | doc | medium   | the Core writes BergDB's keys; a user's scan gets them  | settings        |
| U9-5  | doc | medium   | binary keys: order, empty key, length, null unstated    | edge, Probe     |
| U9-6  | doc | medium   | opening a Core database: no stream type, no example     | the app         |
| U9-7  | doc | medium   | `Db`'s thread safety and the STM's calls undocumented   | threads         |
| U9-8  | doc | low      | outputs and defaults without Javadoc                    | Probe           |
| U9-9  | doc | low      | listings: deletes of absent keys, reclaim's copies      | random          |
| U9-10 | doc | low      | `getKvCount()`, `getTransactionCount()` since the start | random          |
| U9-11 | API | low      | no Core call lists transactions in order                | the app         |
| U9-12 | API | low      | a delete never replaces a put in one transaction        | edge            |
| U9-13 | doc | low      | test methods in the API's Javadoc; `'<'` artifacts      | the Javadoc     |
| U9-14 | API | low      | a read at `stop()` may throw "Storage is closing."      | soak            |

### U9-2. A key of about 90 KB is stored, and the next start overflows (bug, critical)

U5-1 of 020-24-05 again, from the Core with binary keys: a put of one key of 100,000
random bytes commits and reads back; the next `start()` throws `StackOverflowError` (from
`DbStarter.postStartupCheck`, `Dag.visitNodeWithChildren`; 12,344 frames deep for the
first edge phase's keys of up to 300 KB), and the database does not open. With the JVM's
default stack on F53 (2 MB), one key of 50,000, 60,000, 70,000 and 80,000 bytes started
again; 90,000 and 100,000 did not. The start only meets it when the long key is in the
startup section: in the longkey phase, keys of 100 KB and 300 KB written first and
followed by 1,500 transactions started again; after one more transaction that rewrote
them, the start overflowed. A start on a thread with a stack of 256 MB opens the database,
and every value is right. Nothing in `Db`'s or `Trans.Builder`'s Javadoc limits a key's
length. Item 021-16 has this, fixed in `clone-k16` (4f4db2f, 1e01f45), not on main at
`5d45478`.

```java
// Probe2 DIR 100000, shortened
byte[] k = new byte[100_000];
new Random(1).nextBytes(k);
try (Db db = Db.builder().mainStream(new FileStream(dir)).start()) {
    db.execute(db.trans().put(k, new byte[] {1}).build());     // ok, and the close is ok
}
try (Db db = Db.builder().mainStream(new FileStream(dir)).start()) {  // StackOverflowError
}
```

### U9-1. `GetMany.Prefix` stops at the key equal to the prefix (bug, high)

`GetMany.Prefix`'s Javadoc: "Stops when the key is no longer has a given prefix." A key
equal to the prefix has the prefix, but the scan stops there, without adding it, and so
returns nothing at all: a prefix scan written the obvious way, `startKey` the prefix and
`inclusive` its default, true, gives no KV whenever the prefix itself is a key. `PrefixN`
does the same. From the prefix exclusive, or from a start that is no key, the scan is
right; the keys that extend the prefix are compared by bytes, whatever their segments
(`abcdefg` and `abcdefgh`, 7 and 8 bytes). After reading: the stop conditions use
`Keys.isPrefix()`, which is "a strict prefix"; no code of `java/src` but the testers uses
`Prefix` or `PrefixN`, so only a Core user meets it. In the edge phase: `Prefix(61)` from 61
gave 0 KVs, 35 expected; `Prefix(00)`, `Prefix(FF)`, `Prefix(01)` and the empty prefix
the same. Either the code (add the equal key, or at least go on past it) or the Javadoc
(say that the scan stops at the prefix's own key, and to start after it) must change; a
user who scans `user/` and has a key `user/` gets an empty result and no error.

```java
// Probe2 DIR prefix, shortened
byte[] a = "a".getBytes();
db.execute(db.trans().put(a, v).put("ab".getBytes(), v).put("abc".getBytes(), v).build());
GetMany g = db.newGetMany();
g.startKey = Keys.toSegments(a);                              // inclusive by default
g.stopCondition = new GetMany.Prefix(Keys.toSegments(a));
db.getMany(g);                                                // 0 KVs; expected a, ab, abc
g = db.newGetMany();
g.startKey = Keys.toSegments(a);
g.inclusive = false;
g.stopCondition = new GetMany.Prefix(Keys.toSegments(a));
db.getMany(g);                                                // ab, abc
```

### U9-3. A KV's time is a later transaction's, not its write's (bug, high)

`GetMany.result`'s Javadoc: "the resulting KVs including the time it was last written to
the DB" (`Kvt.time`); `getOne()` gives the same time in `GetData.kvTime`. Both give the
time of a later transaction that did not write the key, once that transaction rewrote the
key node that holds it. The value is right, and so is `GetData.tpos`. A read at a time
before the later transaction gives the right time. It happens in every workload: in the
last run 2,474,838 of the times checked differed, in every phase that checks them, and it
lasts over a restart; for the first 3,000 of the gets among them, `getTrans(gd.tpos).tt`
was the model's time.

```java
// ReproTime2: T1 puts 27 keys of one byte, T2 puts a 28th; every key of T1 reads T2's time
Trans.Builder b = db.trans();
for (int i = 0; i < 27; i++) b.put(new byte[] {(byte) (2 * i)}, new byte[] {1});
Trans t1 = b.build();
db.execute(t1);
Trans t2 = db.trans().put(new byte[] {(byte) 55}, new byte[] {2}).build();
db.execute(t2);
GetMany g = db.newGetMany();
db.getMany(g);              // 28 KVs; the 27 of T1 have time t2.tt, not t1.tt
```

With 27 keys before the put: 27 of 28 KVs wrong; 41: 28 of 42; 55: 28 of 56; with 2 to 26
and the other counts up to 64, none. `ReproTime` has a case where a transaction that only
deletes one key (FE) changes the time of 12 others (`ff`, `ffff`, `fe00`, `f5`, ...).

After reading: `KeyNode` keeps a key node's entries in an array of klongs, time markers
followed by the keys entered at that time; a get takes as the KV's time the marker before
the key's entry (`kwi.klongTime`, `KeyNode.java` about line 442 and 534); a node that a
transaction rewrites (by the counts above, a split at 28 entries) seems to put the entries
it moves after that transaction's marker. So the time is when the entry entered its node,
not when the value was written (not checked further in the code). The Pub API does not
seem to use it (`transactionInfo()` reads
`getTrans(tpos)`), so it touches the Core's users: an application that keeps a change
feed by `Kvt.time > T` gets keys that did not change. Fix the time, or document it as the
entry's time and point to `getTrans(tpos).tt`.

### U9-4. The Core writes BergDB's keys, and a user's scan returns them (doc, medium)

`Db`'s section "Keys and the layers above" describes the three kinds of keys "in a
database that the Pub API uses". A database used through the Core alone has BergDB's keys
too, written by the Core's own setters, and a scan from the first key returns them with
the user's: after `setStartupDistance()`, `/#i/-dummy` (01 25 6b 01 2f 66 77 6f 6f 7b)
with a value of 200,000 bytes, which stays (the setter's Javadoc says that it commits a
200 kB value, not that the value stays live at a key of BergDB's, and reclaim then copies
it forward); after `setRetainDuration()` or `setReclaimInternalFraction()`,
`/#i/dreclaim/-settings.txt` (31 bytes). `getTransactionCount()` counts their
transactions. A new database has none. So a Core user's "every key" needs a filter of 01
25, which the Javadoc should say, with the rule that every key whose first bytes are 01 25
is BergDB's whether or not the Pub API is used. (A put at 01 25 41, reserved, is taken
without a word, as the Javadoc says: "the Core does not stop another writer there".)

### U9-5. Binary keys: order, the empty key, length and a null value unstated (doc, medium)

What a C or Rust programmer asks first is not in `Db`'s, `Trans.Builder`'s or `GetMany`'s
Javadoc. Found by trying, all good:

* The order of `getMany()` is unsigned lexicographic by bytes, a key before its
  extensions (`a` < `a 00` < `a 00 00` < `a 01` < `aa` < `b`), as `Arrays.compareUnsigned`.
* The empty key is a key: put, get, scanned first. `Keys.bkey2ikeyOrNull()`'s Javadoc says
  "no key is empty", and `Keys.toBytes(String)` refuses the empty string.
* No length limit is stated (see U9-2); keys of 30 KB work in every operation.
* `put(byte[], null)` is refused with IllegalArgumentException "value == null not
  allowed, use delete() to delete a key-value pair"; only `put(String, String)`'s Javadoc
  says so. An empty value is a value, not a delete.
* A value of 100 MB, a transaction of 400,000 puts (a record of 31 MB, 1.6 s) work; the
  Javadoc names limits only as "too large (bergdb 005-17)".

### U9-6. How to open a Core database: no stream type, no example (doc, medium)

`Db.builder()` needs a stream (`build()` throws IllegalStateException without one), set
by `mainStream(AppendOnlyStream)` or `stream(name, ...)`. The file stream is
`bergdb.stream.FileStream`, which is not a type of `Db`'s signatures and so, by
`bergdb.pub`'s "The API and its jar", not API; nothing in `Db` or `DbBuilder` names it.
`Db`'s class Javadoc has no example of opening, writing, reading and closing; the first
working program came from `FileStream`'s constructor and `DbBuilder`'s method list, where
the user's settings (`cacheSizeIndicator`, `startupDistance`, `clock`) sit among test ones
(`audit`, `secondTopOrdinal`, `testSetup`, `evictionSchedule`, `reclaimStepReserve`). The
default clock (the system clock, as `currentTime()` shows) is not stated:
`clock()` "Chooses a non-default clock". `Db` is AutoCloseable, `FileStream` is not (it
has `close()`), so a try-with-resources of a stream alone does not compile.

### U9-7. `Db`'s thread safety and the STM's calls are not documented (doc, medium)

`Db`'s Javadoc does not say whether `execute()`, `getOne()` and `getMany()` may be called
from several threads (they may: 11 threads, 6,600 transactions, 1.6 to 2.0 million scans, each a
consistent state); `GetData`'s does, for itself; `GetMany`'s does not. The optimistic
transactions are described only in `execute()`'s `RerunException` ("a key in the read key
hash set ... changed after the read time"); `Trans.Builder.lookupTime()`, `keyRead()`,
`addReadHash()`, `addReadHashes()` and `addVirtualWriteHash()` have no Javadoc. Guessed
that `lookupTime(t)` is the read time and `keyRead(key)` adds the key, and it works: four
threads of 150 increments each gave 600, with 34 to 101 reruns.

### U9-8. Outputs and defaults without Javadoc (doc, low)

* `Trans`'s fields after `execute()`: `tt` (the transaction's time), `tpos`, `lastPos`,
  `nextPos`; the only way to learn a transaction's time and position.
* `GetData`: `kvTime`, `tpos`, `actualLookupTime`. `Kvt`: `time` (see U9-3), `spos`.
* `GetMany`'s defaults: `lookupTime` Long.MAX_VALUE, `stopCondition` a `DontStop`,
  forward, inclusive, `startKey` null; a second `getMany()` with the same object starts
  its `result` again (not stated either).
* `Db.currentTime()`, `getFirstAvailablePos()`, `getReclaimIterationCount()`,
  `getStartupDistance()` and `StartInfo`'s fields have none.

### U9-9. Listings: deletes of absent keys left out, reclaim's copies (doc, low)

`getTrans(tpos).getValueNodes()` gives a transaction's puts and deletes, but leaves out a
delete of a key that had no value; the Pub API's `TransactionInfo` says so, the Core's
`StoredTrans` does not. After reclaim has copied a live value forward, a get's `tpos` and
time are reclaim's transaction's (time ending in ...0001); `Connection.transactionInfo()`'s
Javadoc says so for the Pub API, `getOne()`'s and `GetMany`'s do not. With those two rules
added, every listing of the application matched its transactions.

### U9-10. `getKvCount()` and `getTransactionCount()` count since the start (doc, low)

Neither has Javadoc. `getKvCount()` is not the number of live keys: 591 in the edge phase
with none live, 0 after a restart of a database with 55,925; `getTransactionCount()` is 0
after a restart. They seem to count the KVs and transactions written since the start.

### U9-11. No Core call lists transactions in order (API, low)

A transaction is read by `getTrans(tpos)`, with a position from a get (`GetData.tpos`) or
from `Trans.tpos` after `execute()`. There is no call for the transactions after a time or
a position, so an application that wants a log of its changes keeps the positions itself.

### U9-12. A delete never replaces a put in one transaction (API, low)

As `Trans.Builder.build()`'s Javadoc says: "the last put, or a delete if there is no put;
a delete never replaces a put, whatever their order": put then delete of one key keeps
the put. A batch in most embedded stores (RocksDB's WriteBatch, LMDB in a transaction)
takes the last operation; a user who builds a transaction from a log of operations gets
another state. Documented, so only a note.

### U9-13. Test methods in the API's Javadoc, rendering artifacts (doc, low)

The API's types carry test methods and fields: `Db.testHooks`, `Trans.testTransReuse()`,
`testNegativeHash()`, `Keys.main()` and ten `test...()`, `StoredTrans.testSerialize...`,
`FileStream.test...` (40), `DbBuilder.testSetup()`. The generated pages show
`invalid input: '<'` in `Keys.compareKeys()` and in `FileStream`'s class Javadoc
("named invalid input: '<'14-digit index>.bergdb"), a `<` that is not escaped.

### U9-14. A read at `stop()` may throw "Storage is closing." (API, low)

In the first soak run, two of three readers whose `getMany()` ran when another thread
called `stop()` got `StreamIoException` "Storage is closing." (from
`StorageManager.read()`, through `NodeCollection.followValuePointer()`), the writers and
the other readers `DbStoppingException`; in the two runs after it, none got it.
`getMany()`'s Javadoc allows it ("If there was an i/o error with the database stream,
while the database is stopping"), but it is no I/O error, and an application that ends
its threads on `IllegalDbStateException` (`DbStoppingException`) must catch this one too,
and tell it from a real I/O error. A `DbStoppingException` in its place would be simpler.


## 3. What went well

* Every value of every get and scan was right: 2,400 random transactions with 99,070 keys
  of every byte value, prefixes of each other, around 00 and FF; reads at every past time;
  after three restarts; under caches of 200 KB to 1 MB with 40 MB of data; after reclaim
  cut the front; with values of 0 bytes to 100 MB and keys of up to 30 KB; a million keys
  under a cache of 20 MB, cold after a restart.
* The order of scans is the unsigned order of bytes, the empty key first, and GetMany's
  start key, inclusive and exclusive, both directions, `GetN`, `GetOne`, `Endpoint` (both
  directions, inclusive and exclusive) and the application's own stop condition (CONTINUE
  as a filter, ADD_AND_STOP, STOP, `eod()` once and only at the end) did what their
  Javadoc says, in 2,892 checked scans (Prefix and PrefixN too, but for U9-1).
* Fourteen kills with SIGKILL, six during writes of values of up to 6 MB and eight while
  reclaim cut the stream: each recovery kept every synced transaction, at most one more
  than the child reported, the state equal to the model's, no part of a transaction, and
  every past state right from the first available time.
* Concurrency: 1.6 to 2.0 million scans by three readers during 6,000 transactions of four
  writers, each one transaction's state and never going back; the STM counter exact (600,
  with 34 to 101 reruns a run). A read time 10,000 transactions old, of a key that did not
  change, is taken.
* The key spaces of Db's Javadoc hold from the user's side (pubmix): the user's keys
  beside a database of the Pub API, its index and reclaim stay as written and are seen by
  no scan of the Pub API; a Core put of a Pub value at another Pub key is read by the Pub
  API, bytes that are not UTF-8 at a `.txt` key give `DataFormatException` as a String and
  the bytes as a `byte[]`, a Core delete of a Pub key deletes it, and a Core put at an
  indexed object key is left out of the index's scan, as the Javadoc warns.
* The settings did what their Javadoc says: the clamp of the startup distance to 400,000,
  the refusals (IllegalArgumentException for a cache below 1, a startup distance below 10
  or negative, a retain below a second, a fraction of NaN or 0.95), 0.1 kept as 6,554 /
  65,536, and a restart that keeps the startup distance, the retain duration and the
  fraction but takes the builder's cache. Reclaim cut the front (first position 0 to
  47.8 MB) and a read before the first available time threw
  `LookupTimeNotAvailableException`.
* The soak, in three runs: 4.0 to 5.4 million reads at past times while three writers
  wrote about 1.5 to 1.9 GB, reclaim cut the front and eviction ran under a cache of 3 MB,
  with 8,800 to 9,500 interrupts (FileStream's Javadoc: no method is interruptible): each
  read one transaction's state, none missing a transaction committed before its time, none
  refused as not available, no failure of the database; an interrupted `sync()` threw
  `StreamIoException`, as its Javadoc says (741 to 1,085 times a run). After a `stop()` in
  the middle of the writes and a restart, every transaction whose `execute()` had returned
  was there, and at most one more of each writer.
* The lifecycle's refusals are as documented: `start()` twice and a read or a transaction
  after `close()` throw `IllegalDbStateException`, a second `FileStream` on the directory
  is refused, also right after `stop()`, and opens after `close()`. A RuntimeException
  from a stop condition fails only that call. A transaction at 2^56 - 1000 is refused with
  a `DbException` whose message says why, and the database goes on.
* `getTrans(Trans.tpos)` gives exactly a transaction's KVs (with U9-9's two rules).


## 4. Fixes

By coord-1109's fixer x27, 2026-11-09, 16:00 to 16:35, in the clone
`/Users/f/fl/bench/2026-11-09/clone-x27` from main at `62345d3`, after 020-27's check of the
Core API's Javadoc (which this builds on). The rule of 2026.4: the Javadoc made true, no new
API, no change of behaviour. U9-1 and U9-3 are fixed in the code by another agent (c18b);
U9-2 by 021-16. Each documented promise below has a test, new in `DbTesterJavadoc` and
passing on the code as it was, or an existing one.

* **U9-4**. `Db`'s "Keys and the layers above" has a paragraph: the Core writes BergDB's keys
  itself, also in a database that the Pub API never opens (`setStartupDistance()` a live value
  of 200 kB at `/#i/-dummy`, which reclaim copies forward; `setRetainDuration()` and
  `setReclaimInternalFraction()` the settings at `/#i/dreclaim/-settings.txt`; reclaim its
  state under `/#i/dreclaim/`); scans return them and the counters count them; every key
  that starts with 01 25 is BergDB's in every database; skip them with a stop condition that
  returns CONTINUE, or two scans. `setStartupDistance()` and `setRetainDuration()` name their
  keys. Test `testCoreWritesBergDbsKeys`.
* **U9-5**. `Db`, new section "Keys and values": any bytes, the empty array too; the order of
  `Arrays.compareUnsigned`; no maximum length, but a key is a path of key nodes, a level per 7
  bytes, so it costs in proportion to its length, and a long key that shares a long start can
  take seconds to commit (021-16, Q1); an empty value is a value, a null one refused; about
  1.88 GB a transaction. Test `testKeysAndValues` (19 keys around 00, 61, 7F, 80 and FF, a
  key of 3,000 bytes, both directions).
* **U9-6**. `Db`, new section "Opening a database": `FileStream` on a directory or
  `MemoryStream`, of which a user calls only the constructor, closed by the `Db`; the
  builder's defaults; an example that writes, syncs, reads and scans. `DbBuilder`'s class
  comment, `clock()` and `mainStream()`. `FileStream` is named as the stream to use; whether
  it and `MemoryStream` are API is 020-27's Q1.
* **U9-7**. `Db`, new sections "Threads" (what may run at once, the state a read sees) and
  "Optimistic transactions" (the read time, `keyRead()`, the hashes, virtual write hashes, a
  retry loop, hashes compared, a scan's range not covered, `KeyModSet`'s coverage of the last
  96,000 to 128,000 key writes since the start); `Trans.Builder`'s `lookupTime()`,
  `keyRead()`, `addReadHash()`, `addReadHashes()` and `addVirtualWriteHash()`. Test
  `testOptimisticTransactions`.
* **U9-8**. `Trans.tt`, `tpos`, `lastPos`, `nextPos`; `GetData`'s and `Kvt`'s class comments
  (their outputs; `Kvt.time` and `GetData.kvTime` left to U9-3's fix); `GetMany`'s defaults,
  and that a `GetMany` is for one call: with `-ea` a second `getMany()` whose result has KVs
  is refused with an `AssertionError`, the database going on, and without it the call adds to
  the result (not "starts its result again", as section 2 has it); `currentTime()`,
  `getFirstAvailablePos()`, `getReclaimIterationCount()`, `getStartupDistance()`,
  `StartInfo.startPos` and `startupDistance`; `getOne()`'s parameters. Test
  `testGetManyDefaultsAndOneCall`.
* **U9-9**. `getTrans()` and `StoredTrans.getValueNodes()`: a delete of a key that had no
  value stores nothing and is not listed; for a value that reclaim copied, a get gives the
  step's transaction, and a get at the step's time less one unit finds the original, as
  021-17's `transactionInfo()` does. Test `testCountersAndListedDeletes` (the delete); the
  copy by 021-17's `PubTester` tests, which use these Core calls.
* **U9-10**. `getTransactionCount()` and `getKvCount()`: since the start, BergDB's own
  transactions and deletes of absent keys included, 0 after a start. Test
  `testCountersAndListedDeletes`.
* **U9-11**. Not changed: an API wish for Frans's list (a Core call that lists the
  transactions after a time or a position).
* **U9-12**. `Trans.Builder`'s class comment and `delete()`: a delete never replaces a put of
  the key, unlike a batch of most embedded stores; to delete, leave the puts out. Test
  `testTransBuilderOneOperationPerKey` (020-27).
* **U9-13**. The test methods of `Keys`, `Trans`, `StoredTrans`, `RerunException` and
  `FileStream` (55 tests, and `Keys.main()`) are package-private, so that the Javadoc does
  not list them; Nano runs them as before (the same 73 unit tests). The two `<` of
  `Keys.compareKeys()` and `FileStream` escaped, and `AppendOnlyStream`'s `EOFException`
  named in full: the Core API's 14 classes pass doclint (html, syntax, reference). Left:
  `Db.testHooks`, `DbBuilder`'s test settings and `Trans`'s working fields, which their
  Javadoc calls test-only or internal (020-27, Q1).
* **U9-14**. `getOne()`, `getMany()` (`@throws StreamIoException`) and `stop()`: a read that
  runs at `stop()` or `close()` can throw `StreamIoException` ("Storage is closing.") where
  a later one throws `DbStoppingException`, the database not failed, and an I/O error of an
  active database is a `DbFailedException`. No code change: the behaviour is designed and
  tested (`DbTesterFailure.testReadDuringStop`); whether such a read should throw
  `DbStoppingException` is U3-6 on Frans's list.

Commits in the clone, on `62345d3`: `aa553a7` (U9-4 to U9-10, U9-12 and U9-14, with the
five tests and the entry in `releases/next.md`, Documentation) and `0ac5851` (U9-13). Gate on
the tip's tree, under the gate lock: BEFORE COMMIT OK (242 s; unit 1582, f 86, DEMOS OK),
16:27; JAVADOC PUB OK. Output in `/Users/f/fl/bench/2026-11-09/x27-gate1.txt`. Not pushed;
the coordinator takes them to the main tree. A merge with c18b's U9-1 and U9-3 may meet
`GetMany.java` (its class comment and fields, not the stop conditions) and the comments of
`Kvt` and `GetData` (their class comments only, not `time` or `kvTime`).
