# 024-26. User apps against 2026.5's new algorithms

Created 2026-11-11 by Frans Lundberg. Status: open.

A round of "AI as the user" testing (006-20) against the algorithms that
`main` changed on 2026-11-11 for release 2026.5: merges of underfull key
nodes at the delete (024-21), at most theta dead klongs a key node
(024-23, option 2), CRC32C as the node checksum (024-25), and the limits
(024-24), all of record format 7. An agent of coord-1111 ("apps") played
a new user: it built the release jar from a clone of `main` and wrote seven
applications from the README, the Javadoc and `releases/next.md` only, not
from the implementation, each with an oracle of its own that checks every
result. Nothing in the product code was changed.

Findings are U26-1, U26-2, ...


## 1. In short

Written 00:30 (2026-11-12); section 5 has the exact state.

* **Seven applications**, about 2,800 lines of Java, in
  `/Users/f/fl/bench/2026-11-11/apps/` (a copy in this item's directory,
  `26-user-apps/`), on the release jar of `main` at `bf68084b`.
* **What they ran** (section 3), from 20:24 to 00:39: about 1.2
  million Core transactions of churn and reclaim (DeleteHeavy about 26,000
  transactions and 7 million operations, Churn about 870,000, Readers 1.2
  million beside 3 readers), 32,000 Pub transactions with two indexes,
  some 3,000 restarts each followed by a check against the oracle, and
  about 1,070 SIGKILLs of a child JVM with a check of every recovery that
  got that far.
* **No bug found in BergDB**: no wrong value at any time, no failed
  database, no refusal that wrote anything, no recovery short of a synced
  transaction. The three failures of the night were the app's own (a
  range check, section 3).
* **Javadoc and API findings**: eight, none of them serious (section 4):
  a stale sentence in `KeyTransformation` against `Db`'s "Limits"
  (U26-1), builder methods that do not list the 111-byte refusal (U26-2),
  the level sizes of U+0000, U+0001 and bytes levels (U26-3), and
  `DatabaseBuilder.start()` not naming the refusal of 2026.4's databases
  (U26-8), among them.


## 2. The applications

Each is plain Java with `main`, compiled with `javac` against
`bergdb-release.jar` alone, and exits non-zero on a wrong result. They
share `common/Common.java`: a byte key, the oracle (each key's versions by
transaction time) and checks of a Core `Db` against it: full scans at a
time, gets of present, deleted and never-written keys, range scans forward
and backward (startKey, endKey, GetN), and `Kvt.time` within the write's
time and the lookup time (Kvt's Javadoc). `run.sh quick` runs each once
(about 2 minutes); `run.sh soak N` a round of many seeds.

| App | Scenario | Stress point |
|---|---|---|
| 1 DeleteHeavy | bulk loads, scattered, ranged and near-total deletes, refills | merges, the take-back |
| 2 Churn | overwrite and delete churn, reclaim, a moved clock, restarts | option 2, reclaim, the cut |
| 3 Limits | transactions near and over L1 to L6, Pub and Core | refusals before the write |
| 4 Kill | SIGKILL of a child JVM during deletes and reclaim | recovery |
| 5 Readers | 3 readers at older times while a writer deletes | merges under readers |
| 6 IndexChurn | Pub objects, two indexes, long keys and levels, reclaim | BergDB's long keys |
| 7 Upgrade | a database of 2026.4 opened with 2026.5 | the format refusal |

**1. DeleteHeavy** (Core API, FileStream, node sizes 8, 14, 30, 62, some
runs with a cache budget below the data). Each round: a bulk load of N
keys of six shapes (one segment; a 13-byte shared start; random lengths 2
to 111; exactly 7j bytes, which end with an empty segment; keys that
extend each other; dense 3-byte keys) and edge keys (the empty key, zeros,
0xff runs, 111 bytes); deletes of a random third with a few puts mixed in;
four ranged deletes in key order or reversed; deletes of all but every
30th key; a refill of deleted keys and new ones; churn on a hot range of
300 keys (put, delete, put again in successive transactions, deletes of
absent keys); a transaction of 501 calls on 500 keys (taken: the last call
wins) and one of 501 keys (refused, the stream's length unchanged); deletes
of a whole shape, and every third round of all but every 997th key.
Transactions of 1 to 500 operations with noise calls before the real ones
(the last call wins). After each phase: a full scan, 300 gets, 20 range
scans, 10 prefix scans (`GetMany.Prefix` and `PrefixN` of a key's first
1 to 9 bytes), and for 10 live keys `getTrans(tpos)` names the
transaction that wrote the value; at random a restart (half by `stop()` then `close()`)
followed by the same and reads at older times and one unit before them.

**2. Churn** (Core API, a `Clock` that the application moves, 0 to 100
ms a transaction, a retain duration of 1 to 3 s, a startup distance of
400 to 500 kB so that reclaim runs, internal fractions 0.05 to 0.9).
Three modes: random overwrites and deletes over a key universe with a
moving hot range and ranged deletes of up to 500 keys; a queue (keys in
time order put at the tail, the oldest deleted at the head, 021-25's
shape); large values (1 to 4 keys of 30, values up to 8 MiB). Every 50
transactions: the latest state; `getFirstAvailableLookupTime()` at or
before now less the retain duration (the duration's promise); reads at
four older times, which inside the duration must work and before it work
or throw `LookupTimeNotAvailableException` with the first available time
after them; the transaction of a value followed back through reclaim's
copies to the write (getTrans' Javadoc, 021-17); the stream kept from the
first available position against the live bytes. Restarts every 200 to
800 transactions check that the retain duration and the fraction are kept.

**3. Limits** (Pub API on a directory, then the Core API). Pub keys of 105
to 113 bytes as stored, of ASCII, å, €, an emoji, "ab/" (each "/" counts
two), U+0000 and U+0001, in three directories, with the suffixes `.bin`,
`.txt` and none (objects): taken up to 111 and read back; at 112 and 113
refused by `put`, `w().put`, `delete`, `w().delete` and `rw()`. A deep key
of "/d" parts; a key replace at 111 bytes. Values: 8 MiB taken, one byte
more refused (byte[], String by its UTF-8, by `put`, `w()` and `rw()`);
the largest object near 8 MiB. Operations: 500 puts taken, 501 refused;
600 puts of one key taken; `rw()` of 501 puts refused; new objects and
overwrites in a directory with an index, probed one by one up to the
refusal. Levels of 105 to 112 bytes, one and two levels, a `bytes` level,
a `w()` with one bad object among ten (nothing written), an index built
over objects with long levels (no entry for them). The keys' 56 KiB (L3)
with long keys and long levels in two indexes. 32 MiB of keys and values
exactly (taken) and one byte more (refused). After every refusal the keys
it named are as before, and after each step and a restart every key, every
directory listing and the index `byname` equal the oracle. The Core part:
keys of 111 and 112 bytes by every builder call, a String key, values over
8 MiB, 501 operations (the stream's length and the transaction count
unchanged), L5 exactly, a key transformation that gives 112 bytes
(refused) or 111 (taken), the last call on a key wins, and a key
transformation onto a key that the transaction deletes (refused, nothing
written); then a restart. `WorstCase`, beside it: at each node size, on a database
of 100,000 random keys of 111 bytes, transactions of 500 such keys put,
deleted, put with 32 MiB of values, and half deleted and half overwritten,
which make the most index nodes dirty that the limits allow: each must be
taken (Db's "Limits": within the limits only key or value transformations
can meet the older refusals of 005-17 and 005-31).

**4. Kill** (Core API, node sizes 8 to 62, a retain duration of 0, 1 or
3 s, a startup distance of 300 kB, a cache of 4 MB). The workload is a
function of the seed, the transaction number i and the state before it:
bulk loads, scattered deletes, ranged deletes and churn, each transaction
with a marker key holding i. A child JVM opens the database, reads the
marker n, replays the oracle to n, checks a full scan and 200 gets, prints
"R n", and goes on; every 17th transaction it syncs and prints "S i". The
parent kills it (`destroyForcibly`, SIGKILL) after 0 to 400 ms (in the
start or the check) or 0.3 to 3.3 s, checks that the next child recovers
at least the last synced transaction and never fewer than the start before
it, lets one child in twelve end by itself, and starts a new database
every 25 kills, after a last check with no kill.

**5. Readers** (Core API). One writer: bulk loads to K keys, deletes of
half, a ranged delete of a third, churn, deletes of all but every 25th.
Three readers: full scans, gets and range scans at times the writer has
published, one unit before them and at the latest state, each compared
with the oracle at the read's actual lookup time; with a retain duration
of 1 s a cut read must have its time before the first available one.

**6. IndexChurn** (Pub API, a moved clock, a startup distance of 1 MB, a
cache of 8 MB). Objects with a name of up to 102 bytes (å, €, emoji) and a
number from -500 to 499, in `/items/` with keys of up to 111 bytes, many
sharing long starts, and two indexes: `byname` (string) and `bynamen`
(string, long). Index entries are BergDB's own keys, up to about 230
bytes, so deletes of them go through the merges with keys longer than a
user's. Phases of filling, of 80 % deletes and mixed; `w()` and `rw()`;
puts that keep the levels. Every 40 transactions: the primary scan, gets,
and index scans (all, backward, eq, from/to, prefix, eq then a long bound)
against the oracle, at the latest state and at two older times, with
restarts every 100 to 500 transactions.

**7. Upgrade** (Pub API, two jars). 2026.4's jar (`releases/2026.4`)
makes a database of 2,000 keys with a third deleted; 2026.5's `open()`
and `create()` must refuse it and change no byte of its files (a digest
of the directory before and after); 2026.4's jar then reads every key.


## 3. The runs

Times are F53's, from `date`. Until about 22:00 `night.sh` held the
machine for a timing run, so only short JVMs ran (each under a minute).

| When | What | Result |
|---|---|---|
| 20:24 to 20:50 | each app on a few seeds and configurations, short | all OK |
| 22:24 to 22:46 | `run.sh soak 2`, one slot (below) | 3 FAIL, the app's |
| 22:47 to 22:59 | the three failed runs again; Kill, 300 kills | all OK |
| 22:59 to 23:23 | Kill seed 31: 450 kills, delays from the recovery | all OK |
| 23:23 to 00:02 | larger databases: DeleteHeavy, Churn | all OK |
| 00:02 to 00:24 | `run.sh soak 3`, the same 43 runs on new seeds | all OK |
| 00:24 to 00:39 | Kill seed 41: 300 kills | all OK |

`run.sh soak 2`: DeleteHeavy 16 runs (4 seeds by 4 node sizes, n 6,000,
4 rounds, about 415 transactions, 113,000 operations and 13 to 22
restarts each) and 2 larger (n 20,000 at node size 8 with a cache of 400
kB, 842 transactions; n 30,000 at 30 with 1 MB); Churn 16 runs of 15,000
to 40,000 transactions (about 21 million operations, 750 restarts, 37,000
old reads, 3,000 of them cut, in all) and the large-value mode (300
transactions, values up to 8 MiB, 260 MB of stream kept); Readers 4 runs
of 60 s (100,000 to 140,000 transactions each, 3 readers); IndexChurn 3
runs (16,000 transactions, 55 restarts); Limits; WorstCase at 100,000
keys of 111 bytes. All OK but three runs (Churn 202 at node size 8, Churn
203 at 30, Readers 211), which failed in the app: `TreeMap.headMap()`
threw "toKey out of range" in Common's range check when a scan's start
and end were one key and the start exclusive. Fixed at 22:47 and rerun
in hold 2.

Hold 2: the three runs again, with the app fixed: OK (Churn 202: 20,000
transactions, 36 restarts; Churn 203: 20,000, 42; Readers 211: 137,000
transactions, 3,674 checked reads, 964 of them cut, each after the first
available time). Kill seed 21: 300 kills (26 aimed at the start), 29 clean
exits, 14 databases of 25 kills, 168 recoveries checked against the
oracle; the other children were killed before their check ended, as the
replay grew with the database. So the parent was changed to count most
delays from the child's "R" line, with 10 kills a database (hold 3).

Hold 3, Kill seed 31: 450 kills (41 aimed at the start, the others 50 ms
to 2.3 s after the child's check), 34 clean exits, 49 databases of node
sizes 8 to 62 with a retain duration of 0, 1 or 3 s, 448 recoveries
checked against the oracle (a full scan and 200 gets), each at or after
the last synced transaction: all OK.

Hold 4, larger databases, a cache budget below the data: DeleteHeavy at
node size 30, 300,000 new keys a round, 2 rounds, a cache of 20 MB (5,880
transactions, 1.8 million operations, 7 restarts, 639 MB of stream, 280
s); at node size 8, 150,000 keys a round, 5 MB (3,037 transactions, 0.9
million operations, 489 MB, 383 s); Churn at node size 30 over 200,000
keys, a cache of 20 MB, a startup distance of 2 MB (30,000 transactions,
61 restarts, 2,644 old reads, 820 chain steps, 198 MB kept at most); the
queue at node size 8 with 100,000 live keys (40,000 transactions, 79
restarts, 112 MB kept at most): all OK.

`run.sh soak 3`: the 43 runs of round 2 with the seeds of round 3: all
OK (results/soak-3-0001.log).

Hold 5, Kill seed 41: 300 kills (33 aimed at the start), 29 clean exits,
33 databases, 307 recoveries checked: all OK.


## 4. Findings

No bug so far. Javadoc and API findings:

* **U26-1 (doc).** `KeyTransformation`'s Javadoc says "The new key is not
  size-checked: Db.checkSize counts the key before the transformation";
  `Db`'s "Limits" says that a key that a key transformation makes longer
  than 111 bytes is refused by `execute()` with a `DbException`. The
  behaviour is `Db`'s (refused, nothing written): the sentence in
  `KeyTransformation` is stale. It also names `trans.kvs[index].key`
  (Kv has `getKey()` and `setKey()`, no public field) and
  `trans.transTime` (Trans has `tt`).
* **U26-2 (doc).** `Trans.Builder.delete(byte[])`, `delete(long[])` and
  `put(long[], byte[])` list only the null key under Throws; they also
  refuse a key of more than 111 bytes, as the class Javadoc says.
  `keyRead()` takes a key of 112 bytes (a read, so maybe right; not said).
* **U26-3 (doc).** The package's Limits: "a string level takes its UTF-8
  and a byte". U+0000 and U+0001 take two bytes each in a level: a name
  of 105 U+0000 chars (106 bytes by the Javadoc's count) is refused. A
  `bytes` level's size is not given: bytes 0x00 and 0x01 take two bytes
  each (at most 55 zero bytes), others one (at most 110).
* **U26-4 (doc).** L1 counts a delete of a key without a value: 500 puts
  and a delete of an absent key are refused, though such a delete "stores
  nothing" (Db.getTrans). The Javadoc's "the KVs it puts or deletes"
  allows it; one sentence would make it plain.
* **U26-5 (API, doc).** A `WBuilder` whose `put()` was refused with
  `IllegalArgumentException` (a key over 111 bytes) goes on: a caller that
  catches the exception and calls `execute()` commits the other puts. The
  package says a `w()` writes "all of them, or none"; the Javadoc could
  say that a refused call leaves the builder as before it.
  **Decided** (Frans, 2026-11-12, 07:36, "B. Ensure the behaviour is
  clear in the Javadoc."): a refused call spoils the builder, the
  `WBuilder` and the Core's `Trans.Builder` alike, so that its
  `execute()` writes nothing; made in 024-27, with U26-1 to U26-4 and
  U26-8.
* **U26-6 (note).** `get()` of a key over 111 bytes returns null and
  `exists()` false, where a put or a delete throws. Consistent with
  "Keys" in Connection; a user may expect the same refusal.
* **U26-7 (note).** New objects in a directory with one index cost 1 + k
  operations: 250 fit one `w()`, where the Javadoc's "166 with one" is the
  case of overwrites that change the level (166 taken, 167 refused, as
  said); overwrites that keep the level cost 1. With long keys and long
  levels in two indexes, L3 binds first: 58 overwrites taken, 59 refused
  (295 operations), with a clear message.


* **U26-8 (doc).** `DatabaseBuilder.start()`'s Javadoc names the refusals
  of a database that an earlier release encrypted and of one with an index
  of 2026.3, but not that of every database of 2026.4 (record format 6):
  `start()` throws `bergdb.storage.VersioningStreamException` ("format 6
  was written by release 2026.4, which opens it"), a clear message, and
  changes no file (app 7); `create()` on such a directory too. The release
  notes say it; the Javadoc of `start()` could.


## 5. State

Written 00:30 (2026-11-12).

* **Done**: the seven applications and their runs of section 3, all OK on
  BergDB; the findings of section 4. Nothing in `java/` or `lean/` was
  changed; no branch, no commit.
* **Ended** at 00:39 with the last Kill run (section 3); no slot held.
* **Where**: `/Users/f/fl/bench/2026-11-11/apps/`: the clone of `main` at
  `bf68084b` in `clone/`, the release jar copied to `bergdb-release.jar`,
  2026.4's jar to `bergdb-2026.4.jar` (app 7), the sources, `run.sh` and
  the logs in `results/`. The sources are also in this item's
  `26-user-apps/`; to run them there, copy the two jars beside `run.sh`.
* **To continue**: `sh run.sh quick` (about 2 minutes) after a change of
  the Core, as a regression check; `sh run.sh soak N` (about 22 minutes,
  one slot) with a new N for new seeds; `java -cp
  bergdb-release.jar:out Kill parent SEED data/a4 300 10 2500` (about 15
  minutes) for kills. A FAIL line names the app, the seed and the
  configuration, which rerun it alone. Next scenarios not yet written:
  several writer threads deleting at once, Pub readers at older times
  with indexes beside a writer, and databases of 1M keys and more.
* **For the coordinator**: U26-1 to U26-3 and U26-8 are Javadoc fixes;
  U26-4 and U26-5 one sentence each; U26-6 and U26-7 notes only.


Log
===

2026-11-11. Created by "apps" of coord-1111; the applications and their
short runs (20:24 to 20:50).

2026-11-11 to 2026-11-12. The long runs in slots, 22:24 to 00:39; the app's
range-check bug fixed at 22:47; State written at 00:30.
