Notes for the next release
==========================

What the release notes of the next release after 2026.5 must say, collected
here as the changes are made, so that the release does not have to find them
again. The release folds them into its `releases/VERSION/readme.md`, as
[2026.5](2026.5/readme.md) has them under its changes, and
empties this file. A change of the stream's bytes, within the format,
names the StreamDigest configurations whose digests changed and the entry
that keeps its digests before and after (bergdb 018-01, section 2).

Emptied at release 2026.5 (2026-11-13), whose notes hold what was there.

The release's files are on GitHub Releases, under its tag: the jar and
the Javadoc zip. `releases/VERSION/` holds the notes
(`readme.md`) and `SHA256SUMS`; there is no source zip (GitHub archives
each tag), and `baseline.zip` is not published (bergdb 026, "How the
release is made"; 029). The notes say so where they list the files.


### The stream

* **Databases of release 2026.5 and earlier are refused: make them again**
  (bergdb 028-15, option A; Frans, 2026-11-18, 10:50). The startup
  distance moved out of the meta blocks into a key-value pair of BergDB's
  own, `/#i/-sd`, and the meta block's version is 155 (154
  until now). A start of an older database throws a
  `VersioningStreamException` whose message names release 2026.5, and
  writes nothing. To keep the data, read it with release 2026.5 and put
  it into a new database with this release. Release 2026.5 refuses a
  database of this release in the same way. A change of the startup
  distance (`Database.setStartupDistanceInMb`, `Db.setStartupDistance`)
  now writes a small transaction, not one of 200 kB, and a crash inside
  it starts with the old setting. The Core API: every database has that
  key-value pair from its creation on, and a scan of the whole key space
  returns it (Db, "Keys and the layers above"); the creation writes two
  records, so a new database's first transaction has a time one unit
  later than before. The stream's bytes changed for every configuration
  of StreamDigest (a record after the primordial one, and no dummy
  value).
* **A crash while a database is created gives `DatabaseNotCreatedException`,
  also between the creation's two records** (bergdb 028-18, option C;
  Frans, 2026-11-19, 09:53). A creation now writes two records, the empty
  database and the startup distance; a start that finds the first
  without the second refuses the database as not created and writes
  nothing, as for a crash earlier in the creation: remove the files and
  start again (`DatabaseNotCreatedException`'s Javadoc). So a database is
  created whole or not at all. With the Pub API, `created.txt` is written
  after both records are synced, before `start()` returns.

* **Reclaim charges every index node that its steps make dirty** (bergdb
  028-26). With a finite retain duration (`setRetainDuration`), a
  reclaim step's internal transaction counts toward reclaim's allowance,
  a fraction of the stream's growth, the bytes of the index nodes that
  it makes dirty; since record format 8 and its writer it counted only
  those on its keys' paths, not the nodes that the writer makes (found
  by a review of the writer). It now counts them too, and stores its
  progress again in a small internal transaction of its own after most
  steps, so a restart resumes with the same count. Reclaim so keeps
  closer to its fraction: in a test workload with reclaim the stream
  grew 1.5 to 7.8 % less. The stream's bytes changed for StreamDigest's
  l3-* configurations (reclaim on), not for the l2-* ones; the digests
  before and after are in 028-26.

### Pub API

* **`bergdb.pub.Limits`: the limits as constants, and a check of a key
  before a call, a new class** (bergdb 026-02, option A; Frans,
  2026-11-13, 09:11, QK1 to QK4). `Limits.MAX_KEY_BYTES` and the other
  limits, L1 to L6, as constants, the Core's `Db`'s by reference;
  `Limits.keyBytes(String key)`, a key's bytes as stored (its UTF-8 and
  one byte more for each '/'), also for a key over the limit, so that a
  program knows how far over it is; `Limits.checkKey(String key)`, which
  throws the very `IllegalArgumentException`, with the same message,
  that a put or a delete throws for the key. Both depend on the key
  alone, not on a database or a connection. A program no longer learns
  of a long key from a refused put, which spoils a `WBuilder` (024-27,
  QR1). A put, a delete and `checkKey` run one check
  (`PubKeys.checkedIkey`), and a property test compares `keyBytes` and
  `checkKey` with a put on a memory database. L6, an object's levels in
  an index entry, has no method: the Javadoc of `Limits` says how to
  count them (QK3). The Core API gets no method: a key fits if its
  bytes are at most `Db.MAX_KEY_BYTES`, as Db's Javadoc now says
  (option E). No stream change; no test's expected value changed.


### Core API

* **A value transformation that throws or passes 8 MiB refuses its
  transaction; the database goes on** (bergdb 026-06; 010-04, R5; Frans,
  2026-11-12, 14:42). A user transaction's value transformations now
  run in `Db.execute()` under the write lock, after the key
  transformations and before the go point, in key order, each with the
  value as given and the key's value before the transaction, as before.
  A `RuntimeException` from one, a result over 8 MiB (L4), or results
  that take the transaction over 32 MiB of keys and values (L5) refuse
  the transaction with a `DbException` (the exception as its cause):
  nothing is written, and the `Trans` is left as it was, its values as
  given, its keys as written, its time given back, so it can be run
  again. In 2026.5 each failed the database (2026.5's Known issues;
  024-24, QL6; 015-51). An `Error` still fails it. **A key
  transformation that throws** a `RuntimeException` is refused in the
  same way (026-06, D9). No stream change. Tests whose expected values
  changed: `DbTesterLimits.testTransformedValueOverL4`,
  `DbTester.testTransformedValueBeyondRecordLimit`, `LimitsTester` (a
  result above the value limit refused, no run ends by the caller's
  fault), and three of `DbTesterFailure` that now fail after the go
  point by a test hook.
* **The node size is 30 for every database; `DbBuilder`'s setters of it
  are gone** (bergdb 026-08; Frans, 2026-11-13, 09:17 and 09:21).
  `DbBuilder.maxNodeSize8()`, `maxNodeSize14()`, `maxNodeSize30()` and
  `maxNodeSize62()` are no longer public: a database made by the Core
  API has the node size 30, as one made by the Pub API always had, and
  the stream format promises that size only (027-03, section 6). A
  program that called
  `maxNodeSize30()` drops the call; one that made a database at 8, 14 or
  62 cannot start it with this release, which refuses it, as before,
  with a `StreamFormatException` that writes nothing (the meta block's
  node-size field is kept and checked, a hook for a later release that
  allows other sizes). The other sizes stay for BergDB's own tests
  (`bergdb.core.TestNodeSize`, not API). No stream change; no test's
  expected value changed.
