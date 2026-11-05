Notes for the next release
==========================

What the release notes of the next release after 2026.2 must say, collected
here as the changes are made, so that the release does not have to find them
again. The release folds them into its `releases/VERSION/readme.md`, as
[2026.2](2026.2/readme.md) has them under its changes, and
empties this file.


Pub API
-------

* **`DatabaseBuilder.dir(p)` is gone: `create(p)` or `open(p)`** (bergdb
  015-05; Frans, 2026-11-05). A program that used `dir(p)` does not
  compile; it takes `create(p)`, which does what `dir(p)` did: it opens the
  database in `p`, or creates `p` (with its missing parents) and a new,
  empty database when `p` holds none, as NIO's `StandardOpenOption.CREATE`
  does for a file. 015-01's refusal stays: a directory with `created.txt`
  and no stream byte is refused with `DatabaseMissingException`. The new
  `open(p)` never creates a database: `start()` throws
  `DatabaseMissingException` when `p` is missing, is not a directory, or
  holds no stream file (`*.bergdb`) with a byte, and then creates and
  writes nothing (no directory, lock file, `created.txt` or stream file).
  So a wrong path, or a volume that is not mounted (015-01's case 3, a
  known issue of 2026.2), is refused where `create(p)` would give a new,
  empty database; an application whose database must be there uses
  `open(p)`. 2026.2's recipe for that (check `created.txt` before
  `start()`) is no longer needed. `memory()` is unchanged; the Core API
  and the stream are unchanged.


Reliability
-----------

* **Reclaim's pSafe is the stream length after the call's own records**
  (bergdb 015-54, 016-06's R7-F5; 2026-11-05). The cut waits until the
  startup pos has passed an iteration's pSafe. `Reclaim` set pSafe to the
  end of the user transaction's record, read before the internal records
  that the same call appends before the marking (an iteration's table, a
  step, the table of an iteration done), whose takes can keep nodes dirty
  that the wait is for; it is now the stream's length when it is set, after
  them, as its Javadoc says. Cuts come a little later; no harm was shown
  before. The format is unchanged; the stream's bytes change with reclaim
  on (the table's pSafe values, and where cuts come): StreamDigest's
  decided digests differ from 2026.2's in its 4 configurations with
  reclaim (`l3-*`, 12 of 36), and are 2026.2's in the 8 without. The new
  reference is in 015-54's `digests-new.txt`.
* **An `rw()` keeps the connection's frozen lookup time** (bergdb 015-42,
  016-06's S1-F3; 2026-11-05). The reads of an rw-transaction, and the read
  of an object's previous value by a put in a directory with an index, went
  through the connection's own read state: after `freezeLookupTime()`, the
  first set the frozen time to the latest, and `transactionInfo()` then
  described the transaction's last read. A transaction now reads with its
  own, and leaves the connection's frozen time and `transactionInfo()` as
  they were.
* **`exists()` after `freezeLookupTime()` freezes its own time** (bergdb
  015-48, 016-06's S1-F9; 2026-11-05). It froze the time of the read before
  it, or -1 if there was none, so that every later read threw
  `LookupTimeNotAvailableException` ("Cannot lookup at time -1") until
  `setLookupTime()`; now it freezes the time it read at, as `get()` does.
* **`getLookupTime()` of a new connection is `Time.MAX`** (bergdb 015-59,
  016-06's R8-F4; 2026-11-05), as `setLookupTime()`'s Javadoc says. A
  connection from `newConnection()` had `Long.MAX_VALUE`, above `Time`'s
  range, and `getLookupTime()` threw `IllegalArgumentException`; the reads
  are the same. `Database.connection()`'s Javadoc said "Long.MAX_VALUE"; it
  sets `Time.MAX`, and now says so.
* **`transactionInfo()` after a get that found nothing throws
  `IllegalStateException`** (bergdb 015-62, 016-06's R8-F7; 2026-11-05)
  when no get of the connection has retrieved a value, as when no get has
  been made. It threw `IllegalArgumentException` ("Not a position of a
  transaction, 0."), which the Javadoc does not name. After a get that
  found a value, a later get that finds none leaves `transactionInfo()`
  describing the value found, as before, and its Javadoc now says so.
  The Javadoc of `exists()` and `transactionInfo()` now says that an
  `exists()` that finds the key counts as a get for it, as in 2026.2.
* **`DatabaseBuilder.cryptoKey(CryptoKey.NULL)` after a key means no
  encryption** (bergdb 015-44, 016-06's S1-F5; 2026-11-05), as its Javadoc
  says; NULL was ignored, and the database was encrypted with the earlier
  key. `cryptoKey(null)` throws `IllegalArgumentException`, as `dir(null)`
  did and `create(null)` and `open(null)` do (015-05), not a
  `NullPointerException`.
* **`CryptoKey` has a `hashCode()` that agrees with `equals()`** (bergdb
  015-45, S1-F6; 2026-11-05): equal keys were not found in a `HashSet` or a
  `HashMap`.
* **A `byte[]` value is copied at its put** (bergdb 015-47, S1-F8;
  2026-11-05). The database kept the caller's array as the value in
  memory: a change of the array after a put changed what reads returned
  until the value left memory or the database restarted, while the stream
  had the bytes of the commit. A get still returns the database's own
  array, zero-copy, as before (Frans, 2026-11-05): it must not be changed,
  and the Javadoc of `Connection.get`, `ReadInterface.get`,
  `RwEnvironment.get`, `useIndex()` and `usePrimary()` now says so, and
  what a change does. The Javadoc of `Connection.put`, `WBuilder.put` and
  `RwEnvironment.put` says that a `byte[]` is copied. The Core API keeps
  its arrays, and `Db.getOne`'s and `Trans.Builder`'s Javadoc says so.
* **Key replace replaces every `${transactionTime}` of a key** (bergdb
  015-64, R8-F9; 2026-11-05), as `Connection.setEnableKeyReplace()` says;
  only the last was replaced. A key with two or more occurrences is stored
  under another key than before; one with a single occurrence is unchanged.
  StreamDigest's digests are unchanged: its workloads use the Core API.


Documentation
-------------

* **DbObject and user indexes are experimental** (bergdb 018-01, D2 and D6,
  W1; 2026-11-05). The Javadoc says that they are experimental in 2026.3,
  with known faults, and may change in a later release:
  `Database.indexBuilder` and `deleteIndex`, `Connection.useIndex` and
  `usePrimary`, the interfaces `IndexBuilder`, `UseIndexBuilder` and
  `UsePrimaryBuilder`, and a value that is neither a `String` nor a
  `byte[]`: `put(Object)` (`WBuilder`, `RwEnvironment`), a put of an object
  at a key (`Connection`, `WBuilder`, `RwEnvironment`) and a get into
  another class (`Connection`, `ReadInterface`, `RwEnvironment`); also
  `Database.PRIMARY`, `StartupInfo.getStartupJobs()` (the index jobs a
  start resumes), and `DbObject` and `DbArray` (`bergdb.pubimp`), and the
  exceptions `IndexAlreadyExistsException`, `NoSuchIndexException`,
  `MissingKeyFieldException` and `ObjectCreationException` say that they
  belong to these parts (Frans, 2026-11-05, 10:31). So do the Pub API's
  overview, `bergdb.pub`'s package description, README.md and
  docs/levels.md, section 1. Their tests still run in `before-commit.sh`.
  The notes say it in "What it is" and in the known issues, as 2026.2's say
  it of replication; their faults are those of 018-01, section 3.2.
