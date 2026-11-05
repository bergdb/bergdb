Notes for the next release
==========================

What the release notes of the next release after 2026.2 must say, collected
here as the changes are made, so that the release does not have to find them
again. The release folds them into its `releases/VERSION/readme.md`, as
[2026.2](2026.2/readme.md) has them under its changes, and
empties this file. A change of the stream's bytes, within the format,
names the StreamDigest configurations whose digests changed and the entry
that keeps its digests before and after (bergdb 018-01, section 2).


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
* **`exists()` of a malformed key throws `IllegalArgumentException`, as
  `get()` does** (bergdb 019-05; Frans, 2026-11-05). A connection's
  `exists()` answered `false` for a key that does not follow the allowed
  format (empty, without the leading `/`, `/` alone, ending with `/`, or
  with `//`), where `get()` threw, and an rw-transaction's `exists()` threw
  too; now the two agree with `get()`. A program that passed such a key to
  a connection's `exists()` gets the exception where it got `false`: a call
  that is a programming error, as a null key already was. The Javadoc of
  `Connection.exists` and `ReadInterface.exists` says so. The Core API and
  the stream are unchanged.
* **The retain duration is kept in the stream;
  `DatabaseBuilder.retainDuration` is gone** (bergdb 015-87; Frans,
  2026-11-05). A start took the builder's retain duration, forever by
  default, not the one the database ran with (2026.2's known issue "The
  retain duration is not kept in the stream"): a program that set it with
  `Database.setRetainDuration` after the start got no reclaim after a
  restart, and a stream that grew without a bound; one that opened the
  database with another value got other bytes than without the restart
  (010-01, P2). Now `Database.setRetainDuration` commits the value in a
  small transaction of the database's own, and a start reads it: a restart
  keeps it. A call with the value in force writes nothing; a call on a
  database that is stopping, stopped or failed throws as a transaction
  does and changes nothing; its Javadoc no longer says that it can be
  called before `start()`. The builder's `retainDuration(Duration)` is
  removed (Frans: "remove it from both layers"): a program that used it
  does not compile, and calls `Database.setRetainDuration` once, after
  `start()`, instead. A database whose duration was never set keeps every
  state (forever), as before. The Core API follows:
  `DbBuilder.retainDuration` and `retainForever` are removed, and
  `Db.setRetainDuration` (JMX's three setters go through it) and
  `Db.setReclaimInternalFraction` (JMX only) keep their values in the
  stream the same way. The step reserve (`DbBuilder.reclaimStepReserve`)
  is a setting for tests, not kept. The format: under Format, below.
* **`Time.resolve(TimeZone, String)` uses its time zone** (bergdb 015-57,
  016-06's R8-F2; 2026-11-05); it resolved in UTC whatever zone was given,
  so `Time.resolve(Europe/Stockholm, "2013-08-19 14:29")` was 14:29 UTC, not
  12:29 UTC. A null zone is refused with `IllegalArgumentException`, as by
  `resolve(TimeZone, Time, String)`; it was ignored. `Time.utc(String)` is
  unchanged.
* **`TestClock.setTime()` takes the clock's current time** (bergdb 015-58,
  016-06's R8-F3; 2026-11-05), as its Javadoc says ("larger than or equal
  to"); it threw `IllegalArgumentException`, also for time 0 on a new clock.
  An earlier time is still refused.


Reliability
-----------

* **A transaction is no longer refused because a cut overtook its warmup**
  (bergdb 015-52, 016-06's R7-F3; 2026-11-05). Before the write lock, a
  transaction reads its keys once to load their nodes, at the latest time
  when it starts. When such a read waited on the storage while other
  writers committed and reclaim cut the stream past that time, `execute()`
  (and a Pub API transaction through it) threw
  `LookupTimeNotAvailableException`, which its Javadoc does not list, and
  the transaction was not run. Now that read just ends, and the
  transaction runs. It needed a read stalled for longer than the retain
  duration, at least a second, with other writers busy. The stream's bytes
  are unchanged.
* **A reclaim step keeps its values within the value limit** (bergdb
  015-50, 016-06's R7-F1; 2026-11-05). A step rewrote the old values of
  its scan, about 16 KB, in one transaction, whose last value could be of
  any size; when they passed 7/8 of the record limit together (a value
  within about 16 KB of 1.88 GB, each committed within the limit), the step
  was refused inside a user transaction's commit, which failed the
  database, and again at the first commit after every restart. A value
  that would pass the limit now starts the next step. The stream's bytes
  are unchanged by this: StreamDigest's digests are those before it.
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
* **The sleep between reruns of a conflicting rw-transaction is capped at
  640 ms** (bergdb 015-88; Frans, 2026-11-05): 10, 20, 40, 80, 160, 320,
  640, then 640 ms for every further rerun; it was capped at 10,240 ms. On
  a hot key a call took up to 10.23 s, eleven attempts whose ten sleeps
  were 10 + 20 + ... + 5,120 ms. The same holds for a write-only
  transaction with object operations, which uses the same loop. The
  contract is unchanged: a transaction is rerun until it commits. The
  Javadoc of `Connection.rw` now says so, and that under overload it may
  never commit: a long action while other transactions write more than
  about 100,000 keys, the conflict history, has every attempt refused.
* **A failed eviction batch lets no transaction in before the failure**
  (bergdb 015-66, 016-06's R4-F1; 2026-11-05). A batch of the eviction
  thread that throws (a bug, an `OutOfMemoryError`) fails the database
  (2026.2, 015-25), but it did so after it had let go of the write lock: a
  transaction that waited for the lock could still commit and append, on
  the memory state the batch left. The failure is now set before the lock
  goes, and such a transaction is refused with `DbFailedException`.
* **An eviction batch examines at most its handles** (bergdb 015-67,
  016-06's R4-F2; 2026-11-05): 4,096, or 65,536 under pressure, as the
  documentation says. A batch took each of the node table's 4,096 maps
  whole, and a map grows with the resident index nodes, so in a large
  database one batch, which a writer may wait for, did more work than its
  bound. A map with more handles than a batch has left is now taken in
  parts, and the next batch goes on where one stopped.
* **A start no longer keeps the large values of its rerun in memory**
  (bergdb 015-68, 016-06's R4-F3; 2026-11-05). A start reruns the
  transactions after the startup position; their values over 1 MiB stayed
  in memory, outside the cache's budget, until the database's next write,
  so a database opened for reads kept them for as long as it ran. They are
  now treated as after any write: read from the stream when needed.

* **A record whose size field is larger than its content is refused** at a
  start (bergdb 015-72, 016-06's R6-F1; 2026-11-05), with a
  `StreamFormatException`. A corrupt size that ended on the last byte of a
  later record was taken, and the records it covered were skipped without a
  word: the start succeeded with their transactions lost. Valid streams are
  read as before; the stream's bytes are unchanged.
* **A corrupt got-dirty id, topPos or startupPos is refused at a start**
  (bergdb 015-75, 016-06's R6-F4; 2026-11-05), with a
  `StreamFormatException` that names it. These were checked by asserts
  only: without `-ea` a got-dirty entry whose id was not the node's at its
  position was accepted, and a negative startupPos gave an
  `IllegalArgumentException`; with `-ea` they were `AssertionError`s. A
  startupPos that is not a multiple of 8, is in the first meta block, or is
  after its record is refused too. Valid streams are read as before; the
  stream's bytes are unchanged.
* **A transaction that runs when `stop()` or `close()` comes returns** as
  committed (bergdb 015-53, 016-06's R7-F4; 2026-11-05). With a finite
  retain duration, a reclaim step or table write that the transaction
  allowed was refused as the database was stopping, and `execute()` threw
  `DbStoppingException`, which says the call was refused, although the
  transaction was committed and was there after a restart; a caller that
  retried it applied it twice. `setStartupDistance()` at that moment put
  back the old distance in memory and threw, while the stream kept the new
  one. The stream's bytes are unchanged.
* **A user transaction in the last 1,024 database times is refused**
  (bergdb 015-55, 016-06's R7-F6; 2026-11-05), with a `DbException`, and the
  database goes on: those times, before 2^56 - 1 units (about the year
  2198), are kept for reclaim's internal transactions after a user
  transaction. One at the last time was taken, the reclaim step it allowed
  found no time left, and the database failed although the transaction was
  committed. Only a wrong or a test clock reaches these times.

Format
------

* **A reserved internal key: reclaim's settings,
  `/#i/dreclaim/-settings.txt`** (bergdb 015-87), beside reclaim's table
  and current row; a format change that Frans approved (2026-11-05, 13:12:
  "Yes, let's do B as recommended"). Its value is two lines, each ending
  with a newline: `retain=` and the retain duration in time units
  (9223372036854775807, `Long.MAX_VALUE`, for forever), and `fraction=`
  and the internal fraction in units of 2^-16 (16384, a quarter, by
  default), in decimal. A setter call writes it when it changes a value,
  and only then (Frans, 13:52: "Implement your recommended (1)"), so a
  database whose settings were never changed has none and runs with the
  defaults, as do 2026.2's databases, which open as before. A start
  refuses a value in another form with an `InternalDataException`.
  Reclaim's steps rewrite it like any live value, so cuts keep it. 2026.2,
  and the C clone (012, a port of 2026.2), read such a stream and keep the
  KV (their steps rewrite it) but do not honour it: they run with the
  values their own API sets.
* **The stream's bytes change only where a setter is called.**
  StreamDigest's 8 configurations without reclaim give 2026.2's digests.
  Its 4 with reclaim (`l3-*`, 16 of 48 digests) change: StreamDigest sets
  their retain duration after the first start, which now writes the
  settings' record before the first user transaction. In each
  configuration the modes plain, reads, restarts and the new
  `restarts-once` (the duration set after the first start only, which
  differs from plain on 2026.2's jar: the fault) give the same stream. The
  digests before and after are in 015-87's folder
  (`items/015-todo/87-retain-duration-in-stream/`: `digests-base.txt`,
  `digests-new.txt`, `digest-summary.txt`). 2026.2's reference has three
  modes: compare with it with `-Dmodes=plain,reads,restarts`.


Internal
--------

* **`AppendOnlyStream.seekFirstPos()` is gone** (bergdb 019-04; Frans,
  2026-11-05), from the interface and from every stream. It made an empty
  stream start at a later position, for replication, which is gone since
  2026-11-04 (005-11); no layer of BergDB called it, and `MemoryStream`,
  `OneFileStream`, `DummyStream` and `StorageManager` threw
  `UnsupportedOperationException`. `FileStream` keeps it as a
  package-private method for its own tests. An `AppendOnlyStream` of a
  program's own that has the method still compiles, unless it marks it
  `@Override` or calls it on the interface. The Core API, the Pub API, the
  stream format and the stream's bytes are unchanged.
* **`FileStream`, `BufferedStream` and `StorageManager` refuse an append
  of a negative length** (bergdb 015-26 and 015-79; 2026-11-05) with
  `IllegalArgumentException`, as `AppendOnlyStream`'s Javadoc says, and
  leave the stream as it was. `FileStream` lowered its length, which hid
  appended bytes and failed the next append; `BufferedStream` returned, and
  `StorageManager` lowered its length. No layer of BergDB passes a negative
  length; the stream's bytes are unchanged.
* **`FileStream.setMax2G(true)` caps the size of every new file at 2 GB**
  (bergdb 015-33; 2026-11-05): after a start that chose small files from
  the last two, the next file could take the size rule's 10 GB. Nothing in
  BergDB sets it; the stream's bytes are unchanged.


Documentation
-------------

* **A value transformation's result is the caller's to keep within the
  limit** (bergdb 015-51, 016-06's R7-F2; 2026-11-05). In the Core API, a
  transaction's size is checked before its go point (005-17), with a value
  transformation's input; the transformation runs after it, and its result
  is not checked. `ValueTransformation`'s Javadoc now says that the result
  must keep the transaction's value nodes within 7/8 of the record limit
  (about 1.88 GB), as a value given directly must, and that a result whose
  record does not fit fails the database, as an exception of the
  transformation does; `KeyTransformation`'s says the same of its key, and
  docs/levels.md, section 3. The Pub API uses no value transformation. The
  code and the stream's bytes are unchanged.
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
* **The crash contract is stated** (bergdb 014-01, section 7; Frans,
  2026-11-05). BergDB assumes that its stream's bytes are read back
  exactly as they were written, and that a crash leaves a prefix of what
  was appended, at least up to what was forced to storage; the storage
  under the stream (a file system, block storage, flash) ensures this, not
  BergDB. A transaction is then seen whole or not at all, and `sync()`
  adds durability: a transaction it returned for survives. A start
  recovers only a truncated tail, as before: it completes a torn last
  record as an aborted one, by appending. Other damage is an integrity
  failure outside the contract: a start may refuse it, or a read fail the
  database. `FileStream` relies on a file system that keeps appends in
  order: POSIX does not promise it for writes that are not forced, though
  common file systems keep it. 2026.2's known issue "Holes in an unforced
  tail" is such damage, outside the contract, and not a known issue of
  2026.3. `AppendOnlyStream`'s Javadoc states an implementation's duty,
  and docs/levels.md, section 8, the assumption. The code, the format and
  the stream's bytes are unchanged.


Known issues and limits
-----------------------

* **A corrupt record header can still lose data at a start that
  succeeds** (bergdb 015-73, 016-06's R6-F2; Frans, 2026-11-05). No
  checksum covers a record's header. 015-72 and 015-75 refuse a corrupt
  size, got-dirty id, topPos or startupPos in most forms. What is left:
  the last record's startupPos damaged to an aligned value that is exactly
  the start of an earlier record, one that the take never reached. The
  start then begins there, and the transactions before it are lost without
  a word. Such damage is outside the crash contract (014-01, section 7),
  and its detection is best effort. A checksum of the record header would
  catch it, at the next change of the record format (019-07). In 2026.2
  and 2026.1 too.
