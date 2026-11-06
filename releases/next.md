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
* **`Time.toString()` and `toUtcString()` may be called from any thread**
  (bergdb 015-63, 016-06's R8-F8; 2026-11-05). They formatted with one
  shared `SimpleDateFormat`, which is not thread-safe, so threads that
  formatted times at once (a `Transaction.getTime()` or
  `Database.currentTime()` in a log line, say) could get another thread's
  time or an `ArrayIndexOutOfBoundsException`. The strings are unchanged.
* **Each `freezeLookupTime()` freezes anew, at the latest state** (bergdb
  018-04, Q2; Frans, 2026-11-06). A connection has one lookup time:
  `setLookupTime(t)` sets it to t, and `freezeLookupTime()` to the latest
  state as of the next read, which the next read fixes; each undoes the
  other. A second call on a frozen connection kept the first frozen time,
  and a call after `setLookupTime(t)` froze the state at t; now each call
  freezes the latest state as of its next read, so a loop that calls
  `freezeLookupTime()` before each batch of reads reads the new state each
  time. `getLookupTime()` is `Time.MAX` until that read. The stream is
  unchanged.
* **A deletion job that ended early says "Stopped"** (bergdb 019-40,
  015-61; a known issue of 2026.2 and 2026.1). A deletion job that a
  `stop()`, a `close()` or a failure ended reported progress 100 and
  "Done! Deleted ..."; now its note starts with "Stopped", as an index
  build's does, and the deletion goes on at the next start.
* **A String value with a lone surrogate is refused** (bergdb 019-44;
  2026-11-06) with `IllegalArgumentException` at the put, as a key with
  one is (015-49): it was stored with `?` in its place, silently, and a get
  returned other characters than were put. Values with surrogate pairs are
  stored as before; strings inside an object (experimental) keep the `?`.
* **`DatabaseBuilder.clock(null)` throws `IllegalArgumentException`**
  (bergdb 019-44; 2026-11-06); it was taken, and `start()` threw after it
  had made the directory and `bergdb.lock`. `TestClock` is thread-safe
  (its time volatile), and a `Clock` must be.


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
  reclaim (`l3-*`, 12 of 36), and are 2026.2's in the 8 without. The
  digests before and after are in 015-54's folder (`digests-base.txt`,
  `digests-new.txt`).
* **A String or `byte[]` put and then a delete of a key without a suffix
  leave no entry** (bergdb 015-41, 016-06's S1-F2; 2026-11-05), in an
  `rw()` or a `w()`: the put stayed, as the delete of such a key, an object
  key, was kept apart from the put. An object put and then a String put of
  one key now leave the String; the object stayed (an object put is
  experimental). The last call on a key wins, as for a key with a suffix
  (015-40).
* **`Database.connection()` no longer keeps the connection of every thread
  that called it** (bergdb 015-60, 016-06's R8-F5; 2026-11-05). Each thread
  that had called it, and its connection, stayed in the database's map until
  the database stopped: memory without a bound in a program whose threads
  come and go. The map now holds its threads weakly: an ended thread's
  connection goes once the thread is no longer referenced and the collector
  has taken it, at a later call of `connection()`.
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
* **A key with a lone surrogate is refused** (bergdb 015-49, S2-F24;
  2026-11-05) with `IllegalArgumentException`, as a malformed key, by
  every call that takes a key, a directory or an index name: a char of
  U+D800 to U+DFFF that is not part of a surrogate pair. It was stored
  with `?` in its place, so "/k/a" followed by U+D800 and "/k/a?" were one
  key, and a put of one overwrote the other (two index names, likewise
  one index in the database). Keys with surrogate pairs, and every key
  taken before, are stored as before; a key that was stored with `?`
  stays and is read by its `?`.
* **A second `start()` of a `memory()` builder whose database runs is
  refused** (bergdb 015-65; 2026-11-05), with `IllegalStateException`, also
  while that database is closing after `stop()`; it gave the running
  database's stream to a second database: both appended to it, each missed
  the other's puts, and the close of one closed the stream of the other
  (with a crypto key, the second start wrapped the stream's encryption
  again). The running database runs on as before; `memory()` again gives a
  new database, as a directory of `create()` is refused while a database
  has it (005-63). The stream is unchanged.
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
* **A lowered cache size is reached when what must stay in memory fits**
  (bergdb 015-70, 016-06's R4-F5; 2026-11-05). After
  `Database.setCacheSizeInMb` lowered the budget, eviction could stop
  above it, with memory that could go still held, when the nodes that must
  stay in memory (those changed since the startup position) had shrunk
  since eviction last counted them. It now goes on until the cache is
  within the budget, or until what is left cannot go.
* **The cache's measure of memory counts changed index nodes** (bergdb
  019-20 and 019-21; 2026-11-06). Two kinds of index node stayed counted
  below their size: a node that a transaction changed and then replaced
  (a split), and the nodes of the startup section that a start's rerun of
  the transactions changed. The difference, small, stayed until the node
  left memory, and in a database opened for reads for as long as it ran.
  Both are now counted with their size.
* **A transaction no longer keeps a large value in memory** (bergdb
  019-22; 2026-11-06). Before the write lock, a transaction reads its keys
  once to load their nodes; that read kept a key's current value over
  1 MiB in memory, against the rule that such values are read from the
  stream when needed, so a transaction that replaced a large value
  brought the old one back into memory, until eviction took it. It now
  keeps no value over 1 MiB, as a get does.
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
* **A failed background write fails the database at the next call**
  (bergdb 015-35 and 015-81, 016-06's R3-F10, R5-F3 and R5-F6;
  2026-11-05). When the storage thread's write failed (a disk error), the
  database stayed active until a transaction, a sync or a read from the
  disk met the failure: gets served from memory went on, also of the
  transaction whose record was never written. Now every call after it
  throws `DbFailedException`, as after a failed transaction (010-01, P7).
  And if the stream's close then threw an unchecked exception, a sync
  waited for ever and the database ran on; now the sync throws. After
  such a failure, `close()` returns when the stream is closed and its
  directory released, also while the failed call still closes it (review
  R1 of night 006-12). The stream's bytes are unchanged.
* **`close()` reports a failed background write that no call met**
  (bergdb 019-09, review R1 of night 006-12; Frans, 2026-11-05). When the
  storage thread's write failed and the application's next call was
  `close()`, close returned normally: the transactions that were buffered
  were lost, and no call said so (also in 2026.2 and 2026.1). Now
  `Database.close()` throws `StreamIoException` with the write's failure as
  the cause, also after `stop()`; in a try-with-resources block it is thrown
  when the block ends, or added as suppressed to the block's exception. A
  close of a database that has already failed (a call threw
  `DbFailedException`) returns normally, as before. The stream's bytes are
  unchanged.
* **An unchecked exception of a read fails the database** (bergdb 019-10,
  found by harness 6.2, 018-03; 2026-11-06). When the stream's read threw
  an unchecked exception in a get or in a transaction's warm-up, it was
  thrown as it was and the database went on, where an `IOException` fails
  it. Now the storage fails, and the call throws `DbFailedException` with a
  `StreamIoException` as the cause, as for an I/O error (010-01, P7). The
  stream's bytes are unchanged.
* **An `Error` in a read, a transaction or a sync fails the database, and
  is thrown as it is**
  (bergdb 019-10; Frans, 2026-11-06). The error model, now in `Database`'s
  and `Db`'s Javadoc and docs/levels.md, section 3: BergDB assumes a sound
  environment (correct storage, enough memory and stack), and an `Error`,
  such as `OutOfMemoryError`, during a read, a transaction (its `Action`
  too) or a sync fails the database; the call throws the `Error`, every
  later read and transaction `DbFailedException`, and the application
  should end its process (`-XX:+ExitOnOutOfMemoryError`). In 2026.2 an
  `Error` before a transaction's go point, as in a read, passed through and
  the database went on. BergDB's own threads fail the database on anything
  that ends their work; in 2026.2 an index job's thread ended, the
  database went on, and after a restart the job said "done"; the storage
  thread ended, and syncs waited for ever. An index job's refused
  transaction or expired read is not a failure: the job takes its step
  again (bergdb 019-38); an index build's other exceptions end the build,
  not the database (bergdb 019-42). The stream's bytes are unchanged.
* **`stop()` and `close()` no longer hang when a thread cannot start or
  its failure cannot be wrapped** (bergdb 019-39; 2026-11-06): a `stop()`
  whose closer thread could not start (an `OutOfMemoryError`) left
  `close()` waiting for ever, and so did a cut whose thread could not
  start; the storage thread and the cut's thread now record an `Error`
  without allocating. While the heap stays full, a `sync()` or `close()`
  may still wait: use `-XX:+ExitOnOutOfMemoryError`.
* **A failed close of the stream is reported by `close()`** (bergdb
  015-78 and 015-34, 016-06's R5-F1, R3-F6 and R5-F2; 2026-11-05). The
  storage thread closed the stream as it ended and dropped a failure of
  that close; the close that followed could work, and `Db.close()`
  returned as if all was well. Now `close()`, and every later one, throws
  a `StreamIoException` with the first failure. And the storage thread,
  interrupted as it stopped, ended without closing the stream (reached
  only by the Core's `BufferedStream.stop()` and `StorageManager.stop()`).
  The stream's bytes are unchanged.
* **A failed background write no longer ends the storage thread with
  "Self-suppression not permitted"** (bergdb 019-37; 2026-11-06): when the
  stream's close threw the write's own `IOException` again, as `FileStream`
  can, the thread ended with an `IllegalArgumentException` (printed on
  stderr) after it had failed the database; now it ends quietly.
* **A start refused after the open leaves no empty stream file**
  (bergdb 015-06; 2026-11-06), 2026.2's known issue "A start refused
  after the open": a start on a directory without a stream file, refused
  after it opened it (a clock out of range), left an empty
  `00000000000000.bergdb`, which broke a later restore in place of a
  database whose first file has another name. Now a stream's first file is
  made by its first append; such a start leaves `bergdb.lock` only (and
  the directory, if it was missing), as the lock file is never deleted.
  The stream's bytes are unchanged.
* **A waiting `sync()` throws at once when the storage fails or closes**
  (bergdb 019-41, review R7 of 006-13; 2026-11-06), not at its next poll,
  up to 500 ms later. The stream's bytes are unchanged.
* **An interrupted eviction thread no longer spins while writers wait**
  (bergdb 019-41; 2026-11-06): an interrupt from outside, during a batch,
  made it use a whole core until no writer waited. The stream's bytes are
  unchanged.
* **A failed open of a directory closes its file and releases the
  directory** (bergdb 015-32, 016-06's R2-F3; 2026-11-05), whatever it
  throws. After an unchecked exception (such as from a file system) the
  opened stream file stayed open; after an `Error` (such as
  `OutOfMemoryError`) the directory also stayed locked within the JVM, and
  a new start on it was refused with `DirectoryInUseException` until the
  JVM ended. The stream's bytes are unchanged.
* **A start refuses a meta block whose version is not 154 as an int**
  (bergdb 019-01, 016-06's R6-F3; 2026-11-05). The version at offset 4 is
  written as an int, but it was read as 2 bytes, so a block with 154 there
  and nonzero bytes 6 or 7 was taken as version 154. Now it is refused
  with a `VersioningStreamException`, as a block of another version is.
  Every version of BergDB writes 0 in those bytes, so no database that was
  valid is refused; the stream's bytes are unchanged.
* **A start refuses a meta block that names a transaction outside the
  stream** (bergdb 019-34, found by harness 6.1, 018-07; 2026-11-06), with
  a `StreamFormatException`, before anything is written. A meta block whose
  last transaction's position was past the stream's end (such as one with
  its high byte flipped) made recovery throw an `IllegalArgumentException`.
  Valid streams are read as before; the stream's bytes are unchanged.
* **A start or a read refuses a damaged node that its checksum misses**
  (bergdb 019-32, found by harness 6.1, 018-07; 2026-11-06): a key node's
  klong of no type, a negative pointer or a count below its size, a value
  node's key that is no key, a pointer to a node of another type, or two
  nodes of different types with one id now refuse the start or fail the
  database (`StreamFormatException`), where an `AssertionError`, an
  `IllegalStateException` or a `ClassCastException` was thrown. Valid
  streams are read as before; the stream's bytes are unchanged.
* **The message of `LookupTimeNotAvailableException` names the right
  times when several readers are refused at once** (bergdb 019-08;
  2026-11-05). The Core formatted the times of the message, and the JMX
  bean's time strings, with one shared `SimpleDateFormat`, which is not
  thread-safe, so readers refused at once (a cut that overtakes several)
  could get another reader's time, or another exception from the read.
  The strings are unchanged.

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
* **Every stream refuses a read or an append of a range outside its array
  with `IllegalArgumentException`** (bergdb 019-02; 2026-11-05), as
  `AppendOnlyStream`'s Javadoc says, before anything changes: a negative
  offset or length, or an offset and length that go past the array.
  `FileStream`, `MemoryStream`, `CutStream`, `OneFileStream`,
  `SalsaStream`, `BufferedStream` and `StorageManager` threw
  `IndexOutOfBoundsException`, `ArrayIndexOutOfBoundsException`,
  `NegativeArraySizeException` or an `AssertionError` (with `-ea`) for
  some of them, and `SalsaStream` returned on a negative append. The
  Javadoc now names the offset too. No layer of BergDB passes such a
  range; the stream's bytes are unchanged.
* **`FileStream.setMax2G(true)` caps the size of every new file at 2 GB**
  (bergdb 015-33; 2026-11-05): after a start that chose small files from
  the last two, the next file could take the size rule's 10 GB. Nothing in
  BergDB sets it; the stream's bytes are unchanged.
* **`BufferedStream` makes a cut that arrives while it makes another**
  (bergdb 015-82; 2026-11-05): a cut kept for the bytes being written,
  asked for while the storage thread made an earlier kept cut, waited for
  a next write, and `close()` returned without it. BergDB's reclaim cuts
  behind the durable length and does not meet it; the stream's bytes are
  unchanged.
* **`FileStream` accepts a cut at its length** (bergdb 015-31; 2026-11-05)
  and keeps its last file; it threw an internal `Bug`, and through
  `BufferedStream` that failed the storage. BergDB's reclaim cuts behind
  the stream's end and does not meet it; the stream's bytes are unchanged.
* **`BufferedStream` and `StorageManager` throw `EOFException` for a read
  past the end** (bergdb 015-83; 2026-11-05), as `AppendOnlyStream`'s
  Javadoc says; it was an `IOException`. The storage fails at it as before;
  the stream's bytes are unchanged.
* **`BufferedStream` makes one call at a time to the stream below**
  (bergdb 015-80, 016-06's R5-F5; 2026-11-06), as `AppendOnlyStream`'s
  contract allows a stream to require: a cut, and `getFirstPos()`, ran
  beside the storage thread's append, and a cut beside its close. Now a
  lock is held for each append, cut and close of the stream below (reads
  take none), and `getFirstPos()` returns the first position kept after
  the last cut. A cut that comes during the thread's append waits for it
  and its force, at most one append (half the write buffer); reclaim's cut
  is the one on a commit's path, once per cut. `FileStream`'s own locks
  covered the overlap; a stream that relies on one writer did not. The
  stream's bytes are unchanged.
* **`Jmx.Speed`'s monitor thread goes on after an interrupt** (bergdb
  015-38, 016-06's R3-F4; 2026-11-05): it ended, its speeds stayed as they
  were, and `registerAndStart()` did not start it again. `stop()` waits for
  the thread to end, also when the caller is interrupted, and keeps the
  caller's interrupt flag; it returned early and cleared it. Nothing in
  BergDB starts `Jmx.Speed`.


Documentation
-------------

* **`Db.setStartupDistance` says that it clamps its value** (bergdb
  015-76, 016-06's R6-F5; 2026-11-05). In the Core API (and JMX's
  `setStartupDistance`), the value is clamped to 400,000 to 1,000,000,000
  bytes and the clamped value is set; a call whose clamped value is the
  setting in force writes nothing. The Javadoc said that a call with the
  setting in force writes nothing, which did not hold for a setting outside
  the range, which `DbBuilder.startupDistance` allows: there any call
  writes its 200 kB transaction and sets a value inside the range. The
  Pub API clamps to 5 to 1000 MB first and is not affected. The code and
  the stream's bytes are unchanged.
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
  An index build that meets an object it cannot index (a null indexed
  `String`) ends as failed and the database goes on (bergdb 019-42).
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
* **Key replace leaves a delete's key as written** (bergdb 019-15; Frans,
  2026-11-06): `Connection.setEnableKeyReplace()` now says so; no code change.
* **The Javadoc read through for the release** (bergdb 018-01, "Ready",
  4; 2026-11-06): the keys' format (`Connection`), what an `Action` that
  throws does, the clamps of `startupDistanceInMb` (5 to 1000) and
  `cacheSizeInMb` (4 to 100,000), `LookupTimeNotAvailableException` for a
  read that a cut overtakes, `Time.MAX`'s exact time, the refusals of
  `Db.execute`, and the overview's example, which closes its database and
  opens it with `open()` to read; stale text and typos. No code change.
* **The Pub API's Javadoc says what it left open** (bergdb 018-04, Q1, Q3
  to Q5; Frans, 2026-11-06): an rw-transaction's reads see the state as of
  its first read, not its own puts and deletes (`RwEnvironment`, `Action`);
  `getLookupTime()` gives the frozen time after a frozen read;
  `TransactionInfo.kvs()` leaves out a delete of a key that had no entry;
  `currentTime()`'s promise is for the started database. No code change.


Known issues and limits
-----------------------

* **DbObject and the user indexes are experimental**, with known faults
  (bergdb 018-01, D2 and D6; the parts are listed under Documentation,
  above): their faults are 018-01's, section 3.2 (015-23, 28, 29, 30, 36,
  37, 39, 43, 46, 61, and 015-49's S2 faults but S2-F24), and 019-42.
* **A corrupt record header can still lose data at a start that
  succeeds** (bergdb 015-73, 016-06's R6-F2; Frans, 2026-11-05). No
  checksum covers a record's header. 015-72 and 015-75 refuse a corrupt
  size, got-dirty id, topPos or startupPos in most forms. What is left:
  the last record's startupPos damaged to an aligned value that is exactly
  the start of an earlier record, one that the take never reached. The
  start then begins there, and the transactions before it are lost without
  a word. Such damage is outside the crash contract (014-01, section 7),
  and its detection is best effort. A checksum of the record header would
  catch it, with a change of the format that may come in a future release
  (017-08). In 2026.2 and 2026.1 too.
* **Other damage that a start does not detect** (bergdb 019-30, 019-31,
  019-33; Frans, 2026-11-06). BergDB assumes correct storage; its
  checksums and checks are a best effort. A start can take a damaged
  stream without an error, and reads then answer other values than were
  written, when: a record's time or `topPos` is changed to a value that
  passes the checks; whole records are cut out of a stream's middle; or a
  node byte is changed between 0x00 and 0xff, which the node checksum
  (Fletcher-16 modulo 255) does not see. Checksums that cover the whole
  stream may come in a future release (017-08), not in 2026.3. In 2026.2
  and 2026.1 too.
* **At most as many busy readers as the cores less the collector's
  workers: 7 on F53** (bergdb 015-86; Frans, 2026-11-06). With more, a
  reader waits for a core, the operating system's scheduling, not
  BergDB's work. On F53 (10 cores, ZGC with up to 3 workers, 10M keys from
  the OS's cache at a 665 MB budget), 7 readers had 0.4 gets over 10 ms in
  a million, the longest 33 ms, and 8 readers 11 to 12 in a million, the
  longest 49 to 89 ms. It is 2026.2's limit "As many readers as cores",
  now measured.
* **2026.2's other limits stay** (bergdb 018-01, D5): the collectors, a
  decrease of the startup distance at 50M keys, a small commit after a
  large transaction, D's loose bound, the default startup distance, loads
  in memory, bounded startup (T4), the files after a physical cut,
  overload (a rerun's sleep is now capped at 640 ms, 015-88, above),
  concurrency, power loss, JDKs and systems, and the documentation.
