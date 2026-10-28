Notes for the next release
==========================

What the release notes of the next release after 2026.1 must say, collected
here as the changes are made, so that the release does not have to find them
again. The release folds them into its `releases/VERSION/readme.md`, as
[2026.1](2026.1/readme.md) has them under "Changes since 2015.4", and
empties this file.


API changes
-----------

* **`stop()` or `close()` is required** (bergdb 005-55, 2026-10-27,
  `cec0032`). `Db.finalize()` is gone, with nothing in its place: nothing
  stops a database that the application drops. Until 2026.1,
  `Database.stop()`'s Javadoc promised that a `Database` that nothing referred
  to was stopped when the collector found it; that promise is gone. A `Db`
  or `Database` that is not stopped keeps its storage threads (one per
  stream), its open files, its write buffer and its memory until the JVM
  exits. What it has committed is still written within the buffer time, as
  after any commit; the storage threads are daemon threads, so they do not
  keep the JVM alive, and at its exit what is buffered and not yet written is
  lost, as in a crash, which the database tolerates. An application that
  stops each database it starts, as an application closes a file, sees no
  change. (Frans: "Typically there is only one database in an application.
  Calling close() is a reasonable requirement. And the database is
  crash-tolerant anyways.")
* **`Db` and `Database` are `AutoCloseable`** (bergdb 005-59). A
  `try`-with-resources block closes a database when it ends, also when it
  throws. `Database` has a new method, `close()`: it stops the database as
  `stop()` does and waits until it is closed, as `Db.close()` does;
  `stop()` still returns at once. Every call of 2026.1 works as before.
* **Interrupts** (bergdb 005-46, `eaec93e`). An interrupt of a thread that
  calls BergDB never fails or hangs the database, as it could before (a
  commit that waited for room in the write buffer or made a cut failed the
  database; an interrupt of the storage thread stopped its writes). `sync()`,
  a job's `join()` and the wait before an rw-transaction's rerun end on an
  interrupt; every other call ignores it until it is done; the interrupt flag
  is always kept. The rule is in `Database`'s class Javadoc.
* **One database per directory** (bergdb 005-63, 2026-10-28). A `FileStream`
  takes an exclusive lock on a file of its own in the directory,
  `bergdb.lock`, before it reads anything, and releases it when it is
  closed. A second database on the directory, in the same JVM or in another
  process, is refused at once with a `DirectoryInUseException`
  (`DatabaseBuilder.start()` throws a `StreamIoException` with it as the
  cause); so is one started right after `stop()`, while the first is still
  closing: start it after `close()` has returned. Before, nothing refused a
  second database, and one started right after `stop()` could take files
  that the first was still deleting (005-46), and fail. The operating system
  holds the lock and drops it when the process ends, so a crash leaves none;
  the file stays, with a text for people. On a network file system a crashed
  client's lock may stay until the server notices (NFSv4: about 90 s), and
  where the file system supports no locks, a start fails.
* **`SyncLevel` is in `bergdb.pub.util`** (bergdb 005-56, 2026-10-28). It
  was `bergdb.core.SyncLevel`, a class of the Core Layer in the Pub API's
  signatures (`Database.sync`, `Connection.sync` and `Transaction.sync`);
  now it is `bergdb.pub.util.SyncLevel`, with the same constants, `NONE`,
  `ORDINARY` and `STRONG`. Code that names it changes its import, from
  `bergdb.core.SyncLevel` to `bergdb.pub.util.SyncLevel`, and code compiled
  against 2026.1 that uses it must be compiled again.
* **The builder opens the directories in `start()`** (bergdb 005-66,
  2026-10-28). `DatabaseBuilder.dir()` and `replica()` only record their
  directories; `start()` opens them, the database's first, and closes them
  again if it fails. So a builder that is never started holds nothing, where
  since 005-63 it held the directory's lock until the JVM ended, and so did
  the first of two `dir()` calls and a replica given before `dir()`. A
  replica given before `dir()` is now kept; before, `dir()` dropped it. A
  directory that cannot be opened, or that another database has, is reported
  by `start()`, with the same `StreamIoException` that `dir()` threw;
  `replica()` no longer throws its `IOException`.
* **The startup distance changes while the database runs** (bergdb 005-53,
  2026-10-28). `Database.setStartupDistanceInMb(int)` and
  `getStartupDistanceInMb()`: the setter clamps as
  `DatabaseBuilder.startupDistanceInMb` does (5 to 1000 MB), and the new
  setting is in force when it returns, written to the stream with a small
  transaction of the database's own (a value of 200 kB), so that a restart
  keeps it. A call with the setting in force writes nothing, so an
  application may call it after every start; one on a stopped or failed
  database throws as a transaction does and changes nothing. After a
  decrease, the commits that follow bring the startup section down to the
  new setting, with no commit writing the whole of it (007-07). Until now
  only a new database could choose its startup distance through the Pub
  API.
* **The cache size changes while the database runs** (bergdb 005-52,
  2026-10-28). `Database.setCacheSizeInMb(int)` and `getCacheSizeInMb()`:
  clamped as `DatabaseBuilder.cacheSizeInMb` (4 to 100,000 MB), in force
  when the setter returns, for this run only (a restart takes the
  builder's value). After a decrease the database evicts down to the new
  budget in batches of at most 2 ms, also when no other call follows. The
  rule for both setters: a setting that changes the stream's bytes, as the
  startup distance, is kept in the stream; one that does not lasts for the
  run.


Format
------

* **The node size is in the stream** (bergdb 005-50, `bf19075`). Every meta
  block holds the maximum node size the database was written with, in 2
  bytes at offset 44 that were reserved; the meta block's version stays 154.
  A start with another node size is refused with a `StreamFormatException`
  that names both sizes, where it failed before with what looked like a
  corrupt stream, or started and could leave a stream no start opened. A
  stream written before, by 2026.1 or earlier code, is refused with a
  `VersioningStreamException`, before anything is written: databases of
  2026.1 must be made again. (Frans: "No need to consider "today's
  databases". There are none.")


Performance
-----------

* **Reads do not wait for the writer** (bergdb 005-46). A read of the
  stream's last file no longer waits for the writer's append and its force,
  nor for a new file's force or reclaim's deletes of cut files (a thread of
  their own, `FileStream-cut`); an encrypted database's reads no longer wait
  for each other.
* **Startup without header reads** (bergdb 005-57, part 1, `07b6375`). A
  start finds the nodes of the startup section's pointers by their position
  instead of reading a header for each: in the prototype a cold start of 10M
  keys on s1 took about 46 and 51 s at startup distances of 50 and 200 MB,
  where it took 214 and 210 s.
* **Index writes in proportion to each commit, and bounded startup**
  (bergdb 005-49; 007-03, step 3; 007-07, 2026-10-28). Each commit writes
  its share of the dirty index nodes, in proportion to its size, so that
  the startup section stays near the startup distance, and a deadline
  takes every transaction that begins twice the startup distance or more
  before the end of the stream, so that a start reruns less than that. At
  10M keys the largest record of a run is 2 to 10 times smaller; a put
  costs 24 and 36 percent more stream at startup distances of 50 and 200
  MB, and 13 percent less at 1000 MB. `Db.setStartupDistance` lowers the
  distance in one call, with no commit that writes the whole startup
  section; the section comes down as transactions are committed. Every
  stream differs from what 2026.1 wrote; the format does not.
