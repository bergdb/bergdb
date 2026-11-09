# 020-24-10 Many small databases, opened and closed all the time

Created 2026-11-09 by Frans Lundberg.

An application written as a new user of 2026.4 would write it (u10, for coord-1109, round 4
of the common brief of 020-24): only the release jar on the class path, built from a clone
of main at `20e8d5a`, and only what a user reads: README.md, `releases/next.md`,
`java/src/overview-pub.html`, and the Javadoc in the sources of `bergdb.pub` and
`bergdb.pub.util` (`Factory`, `DatabaseBuilder`, `Database`, `StartupInfo`, `Connection`,
`WBuilder`, `UsePrimaryBuilder`, `Kv`, `SyncLevel`, the exceptions, the package page). The
implementation was read only afterwards, to explain U10-1 to U10-5.


## 1. The application

A desktop or mobile application that keeps one small database per document: many
databases in one parent directory, opened when a document is opened and closed when it is
closed, with small startup distances and cache budgets, file and memory databases. Every
value is checked against the application's own model (each document's map of key to
value) after every start. The application is
`/Users/f/fl/bench/2026-11-09/app-u10/app/src/App.java`, with `run.sh` (compiles it and
runs `App all`; `sh run.sh PHASE` runs one phase; heap 1 GB, `XMX=-Xmx512m` to change it).
The probes are beside it in `src/`: `ProbeRetain` (U10-3), `ProbeMkdirs` (U10-5),
`ProbeSync` (U10-6), `ProbeRecreate` (U10-1), `ProbeLeak` (heap over 3,000 cycles). The
output of the last full run is `/Users/f/fl/bench/2026-11-09/app-u10/last-run.txt`.

The phases:

* **cost**: 40 small file databases open at once (`startupDistanceInMb(5)`,
  `cacheSizeInMb(4)`, one put each), then 40 memory databases: the threads, open files and
  heap after GC that each adds. `sh run.sh cost` opens 100 (U10-2).
* **cycles**: 150 file databases (`run/docs/doc-NNN`) and 30 memory databases; 1,200
  starts (4,000 in a second run), with 1 to 25 open at once; at each start a full check (a
  get of every key, a primary scan of the directory that must list exactly the model's
  keys, an absent key), then 1 to 12 puts of text and bytes (up to 300 KB) and deletes,
  single or in one `w()`, and the check again. A database is closed with `close()` (40
  percent) or `stop()` (60 percent), half of them after a `sync()`; a third of the stops
  are followed by a start of the same directory at once, retried while it is refused as
  in use. 1 in 30 closed databases is deleted from disk and created again. Every 100
  starts: the threads (`Thread.getAllStackTraces`), the open files (`lsof -p`), the heap
  after GC. At the end: all closed, the threads and open files back to the baseline, and
  every file database started and checked once more. `StartupInfo` of every start against
  the wall time of `start()`.
* **race**: 8 threads for 20 s, each starting a random one of 16 databases, refused when
  another thread has it; checks and writes under the model, then `close()` or `stop()`;
  a counter per directory catches two databases on one.
* **paths**: a running database's directory under other names (trailing slash, `/./`,
  `x/../`, relative, a symbolic link, other case on macOS's file system, `//`), with
  `create()` and `open()`; a database in a subdirectory of a running one's directory, and
  in its parent.
* **recreate**: 50 rounds of create, write, `close()`, reopen, delete the directory; 50
  rounds of delete right after `stop()` and create again at once, with 40 KB written
  (B); 20 such rounds with 1 MB not yet written at the stop (B2); a directory deleted while
  its database runs, and a new database at the path (C); the stream files deleted with
  created.txt kept (D).
* **memory**: 400 memory databases, half closed, half stopped; the `memory()` builder's
  second start while its database runs, right after `stop()`, and after `close()`.
* **afterStop**: every call of `Database` and `Connection` after `stop()` and after
  `close()`.
* **exit**: child JVMs that write (a value, a `sync()`, then 200 puts, in the Big modes 8
  MB more and a last value) and end: return from main without `stop()`, after a sleep of 2
  s, `System.exit(0)`, `stop()` and return, `stop()` and `System.exit(0)`, `close()` or
  `stop()` in a shutdown hook, an uncaught exception, `Runtime.halt()`, 50 databases
  without and with `stop()`; three times each. The parent times the exit and checks the
  data.

Size: `App.java` 1,404 lines, `run.sh` 8, the probes 218. A run of `App all` takes 92 s on
F53 and makes about 4,500 starts in its own JVM and 45 child JVMs.

The last run: every value of every check was right in the cycles, race, paths, memory and
exit phases; it fails on U10-1 (B2 in 20 of 20 rounds, C) and U10-5 (4 starts in the race
phase), and so exits with 1. The cost phase with 100 databases fails on U10-2.


## 2. The findings

Most severe first. A reproduction names a file in the application's `src/`, or a phase of
`App` (`sh run.sh PHASE`).

| ID | Kind | Severity | What | Reproduction |
|----|------|----------|------|--------------|
| U10-1 | bug | high   | a deleted directory's database writes into the new one    | ProbeRecreate |
| U10-2 | API | high   | each database holds 11 MB, whatever its size              | cost          |
| U10-3 | bug | medium | a closed Database still referenced keeps its 11 MB        | ProbeRetain   |
| U10-4 | doc | medium | `stop()`, then `System.exit()` or in a hook, loses writes | exit          |
| U10-5 | bug | low    | concurrent starts on a new directory: not created         | ProbeMkdirs   |
| U10-6 | bug | low    | `sync()` after `close()` throws, though all is durable    | ProbeSync     |
| U10-7 | doc | low    | `StartupInfo`'s duration is a part of the start, unsaid   | cycles        |
| U10-8 | API | low    | in use told by a class outside the API; Core's words      | afterStop     |
| U10-9 | doc | low    | "the buffer time" and the write buffer undescribed        | exit          |

### U10-1. A deleted directory's database writes into the new database at the path (bug, high)

An application deletes a document: it stops the database and removes its directory, and
then the user makes a new document of the same name. Or the directory is removed while
the database runs (by the user in the file manager, or by the application's bug), and a
new database is made there. In both, the start at the path is taken, and the old
database, still writing, creates its next stream files by name in the new directory. The
new database is damaged:

* B2, `stop()`, delete, `create()` at once, with 1 MB not yet written at the stop: in 20
  of 20 rounds the start is not refused (`stop()`'s Javadoc: "Until then, a start there is
  refused") and throws `StreamFormatException` ("The meta block at 200000 names the last
  transaction at 161016, which cannot be one in a stream from 200000", or "Could not find
  *any* valid meta block"), since the old close has written `00000000000002.bergdb` and
  `00000000000004.bergdb` there. The directory is then left with them, and every later
  `create()` there throws the same until the application removes them. The delete itself
  can fail: `Files.walk` met `DirectoryNotEmptyException` as the old close added files.
* C, the directory removed while its database runs: the start of a new database there is
  taken, its put and `sync()` return, and its `close()`; the old database's puts,
  `sync()` and `close()` also return without an error, while it writes files 02 to 40 into
  the new directory. The next start fails: `StreamIoException: Bad size of file
  .../00000000000000.bergdb, should have been a multiple of 100000, but was 408`. The new
  database's synced value is lost, and nothing told either database.

With 40 KB at the stop, which the old close writes into its first file, unlinked, 50 of
50 rounds of B were right. Explained afterwards: the lock is `bergdb.lock` in the directory
and, within the JVM, a set keyed by the directory's file key (`FileStream.lockKey()`); a
new directory at the path is another directory, so neither refuses the start; and
`FileStream` opens each new stream file as `new File(dir, name)`. The Javadoc says nothing
of removing a database's directory: when it may be removed (after `close()` has returned)
and what happens otherwise. Possible fixes: refuse a start while a database of this JVM
holds the same path, not only the same directory; have a running database notice that its
directory is gone before it creates a file there (fail it); document it.

```java
// ProbeRecreate DIR b2, shortened
Database old = Factory.database().create(dir).start();
for (int i = 0; i < 50; i++) old.connection().put("/big" + i + ".bin", new byte[20_000]);
old.stop();                                           // the document is closed
deleteTree(dir);                                      // and deleted
Database db = Factory.database().create(dir).start(); // throws StreamFormatException
// ProbeRecreate DIR c: old.sync() instead of stop(); the new start is taken, its
// put and sync() return; after old's next 1 MB and both closes, open(dir) throws.
```

### U10-2. Each database holds 11 MB of heap, whatever its size and settings (API, high)

A started file database with one small value holds 11.0 MB of heap after GC, a memory
database 12.0 MB, at `startupDistanceInMb` 5, 50 and 200 alike and at `cacheSizeInMb(4)`:
measured with 10 and 40 open, and per database the same. Each also has one thread
(`BufferedStream-consumer-N`, daemon) and 3 open files. So 48 small databases fill a heap
of 512 MB, and the 49th start throws `OutOfMemoryError` (from `BufferedStream.<init>`;
the start leaves no thread behind, as `start()` says). An application with 50 to 200
documents open needs 0.55 to 2.2 GB of heap for them; a phone's heap of 256 MB holds about
20. The cycles phase therefore keeps at most 25 open, with 1 GB.

The Javadoc leads elsewhere: `startupDistanceInMb()` says that the startup distance, not
the budget, sets the heap a database needs, and that at 5 a catalogue held 21 to 42 MB;
`cacheSizeInMb()` says that what must be kept is "of the order of the startup distance";
"For a low-end PC with 0.5 GB of RAM, a value of 5 is reasonable". Nothing says that every
database, however small, holds about 11 MB from its start, nor how to make that smaller.
Explained afterwards: the write buffer, `StorageManager.DEFAULT_BUFFER_SIZE`, 10 MB,
allocated at the start; the Pub API has no setting for it. For this application, a
setting of the buffer (or a buffer that grows with use) is what it needs; at least the
Javadoc of `DatabaseBuilder` and `Database` should give the fixed cost per database.

### U10-3. A closed Database that is still referenced keeps its 11 MB (bug, medium)

`close()` and `stop()` do not release the write buffer: a closed `Database` object holds
its 11 MB (a memory database its 12 MB, though it is "gone when it closes") until the
application drops the object. With 30 databases closed (or stopped and closed in the
background) and the objects kept: 331 MB of heap after GC (362 MB for memory databases);
after the references are dropped: 1.9 MB. The application's first design kept a stopped
`Database` in its document object, to call `close()` on it later as `stop()`'s Javadoc
allows ("call only close() on this Database"); its cycles phase ran out of 1 GB after
400 starts with 4 open. A list of recent documents, each with its closed `Database`, does the
same. `close()`'s Javadoc says that the object "must not be used anymore", not that it
holds its memory. Java's own closeables (`BufferedOutputStream`, channels) let go of
their buffers at `close()`; the database could drop its buffer when its storage has closed.
After the application dropped its references, no leak was found: the heap after GC stayed
at 3.2 MB over 3,000 cycles of `create()`, put, get and `close()` (one directory, a new
directory each time, memory databases, `stop()`; `ProbeLeak`), and at 8.6 MB (the model's
data) after the 1,200 starts of the cycles phase.

```java
// ProbeRetain DIR close: 30 times
Database db = Factory.database().create(dir + "/r" + i).startupDistanceInMb(5).start();
db.connection().put("/a.txt", "a");
db.close();
kept.add(db);          // heap after GC: +331 MB; after kept.clear(): +1.9 MB
```

### U10-4. stop() then System.exit(), or stop() in a shutdown hook, loses writes (doc, medium)

`stop()` "returns at once"; the transactions that have returned are written in the
background, "also when the program returns from main right after this method". So
`stop()` looks like the call for the end of a program. It is not, when the program ends
with `System.exit()`, as a desktop application's window listener does, or calls it from a
shutdown hook: the close runs in a non-daemon thread (`Db.stop()`, "Db-close-N"), which a
return from main waits for and `System.exit()` does not. In child JVMs, three runs each:

| How the child ends                                 | Lost of its returned puts     |
|----------------------------------------------------|-------------------------------|
| `stop()`, return from main (100 KB, or 8 MB more)  | none                          |
| `stop()`, `System.exit(0)` (100 KB)                | none                          |
| `stop()`, `System.exit(0)` (8 MB more)             | the last ones, 3 of 3         |
| `stop()` in a shutdown hook, `System.exit(0)`      | all 200 (100 KB), 3 of 3      |
| `close()` in a shutdown hook, `System.exit(0)`     | none                          |
| no `stop()`: return, exit, exception, `halt()`     | all 200 not synced, 3 of 3    |
| no `stop()`, a sleep of 2 s, return                | none                          |
| 50 databases, no `stop()`, return                  | 12 to 16 percent              |

Without `stop()` the JVM ends at once (BergDB's threads are daemons), and what was not
written is lost, as `stop()`'s Javadoc says ("as in a crash"); the synced value was there
in every run, and every database opened. The loss after `stop()` is a crash's too, which
the database tolerates, but `stop()` had promised to write. The Javadoc of `stop()` and
the package page's "Good to know" should say: before `System.exit()`, and in a shutdown
hook, call `close()`, not `stop()`.

### U10-5. Concurrent starts on a new directory: "could not be created" (bug, low)

Eight threads start `create(dir)` at once on one directory that does not exist yet (30
rounds): one start is taken each time, 51 starts are refused as the Javadoc says (cause
`DirectoryInUseException`), and 159 throw `StreamIoException: Directory .../doc could not
be created.`, without that cause, although the directory exists. An application that
retries a start refused as in use gets an error instead. The race phase met it 4 times in
2,434 starts, at the first starts of a directory. Siblings in a new parent, one directory
per thread, were all taken (240 of 240). Explained afterwards: `FileStream`'s directory
creation throws when `mkdirs()` returns false, which it does when another thread made the
directory first; it could check `isDirectory()` then. Nothing was damaged.

### U10-6. sync() after close() throws, though every transaction is durable (bug, low)

A put, `close()` (or `stop()` and a wait of 1 s), then `sync()`: it throws
`StreamIoException: StorageManager has error: Storage is closing.`, from `Database` and
from `Connection`. `Database.sync()`'s Javadoc: if the database is stopping or stopped and
the transaction is not yet durable, it throws; "If it is durable, this method returns,
also then", and `close()` has made it durable. With a `sync()` before the stop it returns.
An application that syncs in its save handler after another part has closed the
database reports a failed save of data that is safe.

### U10-7. StartupInfo's duration is a part of the start, and says not which (doc, low)

`getStartupDuration()` "Returns the number of seconds it took to start the database". Over
4,150 starts of small databases it was a third of the wall time of `start()` at the median
(0.8 ms of 2.5 ms; 0.4 of 1.1 ms in the last run) and half at the maximum (40 of 81 ms).
What it leaves out (the directory, its lock, the buffer?) is not said, so an application
that reports its start times cannot tell which to use. `StartupInfo` has no `toString()`
(`bergdb.pubimp.StartInfoImp@67620d80`).

### U10-8. In use is told by a class outside the API; the Core's messages (API, low)

`DatabaseBuilder.start()` says that a directory in use throws a `StreamIoException` whose
cause is `bergdb.stream.DirectoryInUseException`, a class outside the API's packages
(README: `bergdb.pub`, `bergdb.pub.util` and the Core's `Db`). The application tells it
by the cause's simple name. After `stop()` and after `close()`, a get or a put throws
`bergdb.core.DbStoppingException` (an `IllegalDbStateException`, as documented) with "Cannot
call getOne() while DB is stopping." and "Cannot call execute() while DB is stopping.":
the Core's method names, and "stopping" for a closed database. `sync()`'s message names
`StorageManager`. A `DirectoryInUseException` in `bergdb.pub.util`, or a method that
tells it, and messages in the Pub API's words would serve a user.

### U10-9. "The buffer time" and the write buffer are not described (doc, low)

`stop()`'s Javadoc: a database that is not stopped keeps "its write buffer", and "What it
has committed is still written within the buffer time". Neither is described anywhere in
the Javadoc: not the time (50 ms, `StorageManager.DEFAULT_BUFFER_TIME`), not the size (10
MB, U10-2). An application that ends without `stop()` cannot tell how long to wait; the
exit phase found that 2 s was enough and that a return from main at once lost all 200
puts not synced.


## 3. What went well

* Every value was right after every start: 1,200 starts in the last run and 4,000 in a
  second run of the cycles phase, of 150 file and 30 memory databases in one parent, up to
  19 open at once, with `close()`, `stop()` and deletes; 2,306 starts right after
  `stop()`, 314 refused at first, as documented, the longest wait 41 ms; then every
  database once more.
* No leak, once the application dropped its closed databases (U10-3): after all were
  closed, the threads were back at the baseline (6), no file under the application's
  directory was open, and the heap after GC did not grow over 3,000 cycles. One thread and
  three files per open database; the threads of 200 stopped memory databases had ended
  1.5 s later.
* The directory lock held under every name tried: a trailing slash, `/./`, `x/../`, a
  relative path, a symbolic link, the other case, `//`, with `create()` and `open()`. A
  database in a subdirectory of a running database's directory, and one in its parent,
  run beside it, each with its own data. Eight threads starting 16 databases: 2,434 starts,
  1,989 refused as in use, never two databases on one directory, and every value right.
* The JVM ends without `stop()`, at once; a synced value was always there, and every
  database opened after a return, an exit, an uncaught exception, `Runtime.halt()` and 50
  open databases. `stop()` and a return from main kept every write, also of 50 databases.
* `memory()`: 400 databases left no thread; the builder's second start while its database
  runs, and right after `stop()`, is refused with `IllegalStateException`; a start on its
  closed stream reads, and its first write fails it with `DbFailedException`, all as the
  Javadoc says. Deleted stream files with created.txt kept give `DatabaseMissingException`
  with a message that says what to do.
* Starts are quick for small databases: a median of 1 to 3 ms for `start()`, at most 81
  ms, in the cycles.
* The Javadoc of `stop()` and `close()` answered almost every lifecycle question of this
  application before it was written.


## 4. Fixes

Made by l20 for coord-1109 on 2026-11-09 in `clone-l20`, on main's `9ed1e6c`, one commit
each; the details in 021-20's log.

| ID    | What was done                                                         | Commit  |
|-------|-----------------------------------------------------------------------|---------|
| U10-1 | a start at the path waits; a database whose directory went fails      | 2557286 |
| U10-3 | the write buffer is released when the storage's thread ends           | 2e9ea7d |
| U10-5 | the losers of the race to make the directory are refused as in use    | 5ca4249 |
| U10-6 | `sync()` after `close()` returns                                      | 10335ee |
| U10-2 | Javadoc: 10 MB of heap per started database, no setting in 2026.4     | 41e4da5 |
| U10-4 | Javadoc: `close()`, not `stop()`, before `System.exit()` and in hooks | 41e4da5 |
| U10-7 | Javadoc: what `getStartupDuration()` includes and leaves out          | 41e4da5 |
| U10-9 | Javadoc: the write buffer and the buffer time, 50 ms                  | 41e4da5 |

U10-8, and a setting of the write buffer (U10-2), are on Frans's list. On the fixed build:
ProbeRecreate `b2` takes the start once the old close is done, with `/new.txt` there after
a reopen, and `c` is refused as in use while the old database runs; ProbeRetain holds 0.54
MB per closed file database (1.6 MB for a memory one); ProbeMkdirs gives no exception but
the refusal as in use; ProbeSync returns in all five cases.
