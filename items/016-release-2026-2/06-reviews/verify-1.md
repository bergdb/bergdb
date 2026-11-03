016-06/verify-1. Verification of R2's and R3's findings
=======================================================

Created 2026-11-03 by Frans Lundberg. Base: b9ba427. Started 19:34, ended 19:44 (from date).

Eight findings, in the order of the list handed to this verification. Each
probe or patch was copied from R2's folder (06-reviews/R2/) or R3's
(07-concurrency/r3/) into `/Users/f/fl/bench/016/verify-1/out/` and run
against a clone of b9ba427 built with `sh java/build.sh`; probes written
for this verification are in `/Users/f/fl/bench/016/verify-1/v/`. One JVM
at a time. Commands below run from `/Users/f/fl/bench/016/verify-1`, where
`repo/` is the clone.

Effect classes: loses data, invents data, wrong answer, hangs, or none of
these (a contract mismatch only).


## R2-F1 (confirmed)

A second copy of BergDB in another class loader that is refused on a
directory releases the first copy's operating-system lock; the first
database stays open and writable, and another process can then take the
lock.

Reasons.

* `LOCKED_DIRS` (FileStream, lines 139-140) is a static field, so each
  class loader that loads `bergdb.stream.FileStream` has its own set. The
  second copy's `lockDir()` passes `LOCKED_DIRS.add(key)` (line 587),
  opens `bergdb.lock` with a new `RandomAccessFile` (line 604), and
  `tryLock` throws `OverlappingFileLockException` because the JDK's lock
  table is shared by the whole JVM (it lives in java.base). The handler
  (lines 614-618) calls `f.close()`. On macOS and Linux closing any
  descriptor of a file drops every `fcntl` lock the process holds on it;
  the class Javadoc says so itself ("closing any channel of the file
  releases the process's lock"), and LOCKED_DIRS exists to avoid exactly
  this close within one loader.
* The probe is a fair use. It calls only the public constructor and
  `append` of FileStream in the first loader and the public constructor in
  the second, and checks the lock from a separate Python process with the
  same region (`lockf(LOCK_EX|LOCK_NB, len 1, start 2^62)`), which is the
  `fcntl F_SETLK` that another JVM's `tryLock` would use. The check reads
  `REFUSED` before the second open, so it does see the lock.
* Against the contract: FileStream's class Javadoc ("A second FileStream
  on the directory, in this JVM or in another process, is refused ... The
  constructor takes an exclusive lock ... and close() releases it, last")
  and 005-63, "The lock file", points 5 and 6: the lock is held until
  `close()`, and the Outcome note in point 6 states the very hazard that
  LOCKED_DIRS was added to prevent. A refused open must not end the first
  stream's exclusion.
* Run as given, the output matches R2's: `Before second loader: REFUSED`,
  `Second loader: bergdb.stream.DirectoryInUseException`, `After rejected
  open, first still open: ACQUIRED`, `length=4`.

Reach: the Pub API, in normal use. `PubLockLoaderProbe` (written for this
verification) does the same with `Factory.database().dir(d).start()` in
both loaders: the second `start()` fails with `StreamIoException` (cause
`DirectoryInUseException`), after which the Python check gets `ACQUIRED`
and the first `Database` still takes a put and returns it. A user meets it
with two applications in one JVM that each bundle bergdb.jar (two webapps
in one servlet container, plugins with their own loaders), or with a hot
redeploy whose new loader starts the database while the old one is still
open: the start is refused as it should be, and the old database loses its
exclusion silently.

Effect: can lose data, but only through a second step: once the lock is
gone, another process can start a database on the same live directory, and
two writers on one stream corrupt it (the case 005-63 exists to prevent).
The refusal itself loses, invents or misreports nothing and does not hang.

Commands:

    javac --release 17 -cp repo/java/build/bergdb.jar -d out/R2/classes out/R2/LockLoaderProbe.java
    java -ea -cp out/R2/classes:repo/java/build/bergdb.jar bergdb.core.LockLoaderProbe out/R2 repo/java/build/bergdb.jar
    javac --release 17 -cp repo/java/build/bergdb.jar -d v/classes v/PubLockLoaderProbe.java
    java -ea -cp v/classes:repo/java/build/bergdb.jar bergdb.core.PubLockLoaderProbe v repo/java/build/bergdb.jar

Output of the second:

    Before second loader: REFUSED
    Second loader start: bergdb.storage.StreamIoException: Directory .../db is in use in this JVM
        (bergdb.lock is locked). / cause bergdb.stream.DirectoryInUseException
    After refused start, first still open: ACQUIRED
    First still accepts puts: get /b = two


## R2-F5 (confirmed)

`FileStream.append` with a negative length neither refuses it with
IllegalArgumentException nor leaves the stream as it was: it lowers the
last file's length (and, without assertions, the stream's length), and the
next valid append fails.

Reasons.

* `FileStream.append` (lines 271-291) has no argument check; it inherits
  the contract of `AppendOnlyStream.append`, whose Javadoc says
  "@throws IllegalArgumentException if 'length' is less than 0", and of
  `getLength()`, "The length always increases".
* `DbFile.append` (lines 1329-1372): `toAppend = len` (negative, below
  `availableInt`), the write and force are skipped (`toAppend > 0` is
  false), then `fileLength += toAppend` lowers the file's length, and the
  `assert fileLength == rfile.length()` comes after that change. With `-ea`
  the AssertionError leaves `FileStream.length` at 3 but `DbFile.fileLength`
  at 2; without `-ea` the method returns -1 and `FileStream.length += -1`
  gives 2. Either way the third byte is unreadable (EOFException), and the
  next append finds `rfile.length() != fileLength` and throws IOException
  (and sets the stream's `ioException`, so the stream is unusable from
  then on).
* The probe calls only the public constructor, `append`, `read`,
  `getLength` and `close` of FileStream, with exactly the argument the
  interface says it refuses. It is not its own bug.
* Both runs printed exactly R2's output (with `-ea`: AssertionError,
  length 3; without: returned normally, length 2; both: EOFException on the
  last byte, IOException on the next append).

Reach: internal only. FileStream is a public class but in `bergdb.stream`,
not `bergdb.pub`. The production callers (BufferedStream's flush, lines
255-258, RecoverableStream, StorageManager's copy loop, lines 400-410) pass
lengths computed from buffer indices and differences that are asserted
non-negative; I found no way from `bergdb.pub` to a negative length, and
R2 claims none.

Effect: wrong answer at the stream level (a lower length, an unreadable
committed byte) and a stream that refuses further appends, after a caller's
bug only. No data is lost on disk (the bytes stay, and a reopen reads the
file's real length), none is invented, nothing hangs. Within a database a
later append would fail the database, not corrupt it.

Commands:

    javac --release 17 -cp repo/java/build/bergdb.jar -d out/R2/classes out/R2/NegativeAppendProbe.java
    java -ea -cp out/R2/classes:repo/java/build/bergdb.jar bergdb.core.NegativeAppendProbe out/R2
    java -cp out/R2/classes:repo/java/build/bergdb.jar bergdb.core.NegativeAppendProbe out/R2


## R3-F3 (confirmed)

A throwable in an eviction batch ends the eviction thread, but the
database stays active, `evictor` keeps naming the dead thread and `wanted`
stays set, so no later load or cache decrease evicts again.

Reasons.

* `EvictorRun.run` (Eviction, lines 496-544) has only a `finally` that
  clears `running`; nothing catches a throwable from `sweep`, fails the
  database, or sets `evictor = null` (it is cleared only on the two normal
  exits, lines 502 and 509). `wake` (lines 421-430) starts a thread only
  when `evictor == null`; with a dead thread it sets `wanted = true` and
  notifies nobody, and from then on returns at its first line
  (`if (wanted) return;`). Each step is reachable as stated; the locks are
  as stated (wanted and evictor under `evictorLock`; the batch under the
  write lock and, at the hook, under Eviction's monitor, both released by
  the throw).
* The probe's hook is the existing package-private seam in `sweep`
  (line 658), the place where a Bug, an AssertionError or an
  OutOfMemoryError from the batch would leave it. It is written before
  `setCacheSizeIndicator`, whose `wake` starts the thread
  (`Thread.start` is a happens-before edge) or, for a thread that already
  waits, releases `evictorLock` that the thread then takes; so the
  worker sees it. The uncaught-exception latch and the join order the
  observations. Run here it printed R3's output exactly.
* Against the contract: 010-01, P7 ("A database ... that has a bug, does
  not run on. It fails ... every later transaction and read") and
  `Db.setCacheSizeIndicator`'s Javadoc ("After a decrease the method wakes
  the eviction thread ... until they are at most the budget"). The code is
  aware of it: `wake`'s Javadoc, point 3, says "unless an error ended the
  thread (a batch that throws), which, as before 005-65, stops the loads'
  eviction". So it is a known, commented limitation, but it contradicts P7
  and the public setter's promise.
* `EvictorDeadBudgetProbe` (written for this verification) shows the
  user-visible part. 2,000 puts give 251,569 resident bytes. In the
  control run a decrease to a 100,000-byte budget evicts to 111,752, and
  2,000 reads end at 231,298 with the thread alive. With one injected
  Error in the first batch, the same decrease evicts nothing (251,569),
  2,000 reads grow it to 326,683, the thread is dead and `wanted=true`;
  every value read is correct.

Reach: the trigger is internal, a throwable inside a batch: a bug or a VM
error such as OutOfMemoryError in the eviction thread (sweep does no I/O,
so no environment failure reaches it). No Pub API call causes it in normal
use. After it, the Pub API in normal use meets the consequence: reads and
`Database.setCacheSizeInMb` no longer bring the cache down, and the
database reports nothing.

Effect: none of the four. Reads return correct values; nothing is lost or
invented; close does not hang (`endThread` joins a dead thread). The cache
grows past its budget under reads (a step towards OutOfMemoryError), and a
load under pressure parks for up to `LOAD_WAIT_NANOS` (2 ms) waiting for a
batch that never comes: a slowdown, not a hang. The failure that P7 asks
to surface stays silent.

Commands:

    javac -cp repo/java/build/bergdb.jar -d out/r3/classes out/r3/EvictorFailureProbe.java
    java -ea -cp out/r3/classes:repo/java/build/bergdb.jar bergdb.core.EvictorFailureProbe
    javac -cp repo/java/build/bergdb.jar -d v/classes v/EvictorDeadBudgetProbe.java
    java -ea -cp v/classes:repo/java/build/bergdb.jar bergdb.core.EvictorDeadBudgetProbe control
    java -ea -cp v/classes:repo/java/build/bergdb.jar bergdb.core.EvictorDeadBudgetProbe


## R3-F8 (confirmed)

A transaction whose record append fails after the go point has already
made its time a lookup time, so a concurrent read can return its values,
which the failure and the restart then take away; docs/levels.md, section
3, says that time never becomes a lookup time.

Reasons.

* `Db.executeInner` (lines 2005-2051): after the go point the order is
  `putKvs()`, `synchronized (readSync) {}`, `dbClock.transactionEnd()`,
  then `stmRecordKeys`, `store()`, `aux.updateStats()`, the listener and
  hooks, `eviction.afterTransaction`, audit, and reclaim's
  `transactionCompleted`; the catch calls `fail(t, e)` only after any of
  these throws. So from `transactionEnd` until `fail` sets the state, a
  reader admitted with the latest lookup time reads the transaction's
  in-memory state. The code comment (lines 2018-2021) promises only the
  narrow case ("when putKvs() throws, t.tt never becomes a lookup time").
* docs/levels.md, section 3, second bullet, names "an append error" and
  "reclaim's work after the transaction" among the failures after the go
  point and says "the transaction's time never becomes a lookup time".
  Both happen after `transactionEnd`. The claim is false as written.
* The probe uses only supported internal calls: a MemoryStream subclass
  as the main stream (as the storage failure tests do), a legal 1,024-byte
  buffer (`DbBuilder.stream(name, stream, bufferSize, bufferTime)`), and
  `db.getOne(Long.MAX_VALUE, ...)`, which is exactly the call
  `ConnectionImp.getBytesAtLookupTime` makes for a connection's default
  lookup time (`Long.MAX_VALUE`, ConnectionImp line 47). The held consumer
  makes the 8 kB record's `store()` wait for room; the latch orders the
  read before the injected IOException. Output as R3's: the writer is
  still executing, the reader got 8,192 bytes, the lookup time equals the
  transaction's time, 0 new bytes in the stream, then DbFailedException,
  and the reopened copy holds the old 1-byte value.

Reach: the Pub API in normal use, with an environment failure: a
`Connection.get` (or a query) on one thread while another thread's put is
between `transactionEnd` and its failure, in practice while `store()`
waits for room in the write buffer (a record larger than the free part of
the 10 MB default buffer, or a consumer that is behind) and the disk then
fails. A bug in the later steps (statistics, eviction, audit, reclaim)
gives the same window without I/O.

Effect: none of loss, invention or hang. The reader gets the value of a
transaction whose call then throws and which the restart removes. That is
what a read of any unsynced transaction already risks in a crash, and no
acknowledged or synced transaction is lost; the database fails correctly.
It is a wrong answer only against section 3's promise: a documentation
mismatch, as R3 says.

Commands:

    javac -cp repo/java/build/bergdb.jar -d out/r3/classes out/r3/PublishedFailedTransactionProbe.java
    java -ea -cp out/r3/classes:repo/java/build/bergdb.jar bergdb.core.PublishedFailedTransactionProbe


## R3-F12 (confirmed)

A typed primary scan ends early, silently, when one page of 100 scanned
entries holds no object after its last returned one: every object after
such a run of non-object entries is left out.

Reasons.

* `IterStopCondition.handleKvt` (UseIndexBuilderImp, lines 714-745)
  counts every entry in the prefix, filtered or not. At the 100th it
  chooses ADD_AND_STOP, which for a non-object becomes STOP: the page ends
  without that entry. `getMany` (lines 572-596) takes the next start key
  only from returned entries, and `hasNext` (lines 598-610) sets `done`
  on any empty page, without looking at `gotEod`. `excludeNonObj` is on
  for `usePrimary` with an ordinary or DbObject type (lines 89-91), and
  `Entries.isProbablyDbObject` filters a value without DbObject's magic or
  a key with a suffix other than `obj`. So skipping such entries is
  intended; ending the scan on them is not.
* Against the contract: `UsePrimaryBuilder`'s Javadoc ("iterate database
  objects in the order specified by the primary index") and
  `objects()`/`kvs()` ("an Iterable for iterating over the objects").
  Nothing in the Pub API limits how many non-object entries a directory
  may hold, and `Connection.put` takes any object, a String or a byte[]
  included.
* The probe uses only the Pub API (`Factory.database().memory()`, one
  `WBuilder` transaction, `get`, `usePrimary(...).dir(...).objects()`)
  and closes the database. Run here: the object exists, the scan returns
  0. `FilteredScanVariants` (written for this verification) puts the edge
  where the code says: 99 strings then an object gives 1 (right), 100
  gives 0; an object, 100 strings and an object gives 1 of 2, with 99
  strings 2 of 2; an object, 150 `.jpg` byte[] blobs and an object gives
  1 of 2.

Reach: the Pub API in normal use: any directory where objects and at
least about 100 consecutive non-object entries (Strings, byte arrays,
keys such as `photo.jpg`) share the scanned prefix, read with
`Connection.usePrimary(type).dir(...).objects()` or `.kvs()`. No
concurrency or timing is needed. (The byte and time limits, 50 MB and 1 s
a page, can end a page on a filtered entry in the same way.)

Effect: wrong answer: the iteration ends early without an error and
omits objects that are in the database. Nothing is lost or invented in
the stored data, and nothing hangs.

Commands:

    javac -cp repo/java/build/bergdb.jar -d out/r3/classes out/r3/FilteredScanProbe.java
    java -ea -cp out/r3/classes:repo/java/build/bergdb.jar bergdb.core.FilteredScanProbe
    javac -cp repo/java/build/bergdb.jar -d v/classes v/FilteredScanVariants.java
    java -ea -cp v/classes:repo/java/build/bergdb.jar bergdb.core.FilteredScanVariants


## R3-F9 (confirmed)

A `deleteIndex` whose metadata transaction is refused before the go point
leaves the cached index deleting and unmapped while the stored metadata
says active: later transactions stop writing its entries, and the active
index omits those objects, also after a restart.

Reasons.

* `IndexManager.ensureDeletingState` (lines 622-640), under `lock`, sets
  `index.state = STATE_DELETING` and calls `dirToActiveIndexes.remove(index)`
  before `storeIndex`, which runs the metadata transaction with
  `db.execute`. A refusal there (a DbException before the go point) leaves
  both changes; nothing restores them. Writers find a directory's indexes
  in `dirToActiveIndexes`, so later puts in `/items/` write no entries.
  `useIndex` decides from the stored index info at the lookup time, which
  still says active, so the query is allowed and returns the incomplete
  index. The lock comment (lines 87-93: the maps "match the latest data in
  the database") and docs/levels.md section 3 ("A refused transaction
  leaves the database as it was, and it goes on") are both broken.
* The pre-go refusals that this one small transaction can meet: the
  clock out of range or exhausted (`DbClock.transactionBegin`, 005-18),
  the record limit (005-17), the top node ordinals (005-02). It has no read
  set, so no RerunException. A stopping or failed database refuses too,
  but then the cache is discarded and a restart reads the stored state, so
  no harm.
* R3's probe lowers `StoredTrans.recordLimit`, the same seam
  `DbTester.testTransactionTooLarge` uses, restores it in finally, and
  otherwise uses the Pub API on a `DatabaseImp` over a MemoryStream. Run
  here: refused "too large", stream length unchanged, database active, the
  new object exists, the index returns 1 of 2, after reopen 1 of 2.
* `PubRefusedIndexDeleteProbe` (written for this verification) needs no
  seam: a user `Clock` (`DatabaseBuilder.clock`) returns -1 during the one
  `deleteIndex` call, which is refused with "The clock's time, -1, is
  outside the range ... No transaction is executed."; with the clock good
  again the next put succeeds, and the index returns 1 of 2, on a
  directory database, also after a restart.
* By reading only (not run): `addIndex` (lines 346-348) and
  `setIndexStateToActive` (lines 610-612) change the maps or the state
  before `storeIndex` in the same way, as R3 says.

Reach: the Pub API (`Database.deleteIndex`), but only when its metadata
transaction is refused, which normal use with the default clock does not
produce: a user-supplied clock that is out of range for that call, the
database time exhausted, or an internal limit. Not in normal use.

Effect: wrong answer, lasting: index queries omit the objects written
after the refusal, after restarts too, and nothing reports it. The
primary objects are intact, so no user data is lost; nothing is invented
and nothing hangs.

Commands:

    javac -cp repo/java/build/bergdb.jar -d out/r3/classes out/r3/RefusedIndexDeleteProbe.java
    java -ea -cp out/r3/classes:repo/java/build/bergdb.jar bergdb.core.RefusedIndexDeleteProbe
    javac -cp repo/java/build/bergdb.jar -d v/classes v/PubRefusedIndexDeleteProbe.java
    java -ea -cp v/classes:repo/java/build/bergdb.jar bergdb.core.PubRefusedIndexDeleteProbe v


## R3-F1 (confirmed)

Two `deleteIndex` calls on one name start two delete jobs; when the second
has finished and the name is created again, the first, still running,
deletes the new index's entries and its metadata.

Reasons.

* `DatabaseImp.deleteIndexInternal` (lines 303-337) calls
  `ensureDeletingState`, which for an index that is already deleting
  changes and stores nothing and returns the same object (IndexManager,
  lines 630-636), and then starts a new thread every time. The worker
  calls `deleteIndexEntries(indexName, ...)` (lines 399-453), which scans
  and deletes `IKP/i/<name>/` at `Long.MAX_VALUE` by name, and
  `deleteIndexInfo(connection, index)` (lines 456-464), which deletes the
  info key of `index.name` and `nameToIndex.remove(index.name)`, so
  whatever index holds the name then. No step compares the object or a
  generation. `addIndex` refuses a name only while `nameToIndex` holds it,
  so after the second job's `deleteIndexInfo` a new index of that name is
  admitted, while the first job runs on.
* The probe only delays the first job: a `Db` subclass whose `getMany`
  parks the first thread named `DatabaseImp-delete-` until a latch is
  released, then calls the real `getMany`. Everything else is public calls
  (`deleteIndex` twice, `Job.join`, `indexBuilder(...).createFast()`,
  puts, `useIndex`). Without the latch the same order arises when the
  first job is simply slower (it runs at `Thread.MIN_PRIORITY`, and on a
  large index both scan the same entries in batches of 100). Run here:
  R3's output exactly, the replacement index is gone with
  NoSuchIndexException, and also after reopen.
* `DuplicateDeleteAfter` (R3's probe with more steps, written for this
  verification) shows a further consequence: `deleteIndexInfo` does not
  touch `dirToActiveIndexes`, so the removed replacement stays mapped and
  writers keep writing its entries into `IKP/i/amount/` with no metadata.
  A third object put then, and an index of that name made again with
  `createFast` ("Only new objects ... will be indexed"), returns `[3]`, an
  entry from the ghost. The stale first job's status reads "Done! Deleted
  'amount', 1 index entries were deleted."
* Against the contract: `Database.deleteIndex` deletes the named index,
  and an index created afterwards is a new one (`IndexBuilder`); 010-01,
  P1 and P6 (index changes concurrent with application calls).

Reach: the Pub API in normal use: `deleteIndex` called twice on one name
(a retry, or two threads or components), then `indexBuilder` of the same
name once one job reports done, while the other is still running. Hitting
it without the latch needs that timing, which a large index makes likely.

Effect: loses data, of the derived kind: the replacement index, its
definition and entries, vanishes, and stays gone after restart; queries on
it throw NoSuchIndexException. Primary objects are intact. A later index
of the name can then show entries it should not have (a wrong answer).
Nothing hangs.

Commands:

    javac -cp repo/java/build/bergdb.jar -d out/r3/classes out/r3/DuplicateDeleteProbe.java
    java -ea -cp out/r3/classes:repo/java/build/bergdb.jar bergdb.core.DuplicateDeleteProbe
    javac -cp repo/java/build/bergdb.jar -d v/classes v/DuplicateDeleteAfter.java
    java -ea -cp v/classes:repo/java/build/bergdb.jar bergdb.core.DuplicateDeleteAfter


## R3-F2 (confirmed)

A build job whose index is deleted goes on writing entries under the
index's name; if the name has been created again, the old build's entries
land in the replacement, and the old job then reports 100 although its
activation threw.

Reasons.

* `createInThread` (IndexBuilderImp, lines 298-342) loops `createStep`
  until `createState.isDone` and stops only on StreamIoException,
  DbStoppingException or DbFailedException. `createStep` (lines 375-447)
  runs an RW action that scans the next part of the directory and calls
  `RwEnvironmentImp.setIndexEntry(dbo, ..., createState.index, ...)` for
  each object, writing keys under the index's name; neither it nor the
  action reads the index info or checks the state. The state is checked
  only in `handleStepResult` (lines 449-467), after
  `createState.update(true, ...)` has already made the status 100, by
  `setIndexStateToActive`, which throws IllegalStateException ("State not
  STATE_CREATING, but 30", 30 being STATE_DELETING) out of the thread.
* `deleteIndexInternal` (DatabaseImp, lines 308-310) says that after
  `ensureDeletingState` "there should be no more index entries added to
  the index directory". The builder holds the same `Index` object, whose
  state `ensureDeletingState` sets to deleting, but it does not look at
  that state until activation, and it never uses `dirToActiveIndexes`.
* The probe only delays the first build step (a `Db.getMany` override
  that parks the thread named `IndexBuilderImp-CreateIndex-` once), then
  uses public calls: `deleteIndex(...).join`, `createFast` of the same name
  on field `other`, a put, `useIndex`. Without the latch the same happens
  to any build that is deleted while it still has steps to take, since no
  step checks the state; the latch only fixes the order. Run here: R3's
  output exactly (`[100]`, then `[200, 100, 100]`, the
  IllegalStateException, progress 100, the database active).
  `BuildDeleteReopen` (written for this verification) adds a MemoryStream
  and a reopen: the replacement still returns `[200, 100, 100]`.
* Against the contract: `Database.deleteIndex`, the comment above,
  `IndexBuilder.start` ("The index state will be CREATING until the job
  finishes and the index state becomes ACTIVE") and `JobStatus.progress`
  ("100 means finished"), and 010-01 P1/P6.

Reach: the Pub API in normal use: `indexBuilder(name)...start()` on a
directory large enough to take several steps, `deleteIndex(name)` while it
builds, then `indexBuilder(name)` again (for example on another field)
before the old build has scanned its directory. Without re-creation the
old build still leaves orphan entries under the name.

Effect: wrong answer, lasting: queries on the replacement index return
objects that do not match it, duplicates, and the wrong order, after a
restart too. Primary objects are intact; nothing hangs. The old job's
status says finished although it failed.

Commands:

    javac -cp repo/java/build/bergdb.jar -d out/r3/classes out/r3/BuildDeleteProbe.java
    java -ea -cp out/r3/classes:repo/java/build/bergdb.jar bergdb.core.BuildDeleteProbe
    javac -cp repo/java/build/bergdb.jar -d v/classes v/BuildDeleteReopen.java
    java -ea -cp v/classes:repo/java/build/bergdb.jar bergdb.core.BuildDeleteReopen
