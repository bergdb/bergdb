# 020-24-03 A concurrent service: cache, counters and transfers

Created 2026-11-09 by Frans Lundberg.

An application written as a new user of 2026.4 would write it, from README.md, the overview,
the Javadoc of `bergdb.pub` and `bergdb.pub.util` and releases/next.md only, against
`java/build/bergdb-release.jar` of main at b7aa2a0 (020-24's brief). Its subject: threads,
conflicts, retries, interrupts, stop and close, as the Javadoc promises them.


## 1. The application

A small multi-threaded service, in `/Users/f/fl/bench/2026-11-09/app-u3/app/ConcurrentApp.java`:
one file of 2,494 lines, plain `javac` and `java`, a `main` that runs every phase and exits 1
on a wrong result. The minimal reproductions of section 3 are in
`/Users/f/fl/bench/2026-11-09/app-u3/probe/`, the runs' output in `run-all-1.txt` (phases of
20 s, 96 s in all, F53 under a load of about 14) and `run-all-ea.txt` (15 s, with `-ea`), both
`CONCURRENT APP OK`.

    javac -cp bergdb-release.jar -d classes ConcurrentApp.java
    java -cp "${JAR}:classes" ConcurrentApp WORKDIR [SECONDS] [main|multi|misc|edges|reclaim|churn]

What it keeps, and how it uses BergDB:

* A bank: 50 accounts, Data Objects (`owner`, `balance`, `transfers`) at `/acc/aNN`, a user
  index on the balance. A transfer is an `rw()` that reads two accounts, the global counter
  `/ctr/transfers.bin` and the writer's own counter `/w/wI.bin` (byte[] values), writes all
  four and a log entry, a String at `/log/wI/SEQ.txt`; its outputs give the amount and the
  sequence number.
* Counters: eight byte[] counters incremented in `rw()`, and a `DbObject` counter (`n`, built
  with `DbObject.Builder`); each increment's output is its new value.
* A cache of 200 entries, each three keys written in one `w()`: the text (String, `.txt`),
  its SHA-256 (byte[], `.bin`) and an object holding both; deletes of all three in one `w()`.
* A write-skew guard (pairs of `Long` values, a withdrawal only if the pair's sum allows it),
  name claims (`rw()` with `exists()`: put if absent), and 3,000 blobs of 8 KB rewritten in
  place.
* 8 writer threads (half with `db.connection()`, half with `db.newConnection()`) and 8 reader
  threads. A reader freezes its lookup time and checks one state: the sum of the balances,
  the global counter against the writers' counters and the account counts, one writer's log
  by a primary scan, the index scan against the gets, a second connection set to the same
  time, counters that never go back, the cache's three keys alike; it reads again, later, at
  earlier frozen times, and expects the same values; it runs read-only `rw()`s.

The phases: (1) 20 s of the workload, two claim races (8 threads claim the same new name at a
barrier, 150 rounds each, with `exists()` and with `get()`), connection checks, a restart;
(2) `close()`, `stop()` then `close()`, and 4 `stop()`s and 2 `close()`s at once, each while
the 16 threads work, then a restart; (3) 15 s of interrupts, each of a random thread, the
next one sent only after the thread has seen the flag after a call, with a 4 MB cache so that
reads go to the files; (4) three databases in one JVM, two directories and one in memory,
4 + 4 threads each; (5) edge cases: an `rw()` whose action runs while `close()` is called, a
scan's iterator when `stop()` comes, `start()`, gets and `close()` with the interrupt flag
set, 3,000 short-lived threads, 16 threads on one hot key, `stop()` during an index build;
(6) one thread creates and deletes indexes on a directory that 4 writers change while 4
readers check each index scan against the primary scan at the same frozen time, and scan
again at earlier times, also indexes deleted since; (7) a retain duration of 1 s with slow
readers. Misc checks: a throwing action, the environment after `run()`, own writes not seen,
outputs, the interrupt flag before calls, a `put()` and a `close()` inside an action, an
`AssertionError` inside an action, writes interrupted while indexes come and go.

After each phase, and after each restart, a final check compares the database with what the
threads counted from calls that returned: every counter exact, every committed increment's
output distinct (no lost update), the cache's and the blobs' last write by transaction time,
the claims' winners, the logs complete and in order.


## 2. The findings

No wrong result, no hang and no failure of a database in any run. The findings are of the
Javadoc and the API, the most severe first. The reproductions are in the `probe` directory
above, or name the app's phase.

| ID | Kind | Severity | What | Reproduction |
|----|------|----------|------|--------------|
| U3-1 | doc | medium | close() refuses an rw() whose action runs        | RwDuringClose.java   |
| U3-2 | API | medium | an action's own Error fails the database         | misc checks          |
| U3-3 | doc | low    | sync() in a stop throws a StreamIoException      | SyncDuringClose.java |
| U3-4 | doc | low    | a put, delete or w() refused by an interrupt     | InterruptedPut.java  |
| U3-5 | doc | low    | reads and scans after stop(): not in Javadoc     | phases 2 and 5       |
| U3-6 | API | low    | non-API exception classes, internal messages     | phases 2 to 4        |
| U3-7 | API | low    | db.connection() unfreezes the thread's view      | connection checks    |
| U3-8 | doc | low    | connection() or newConnection(): two rules       | the Javadoc          |
| U3-9 | doc | low    | retain 1 s: no reclaim at the default distance   | phase 7              |


## 3. The findings in detail

* **U3-1, doc, medium: a running transaction does not complete at a stop.** stop()'s
  Javadoc: "no transaction or read starts after this method, and a transaction that runs
  completes"; close() "waits until the database is closed". An `rw()` whose action is
  running when `close()` is called is refused instead, and `close()` does not wait for it:
  in RwDuringClose.java (a memory database) and in phase 5 (a directory), `close()` returned
  after 0 to 15 ms while the action waited, and the `rw()` then threw
  `bergdb.core.DbStoppingException` ("Cannot call execute() while DB is stopping.", or
  "getOne()" when the action read after the close began); nothing was written (after the
  restart the key held its old value). The behaviour is safe and atomic, but a service that
  closes its database at shutdown, trusting the Javadoc to let requests in flight complete,
  has them refused. The reproduction:

      db.connection().put("/a.txt", "0");
      // thread T: db.newConnection().rw(env -> { env.get("/a.txt", String.class);
      //               inAction.countDown(); go.await(); env.put("/a.txt", "01"); });
      inAction.await();
      db.close();          // returns after 2 ms
      go.countDown();      // T's rw() throws DbStoppingException; /a.txt stays "0"

  Either the Javadoc says that only a commit in progress completes, and a transaction whose
  action runs is refused with IllegalDbStateException, nothing written; or `close()` waits
  for the running actions.

* **U3-2, API, medium: the action's own Error fails the database for every thread.** An
  `AssertionError` thrown by the application's code in an action (an `assert` with `-ea`)
  is rethrown by `rw()`, and every later call of every thread throws `DbFailedException`
  ("Cannot call getOne(): the database failed (the cause) and must be restarted.") until a
  restart. It is documented (Action.run(), Database "Errors", bergdb 019-10), but the action
  runs before the transaction's checks, when nothing has changed, and a `RuntimeException`
  there only fails the call. In a service, one request whose handler meets an assert, a
  `NoClassDefFoundError` or an `ExceptionInInitializerError` of the application's own classes
  stops the database for all. To consider: treat an Error thrown by the action, before its
  writes are applied, as a RuntimeException is treated, and fail the database only for a
  `VirtualMachineError` (OutOfMemoryError, StackOverflowError).

* **U3-3, doc, low: sync() in a stop throws StreamIoException.** SyncDuringClose.java:
  four threads put and `sync()` in a loop, and the main thread calls `close()`; each thread's
  `sync()` threw `bergdb.storage.StreamIoException` "StorageManager has error: Storage is
  closing." In phase 2, 16 such throws in three stops; after a refused call, a later
  `sync()` of the same connection returned normally 16 times and threw the same 32 times.
  Every other call in a stop throws `IllegalDbStateException` (put()'s Javadoc says so); the
  Javadoc of Connection.sync(), Database.sync() and Transaction.sync() names only a faulty
  database and an interrupt, and DbException's says that a stream error in a sync comes as a
  DbFailedException with the StreamIoException as its cause. So the type is neither of the
  documented kinds, and "has error" reads as a failure of the storage, while the database
  had not failed: every transaction that returned was there after the restart. The Core's
  `Db.sync` documents it ("or the database is stopping"); the Pub API's three do not. Either
  an IllegalDbStateException, as the other calls, or a line in the three Javadocs.

* **U3-4, doc, low: a put, a delete or a w() may be refused by an interrupt.**
  InterruptedPut.java: `put("/d/x", item)` in a loop, a second thread creating and deleting
  an index on `/d/`, and the main thread interrupting the writer every 0.2 ms for 3 s: 126
  of 185,838 puts threw `DbException` "The transaction was not run: the thread was
  interrupted while it waited to run it again after a conflict." In the app's misc checks,
  `put()`, `delete()` and `w().execute()` at object keys alike (56, 54 and 46 of about
  330,000 writes under 11,517 interrupts), each with the flag set and nothing written
  (checked: every key held the last write that returned). Without index changes (phase 3,
  577 interrupts) no write threw. Database's "Interrupts" paragraph says that "a transaction
  that waits to run again after a conflict throws a DbException", which a reader takes for
  `rw()`, the only call whose Javadoc mentions conflicts; the Javadoc of Connection.put(),
  delete() and WBuilder.execute() says neither that such a write may conflict and run again
  (releases/next.md does, 020-08, step 4) nor that an interrupt may then refuse it. A line
  in each one's `@throws DbException`.

* **U3-5, doc, low: reads and scans after stop() throw what their Javadoc does not name.**
  A `get()` or `exists()` after `stop()` throws `DbStoppingException`, an
  IllegalDbStateException ("Cannot call getOne() while DB is stopping."), where their
  Javadoc names a DbException only "if the database is faulty"; DbFailedException's Javadoc
  says that such a read does not fail the database, so it is meant. A primary scan's
  iterator in the middle of 4,000 keys threw it from `hasNext()` at its next batch, after
  100 values (phase 5): UsePrimaryBuilder's and UseIndexBuilder's Javadoc name only
  LookupTimeNotAvailableException and the conversion's exceptions. `currentTime()` and
  `newConnection()` returned normally after a stop, which "call only close()" allows.

* **U3-6, API, low: exceptions of classes outside the API, with internal messages.** In
  ordinary concurrent use the application meets `bergdb.core.DbStoppingException`, with
  "Cannot call getOne() / getMany() / execute() while DB is stopping." for a user's get,
  scan or rw(); `bergdb.storage.StreamIoException` for an interrupted sync, "Thread was
  interrupted while waiting for D1 size 114562720."; and, for a start on a directory that a
  database holds (after `stop()`, before `close()` has returned), a StreamIoException whose
  cause is `bergdb.stream.DirectoryInUseException`: DatabaseBuilder.start()'s Javadoc tells
  the user to look for that cause, but neither class is API (020-10, section 7), so the
  application compares `getCause().getClass().getSimpleName()`. A public exception for a
  directory in use, or the documented way to tell it, and messages in the API's words.

* **U3-7, API, low: connection() unfreezes the thread's connection.** Database.connection()
  "sets the requested lookup time of the returned Connection to Time.MAX" at each call
  (documented). A helper that calls `db.connection()` while its caller in the same thread
  reads a frozen state through the same object moves that state to the latest, silently: in
  the connection checks, `c1.setLookupTime(t0); db.connection();` left `c1` at Time.MAX. The
  caller's consistent read is then no longer one, with no error. Keep the lookup time
  (`newConnection()` gives a fresh connection), or warn in freezeLookupTime() and
  setLookupTime().

* **U3-8, doc, low: which connection for a thread.** Connection's class Javadoc: "create a
  Connection object for each thread by calling Database.newConnection()"; the package page:
  "db.connection() gives each thread its own, and db.newConnection() a new one". Both work
  (the app uses both, and 3,000 short-lived threads with `connection()` ran clean), but a new
  user reads two rules. One recommendation would do: `connection()` for a thread's own
  connection, `newConnection()` for a second view, such as a reader at another time.

* **U3-9, doc, low: when reclaim starts.** With `setRetainDuration(Duration.seconds(1))` on a
  database of the default startup distance (50 MB), 15 s of the workload and a stream of
  140 MB left `getFirstAvailableLookupTime()` at 1970-01-01, so no read expired; with
  `startupDistanceInMb(5)` it moved within seconds and slow readers met
  LookupTimeNotAvailableException, as documented. setRetainDuration()'s Javadoc says that a
  finite duration makes the database reclaim, not when: a user who tests the expiry of old
  states sees nothing happen. A sentence on what starts a cut would do.


## 4. What went well

* Every invariant held, in every run: in phase 1 alone (20 s), 114,706 `rw()`s (1.05 runs a
  commit) and 32,474 `w()`s, 39,355 transfers with the sum of the balances conserved,
  27,344 counter increments with distinct outputs (no lost update), and 102,450 checks by
  readers, every frozen state consistent: gets, the primary scan, the index scan and a
  second connection at the same time agreed, counters never went back, earlier states read
  again unchanged, before and after restarts.
* `rw()` is serializable as the Javadoc says: no write skew in 10,900 transactions on the
  guarded pairs, and in 300 claim rounds of 8 threads exactly one winner each, with
  `exists()` and with `get()` of a missing key. Reads do not see the action's own writes,
  outputs are the committed run's, a throwing action writes nothing, the environment
  refuses use after `run()`.
* Stop and close while 16 threads work, in three ways: every transaction that returned was
  in the database after the restart, and none that was refused; every call after the first
  refusal was refused with IllegalDbStateException; `close()` returned in 15 to 311 ms;
  concurrent `stop()`s and `close()`s returned.
* Interrupts: 577 (600 with `-ea`) in phase 3, each seen by the thread after the call, the
  flag never lost; `rw()` refused as documented, nothing written; no failure, also for reads
  from the files with the flag set, `start()` and `close()` with the flag set.
* Retries are fair: 16 threads on one key, 960 increments, at most 4 runs of one and 86 ms.
* Three databases in one JVM stayed apart and consistent; a second start on an open
  directory was refused and the first ran on.
* Indexes under churn: 197 created and deleted against 4 writers, 32,024 scans equal to the
  primary scan at the same frozen time, 10,646 scans at earlier times (1,940 of an index
  deleted since) right; a stop in the build of 20,000 objects left it BUILDING, and the
  restart built it right.
* With a retain duration of 1 s, slow readers at frozen times read right or met
  LookupTimeNotAvailableException, never a wrong value.
* The Javadoc of `rw()`, freezeLookupTime(), the Interrupts paragraph and stop() and close()
  was precise enough to write every check from it; U3-1 and U3-4 are its only places where
  the behaviour differed from a careful reading.


## 5. Fixes

By coord-1109's fixer x24, 2026-11-09, in the clone
`/Users/f/fl/bench/2026-11-09/clone-x24` rebased on `main` at `ec8d16f`, under Frans's rule for
2026.4 (2026-11-09): fix faults against today's specs and Javadoc, make the Javadoc true
where the code is as designed, no new API and no change of meaning. Each commit below has
its tests in `PubTesterJavadoc` and a line in `releases/next.md`, Documentation; JAVADOC
PUB OK. The gate under the lock, on the clone's tip `ed23b80`: BEFORE COMMIT OK (187 s, unit
1535, f 86, demos; `/Users/f/fl/bench/2026-11-09/x24-gate2.txt`).

* U3-1, U3-3 and U3-5: `2491196`. `Database.stop()` says that a transaction whose commit
  has begun completes, and that another call that runs at the stop is refused with
  `IllegalDbStateException`, nothing of it written, the database not failed: an `rw()`
  whose action runs (its next read or its commit throws), a write before its commit,
  `get()`, `exists()`, `useIndex()`, and a scan's iterator at its next read; `close()`, that
  it does not wait for such a call. The three `sync()`s say that at a stop, before the
  transaction is durable, they throw a `DbException` (a `StreamIoException`, "Storage is
  closing."), the database not failed and `close()` still writing it. `get()`, `exists()`,
  `useIndex()`, `rw()` and the two scans say what a stop does to them. Tests
  `testRwRefusedAtAStop`, `testSyncAtAStop`, `testReadsAfterStop`.
* U3-8: `8ba4003`. One rule, in `Connection` and the package page: `db.connection()` is the
  thread's own and the one to use, `db.newConnection()` for a second view; `Connection`
  says too that `connection()` sets the lookup time to `Time.MAX` at each call (U3-7's
  case, the behaviour unchanged). Javadoc only (`testConnections`).
* U3-9: `e68315e`. `setRetainDuration()` says when reclaim begins and cuts: nothing is cut
  before the stream has grown by about four times the startup distance in a small
  database; measured on the release jar, the first cut after 201 MB of puts at 50 MB and
  18 to 28 MB at 5 MB. Test `testReclaimCutsLater`.
* U3-4: 020-23's V1-2 says it in `Connection.put()`, `delete()` and `WBuilder.execute()`.
* For Frans (U3-6, confirmed): the class that a stop throws is
  `bergdb.core.DbStoppingException`, not API, a subclass of the API's
  `IllegalDbStateException`, which the Javadoc names; its messages name internal methods
  ("Cannot call getOne() while DB is stopping."). A sync at a stop throws
  `bergdb.storage.StreamIoException`, not API either (no signature of `Db` names it), a
  subclass of the API's `DbException`, which the Javadoc names, as it named the class
  before for an interrupted sync. U3-2 and U3-7: API, not changed.
