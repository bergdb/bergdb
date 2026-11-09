# 020-24-11 A hurried service: reentrant calls, shared objects

Created 2026-11-09 by Frans Lundberg.

An application written as a new user of 2026.4 would write it (u11, for coord-1109, round 4
of the common brief of 020-24): only `java/build/bergdb-release.jar` on the class path, built
from a clone of main at `20e8d5a`, and only what a user reads: README.md, the Javadoc of
`bergdb.pub` and `bergdb.pub.util` (from the sources), the package page and releases/next.md.
The implementation was read only afterwards, to explain U11-1, U11-2, U11-3 and U11-5.


## 1. The application

A service written by a hurried developer, who calls BergDB in every way that the Javadoc
does not forbid, and in some that it does, in
`/Users/f/fl/bench/2026-11-09/app-u11/app/ReentrancyApp.java` (one file, 2,446 lines, plain
`javac` and `java`; `sh run.sh [IDS]` compiles it and runs every scenario, or those named, such
as `A4,E3` or `E*`). Each of its 57 scenarios runs in a thread of its own under a watchdog: a
call that does not return within its time (10 to 60 s) is recorded as a hang, with a thread dump
(ThreadMXBean, and `jstack -l`) in `/Users/f/fl/bench/2026-11-09/app-u11/work/`, and the thread
is then interrupted. After each scenario the database is probed (a put and a get on a new
connection, in another thread, within 5 s); a directory database is also closed, restarted and
its data compared with what the scenario committed. A scenario that finds a wrong value, a
failed database or a hang where the Javadoc promises a return counts as BAD, and `main` exits
1 if any does. The last full run, `run-all.txt` beside it, took 124 s and ended "REENTRANCY APP
FOUND 6" (A10b, E3, E4, F3, H1, I1; section 3), and I7, added after it, is in `run3.txt`; the
minimal reproductions of section 3 are in `app/repro/`, each a `main` with the release jar
alone on the class path.

What it does, by group:

* A, the same connection from inside its rw() action: `c.put()`, `c.delete()`, `c.w().execute()`,
  `c.get()`, `c.transactionInfo()`, a nested `c.rw()` (other keys; the key the outer read; an
  inner action that throws), `c.sync()`, `db.sync()`, `Transaction.sync()`, `c.usePrimary()` and
  `c.useIndex()` iterated there, `indexBuilder().start().join()`, `deleteIndex()` (and a rebuild
  of the same name), the Database's settings and `indexJob().join()`, `stop()`, `close()`,
  `setLookupTime()` and `freezeLookupTime()` around the action's reads, key replace toggled.
* B, another connection and another database: a put of the key the action read through a
  second connection; two memory databases, four threads, each `rw()` on one calling `rw()` on
  the other inside its action, crosswise; an action that waits for another thread's 600 puts,
  gets and `rw()`s.
* C, the action's exceptions: a checked IOException (thrown without a declaration), a plain
  Throwable, an InterruptedException, `rw(null)`, the action catching the environment's
  IllegalArgumentException and ObjectCreationException and going on, an Error from a Data
  Object constructor in `get()` and in `env.get()`, a static initializer that throws.
* D, long and interrupted actions: a 1-second action on a key another thread writes every
  50 ms; an action that interrupts its own thread and then reads 5,700 values from the files
  (cache 4 MB); 12,315 interrupts in 8 s of a thread whose actions read the files.
* E, the RwEnvironment beyond its action: kept and used after `rw()` returned; used by another
  thread while the action waits for it; read and written by a parallel stream; leaked to a
  thread that goes on putting while `rw()` commits.
* F, one Connection shared by threads: 8 threads putting through it (put, w(), rw()); 8 threads
  incrementing one counter by `rw()` through it; a thread's `db.connection()` handed to a pool
  of 8 doing puts, gets, frozen gets, scans and `rw()`s in a directory with an index; key
  replace on it.
* G, iterators: one read by 4 threads at once; every key of a directory updated (put and
  `rw()`) while iterating it; one made inside an action and read after it; one read after
  `stop()`, and after `close()` and a new start on the directory; one read while another
  thread closes the database.
* H, a WBuilder shared: 4 threads putting into one builder, then `execute()`; two threads calling
  `execute()` on one builder at once, 200 times.
* I, Data Object classes that call BergDB: a constructor that gets, puts or runs `rw()` through
  the thread's connection, in `get()`, in a scan and in `env.get()`; a constructor that scans
  the same connection during a primary and an index scan; a constructor that sets the
  connection's lookup time; one that waits for another thread's put, `rw()`, `sync()` and index
  build, in a get, both scans and `env.get()`; static initializers that get, put and run `rw()`,
  first reached inside BergDB's `get()`, in 4 threads at once.


## 2. The findings

No hang where the Javadoc promises a return, and no deadlock: every hang of an `rw()` was one
whose action wrote, through a connection, what the action had read (U11-4), and it ended on an
interrupt or a stop; the one other hang was a thread spinning in a WBuilder shared by threads
(U11-6). The two high findings are threads sharing what BergDB keeps per connection or per
transaction. The most severe first:

| ID | Kind | Severity | What | Reproduction |
|----|------|----------|------|--------------|
| U11-1 | bug | high   | RwEnvironment in threads: wrong reads, a failed DB   | ParallelEnv        |
| U11-2 | API | high   | shared Connection, reads: wrong values, a failed DB  | SharedReads        |
| U11-3 | bug | medium | a leaked environment: an object not in its index     | LeakedEnvIndex     |
| U11-4 | doc | medium | calls in an action: own transactions, endless reruns | SelfConflict       |
| U11-5 | bug | low    | transactionInfo() after a constructor's own get      | I1                 |
| U11-6 | API | low    | shared iterator or WBuilder: skipped or lost values  | SharedIterator, H1 |
| U11-7 | doc | low    | an action's checked exception, rw(null), a catch     | C1 to C6           |


## 3. The findings in detail

* **U11-1, bug, high: an RwEnvironment used by several threads gives wrong reads, loses
  puts, and fails the database.** The Javadoc gives the environment no thread rule:
  RwEnvironment says that it is "valid only while Action.run() runs", and Connection's rule
  ("A Connection object assumes it and any objects returned from its methods are accessed
  from a single thread") is about what Connection's methods return, which the environment is
  not. So a developer who reads the action's keys with a parallel stream, or hands them to a
  CompletableFuture and joins it, is within the documented API. ParallelEnv.java, one thread,
  a memory database, 32 keys, no other writer:

      c.rw(env -> {
          long bad = IntStream.range(0, 32).parallel().filter(
                  k -> !Integer.toString(k).equals(env.get("/p/k" + k + ".txt", String.class)))
                  .count();
          env.setOutput("bad", bad);
      });

  In three runs: the first `rw()` returned normally with 5 of its 32 reads giving another
  value, and the second threw DbFailedException "A read failed on the storage (the cause). The
  database takes no more transactions or reads and must be restarted."; in the other two runs
  the first `rw()` threw it. Every later call of every connection then throws
  DbFailedException: the in-memory database is lost. In the app's E3 the cause was a
  StreamFormatException, "Bad value pointer -1, index 12 of node 409." in one run and "index 7
  of node 0." in the next. An action that had written what it computed from such reads
  would have committed wrong values. With puts, `ParallelEnv puts`: 30 `rw()`s, each putting
  200 keys with `IntStream.range(0, 200).parallel().forEach(i -> env.put(...))`, all returned
  normally, and 546 of the 6,000 keys were not in the database (735 in the app's E4): a
  transaction that commits only part of what its action put, with no error. In the last full
  run, E4 also met a `StackOverflowError` in an `rw()`, presumably from the environment's
  HashMap broken by the concurrent puts, which failed the database as an Error does. In the
  app (E3), 8 threads whose actions read 32 counters in parallel failed the database in 57 ms;
  the same transactions with sequential reads (E5) gave 2,000 commits and exact sums. A second
  thread that uses the environment while the action waits for it (E2) worked: its put was
  committed and its output set. Afterwards, from the implementation: the environment keeps
  its reads' GetData (the Core's per-operation scratch, "must not be used by multiple
  threads"), the read set (`MyLongSet readHashes`) and the writes (`HashMap`s) unsynchronized,
  so a parallel read also may drop an entry of the read set, and a conflict would then go
  unseen. Either a guard
  (the environment remembers the action's thread, and a call from another thread throws
  IllegalStateException; or the calls are made safe) or, at least, a sentence in RwEnvironment
  and Action.run(): the environment is for the action's thread only, and what follows from
  another thread's use.

* **U11-2, API, high: a Connection shared by threads that read returns wrong values, then
  fails the database, reported as a failure of the storage.** Documented as not allowed
  (Connection, above), but the consequence is not said, and a static `Connection` field in a
  service is a common mistake. SharedReads.java: a memory database of 2,000 keys, no writes
  while 4 threads `get()` random keys through one Connection:

      shared connection: 773 gets, wrong 12, first throw: DbFailedException: Cannot call
      getOne(): the database failed (the cause) and must be restarted.
      wrong value for k606: value of k406     (and null for existing keys)
      a new connection reads: DbFailedException

  With a connection each (`own`), 800,000 gets, none wrong. SharedReadsDisk.java, a directory
  database (100,000 keys, cache 4 MB, so that reads load from the stream), one writer with its
  own connection, 4 readers sharing one, six runs of up to 20 s: in four the database failed
  within a second (DbFailedException "A read failed on the storage", cause StreamFormatException
  "Bad value pointer -1, index 11 of node 3226453."); in the other two it went on, and each
  reader ended on a raw `java.lang.ArrayIndexOutOfBoundsException` ("Index 8 out of bounds for
  length 2", "Index 16 out of bounds for length 14"), which two of the four runs met first too;
  5 to 80 wrong values were returned before that in each run. After `close()` and a restart, every
  key held what the writer had committed, and the scan had all 100,000 keys, in all six runs:
  the stream was not harmed. The app's F3 (a thread's `db.connection()` handed to a pool of 8,
  mixed calls) failed the database in the same way; after the restart the 400 keys, the primary
  scan and the index agreed. Shared for writes only (F1: 24,000 puts, `w()`s and `rw()`s
  through one connection from 8 threads; F2: 4,000 counter increments by `rw()`; F4: key
  replace) everything was right. Afterwards, from the implementation: ConnectionImp holds one
  GetData for its reads (get(), exists(), transactionInfo()), which concurrent reads share.
  The failure misleads: an operator reads "A read failed on the storage" and "Bad value
  pointer" as a corrupt disk, and restores a backup, while the cause was the application's
  threads; an in-memory database is lost. A cheap guard would turn it into an exception of the
  caller: the connection's reads mark it busy (an atomic flag) and a concurrent read throws
  IllegalStateException ("a Connection is for one thread at a time"); or a GetData per read.
  Either way the Javadoc should say what concurrent use does.

* **U11-3, bug, medium: the environment after the action, from another thread: puts are
  taken during the commit, a put may be committed without its index entry, and rw() may throw
  a ConcurrentModificationException.** RwEnvironment: "The environment is valid only while
  Action.run() runs; a call to it after that throws IllegalStateException." For the action's
  thread it does (E1: get, put, exists, delete and setOutput after `rw()` each threw it). An
  action that starts a thread with the environment, and returns, is a hurried developer's
  "fire and forget". LeakedEnvIndex.java, a memory database with an index on `/o/`, 500
  `rw()`s, each putting 20 objects and leaving a thread that puts 3,000 more:

      rw(env -> { for (i < 20) env.put("/o/r" + r + "-k" + i, new Obj(i));
                  new Thread(() -> { for (i < 3000) env.put("/o/late-r" + r + "-k" + i, ...); })
                          .start(); });

  In three runs: 56,119 to 78,405 late puts returned normally; 35 to 96 `rw()`s threw a raw
  `java.util.ConcurrentModificationException` (nothing of them written: the counter of the app's
  E6 ended at 298 of 300); in one run 3,000 late puts were committed, in the others 0 or 1; and
  in one run the late object `/o/late-r41-k0` was committed with no index entry: the primary
  scan had 8,081 objects, the index 8,080. A wrong index, kept by later commits, with no error.
  The database stayed sound otherwise. Afterwards, from the implementation: RwTransaction
  closes the environment after the commit (`env.close()` in a finally), with a plain boolean,
  so the environment takes puts while the index entries are computed and the transaction is
  made; a put between the two is, presumably, written without its entry. The fix the Javadoc
  implies: close the environment when run() returns, before the index entries, so that a late
  call throws IllegalStateException, as documented.

* **U11-4, doc, medium: calls to the database inside an action are transactions of their own,
  and a write to what the action read makes rw() rerun until interrupted or stopped.** Action
  and Connection.rw() say that the action may run more than once; only the package page says
  that "an action should have no effect but its reads and writes through env". Nothing says
  what a call of the connection, of another connection or of the Database inside the action
  does. What happens: each is a transaction of its own, committed at once (A1: an inner put's
  time is before the outer transaction's), not undone when the action throws (A17: the outer
  action threw after `c.put("/nested.txt")`, which stayed) or is run again, and repeated at each
  run. When it writes a key that the action read, through the same connection (A2), a nested
  `rw()` (A4b) or another connection (B1), the outer transaction conflicts with it at every
  run: SelfConflict.java ran 13 runs in 5 s, each committing its nested put (the key grew by
  13 characters), and `rw()` never returned, without an error, until `close()` from another
  thread ended it (DbStoppingException after 153 ms); an interrupt ends it too (DbException,
  "not run"). With the index calls: `indexBuilder().start().join()` in an action that writes
  the indexed directory joined (ACTIVE), the commit then reran, as the directory's indexes had
  changed, and the second run threw IndexAlreadyExistsException out of `rw()` (A9);
  `deleteIndex()` the same with NoSuchIndexException (A10); an action that deletes and
  rebuilds an index of the same name reran forever (A10b, 20 s). The sleep between runs
  reaches 640 ms, so such an `rw()` runs about twice a second forever: a service's request
  thread is lost, with no message. A paragraph in Action.run() and Connection.rw(): calls of a
  Connection or the Database in an action are separate transactions, committed at once, not
  undone and repeated at each run; one that writes what the action read makes it conflict at
  every run, so `rw()` does not return until the thread is interrupted or the database stops.
  Writes belong in env; reads of the same state belong in env.

* **U11-5, bug, low: transactionInfo() after a get whose Data Object constructor reads
  through the same connection describes the constructor's read.** I1: `Configured`'s
  constructor reads `/cfg/a.txt` through `db.connection()`, the thread's connection; after
  `c.get("/con/x", Configured.class)` returned, `c.transactionInfo()` gave the transaction of
  `/cfg/a.txt`, not that of `/con/x`, the value the get retrieved. The Javadoc: "information
  about the transaction that wrote the last value retrieved with the get() method". The get
  records its value's transaction in the connection's GetData and `infoKey` before the
  conversion, which the constructor's get overwrites. A lookup of configuration or of a
  related object in a constructor is plausible; a rare case otherwise. Either the get records
  its transaction after the conversion, or a line in transactionInfo().

* **U11-6, API, low: a shared iterator or WBuilder skips or loses silently and throws
  internal exceptions; the database stays sound.** Both are covered by Connection's rule, so
  this is about the consequence only. SharedIterator.java, one primary scan's iterator read by
  4 threads: 4,959 of 5,000 keys returned (41 skipped, others twice in the app's G1), and
  `IndexOutOfBoundsException: Index 100 out of bounds for length 100`, `IllegalArgumentException:
  ikey == null not allowed` (KvToObjectImp) and `NullPointerException: Cannot read field "value"
  because "this.next" is null`; later reads were right. H1, 4 threads putting 1,000 keys each
  into one WBuilder: `execute()` returned normally and 3,809 of the 4,000 keys were written, none
  wrong; in the last full run, H1 hung instead: one putting thread spun in
  `HashMap$TreeNode.split` under `RwEnvironmentImp.setKv` (the builder's HashMap broken by the
  concurrent puts), an interrupt did not end it, and it used a core until the JVM ended (dump
  `work/dump-H1.txt`). Two threads calling `execute()` on one builder at once (H2) never both
  executed in 200 tries. Unlike U11-2, the database went on, so a sentence in Connection's
  Javadoc on what sharing does (wrong and missing results, a thread that may spin forever;
  for reads through the connection, a failed database) would do.

* **U11-7, doc, low: what an action may throw, rw(null), and a caught
  ObjectCreationException.** Action.run(): "If this method throws a RuntimeException, nothing
  is written, rw() throws it, and the database goes on; an Error fails the database." A checked
  exception thrown without a declaration (C1, an IOException; a lambda that wraps a library
  call this way is common) and a plain Throwable (C2) are treated as a RuntimeException:
  rethrown as they are, nothing written, the database sound; the Javadoc names neither. `rw(null)`
  throws IllegalArgumentException "action == null not allowed" (C4), which rw()'s `@throws` does
  not name. RwEnvironment.get(): ObjectCreationException is "the action's exception, which ends
  the action"; an action that catches it and goes on commits (C6: the put after the catch was
  written). A clause each: "any other Throwable as a RuntimeException"; `@throws
  IllegalArgumentException if action is null`; "which ends the action unless it catches it".


## 4. What went well

* No deadlock in any of the 57 scenarios, also where one was likely: `db.sync()`, `c.sync()` and
  `Transaction.sync()` inside an action (A6, 10 ms), `indexBuilder().start().join()` inside an
  action (A9), `stop()` and `close()` inside an action (A11, A12: `rw()` threw
  IllegalDbStateException, nothing written, the restart right), an action waiting for another
  thread's 600 calls (B3: 6 ms, no call blocked by the action), `rw()` on two databases inside
  each other's actions crosswise in 4 threads (B2: 1,200 transactions, exact), static
  initializers that get, put and run `rw()`, first reached inside BergDB's get, in 4 threads at
  once (I3), and 46 Data Object constructors, in a get, a primary scan, an index scan and
  `env.get()` on a directory with a 4 MB cache, each waiting for another thread's put, `rw()`,
  `sync()` and, for 5 of them, an index build and its deletion (I7: no wait over 10 s).
* Reentrancy in one thread is sound: a put, a delete, a `w().execute()` and a nested `rw()` of
  other keys inside an action committed as separate transactions, the outer one right after
  them, its outputs and the nested one's apart (A1, A4, A5); a nested `rw()` whose action threw,
  caught by the outer action, wrote nothing and left the outer one committing (A16); scans of
  the same connection inside an action (A8), every key of a directory updated by put and
  `rw()` while iterating it (G2: 1,000 updated, 1,000 added, the iterator at its time), an
  iterator made inside an action and read after it (G3), constructors that get, put, run `rw()`
  or scan the same connection during a get, a primary scan and an index scan (I1, I2, I5: 450
  objects each, in order, each constructor's scan right).
* The action's reads are the transaction's: `c.setLookupTime(old)` or `c.freezeLookupTime()`
  around them did not change what env read (A13, A13b); key replace is taken at `rw()`, as
  documented (A14); an action that set the retain duration, the startup distance and the cache
  size and joined an index job committed in one run (A15).
* Exceptions from the action, of every kind but an Error of its own, left the database sound
  and nothing written (C1 to C6); an Error from a Data Object constructor, in `get()` and in
  `env.get()`, and a failing static initializer came as ObjectCreationException with the cause,
  the database going on, as 019-40 says (C7, C8).
* Interrupts: an action that interrupts its own thread and reads 5,700 values from the files
  committed, the flag kept (D2); 12,315 interrupts in 8 s of a thread in actions that read the
  files gave 21,790 commits, none refused, the counter exact after a restart (D3). A livelock
  (U11-4) and a long action that never commits (D1, 12 runs in 15 s, documented) end on an
  interrupt with the documented DbException.
* Iterators after `stop()`, and after `close()` and a new start on the same directory, threw
  IllegalDbStateException and read nothing of the new database (G4, G5).
* Writes through a shared Connection, and `execute()` raced on one WBuilder, were right (F1, F2,
  F4, H2); the stream survived every failure of U11-2 on a directory (seven runs).


## 5. Fixes

By t21 for coord-1109, 2026-11-09, in `clone-t21` on main's 279dba1, to land: three commits,
each with tests in the new `PubTesterThreads` that fail before it. The principle: misuse ends
in an exception to the caller, never in a wrong value, a lost write or a failed database.

| Finding | Commit | Item | What changed |
|---|---|---|---|
| U11-1     | fa019d5 | 021-21 | RwEnvironment safe for the action's threads: one lock |
| U11-3     | fa019d5 | 021-21 | the environment closed at the action's return; one per run |
| U11-2     | ed157ee | 021-22 | a Connection guard: a call during another thread's throws |
| U11-6     | ed157ee | 021-22 | the same guard on scan iterators; a WBuilder synchronized |
| U11-5     | 5fca061 | 020-24 | the get's transaction kept across its conversion |
| U11-4, -7 | 5fca061 | 020-24 | Javadoc of Action.run(), Connection.rw(), RwEnvironment.get() |

* U11-1: the action may use its environment from several threads; their reads and writes
  are taken one at a time, under the environment's lock, uncontended for one thread; the
  conversions run outside it. Chosen over refusing other threads, as E2's use is plausible
  and the change small. ParallelEnv on the fixed jar: 2,000 rounds of parallel reads, none
  wrong; 0 of 6,000 parallel puts missing.
* U11-3: the environment is closed, under the lock, when the action returns or throws,
  before the index entries and the commit; a call after that throws IllegalStateException
  from any thread and changes nothing. LeakedEnvIndex: every late put that returned is
  committed with its index entry, the others threw; no ConcurrentModificationException.
* U11-2: each call of a Connection that reads, writes, syncs, scans or sets the lookup
  time enters with a compare-and-exchange; a call of another thread meanwhile throws
  IllegalStateException ("A Connection is used by one thread at a time"), a call inside a
  call of the same thread is taken. SharedReads and SharedReadsDisk: 0 wrong values, the
  readers end on the refusal, the database goes on. F1 to F3 now throw it too.
* U11-6: SharedIterator's threads are refused in the same way; a WBuilder's calls are
  synchronized, so H1 writes all 4,000 keys, and a put after execute() throws.
* U11-5: transactionInfo() describes the get's value, also when its constructor read
  through the connection (I1).
* U11-4, U11-7: Javadoc only, as section 3 proposes.
* Cost for one thread, medians of 16 alternating rounds in one JVM on a loaded F53: get()
  578 and 568 ns, rw() 3,370 and 3,480 ns, a scan's next() 390 and 396 ns: within the noise.
* Runs, under the gate lock on the tree of the three commits: BEFORE COMMIT OK (228 s, unit
  1598, f 86, demos), JAVADOC PUB OK, LEVEL 1 OK. Details in 021-21 and 021-22.
