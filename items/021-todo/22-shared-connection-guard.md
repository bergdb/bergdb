021-22. Fix: a Connection, an iterator or a WBuilder shared by threads
======================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-09 by Frans Lundberg.

What: a `Connection` shared by reading threads, which the Javadoc
forbids, returns another key's value or null, throws a raw
`ArrayIndexOutOfBoundsException`, and then fails the database with a
message that looks like corruption ("A read failed on the storage", "Bad
value pointer -1"), which loses an in-memory database and sends an
operator to a backup (020-24-11, U11-2, high). A scan's iterator or a
`WBuilder` shared by threads skips or loses values silently, throws
internal exceptions, or leaves a thread spinning in a broken `HashMap`
(U11-6, low). The reproductions `SharedReads.java`,
`SharedReadsDisk.java` and `SharedIterator.java` in
`/Users/f/fl/bench/2026-11-09/app-u11/app/repro/`, and the application's
H1.

Why: misuse must end in an exception to the caller, not in wrong data or
a failed database (2026.4, "a bug-free database").

Frans: none.

Done when: tests that fail before the fix; a cheap guard per connection
(set and cleared around each call) that throws `IllegalStateException` on
concurrent use, measured to cost nothing measurable for one thread; the
same for a shared `WBuilder` and a scan's iterator if cheap, else the
Javadoc says what sharing does; `BEFORE COMMIT OK`, `JAVADOC PUB OK` and
`java/stress/level1.sh` under the gate lock; a line in
`releases/next.md`.

First step: what state of a connection each call reads and writes.


Log
---

2026-11-09. Registered by coord-1109 from 020-24-11's U11-2 and U11-6,
and taken by its agent t21 (clone `clone-t21`, on main's 9ed1e6c).

2026-11-09. Done by t21: commit ed157ee in `clone-t21`, after fa019d5
(021-21), on main's 279dba1, to land.

* State of a connection: `getData` (`get()`, `exists()`,
  `transactionInfo()`), `infoKey`, the lookup time and its freeze (set by
  reads and scans), `lastSposOfLastTrans` (`sync()`). Writes through a
  shared connection were right in 020-24-11 (F1, F2), but `sync()` could
  wait for another thread's transaction, not the caller's.
* Guard: `ConnectionImp` holds the thread in a call of it, or null, in an
  `AtomicReference<Thread>`. Each call that reads or changes that state or
  runs a transaction (`get`, `exists`, `transactionInfo`, `put`,
  `delete`, `rw`, both `sync`s, `usePrimary`, `useIndex`, `setLookupTime`,
  `freezeLookupTime`, `setEnableKeyReplace`, and `WBuilder.execute()`)
  enters with a compare-and-exchange (acquire) and leaves with a release
  store, a lock's orders; a call of another thread meanwhile throws
  `IllegalStateException` "A Connection is used by one thread at a time:
  another thread is in a call of it. Nothing was read or changed (bergdb
  021-22)." before it reads or changes anything. A call inside a call of
  the same thread (a plain read finds it: only the thread sets itself) is
  taken: a Data Object constructor's get in a get, a put or nested `rw()`
  in an action. Threads that take turns are not refused. Not guarded: the
  getters, `currentTime()` and `w()`. `Database.connection()` sets the
  thread's connection's lookup time, so it throws too when another thread
  is in a call of that connection (the Javadoc says so).
* Iterators: the scans' `Scan` of `usePrimary()` and `useIndex()` hold
  the same guard around `hasNext()` and `next()` ("An iterator is used by
  one thread at a time: ..."); the index scan's own `GetData` was shared
  as the connection's was.
* `WBuilder`: its `put()`, `delete()` and `execute()` are `synchronized`
  rather than refused: a shared builder takes the calls one at a time,
  so no put is lost, and a put after `execute()`, also one that waited
  for it, throws the documented `IllegalStateException` (spent).
  `execute()` enters the connection's guard (it runs a transaction on it)
  before it spends the builder.
* Two tests shared a connection between threads, through
  `db.connection()` in the test's thread, which is the connection they
  gave the other thread: `PubTester.testRw2` and
  `PubTesterOutput.testRerun` now give the other thread
  `db.newConnection()`. Nothing else in the unit tests, f-tests, demos or
  level 1 met the guard.
* Javadoc: `Connection`, "Threads"; `WBuilder` (a shared builder);
  the package page.
* Tests in `PubTesterThreads`, each failing before the fix except the
  third, which guards reentrancy: `testConnectionInACallOfAnotherThread`
  (while a get's Data Object constructor waits, 11 calls of another
  thread each throw, and change nothing; before they ran),
  `testConnectionSharedByReaders` (4 threads, 20,000 gets on one
  connection: each right or refused, the database goes on; before
  `ArrayIndexOutOfBoundsException`), `testConnectionInACallOfTheSameThread`,
  `testWBuilderSharedByThreads` (4 threads, 10 builders of 1,000 puts: 947
  missing before), `testIteratorInACallOfAnotherThread` (a call while
  another thread is in `next()` throws; the iterator then gives the rest,
  each once).
* Reproductions on the fixed release jar: `SharedReads shared`: the
  first concurrent call threw the `IllegalStateException`, 0 wrong, a new
  connection reads; `SharedReadsDisk` (8 s, a directory, 100,000 keys,
  one writer): 606,980 reads, 0 wrong, the readers ended on the
  `IllegalStateException`, the restart's data and scan right;
  `SharedIterator`: 5,000 distinct keys, then the refusal. On 2026.3's
  jar `SharedReads` failed the database after 28 gets.
* Cost, one thread, as in 021-21 (medians of 16 alternating rounds in one
  JVM, F53 under load): a `get()` 578 ns before and 568 after (minima 491
  and 483); a scan's `next()` 390 and 396 ns (1.5 %; minima 357 and 375).
  A first version with `compareAndSet` and a volatile store cost a scan
  about 5 % (387 and 405 ns); acquire and release brought it to the
  noise.
* `releases/next.md`, Pub API.

Runs: Under the gate lock (2026-11-09, 16:51 to 16:57), on the tree of the three
commits: `BEFORE COMMIT OK (228 s)` (unit 1598, f 86, demos); `JAVADOC PUB
OK`; `java/stress/level1.sh`: `LEVEL 1 OK`.

2026-11-09. Independent review of fa019d5 and ed157ee by coord-1109's Pub
reviewer v1 (17:03): sound; no deadlock or lost wake-up possible (the busy
flag never blocks; the environment's lock is never held while taking the
IndexManager lock or writeLock); close before commit and reruns correct;
every legal single-thread pattern still works (probe
/Users/f/fl/bench/2026-11-09/v1/probe22/). Low: getLookupTime(),
getEnableKeyReplace(), currentTime() and w() are unguarded though the
Javadoc says "every call that reads"; reads in one action are serialized
(as documented); IndexBuilder and the use-builders are not thread-safe while
WBuilder now is.
