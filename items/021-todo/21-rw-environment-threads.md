021-21. Fix: an RwEnvironment used by several threads, and after its action
===========================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-09 by Frans Lundberg.

What: an rw() action that uses its `RwEnvironment` from several threads,
with a parallel stream or a task that it waits for, which the Javadoc
does not forbid, reads another key's value, commits only part of its puts
while `rw()` returns normally, and then fails the database (020-24-11,
U11-1, high). And the environment used after its action returned, from
another thread, takes puts while the commit is made, and once an object
was committed without its index entry, where the Javadoc promises
`IllegalStateException` (U11-3, medium). The reproductions
`ParallelEnv.java` and `LeakedEnvIndex.java` in
`/Users/f/fl/bench/2026-11-09/app-u11/app/repro/`.

Why: no use of the API, documented or not, may give wrong data silently
or fail the database; misuse ends in an exception to the caller (2026.4,
"a bug-free database").

Frans: none.

Done when: tests that fail before the fix; the environment safe for its
action's threads with the least change (one lock, uncontended for one
thread), or calls of other threads refused, and the Javadoc says which;
the environment closed when the action returns, before the commit; a
single-threaded `rw()` measured to cost the same; `BEFORE COMMIT OK`,
`JAVADOC PUB OK` and `java/stress/level1.sh` under the gate lock; a line
in `releases/next.md`.

First step: what state of the environment each call reads and writes.


Log
---

2026-11-09. Registered by coord-1109 from 020-24-11's U11-1 and U11-3,
and taken by its agent t21 (clone `clone-t21`, on main's 9ed1e6c).

2026-11-09. Done by t21: commit fa019d5 in `clone-t21`, on main's
279dba1, to land (with ed157ee of 021-22 and 5fca061 of 020-24 after it).

* Why. `RwEnvironmentImp` kept its reads' `GetData` (the Core's
  per-operation scratch, for one thread), its read set (`MyLongSet`), its
  read time and its three write maps (`HashMap`) unsynchronized: threads
  in the action shared the `GetData` (wrong values, then a
  `StreamFormatException` "Bad value pointer -1" that failed the
  database), broke the maps (lost puts, once a `StackOverflowError`), and
  could drop an entry of the read set, so that a conflict went unseen.
  `RwTransaction.execute()` closed the environment in a `finally` after
  the commit, with a plain boolean: a late put landed in `objectOps`
  while `indexEntries()` iterated it (a `ConcurrentModificationException`
  out of `rw()`), or after the index set was read, so that its object was
  committed with no entry.
* Chosen: the environment is made safe for its action's threads, not
  refused to them. The change is small: each call of the user's that
  reads or changes that state (`get()`, `exists()`, `put()`, `delete()`,
  `setOutput()`) does so in a `synchronized (this)` block, uncontended
  for one thread, and checks there that the environment is open; a
  conversion, from a value read or to a value put, runs outside it, as it
  may run user code (a constructor that waits for another thread would
  otherwise hold the lock). A task that the action hands the environment
  to and waits for is plausible use (020-24-11's E2 worked before), and a
  refusal would have broken it. Reads of several threads are serialized:
  correct, not faster.
* The environment is closed when the action returns or throws, under the
  lock, before `indexEntries()` and the commit: every later call throws
  the documented `IllegalStateException`, from any thread, and changes
  nothing; a call either made its change before (it is in the
  transaction) or throws. The commit's internal calls take no lock, as no
  call changes the state any more. Each run of the action has an
  environment of its own (`RwEnvironmentImp.nextRun()`, with key replace
  as the connection had it at `rw()`, 020-24-02, I-6), so a thread left by
  an earlier run cannot put into a later one, where it could before;
  `prepareForRWRerun()` and `clearOutput()` are gone. A `WBuilder`'s
  environment and an index build's are unchanged.
* Javadoc: `RwEnvironment`, "Threads": the action may use the
  environment from several threads; their reads and writes are taken one
  at a time; it is closed when the action returns or throws, for every
  thread, so the action waits for its threads; each run has its own.
  `Action.run()` and the package page point there.
* Tests, in the new `PubTesterThreads`, each failing before the fix:
  `testEnvironmentReadByThreads` (8 threads read 32 keys 4 times in each
  of 20 actions: `ArrayIndexOutOfBoundsException` before),
  `testEnvironmentWrittenByThreads` (8 threads put 200 keys in each of 30
  actions: 361 missing before), `testEnvironmentClosedAtTheActionsReturn`
  (a put through the leaked environment from the index manager's hook
  after the index set: taken before, and committed without its entry;
  now `IllegalStateException`, the primary scan and the index 1 each),
  `testEnvironmentOfAnEarlierRun` (the first run's environment, used in
  the second run: the same object before, and its put committed).
* Reproductions on the fixed release jar: `ParallelEnv reads`, 2,000
  rounds, 0 with a wrong read; `ParallelEnv puts`, 0 of 6,000 missing;
  `LeakedEnvIndex`, 500 rounds: every late put that returned normally
  (35,718) is committed with its entry, the others threw
  `IllegalStateException`, `rw()` threw nothing, 0 objects not in the
  index. On 2026.3's jar `ParallelEnv` failed the database in round 0.
* Cost, one thread (`/Users/f/fl/bench/2026-11-09/t21-perf/`,
  `GuardCost.java` run by `AB.java`, which alternates the jars of main's
  9ed1e6c and of the fix in one JVM, 8 times 3 rounds; F53 under load
  20 to 28): an `rw()` of one get and one put 3,370 ns before and 3,480
  after (medians of 16), minima 2,968 and 2,889: no difference beyond
  the noise.
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
