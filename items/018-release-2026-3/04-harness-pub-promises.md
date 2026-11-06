018-04. Harness 6.7: the Pub API's promises
===========================================

Created 2026-11-05 by Frans Lundberg, as harness 6.7 of 018-01 (W2), in
the night 006-12 (Frans, 21:33: "Will you fix all bugs? [...]").

**Status: built; runs in `before-commit.sh`'s unit tests (1.5 s) and in
`night.sh`'s night tests (100 s).** It fails on each of the six known
faults of its class (018-01, section 6.7), with each fix reverted, and
found one more, 019-15, closed on 2026-11-06 by the Javadoc (option
(b)); its skip list is empty. It passes on `main`. Its five questions on
the Javadoc (section 6) were answered by Frans on 2026-11-06 and are
done: the Javadoc says each, each `freezeLookupTime()` freezes anew (Q2,
a change of behaviour), and the reference checks each.


## 1. What it checks, and why

The Pub API's Javadoc is a promise: what a get, an `exists()` or a
`transactionInfo()` returns after a sequence of puts, deletes,
transactions, lookup times and restarts. The six known faults of the
class each broke one such promise, and each was found by a review that
read one method. The harness checks the promises together, on random
sequences of calls, so that a breach no review has met is found too.

The calls, on `String` and `byte[]` values only (DbObject and the user
indexes are experimental, 018-01, D2; left out):

* `Connection.put`, `delete`, `w()` with 1 to 5 puts and deletes,
  `rw()` with reads first and then writes, and outputs;
* `get(key, String.class)`, `get(key, byte[].class)`,
  `get(key, Object.class)` (a `.txt` key gives a `String`, others a
  `byte[]`; bytes never start with DbObject's magic), `exists()`;
* `transactionInfo()`: the time and the KVs of the transaction that
  wrote the last value found by a `get()` or an `exists()` of the
  connection; `IllegalStateException` if none has found one;
* `setLookupTime()` (`Time.MAX`, a transaction's time, one unit before
  or after it, before the first), `getLookupTime()`,
  `freezeLookupTime()`;
* `currentTime()` of the connection and the database, and
  `getFirstAvailableLookupTime()`;
* `Database.connection()` again (the same object, its lookup time
  `Time.MAX`), and `newConnection()`;
* `setEnableKeyReplace()`, and writes to keys with `${transactionTime}`;
* calls with an invalid key or a null value: `IllegalArgumentException`,
  and nothing written;
* restarts: `close()`, and a start on a copy of the stream.

Every answer is compared with a reference in the test: a map of each
key's versions by time (a value, or a delete), and each transaction's
KVs. The promises it holds BergDB to:

* A read at lookup time T sees the last version at or before T;
  the actual lookup time is the requested one, or the last
  transaction's if that is earlier (`setLookupTime`).
* After `freezeLookupTime()`, the first read freezes its actual time,
  and every read until `setLookupTime()` or `freezeLookupTime()` reads at
  it, while the other connection writes (015-48: an `exists()` as that
  first read). Each call freezes anew, at the latest state as of the next
  read, also on a frozen connection and after `setLookupTime(t)` (Q2).
  `getLookupTime()` is the requested time, and after `freezeLookupTime()`
  `Time.MAX` until the next read and the frozen time after it (Q3).
* An rw-transaction's reads see the latest state as of its first read,
  not its own puts and deletes (Q1); its reads leave the connection's
  frozen time and `transactionInfo()` as they were (015-42). One
  connection at a time, the action runs once; when the other connection
  puts a key that the action read, during its first run, it runs again,
  reads the new value, and the output is the second run's
  (`Connection.rw()`).
* In one transaction the last call on a key wins (015-41).
* A `byte[]` is copied at the put: the harness overwrites the caller's
  array after each put (and, for `w()`, also before `execute()`), and
  the stored value must not change (015-47).
* A new connection's `getLookupTime()` is `Time.MAX` (015-59).
* `transactionInfo()` before any read found a value is
  `IllegalStateException` (015-62); after one, the transaction's time
  and its user KVs, one per key, without the deletes of keys that had no
  entry (Q4).
* Transaction times increase, and are after every `currentTime()`
  returned before them by the same started database (Q5); the first
  available lookup time is not after the first transaction (the retain
  duration is forever).
* Key replace: a put's key has each `${transactionTime}` replaced by
  the time, 18 digits (`%018d`, as `RwEnvironmentImp` does; the Javadoc
  gives no form); a delete's key is taken as written (019-15).
* A restart keeps every committed transaction, and new connections
  start with `Time.MAX`, no frozen time and no `transactionInfo()`.


## 2. How it works

One test class, `bergdb.pubimp.PubPromiseTester`, registered in the
package's `Pack`; test code only, nothing in the production code.

* `run(seed, steps)` starts a database on a `MemoryStream` with a
  `TestClock`, two connections (`connection()` and `newConnection()`),
  and makes `steps` random calls from a `Random(seed)`. The clock moves
  0 to 999 units before a quarter of the calls, so that times collide
  with the last transaction's and pass it.
* The keys: nine fixed ones (with no suffix, `.txt`, `.bin`, two levels,
  and one with `å`, `€` and a surrogate pair), the keys made by key
  replace (up to 200), and seven invalid ones. Values: `String`s of
  `a`-`z`, `å` and `€`, or random bytes, of 0 to 11 or, one time in four,
  0 to 2,999 bytes.
* Each call is logged; a failure throws an `AssertionError` with the
  seed, the step, what differed, and the last 30 calls
  (`-Dbergdb.promise.lines=N` for more). `main(seed, steps, runs)`
  repeats a run; `main(seed, steps, runs, dir)` runs in directories.
* Three kinds of run, by the seed (since the night's second part):
  * on a `MemoryStream`, restarts on a copy of it (the seeds that are 1
    or 3 modulo 4, and 0 outside the night test);
  * in a directory (the night test's seeds that are multiples of 4, and
    the unit test `testSeedDirectory`): the Pub API's `create()`, and
    `open()` at a restart, on `FileStream`;
  * small (the seeds that are 2 modulo 4): the smallest startup distance
    (5 MB) and cache (4 MB), 300 more keys (`/k/N`, with and without
    `.bin`), values of up to 60 KB, and restarts 20 times rarer, so that
    a run passes its startup distance and eviction drops nodes and
    values, which reads then load again from the stream (seed 2, 10,000
    steps: 26 sweeps, 2,824 objects released, at the last start).
    `-Dbergdb.promise.verbose=true` prints eviction's summary.
* `SKIP`, as 6.3's (018-02, section 4): a known fault that is not
  fixed is listed, and the reference then expects what the code does,
  so the harness passes on `main`. A fix makes the harness fail until
  the fix removes its line. `-Dbergdb.promise.skip=none` skips nothing.

Adapted from 018-01's proposal, and why:

* Lookup times: no `LookupTimeNotAvailableException` is checked; the
  retain duration is forever, as reclaim is harness 6.4's and 6.2's.
* The questions of section 6, as Frans answered them (2026-11-06). Until
  then the harness avoided each; now its reference follows each answer
  and checks it:
  * an rw-transaction's reads and writes come in a random order, a read
    now and then of a key that the transaction writes, and every read
    must give the state as of the first read (Q1);
  * `freezeLookupTime()` is called on a frozen connection too, and resets
    the reference's requested time to `Time.MAX` (Q2);
  * `getLookupTime()` is checked on every connection, and after each
    `freezeLookupTime()`: `Time.MAX` until the next read, the frozen time
    after it (Q3). A read before the harness's first transaction freezes
    the time of the new database's own transaction; the reference takes
    it from `currentTime()` at the first start, with the clock at 0;
  * a delete of a key that had no entry must be left out of
    `transactionInfo()`'s KVs (Q4);
  * the bound "after every `currentTime()` returned before" is reset at a
    restart, as the promise is for the started database (Q5).


## 3. Where it runs, and its cost

* **Unit tests** (Nano group "unit"): `testSeeds`, seeds 1 to 4, 2,000
  steps each (seed 2 small), and `testSeedDirectory`, seed 5, 1,000
  steps in a directory; 1.5 s together, mostly the 10 ms sleeps before
  an rw-transaction runs again (one CPU at about half). `before-commit.sh` runs the unit
  tests beside the f-tests, which take the longest, so it adds nothing
  measurable to its time.
* **Night tests** (`testSeedsLong`, Nano group "night", run by
  `night.sh`'s step night-tests): 40 seeds of 10,000 steps, 101 s on
  F53 (81 s before the directory and small runs). Its seeds are new each
  day, the day's number times 1000 and the 39 after it, printed first,
  so that a failure can be repeated: ten in directories, ten small.

From `java/`:

```sh
./unit.sh -c PubPromiseTester                       # the unit tests, 1.5 s
./night.sh tests -c PubPromiseTester                # the night's seeds, 100 s
java -ea -cp build/bergdb.jar bergdb.pubimp.PubPromiseTester SEED STEPS RUNS [DIR]
java -ea -Dbergdb.promise.skip=none -cp build/bergdb.jar bergdb.pubimp.PubPromiseTester 1 5000 30
                                                    # nothing skipped
```


## 4. The skip list

```java
static final String[] SKIP = {
};
```

Empty since 2026-11-06. It listed 019-15 until Frans chose its option
(b): the Javadoc says that a delete's key is taken as written, and the
reference does not replace `${transactionTime}` in it.


## 5. The evidence

The known faults were fixed on 2026-11-05 (439ec79, b8c8da7, a46d2b2,
39cbbec, e451afd). On `main` (45cfb4f) with the harness, in a second
clone, each fix's main hunk was reverted alone, the jar built, and
`PubPromiseTester 1 5000 10` run. Each failed at seed 1:

* 015-41, `kvOps.remove` in `RwEnvironmentImp.delete` reverted: step
  255, `c1.exists(/d/e) at 25238: expected 'false', got 'true'`.
* 015-42, `getInTransaction` reads with the connection's `GetData`:
  step 45, `c1.transactionInfo(), expected the transaction at 1129, its
  time: expected '1129', got '1195'`.
* 015-47, the copy in `RwEnvironmentImp.put` reverted: step 28,
  `rw get(/b, byte[].class): expected [-21, -115, 37, ...], got [120,
  120, 120, ...]` (the caller's array, overwritten after the put).
* 015-48, `getBytesAtLookupTime` freezes before its read: step 93,
  `c1.get(/b, Object.class) at 5549: expected [-61, -91, 99, ...], got
  null`.
* 015-59, a new connection's lookup time `Long.MAX_VALUE`: step 0,
  `IllegalArgumentException: Time ouf of range, units:
  9223372036854775807.`
* 015-62, the check of `tpos == 0` in `transactionInfo()` reverted:
  step 1185, `IllegalArgumentException: Not a position of a
  transaction, 0.`

The reverted hunks are the fixes' own (`git show` of the commits
above); for 015-42, `ConnectionImp.getInTransaction` read with
`getData` and set the frozen time, as `getInternal` did before.

On `main`, with the skip list: 150 seeds of 5,000 steps (100 to 249),
`PubPromiseTester OK`, and the night test's 40 seeds of 10,000. After the
directory and small runs were added (night 006-12, second part): 80
seeds of 10,000 steps (600 to 679, 20 of them small), 15 seeds of 20,000
steps in directories (500 to 514) and 8 more (702 to 709, two of them
small), and the night test: all pass. With
nothing skipped, seed 3 failed at step 4493 on 019-15, until it closed.

After Q1 to Q5 (2026-11-06, section 6), with the reference checking each
answer: the unit tests, seeds 1 to 30 of 5,000 steps with nothing
skipped, 2,000 seeds of 30 steps (1000 to 2999) and 300 of 30 steps in
directories (5000 to 5299), so that a read before the first
transaction freezes, and the night test (seeds 20763000 to 20763039 of
10,000 steps, 91 s): all pass. With Q2's line in `ConnectionImp` taken
out, seed 1 fails at step 56: a `freezeLookupTime()` after
`setLookupTime(4018)`, `getLookupTime()` `4018`, not `Time.MAX`.


### 5.1. A fault it found: 019-15

With key replace enabled, a put's key has `${transactionTime}` replaced,
and a delete's has not: `delete("/r/${transactionTime}")` deletes the
key as written. The Javadoc says that occurrences "in a database key"
are replaced. Registered as 019-15 with two options (replace in a
delete's key too, or the Javadoc says that it is not), recommendation
(a); it changes what a delete does and the bytes it writes, so it waited
for Frans, in the skip list. Frans chose (b) (2026-11-06, 10:00):
`Connection.setEnableKeyReplace`'s Javadoc says that a delete's key is
taken as written, the reference follows it, and the line left the skip
list.


## 6. Questions for Frans

Differences where the Javadoc was not clear, so not faults. Each is shown
by a probe on `main` (below); the harness avoided each until it was
answered.

Answered by Frans on 2026-11-06, to coord-1106 (006-13). At 10:58: "Q1,
as recommended. Q2, let's go through this one in more detail. Q3, tell me
more. Q4, expand a little [...] Q5, as recommended." After the details,
with Q2's option (c), at 11:04: "Q2, c, as recommended. Q3, a, as
recommended. Q4, a, as recommended." Done the same day by agent p5 of
coord-1106: the Javadoc in `bergdb.pub`, short (010-P13), one line of
`ConnectionImp` for Q2, a test, and the harness's reference (section 2).

* **Q1. Does an rw-transaction read its own writes?** In an action,
  `env.put("/k", "3")` and then `env.get("/k", String.class)` returns the
  committed value, `"2"`, and `env.exists()` after `env.delete()` of an
  existing key returns `true`: the reads are of the state when the
  transaction began, not of its own writes. `RwEnvironment`'s and
  `Action`'s Javadoc say nothing of it. Options: (a) the Javadoc of
  `RwEnvironment.get` says so ("reads the state at the transaction's
  first read; the transaction's own puts and deletes are not seen");
  (b) the reads see the transaction's own writes (a change of behaviour,
  through `kvOps`; objects and key replace complicate it).
  Recommendation: (a).
  **Decided: (a)** (10:58). No code change. `RwEnvironment.get`: "The
  action's reads read one state, the latest as of its first read: they
  do not see the transaction's own puts and deletes." `RwEnvironment`
  now declares `exists()`, inherited before from `ReadInterface`, whose
  `@see` led to `Connection.exists` and its lookup time: "Checks whether
  an entry exists for the key, in the state that get() reads: the
  transaction's own puts and deletes are not seen." `Action.run`: "Its
  reads read the latest state as of its first read, not the
  transaction's own puts and deletes."
* **Q2. A second `freezeLookupTime()`.** Its Javadoc: "The lookup time
  of this Connection will not change until setLookupTime() is called or
  this method is called again." After a frozen read, a write, and a
  second `freezeLookupTime()`, a get still reads at the first frozen
  time: the second call changes nothing. "or this method is called
  again" can be read as "a new call freezes anew, at the next read".
  Options: (a) the Javadoc says that a second call keeps the frozen time;
  (b) a second call clears the frozen time, so the next read freezes
  anew (a line in `ConnectionImp.freezeLookupTime`). Recommendation: (b),
  as the sentence reads. In the details that Frans asked for at 10:58
  (006-13): (a) as above; (b) freezes anew from the requested time; (c)
  each call freezes anew at the latest state. In (c) a connection has one
  lookup time: `setLookupTime(t)` sets it to t, `freezeLookupTime()` to
  the latest state as of the next read, and each undoes the other; so
  `setLookupTime(t)` and then `freezeLookupTime()` freezes the latest
  state, not t, and a loop that calls `freezeLookupTime()` before each
  batch of reads reads the new state each time. Recommendation: (c).
  **Decided: (c)** (11:04). A change of behaviour (`releases/next.md`,
  Pub API). `ConnectionImp.freezeLookupTime()` sets the lookup time to
  `Time.MAX` as well as the flag. `Connection.freezeLookupTime`:
  "Freezes the lookup time at the latest state as of the next read. It
  sets the lookup time to Time.MAX; the next get() or exists() of this
  connection sets it to the time it read at, and later reads read at
  that time, until setLookupTime() or this method is called again. Each
  call freezes anew, at the latest state as of the next read, also after
  setLookupTime(t): it does not freeze t." `setLookupTime`: "A call to
  this method undoes the effect of a previous call to
  freezeLookupTime(), and a later call to freezeLookupTime() undoes this
  one's." The test `PubTester.testFreezeAgainReadsNewState`: a frozen
  read, another connection's write, a second `freezeLookupTime()`:
  `getLookupTime()` is `Time.MAX`, the read gives the new value and
  freezes its time, and `setLookupTime(t1)` and then
  `freezeLookupTime()` reads the latest. Before the line it fails at the
  second freeze (`getLookupTime()` the first frozen time; with that
  check taken out, the read `'1'`, not `'2'`); after, it passes.
* **Q3. `getLookupTime()` on a frozen connection.** Its Javadoc:
  "Returns the requested lookup time that was set with
  setLookupTime()." After `freezeLookupTime()` and a read, it returns
  the frozen time (the actual one), not the requested `Time.MAX`. Options:
  (a) the Javadoc says so ("after freezeLookupTime() and a read, the
  frozen time"), which is useful, as it is the only way to learn the
  frozen time; (b) it returns the requested time. Recommendation: (a).
  **Decided: (a)** (11:04). No code change. `Connection.getLookupTime`:
  "Returns the lookup time of this connection: Time.MAX by default, and
  t after setLookupTime(t). After freezeLookupTime(), it is Time.MAX
  until the next read, and the frozen time after it: with
  setLookupTime(), another connection can then read the same state."
* **Q4. A delete of a key with no entry in `transactionInfo().kvs()`.**
  `w().delete("/missing").put("/y", "y")` gives one KV, the put: a delete
  of a key that has no entry is not in the transaction (it is not
  written). `TransactionInfo.kvs()` says "the user's puts and deletes",
  and `Connection.delete` that such a delete "does nothing". Options:
  (a) the Javadoc of `kvs()` says that a delete of a key with no entry is
  left out; (b) leave it. Recommendation: (a), a clause.
  **Decided: (a)** (11:04). No code change. `TransactionInfo.kvs()`: "A
  delete of a key that had no entry is left out, as it writes nothing."
* **Q5. `currentTime()` across a restart.** "The returned time is
  guaranteed to be less [...] than the transaction time of any future
  transaction." A started database keeps it (`DbClock.lastReadTime`);
  after a restart, with a clock that has not moved (a `TestClock`), the
  first transaction has the time that `currentTime()` returned before the
  restart. With a real clock (100 ns units) a restart takes far longer, so
  only a clock that stands still or goes back meets it. Options: (a) the
  Javadoc says "of this started database"; (b) leave it.
  Recommendation: (a).
  **Decided: (a)** (10:58). No code change. `Connection.currentTime()`
  and `Database.currentTime()`, which makes the same promise: "These
  promises are for this started database: after a restart, with a clock
  that has not moved (a test clock), the first transaction can have the
  time that currentTime() returned before the restart."

The probe's output (on `main`, 45cfb4f):

```text
Q3 before a read: getLookupTime 72057594037927935
Q3 after a read: getLookupTime 1001, t1 1001
Q2 second freeze, get 1 (t2 1002)
Q1 rw get after its own put: 2, exists after its own delete: true
Q4 kvs of a delete of a missing key with a put: 1
```


## 7. What it does not cover

* Several threads: one thread makes every call; the rw conflict is
  forced in the same thread. Concurrency is harness 6.6.
* Reclaim and `LookupTimeNotAvailableException` (a finite retain
  duration), large values and times at their limits: harness 6.4.
* Failures, interrupts, `stop()` and the failed database: harness 6.2.
* `FileStream`'s own promises: the directory runs only use it; the
  streams are harness 6.3's.
* `sync()`, `Transaction.sync()`, the startup distance and the cache
  size settings: nothing to compare.
* Objects, `DbObject`, `useIndex()`, `usePrimary()` and the indexes:
  experimental (018-01, D2).
* The action that throws, and calls to an `RwEnvironment` after its
  action (005-12 has tests).


## 8. State (night 006-12)

Clone `/Users/f/fl/bench/006-12/h67`, branch `h67`. Done: the harness,
this item and 019-15 (landed as 4d7a1bb), and the second part, runs in
directories and small runs, which found no new fault. 019-15 is done
(2026-11-06, option (b)); the questions Q1 to Q5 are answered and done
(2026-11-06, section 6). Next,
if the harness is extended: more threads (harness 6.6), a finite retain
duration (6.4).


## 9. Log

2026-11-05, night 006-12. Built (W2 of 018-01, harness 6.7):
`PubPromiseTester`. It fails on the six known faults of 6.7, each with
its fix reverted, and found 019-15 (key replace and a delete), in its
skip list; five questions for Frans (section 6). In the unit tests (1 s)
and the night tests (80 s).

2026-11-06, night 006-12. Runs in directories (the Pub API's `create()`
and `open()`, on `FileStream`) and small runs (startup distance 5 MB,
cache 4 MB, 300 more keys, values of up to 60 KB, so that eviction
drops nodes and values) added; no new fault in 103 seeds. The unit
tests take 1.5 s, the night tests 101 s.

2026-11-06. 019-15 done, option (b) (Frans, 10:00): the reference takes
a delete's key as written under key replace, and the skip list is
empty. Seed 3 (5,000 steps, past step 4493), seeds 1 to 30 (5,000 steps,
nothing skipped), the unit tests and the night tests pass. By agent f15
of coord-1106.

2026-11-06. Q1 to Q5 (section 6) answered by Frans, to coord-1106
(10:58 and 11:04): (a), (c), (a), (a), (a). The Javadoc of
`RwEnvironment.get` and `exists()` (now declared there), `Action.run`
(Q1), `Connection.freezeLookupTime` and `setLookupTime` (Q2),
`getLookupTime` (Q3), `TransactionInfo.kvs()` (Q4), and
`Connection.currentTime()` and `Database.currentTime()` (Q5); Q2's
change of behaviour, one line in `ConnectionImp.freezeLookupTime()`, and
`PubTester.testFreezeAgainReadsNewState`, which fails before it. The
reference follows each answer and checks it (section 2): reads after
writes in rw-transactions, a second freeze, `getLookupTime()` on a frozen
connection, `kvs()` without the deletes of missing keys; and the time of
the new database's own transaction. The unit tests, the night tests and
seeds 1 to 30 with nothing skipped pass (section 5).
`releases/next.md`: Pub API (Q2) and Documentation. By agent p5 of
coord-1106.

2026-11-05. Built by Claude (Opus 5.5, Claude Code), a harness agent of
the night 006-12. (Moved here from the header on 2026-11-06, at Frans's
word, 11:35: 006-12, section 8, point 10, option (b).)
