018-04. Harness 6.7: the Pub API's promises
===========================================

Created 2026-11-05 by Frans Lundberg, as harness 6.7 of 018-01 (W2), in
the night 006-12 (Frans, 21:33: "Will you fix all bugs? [...]"). Built
by Claude (Opus 5.5, Claude Code), a harness agent of that night.

**Status: built; runs in `before-commit.sh`'s unit tests (1 s) and in
`night.sh`'s night tests (80 s).** It fails on each of the six known
faults of its class (018-01, section 6.7), with each fix reverted, and
found one more, 019-15, which waits for Frans's decision and is in its
skip list. It passes on `main`. Five questions for Frans (section 6).


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
  and every read until `setLookupTime()` reads at it, while the other
  connection writes (015-48: an `exists()` as that first read).
* An rw-transaction's reads see the latest state when it starts; its
  reads leave the connection's frozen time and `transactionInfo()` as
  they were (015-42). One connection at a time, the action runs once;
  when the other connection puts a key that the action read, during its
  first run, it runs again, reads the new value, and the output is the
  second run's (`Connection.rw()`).
* In one transaction the last call on a key wins (015-41).
* A `byte[]` is copied at the put: the harness overwrites the caller's
  array after each put (and, for `w()`, also before `execute()`), and
  the stored value must not change (015-47).
* A new connection's `getLookupTime()` is `Time.MAX` (015-59).
* `transactionInfo()` before any read found a value is
  `IllegalStateException` (015-62); after one, the transaction's time
  and its user KVs, one per key.
* Transaction times increase, and are after every `currentTime()`
  returned before them by the same started database; the first
  available lookup time is not after the first transaction (the retain
  duration is forever).
* Key replace: a put's key has each `${transactionTime}` replaced by
  the time, 18 digits (`%018d`, as `RwEnvironmentImp` does; the Javadoc
  gives no form).
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
  repeats a run.
* `SKIP`, as 6.3's (018-02, section 4): a known fault that is not
  fixed is listed, and the reference then expects what the code does,
  so the harness passes on `main`. A fix makes the harness fail until
  the fix removes its line. `-Dbergdb.promise.skip=none` skips nothing.

Adapted from 018-01's proposal, and why:

* Lookup times: no `LookupTimeNotAvailableException` is checked; the
  retain duration is forever, as reclaim is harness 6.4's and 6.2's.
* The rw-transaction's reads are made before its writes: a read of a
  key the transaction has written returns the committed value, not the
  transaction's own, and the Javadoc does not say which (Q1).
* `freezeLookupTime()` is not called twice without a `setLookupTime()`
  between, and `getLookupTime()` is not checked on a frozen connection
  (Q2, Q3).
* A delete of a key that had no entry may be in `transactionInfo()`'s
  KVs or not (Q4).
* The bound "after every `currentTime()` returned before" is reset at a
  restart (Q5).


## 3. Where it runs, and its cost

* **Unit tests** (`testSeeds`, Nano group "unit"): seeds 1 to 4, 2,000
  steps each, 1.1 s, mostly the 10 ms sleeps before an rw-transaction
  runs again (one CPU at about half). `before-commit.sh` runs the unit
  tests beside the f-tests, which take the longest, so it adds nothing
  measurable to its time.
* **Night tests** (`testSeedsLong`, Nano group "night", run by
  `night.sh`'s step night-tests): 40 seeds of 10,000 steps, 81 s on F53.
  Its seeds are new each day, the day's number times 1000 and the 39
  after it, printed first, so that a failure can be repeated.

From `java/`:

```sh
./unit.sh -c PubPromiseTester                       # the unit tests, 1 s
./night.sh tests -c PubPromiseTester                # the night's seeds, 80 s
java -ea -cp build/bergdb.jar bergdb.pubimp.PubPromiseTester SEED STEPS RUNS
java -ea -Dbergdb.promise.skip=none -cp build/bergdb.jar bergdb.pubimp.PubPromiseTester 1 5000 30
                                                    # nothing skipped: 019-15
```


## 4. The skip list

```java
static final String[] SKIP = {
    "019-15",   // a delete with key replace enabled deletes the key as written
};
```

While 019-15 is listed, the reference does not replace
`${transactionTime}` in a delete's key, as the code does today.


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
`PubPromiseTester OK`, and the night test's 40 seeds of 10,000. With
nothing skipped, seed 3 fails at step 4493 on 019-15.


### 5.1. A fault it found: 019-15

With key replace enabled, a put's key has `${transactionTime}` replaced,
and a delete's has not: `delete("/r/${transactionTime}")` deletes the
key as written. The Javadoc says that occurrences "in a database key"
are replaced. Registered as 019-15 with two options (replace in a
delete's key too, or the Javadoc says that it is not), recommendation
(a); it changes what a delete does and the bytes it writes, so it waits
for Frans, and is in the skip list.


## 6. Questions for Frans

Differences where the Javadoc is not clear, so not faults. Each is shown
by a probe on `main`; the harness avoids each, as section 2 says.

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
* **Q2. A second `freezeLookupTime()`.** Its Javadoc: "The lookup time
  of this Connection will not change until setLookupTime() is called or
  this method is called again." After a frozen read, a write, and a
  second `freezeLookupTime()`, a get still reads at the first frozen
  time: the second call changes nothing. "or this method is called
  again" can be read as "a new call freezes anew, at the next read".
  Options: (a) the Javadoc says that a second call keeps the frozen time;
  (b) a second call clears the frozen time, so the next read freezes
  anew (a line in `ConnectionImp.freezeLookupTime`). Recommendation: (b),
  as the sentence reads.
* **Q3. `getLookupTime()` on a frozen connection.** Its Javadoc:
  "Returns the requested lookup time that was set with
  setLookupTime()." After `freezeLookupTime()` and a read, it returns
  the frozen time (the actual one), not the requested `Time.MAX`. Options:
  (a) the Javadoc says so ("after freezeLookupTime() and a read, the
  frozen time"), which is useful, as it is the only way to learn the
  frozen time; (b) it returns the requested time. Recommendation: (a).
* **Q4. A delete of a key with no entry in `transactionInfo().kvs()`.**
  `w().delete("/missing").put("/y", "y")` gives one KV, the put: a delete
  of a key that has no entry is not in the transaction (it is not
  written). `TransactionInfo.kvs()` says "the user's puts and deletes",
  and `Connection.delete` that such a delete "does nothing". Options:
  (a) the Javadoc of `kvs()` says that a delete of a key with no entry is
  left out; (b) leave it. Recommendation: (a), a clause.
* **Q5. `currentTime()` across a restart.** "The returned time is
  guaranteed to be less [...] than the transaction time of any future
  transaction." A started database keeps it (`DbClock.lastReadTime`);
  after a restart, with a clock that has not moved (a `TestClock`), the
  first transaction has the time that `currentTime()` returned before the
  restart. With a real clock (100 ns units) a restart takes far longer, so
  only a clock that stands still or goes back meets it. Options: (a) the
  Javadoc says "of this started database"; (b) leave it.
  Recommendation: (a).

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
* `FileStream` and its directory: restarts are on a copy of a
  `MemoryStream`; the streams are harness 6.3's.
* `sync()`, `Transaction.sync()`, the startup distance and the cache
  size settings: nothing to compare.
* Objects, `DbObject`, `useIndex()`, `usePrimary()` and the indexes:
  experimental (018-01, D2).
* The action that throws, and calls to an `RwEnvironment` after its
  action (005-12 has tests).


## 8. State (night 006-12)

Clone `/Users/f/fl/bench/006-12/h67`, branch `h67`. Done: the harness,
this item, 019-15 registered. Next: more promises if time allows (key
replace in reads, restarts on a `FileStream`), and any new fault from the
night tests.


## 9. Log

2026-11-05, night 006-12. Built (W2 of 018-01, harness 6.7):
`PubPromiseTester`. It fails on the six known faults of 6.7, each with
its fix reverted, and found 019-15 (key replace and a delete), in its
skip list; five questions for Frans (section 6). In the unit tests (1 s)
and the night tests (80 s).
