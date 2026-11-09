# 020-13. The test study before the release cut

Created 2026-11-09 by Frans Lundberg. Status: open.

**State (2026-11-09, 10:30).** Parts 1 to 4 done and written here. The
work is in the clone `/Users/f/fl/bench/2026-11-09/clone-tests`, from
`main` at `1d1b6f3`; its commits are listed in section 1. The work
files, scripts and outputs are outside the repository, in
`/Users/f/fl/bench/2026-11-09/tests-work/` (`tests-work/` below). Each
commit of Java code came after `before-commit.sh` printed BEFORE COMMIT
OK; nothing is pushed, the coordinator integrates. Open: section 7.

Frans, 2026-11-09, 08:41: "I want the test study before the release
cut. This release focus is 'bug-free database'. So let's go
bug-hunting." The study has four parts: the coverage of the unit and
f-tests; their quality, by tests that cannot fail and a sample of faults
planted by hand; a hunt for bugs where the tests are weak or the risk is
high; and tests that could go.


## 1. In short

**Bugs found: four, all fixed in the clone** (section 4.1), each with a
test that fails before its fix and passes after:

1. **An rw() read two states of one key and committed** (`a857539`,
   `RwEnvironmentImp.get`): when the action's first get threw in its
   conversion and the action caught it, the read time was not fixed, so
   the next read and the STM check were at a later time.
2. **An Error of a Data Object class's static initializer passed as it
   is** (`ca13a43`, `DataObjects.make`): a get threw the `AssertionError`
   at the class's first use, and in `rw()` the database failed; 020-09,
   section 5.2 promises `ObjectCreationException`.
3. **Key replace deleted another key's index entries** (`72dfb65`,
   `RwEnvironmentImp.indexEntries`): a put at `/d/${transactionTime}` in
   an indexed directory deleted the entries of the value stored at the
   key as written, which stayed without them.
4. **BufferedStream.close() could wait a quarter of the buffer time for
   nothing** (`ac3291e`, `BufferedStream.consume`, a lost wake-up in the
   Core's storage layer): 12.5 ms at the default buffer time, 15 s in a
   unit test with a buffer time of a minute.

The commits in the clone, after `1d1b6f3`: `a857539` (bug 1), `ca13a43`
(bug 2), `72dfb65` (bug 3), `6e99055` (three tests for the faults the
gate missed), `ac3291e` (bug 4), and this item's commit.

Not fixed, for Frans (section 4.2): `Time.utc` and `Time.resolve` take
strings that break their format, such as "2013-13" and "25:00", though
their Javadoc promises `BadFormatException` (a fix changes what is
accepted); `setRetainDuration(null)` throws `NullPointerException`;
`useIndex(name, String.class)` is accepted but cannot return a value; and
six corners of the Javadoc.

**Coverage** (section 2), by JaCoCo over the unit and f-tests at
`1d1b6f3`, of the production classes of `java/src` (the testers left
out): 93.6 % of lines and 81.2 % of branches. The Pub layer is the best
covered: `bergdb.pubimp` has 95.4 % and 90.2 %, its 2026.4 classes 95 to
99 % of lines. The weakest are the file stream's error paths
(`FileStream` 75 % of branches, `StreamContract` 56 %, `StrictStream`
67 %), the Core's rare branches (`Eviction` misses 155, `Reclaim` 113,
`NodeCollection` 92; `Cache3` 71 %), and `bergdb.pub`'s value classes and
`Time` (77 % of branches in the package). Every method of the Pub API
runs in a test but the `toString()`s, two `hashCode()`s and
`Transaction.sync()` of an `rw()`.

**Mutation score** (section 3.2): 47 faults planted by hand in 2026.4's
code, one at a time. One cannot be caught by any test (P43: the check it
removes is made again in the next class). Of the other 46 the gate caught
43: 30 of the first 33 at `1d1b6f3`, and 13 of 13 more at `6e99055`. The
three it missed now have tests that catch them (`6e99055`): a deletion
that does not write the directory's virtual key, a build step without its
definition's hash in its read set, and a scan that does not compare an
entry with its value. With them, 46 of 46.

**Recommendations** (section 6): take the five commits into `main`;
decide `Time`'s parsing; add the index threads to the gate's check that
no database is left running; move three slow f-test classes that cover
11 lines no other test covers out of the gate (about 30 s of the f-tests'
62); and check reruns, not only final states, in race tests.


## 2. Coverage (part 1)

How: the JaCoCo agent 0.8.16 (`org.jacoco.agent-0.8.16-runtime.jar` and
the CLI `org.jacoco.cli-0.8.16-nodeps.jar`, from Maven Central, their
SHA-1 checked, in `tests-work/jacoco/`) ran `bergdb.dev.Unit` and
`bergdb.dev.F` from a copy of `build/bergdb.jar` at `1d1b6f3`, with `-ea`,
as the gate runs them (`tests-work/cov/run-cov.sh`): 1,415 unit tests in
37 s and 86 f-tests in 71 s under the agent. The reports are
`tests-work/cov/html/`, `all.xml` and `all.csv`. The scripts in
`tests-work/scripts/` sum them (`covsum.py`), list the missed lines
(`missed.py`) and the API methods that no test runs (`apimissed.py`).
level1.sh was not run under the agent: its other steps (DagFuzz,
RestartStress, RestartInvariance) are the Core's, which the level scripts
and the Lean model check apart.

Per package, production classes only (a class whose name ends with
Tester, Harness or Reference is left out; the testers sit beside the
code):

| Package | Lines | Line % | Branches | Branch % |
|---|---|---|---|---|
| bergdb.common   | 1,483  | 93.6  | 488    | 82.6 |
| bergdb.core     | 12,268 | 94.2  | 4,910  | 78.9 |
| bergdb.dag      | 2,721  | 93.3  | 1,368  | 78.0 |
| bergdb.pub      | 821    | 86.0  | 237    | 76.8 |
| bergdb.pub.util | 29     | 100.0 | 0      | -    |
| bergdb.pubimp   | 7,429  | 95.4  | 2,432  | 90.2 |
| bergdb.storage  | 1,981  | 94.2  | 626    | 81.0 |
| bergdb.stream   | 2,608  | 87.9  | 742    | 72.5 |
| total           | 29,340 | 93.6  | 10,803 | 81.2 |

The unit tests alone give 91.8 % and 79.8 %. The f-tests add 542 lines
(`tests-work/scripts/fonly.py`), mostly in `FileStream` (102), `Reclaim`
(83), `Jmx` (44), `Eviction` (16) and `Db` (12).

The classes new or changed for 2026.4 (`git diff --stat release-2026.3
HEAD -- java/src`):

| Class | Line % | Branch % | Missed that matters |
|---|---|---|---|
| ObjectFormat         | 97.3     | 94.5     | none; 17 branches, mostly asserts               |
| DataObjects          | 95.8     | 94.5     | an Error of a static initializer (bug 2)        |
| IndexKeys            | 98.4     | 95.8     | none                                            |
| IndexDefinition      | 96.4     | 91.2     | a few refusals of a bad stored definition       |
| IndexManager         | 95.3     | 83.7     | a build not started; a cleanup over format 1    |
| IndexBuilderImp      | 96.8     | 93.8     | a build's key with no ikey; an interrupted join |
| RwEnvironmentImp     | 96.4     | 86.2     | none but asserts and dead code (below)          |
| RwTransaction        | 89.7     | 86.4     | an interrupt between reruns; an rw's `sync()`   |
| WTransaction         | 90.9     | 100.0    | the `Bug` branch, which cannot run              |
| UseIndexBuilderImp   | 95.9     | 85.7     | format 1 at an entry's key; a key with no ukey  |
| UsePrimaryBuilderImp | 98.9     | 93.8     | the page's limits of bytes and time             |
| KvToObjectImp        | 92.4     | 89.5     | a get as `Object` of format 1                   |
| DbObject             | 89.3     | 86.4     | `toString()`, a few getters' refusals           |
| Db value classes     | 77 to 94 | 75 to 89 | `toString()`, the iterator's `remove()`         |
| Cache3               | 91.4     | 70.6     | the statistics; 019-46's paths are covered      |
| NodeCollection       | 97.3     | 78.9     | rare follows; 019-46's paths are covered        |
| Eviction             | 96.9     | 78.7     | 155 branches of rare schedules                  |
| Db                   | 95.1     | 81.7     | error paths of the start and the sync           |
| Keys                 | 94.8     | 78.6     | a length compare that cannot decide             |
| StringUtil           | 91.6     | 87.0     | formatting helpers                              |

The untested branches that matter, by kind (line numbers at
`1d1b6f3`):

* **Error paths and refusals**: `IndexManager.createInner`'s build that
  does not start (lines 261 to 264: the job FAILED and the exception
  thrown); a cleanup that meets data of format 1 (498); a build's key
  without an ikey (`IndexBuilderImp`, 454); a scan whose entry's key
  holds format 1 (`UseIndexBuilderImp`, 341 to 344) or has no ukey (414);
  a get as `Object` of format 1 (`KvToObjectImp`, 119; P42 shows that
  another test catches its fault); the null checks of `ConnectionImp`
  (56, 220, 245, 262, 339, 343), one line each.
* **Concurrency**: an interrupt in `RwTransaction`'s sleep between reruns
  (146 to 150) and in `BuildJob.join` (225 to 228). The races of the index
  manager are covered by hooks (`PubTesterIndexRaces`,
  `PubTesterIndexJobs`), but two of them only by timing (section 3.2).
* **Limits**: the primary scan's page limits of bytes and time
  (`UsePrimaryBuilderImp`, 362). Sizes near 2^31 are covered by sized
  values that are never written (`DbValue.sized`), not by real ones.
* **Restart**: covered (a start with markers, builds and format 1).
* **Dead code**: `RwEnvironmentImp.getInternal`'s `firstRead` branch
  (100 to 102) cannot run, as `indexEntries` fixes the read time first;
  `WTransaction`'s `Bug`.

The Pub API's methods that no test calls (`apimissed.py`): the
`toString()`s of `DbValue` and its classes, of `Duration` (with
`toStringSeconds` to `toStringDays`) and of `CryptoKey`; `Time.hashCode`
and `Duration.hashCode`; `DbArray`'s iterator's `remove()`; and
`Transaction.sync()` and `sync(SyncLevel)` of an `rw()`
(`RwTransaction.sync`), which a probe found to work (section 4.3).


## 3. Test quality (part 2)

### 3.1. Tests that cannot fail

`tests-work/scripts/noassert.py` lists the `@Nano` methods with no
assertion, refusal check or throw in their body: 61. All but these call a
helper that asserts:

* **No check at all; they fail only by an exception**:
  `Bug.dummyToIncreaseCoverage`, `SeedGenerator.testSanity`,
  `KeyNodeTester.testPrint` and `testSanity1`, `TopTester.test1`,
  `RecoverableStream.testReadMetaBlock3` ("Version 154 should work"),
  `StorageManagerTester.testMultipleClose`. Smoke tests, cheap; the first
  exists for coverage only.
* **An assertion that always holds**: none found by reading the Pub
  layer's tests of 2026.4. The mutation sample found three checks too
  weak to catch their fault (3.2).

Every class with `@Nano` methods is in a `Pack` that the groups run, but
two fixtures of `bergdb.nanotest` (`tests-work/scripts/Unregistered.java`).

### 3.2. The mutation sample

How: `tests-work/mut/mutants.py` lists each fault: the file, the exact
text replaced, and what it breaks. `run.py` applies one fault to a copy
of the sources (never the clone), compiles that one file over a copy of
the clone's classes, runs the unit and f groups, restores the file, and
records whether a test failed. For a fault in the Pub layer it runs only
the `bergdb.pub*` classes, about 15 s; for one in the Core, all of them,
about 70 s. A fault is caught if either group fails. The results are in
`results-1d1b6f3.txt` and `results.txt`.

The first 33, at `1d1b6f3`: 30 caught (P28 was dropped before it ran).

| Fault | What is broken | Caught by |
|---|---|---|
| P01 | writer: the directory's virtual key not in the read set      | PubTesterIndexRaces   |
| P02 | writer: the read time fixed after the index set is read      | PubTesterIndexRaces   |
| P03 | writer: the previous value's entry not deleted               | IndexHarness          |
| P04 | put: a user's DbObject not fully checked                     | DbObject              |
| P05 | put: a String with a lone surrogate not refused              | PubTester             |
| P06 | create: the virtual key not written                          | PubTesterIndexRaces   |
| P07 | delete: the virtual key not written                          | none; now 6e99055     |
| P08 | activate: a deleted index activated                          | PubTesterIndexJobs    |
| P09 | create: the maps changed in a second lock, after a hook      | PubTesterIndexJobs    |
| P10 | build step: the definition's key not in the read set         | none; now 6e99055     |
| P11 | build step: ends after a full step (`<=` for `<`)            | IndexJobsHarness      |
| P12 | build step: its first key inclusive                          | IndexJobsHarness      |
| P13 | index scan: a stale entry returned                           | none; now 6e99055     |
| P14 | index scan: `to()`'s inclusive and exclusive swapped         | IndexHarness          |
| P15 | backward index scan: a page's first key inclusive            | PubTesterIndex        |
| P16 | double level: a negative's sort long not negated             | IndexDefinitionTester |
| P17 | `succ`: trailing ff bytes kept                               | IndexHarness          |
| P18 | entry: a NaN double gets one                                 | IndexDefinitionTester |
| P19 | full check: a duplicate name accepted                        | DbObjectFormatTester  |
| P20 | full check: an array at level 17 accepted                    | DbObjectFormatTester  |
| P21 | full check: the UTF-8 of a surrogate accepted                | DbObjectFormatTester  |
| P22 | full check: an integer not in the fewest bytes accepted      | DbObjectFormatTester  |
| P23 | get: a long into an int not clamped                          | DataObjectsTester     |
| P24 | put: depth 17 accepted                                       | DataObjectsTester     |
| P25 | put: no cycle check                                          | DataObjectsTester     |
| P26 | cleanup: the marker deleted before the entries               | IndexJobsHarness      |
| P27 | w() rerun: the index ops of the run before kept              | PubTesterIndexRaces   |
| P29 | start: a marker of a live generation not refused             | PubTesterIndexJobs    |
| P30 | start: definitions of format 1 not refused                   | PubTester             |
| C01 | follow: the writer's node cached by the policy (019-46)      | NodeCollection        |
| C02 | `dropIfEmpty`: no look after DEAD (019-46)                   | NodeCollection        |
| C03 | start: the resident key nodes not listed as written (019-47) | Eviction              |
| C04 | `bkey2ikeyOrNull`: the byte '/' + 2 accepted                 | Keys                  |

The three faults the gate missed, and why:

* **P07**: `testRacesDelete` deletes the index in a writer's hook and
  then checks that the deleted generation has no entries. The writer
  committed an entry into it, but the cleanup, which starts at the
  deletion, removed it in time; the test does not check that the writer
  ran again. `testWriteRunsAgainAfterDeletion` checks the runs.
* **P10**: `testBuildDeletedInItsStep` deletes the index in a step, but
  checks only the status ("deleted", which the next step gives anyway),
  not the entries that the step committed into the deleted generation.
  `testBuildStepDeletedBeforeItsCommit` holds the cleanup and checks
  them.
* **P13**: no write leaves a stale entry, so no test needed the scan's
  check of an entry against its value (S2-F23).
  `testScanSkipsAStaleEntry` puts one through the Core.

With the three tests (`6e99055`) all three are caught.

The next 14, at `6e99055`: 13 caught, and one that no test can catch.

| Fault | What is broken | Caught by |
|---|---|---|
| P31 | the obsolete `.obj` suffix not an object key                  | Entries               |
| P32 | a high surrogate before any char taken as a pair              | DbObjectTester        |
| P33 | `integerSize`: 32,767 in 5 bytes (writer and check agree)     | DbObjectFormatTester  |
| P34 | `lengthSize`: a length of 127 in 3 bytes (both agree)         | DbObjectFormatTester  |
| P35 | `width`: fields of 255 bytes with 2-byte numbers (both agree) | DbObjectFormatTester  |
| P36 | definition read: a state not building or active accepted      | IndexDefinitionTester |
| P37 | definition read: another version accepted                     | IndexDefinitionTester |
| P38 | put: a null array element left out, not refused               | DataObjectsTester     |
| P39 | primary scan: a key whose name has a '/' listed               | Utf8ReadTester        |
| P40 | put: a String of limit + 1 bytes of UTF-8 accepted            | PubTester             |
| P41 | level: the byte 01 not escaped (writer and length agree)      | IndexDefinitionTester |
| P42 | get as `Object`: an object of format 1 not refused            | DbObjectFormatTester  |
| P43 | `usePrimary`: the class not checked first                     | none: equivalent      |
| P44 | primary scan: `startAt`'s inclusive inverted                  | PrimaryHarness        |

P43 removes the check in `ConnectionImp.usePrimary`, which the
constructor of `UsePrimaryBuilderImp` makes again: no test can tell. P33
to P35 and P41 change the writer and the check alike, so only the
conformance vectors of 020-07 (`object-vectors.txt`, run by
`DbObjectFormatTester`) and the reference codec of the tests can catch
them; they did.


## 4. The bug hunt (part 3)

How: probes against the public API and, where needed, in the package
(`bergdb.pubimp`, run on class directories, as the jars seal it), written
apart from the tests. Four sub-agents of the study took one area each,
in their own directory of `tests-work/`: format 2 and the conversion
(`fork-format/`); reads, scans and lookup times (`fork-scans/`); the
Javadoc's promises (`fork-promises/`); and a randomized stress of the
Pub layer on a file database with restarts, crashes, reclaim and
eviction (`fork-stress/`). The rest is in `probes/`.

### 4.1. Bugs fixed

**Bug 1: an rw() reads two states of a key** (`a857539`).

* Promise: `RwEnvironment.get`, "The action's reads read one state, the
  latest as of its first read" (018-04, Q1).
* Probe (`fork-scans/src/RwFirstRead.java`): `/x` holds the bytes ff 01.
  The action gets `/x` as a `String`, which throws `DataFormatException`
  (not UTF-8), and catches it. Another connection then puts 07 at `/x`.
  The action gets `/x` as `byte[]` and writes, and it commits in one run,
  having read ff 01 and then 07.
* Cause: `RwEnvironmentImp.get` fixed the read time (`readTime`,
  `firstRead`) after `getInTransaction`, which reads and then converts.
  A conversion that threw left the time unfixed, so the next read was at
  `Long.MAX_VALUE`, and the commit's STM check was against that later
  time, which hides the write between the two reads.
* Fix: read with `db.getOne`, fix the time, then convert.
* Test: `PubTester.testRwFirstReadThatThrowsFixesTheReadTime` (before:
  "runs, expected 2, got 1").

Why the fix is correct (concurrency code). The STM check of an rw()
refuses the commit if a key whose hash is in the read set was written
after the transaction's lookup time, `readTime`. The promise holds if
every read is at `readTime` and every key read has its hash in the set.

1. The hash is added before the read, as before, so every key read is in
   the set.
2. The first read is at `Long.MAX_VALUE`, and `getOne` sets
   `readData.actualLookupTime` to the time it read at. `readTime` is now
   set from it as soon as `getOne` returns, so every later read, and the
   check, are at the time of the first read.
3. If `getOne` throws, nothing was read and `firstRead` stays true; a
   hash without a read only adds a conflict, never hides one.
4. The conversion is a function of the bytes and the class, with no
   read, so making it after the time is fixed changes no value read.
5. The other reads were already in this order: `getInternal` runs only
   after `fixReadTime` (from `indexEntries`), and `getMany` (the build's
   step) sets the time from its own read.

So each run reads one state, the check is against it, and a run that read
a key written since then conflicts and runs again.

**Bug 2: an Error of a static initializer** (`ca13a43`).

* Promise: 020-09, section 5.2: a get throws `ObjectCreationException`, a
  `VirtualMachineError` as it is, "nothing else"; inside `rw()` the
  database goes on.
* Probe (`fork-format/src/probe/ProbeF6.java`): a Data Object class whose
  static initializer throws an `AssertionError`. Its first get threw the
  `AssertionError`, and in `rw()` the database failed (`DbFailedException`
  at the next put).
* Cause: the JVM throws an `Error` of an initializer as it is, not in an
  `ExceptionInInitializerError` (JLS 12.4.2), and `DataObjects.make`
  caught only that and `LinkageError`. The same `Error` from the
  constructor was already an `ObjectCreationException`.
* Fix: any `Error` from `newInstance()` but a `VirtualMachineError` is an
  `ObjectCreationException`.
* Test: `DataObjectsTester.testReviewOfStep8`, with `BadInitError` (first
  used by a get) and `BadInitErrorRw` (first used in `rw()`), three times
  each, and the database goes on.

**Bug 3: key replace deletes another key's index entries** (`72dfb65`).

* Promise: an index is a function of the data (020-10, section 3.3); with
  key replace, K is the replaced name (5.3).
* Probe (`probes/src/KeyReplaceLiteral.java`): an index on `/d/`; a put
  of `{v: 1}` at `/d/${transactionTime}` with key replace off (the key as
  written); then a put of `{v: 2}` at the same key with key replace on.
  The index then listed only the new key; the value at
  `/d/${transactionTime}` stayed, without its entry.
* Cause: `RwEnvironmentImp.indexEntries` read the previous value at the
  key as written and deleted its entries, though the put writes the key
  with the transaction's time, which is known only at the go point.
* Fix: a put with key replace has no previous value: its key is new, as
  its time is. The hash of the key as written leaves the read set with
  the read, which is right: the transaction does not depend on that key.
* Test: `PubTesterIndex.testKeyReplaceKeepsTheEntryOfTheKeyAsWritten`.
* What stays: a value stored earlier at the replaced name itself, written
  as literal digits that happen to be the later transaction's time, keeps
  the entry of its old value. The scan never returns that entry (its
  check against the value, S2-F23, is now tested), but it stays until the
  key is written again. Closing it would need a read of the replaced key
  after the go point, which the Core's key transformation does not offer;
  not worth it.

**Bug 4: a close() waits for the timer** (`ac3291e`; Core, storage
layer).

* Found by the per-test times of part 4:
  `PubTester.testTryWithResourcesCloses` took 15,007 ms in a unit run
  under load, and 26 ms alone. Its stream has a buffer time of 60 s, so a
  wait time (a quarter of it) of 15 s.
* Cause: `BufferedStream.close()` sets `flushAndClose` and wakes the
  consumer, under the stream's monitor, and waits until the buffer is
  written. When the wake came while the consumer flushed (not waiting),
  the consumer then took the timer's `wait(waitTime)`: only a waiting
  sync (005-48) or a buffer a quarter full skipped it. It flushed the
  bytes buffered after its flush a whole wait time later. At the default
  buffer time of 50 ms a close took up to 12.5 ms more; with a long
  buffer time, set through the Core's `DbBuilder.stream`, up to a quarter
  of it.
* Fix: the consumer does not take the timer's wait while a close waits
  for buffered bytes (`closeWaits()`, beside `syncWaits()`).
* Test: `BufferedStream.testCloseDuringAFlushDoesNotWaitForTheTimer`: the
  first flush is held in the stream's `append`, 100 more bytes are
  buffered, `close()` starts and wakes the busy consumer, the flush is
  released; the close must end within 5 s (before: it still waited after
  10 s, and took 15 s).
* How often: in three unit runs at `6e99055` on the loaded machine, one of
  the two tests `testTryWithResourcesCloses` (`DbTester`'s, `PubTester`'s;
  both with a buffer time of 60 s) took 15,007 to 15,009 ms in two runs,
  which made the unit group 41 to 57 s; in three runs at `ac3291e` both
  took 1 to 5 ms, and the group 32 to 47 s (`tests-work/times/`).
* Not run: level1.sh, as the machine's load was 23 on 10 cores; the gate
  passed, with the 33 tests of `BufferedStream`. night.sh runs the level
  scripts once the commit is on `main`.

Why the fix is correct (Core, concurrency code):

1. The consumer's checks and its waits are in one `synchronized (this)`
   block, as are `close()`'s write of `flushAndClose` with its
   `notifyAll()` and `stop()`'s write of `stop` with its own. A wake
   reaches the consumer only if it waits at that moment, so a condition
   set while it runs must be checked under the monitor before it waits.
   The idle wait checked `stop` and `flushAndClose`, the timer's wait
   checked a sync and `stop` (just before it), but not `flushAndClose`.
   `closeWaits()` checks it there, under the monitor, so a close's wake
   cannot be lost.
2. No busy loop: when `closeWaits()` is true, `shouldFlush()` is true too
   (`flushAndClose` and bytes buffered), so the consumer flushes. When
   nothing is buffered, `closeWaits()` is false and the consumer waits as
   before, and `close()`'s `stop()` wakes it (`stop` is checked under the
   monitor before the wait, so that wake is not lost either).
3. Nothing else changes: the flush is the same, and a wait is skipped
   only when a flush is due anyway; only `close()` sets `flushAndClose`.

### 4.2. Not fixed: for Frans

* **`Time` takes strings that break its format.** `Time.utc` and
  `Time.resolve` promise `BadFormatException` "If the time string does
  not follow the format above". They take "2013-13" (2014-01-01),
  "2013-02-30" (2013-03-02), "2013-00", "2013-01-00", "25:00" and
  "24:00" (the next day), "00:61", "00:00:60", "00:00:1e1" (10 s),
  "2013-+1-01", "-1d s" (1 s ago) and "-NaN s" (now). An absolute time
  outside BergDB's range ("2199-01-01", "1969-12-31") throws
  `IllegalArgumentException`, which is not listed. Probe:
  `fork-scans/src/TimeProbe.java`. Cause: `TimeResolver`'s lenient
  `GregorianCalendar`, `Integer.parseInt` and `Double.parseDouble`; the
  day's overflow is on purpose (`parseDate`: "Let's allowed "overflow"
  for now, like: 2013-02-50", 2013), the rest follows from it. Not
  2026.4's new code, but in the Pub API. Options:
  * (a) Parse by the ABNF of `Time.resolve`'s Javadoc: digits only, the
    calendar not lenient, each field in its range, a minus time's number
    as `[0-9]+(\.[0-9]+)?`, and an out-of-range time a
    `BadFormatException` too; about 40 lines and a table of refused
    strings.
  * (b) Say in the Javadoc that out-of-range fields roll over.
  * Recommended: (a). A time string that means nothing should not mean a
    time.
* **`Database.setRetainDuration(null)`** throws `NullPointerException`
  (`DatabaseImp.setRetainDuration`), where every other null argument of
  the API is an `IllegalArgumentException`. A fix is one check and the
  Javadoc's `@throws IllegalArgumentException` "If duration is null or
  shorter than one second". Either way it is a bad argument that fails
  only the call; left for Frans, as it changes a documented exception.
* **`useIndex(name, String.class)`** is accepted, but every value of an
  index is an object, so the first `next()` throws `DataFormatException`;
  `usePrimary(String.class)` leaves objects out instead. As the spec says
  ("as a get converts it"), but a trap. Options: refuse `String.class` in
  `useIndex`, or say it in its Javadoc.
* **Corners of the Javadoc** (no fault; a line each would do):
  * `useIndex` can throw `LookupTimeNotAvailableException` itself; not
    listed.
  * `Job.join()` returns BUILDING after the database failed, as after a
    stop ("stopped or failed").
  * `Duration.seconds(NaN)` is zero, `seconds(+infinity)` is `MAX`.
  * `WBuilder.execute()` twice runs the ops twice, as two transactions.
  * A `memory()` builder started again after its database closed starts
    over the closed stream and fails at the first sync (left out on
    purpose by 015-65).
  * `DbObject.toDbObject("abc")` gives `{p: "abc"}`; `toDbObject` of a
    `byte[]` is refused while `toJavaObject(byte[].class)` reads the
    field `array`; 020-09 says nothing of either.

### 4.3. Probed, and it held

* **Format 2** (`fork-format/`): 760,550 mutants of 200 random stored
  objects (a byte inserted, deleted, swapped or changed, a range
  doubled): the full check agreed with the tester's own reader every
  time, and every accepted one wrote back to the same bytes. `isFormat1`
  on 3,000,000 hostile inputs never threw. `find()` never read outside
  its extent. The Builder's limits held: 32,767 fields, 16 levels through
  objects, arrays and views, names of 1 to 255 bytes, lone surrogates
  refused. So did the getters' absent and clamped values, −0.0 and the
  one NaN, and the copies in and out.
* **The conversion**: 5,060,000 gets of random stored objects into 23
  class shapes threw nothing; 2,160,000 get-put-get round trips gave the
  same bytes; depth 16 and 17 through Data Objects, and arrays of 15 and
  16 dimensions; `Connection.get` of 10 classes over 9 kinds of value,
  also in `rw()`.
* **Scans** (`fork-scans/`): 3,840 index and primary scans against a
  reference, over every grammar shape, backward, at the latest and an
  earlier time, with the edge values (Long's ends, ±0.0, NaN, ±infinity,
  subnormals, "", U+0000, U+FFFF against supplementary characters, bytes
  00, 01 and ff, prefixes ending in ff), odd keys and subdirectories; 720
  more over 600 keys across pages (38,514 rows): no difference. Also
  every refusal of the grammar; the 4,096-byte level limit; 8 levels;
  deleted and re-created indexes at past and present times;
  `freezeLookupTime`; and a scan's expiry behind reclaim's cut, forward
  and backward, on its first page or later, as promised, though only the
  primary scan's test checks it. 60 s of 3 writers, 3 readers and an
  index deleted and created 334 times: 51,150 scans, no difference.
  Eviction with a 4 MB cache and 20,000 objects, before and after a
  restart.
* **Jobs and restarts** (`probes/src/RestartJobs.java`, 20,000 objects
  in a file database): a build stopped by `close()` and resumed by the
  start, with writes meanwhile; a deletion whose cleanup was cut by a
  close; the name created again at once with another type; three rounds
  of delete, create and close. Every index equalled its function, and in
  the end `/#i/` held one generation's entries and one definition, no
  marker (`probes/src/bergdb/pubimp/RawIndexKeys.java`). A build over a
  directory whose `.txt` key 1 to 4 threads write in a tight loop (the
  step reads it, and those writers take no lock) ended in 150 to 250 ms:
  no livelock (`probes/src/BuildLivelock.java`).
* **Stress** (`fork-stress/src/Stress.java`): a file database with a
  4 MB cache, values of 0 to 51 KB, retain 1 s; one writer of objects,
  `String` and `byte[]` puts over objects, deletes, multi-op `w()`, rw
  reads, key replace and edge values; two threads of rw() transfers over
  50 accounts in an indexed directory (their sum constant); one thread
  deleting and creating three indexes of 1 to 3 levels. Six seeds of 120
  to 150 s with 13 to 16 restarts each, some with builds and cleanups
  running at the close: 318,387 writes, 1,379,169 transfers, 479 index
  creations, 162 to 164 checks a run of every index against the primary
  scan at a frozen time, and 22 to 32 cuts a run. Three seeds of 12 to 15
  kills (SIGKILL) of a child JVM, 103,411 operations: each start was an
  exact prefix of the operations, between the last synced and the last
  tried. No difference, no lost or doubled write, and no thread left
  after a close.
* **The Javadoc's promises** (`fork-promises/`, eight probes): `close()`
  with a build and a cleanup running (8 ms, no BergDB thread left, both
  resumed at the next start); every call after `stop()` and `close()`;
  every refusal of `IndexBuilder` (names, directories, types, 9 levels,
  field names, nested depth 17, a second `start()`); `deleteIndex` and
  `indexJob` of unknown names; a build FAILED over format 1, again after a
  restart, and ACTIVE after the key's deletion and a restart; the
  `DatabaseBuilder`'s refusals; outputs, and an `rw()` whose action
  throws; `sync()` of `w()` and `rw()`; the settings across a restart;
  the failure model after an `Error` in `rw()`, across every call; Pub
  calls with the interrupt flag set, on a file database.

Promises that no test of the gate checks, each of which held in a probe:

* the index scan's expiry behind reclaim's cut;
* `Transaction.sync()` of an `rw()`;
* no index build or cleanup thread left after `close()` (the gate's
  `StoppedCheck` looks for the storage and eviction threads only);
* Pub calls with the interrupt flag set, but `start()`;
* the failure model across the whole API after an `Error` in `rw()`;
* `transactionInfo().kvs()` without the index entries of an object put;
* `Job.join(0)` as `join()`;
* the Builder's "a field added with an existing name replaces it";
* `toDbObject(DbObject)` returns its argument; `DbByteArray` copies in
  and out.


## 5. Removal candidates (part 4)

Proposals only; nothing removed. The per-test times (`-v`) of three runs
of the f group and six of the unit group, on a loaded machine
(`tests-work/times/`): the f group 69 to 89 s in all, the unit group 32
to 57 s (15 s of it bug 4's, section 4.1).

* **Slow f-tests that add little.** Five classes of `bergdb.test` take 33
  to 37 s of the f group's 69 to 89 s, and cover 11 lines of production
  code that no other test covers (`KeyFactory`'s random keys and a
  `DummyStream` read; `tests-work/cov/run-slow.sh`). The times of the
  first run:

  | Class | Tests | Time, s | What it does |
  |---|---|---|---|
  | BigDb             | 4 | 11.4 | 100 MB in 10 to 10,000 values, a restart, a checksum |
  | Concurrency2      | 1 | 10.1 | a writer and a reader of one key for 10 s            |
  | BigDbWithDeletes  | 3 | 8.0  | as BigDb, with deletes                               |
  | CreateIndexTester | 2 | 4.9  | a build of 100,000 objects through a restart         |
  | BryanIssue        | 1 | 2.5  | the bug report of 2015-11 (level2.sh has it too)     |

  Proposed: BigDb and BigDbWithDeletes to the groups "perf" and "night"
  only (their restarts and checksums are level1.sh's RestartStress and
  RestartInvariance; their memory reports are for `perf`); Concurrency2 at
  2 s in f and 10 s in night; CreateIndexTester's restart at 10,000
  objects with the build held by a hook, as `IndexJobsHarness` does (H3),
  or dropped for it; BryanIssue kept. About 30 s off the f group, which
  is the gate's longer half (unit 37 s, f 62 s on a quiet machine): the
  gate from about 2 minutes to about 1.5.
* **Duplicates**: `PubTester.testDirManyObjects1` and `2` and
  `PubTesterPrimary.testManyObjects1` and `2` run the same helper,
  `manyObjects(233)` and `(200)`, one on `connection()`, the other on
  `newConnection()`; keep the `PubTesterPrimary` pair.
* **Tests that only run code**: `Bug.dummyToIncreaseCoverage` (for
  coverage only), `SeedGenerator.testSanity`, `KeyNodeTester.testSanity1`
  and `testPrint` (`testPrintKeysWithoutIkey` covers it with checks),
  `TopTester.test1` (its `createTestData()` runs and is checked in
  `testBeforeFirst`). Cheap; removing them saves lines, not time.
* **Tests of code that is gone**: none. Every test compiles against
  today's code, and every class with `@Nano` methods is run by a group.


## 6. Recommendations

1. Take `a857539`, `ca13a43`, `72dfb65`, `6e99055` and `ac3291e` into
   `main`, and add the four bugs to 020-11 (not done here, as 020-11
   changes on `main`).
2. Decide `Time`'s parsing (4.2, recommended (a)), `setRetainDuration`'s
   null, and `useIndex(String.class)`.
3. Add the threads `IndexBuild-*` and `IndexCleanup-*` to the gate's
   `StoppedCheck`: a test that leaves a build running leaves a thread,
   and today nothing finds it.
4. In a race test, check the run (its reruns, a step's commit) and not
   only the final state where a cleanup can repair it, as the three new
   tests do; the hooks make it deterministic.
5. One test each for an rw()'s `sync()` and for the index scan's expiry
   behind the cut; both were probes here (4.3).
6. The slow f-tests of section 5, if the gate's time matters.


## 7. Open

* Frans's decisions of section 4.2: `Time`'s parsing, the null of
  `setRetainDuration`, `useIndex(String.class)`, the Javadoc's corners.
* The proposals of section 5, if Frans wants the gate faster.
* Not done: coverage of level1.sh's other steps (the Core's, checked by
  the level scripts and the Lean model), and values near 2^31 bytes (a
  shared machine; the size checks are tested with sized values that are
  never written).
* 020-11 does not list the four bugs yet (recommendation 1).


Log
===

2026-11-09. Created at Frans's request (08:41), by the coordinator's
agent, in the clone `clone-tests`: the coverage (08:45); four sub-agents,
on format 2 and the conversion, reads and scans, the Javadoc's promises,
and a stress of the Pub layer (08:50 to 10:05); the mutation sample
(09:15 to 10:10); bugs 1 to 3 fixed, gated and committed (09:20 to
09:50); the tests for the three faults the gate missed (10:00); bug 4,
found in the per-test times (10:05).
