021-29. Fix: unit tests that wait with no timeout
=================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-13 by Frans Lundberg.

What: two unit tests wait with no limit (024-35, finding 9; 006-17,
section 6.3, point 10; 024-01, TT4, "hangs first"):

* `java/src/bergdb/pubimp/PubTesterOutput.java`, lines 190, 198 and 201:
  `keyChanged.waitForEvent()`, `readDone.waitForEvent()`, `thread.join()`;
* `java/src/bergdb/pubimp/PubTester.java`, lines 788, 804 and 808:
  `modifiedKey1.waitForEvent()`, `getDone.waitForEvent()`, `thread.join()`.

Other test threads are joined with no limit too, such as
`PubTesterOutput.java:246`, `PubTester.java:1652` and `PubTester.java:4245`
(line numbers of 2026-11-13, main `7f408589`).

Why: a fault in the code under test then hangs the test, and with it
before-commit.sh or a night step, instead of failing it with a message;
the night loses the step's time and the rest of its steps.

Frans: none.

Done when: every unbounded `waitForEvent()` and `join()` of a test
thread in the unit tests and f-tests has a limit (`waitForEvent(long)`
exists; `join(ms)` followed by an assertion that the thread has ended),
generous enough for a loaded machine (021-28), with a failure message
that names the wait; `java/before-commit.sh` prints `BEFORE COMMIT OK`.
An index build's `start().join()` is not a test thread's join and is
left as it is, unless it can hang (then a line here says so).

First step: grep `java/src` and `java/src-dev` test classes for
`waitForEvent()` and `.join()` with no argument, and list them here.


Log
---

2026-11-13. Registered by coord-1113 (Frans, 06:38: "Yes, register them"),
from coord-1112's handover (006-23, section 6, point 3) and 024-35, finding 9.

2026-11-13. Done by coord-1113's agent "waits": commit "021-29" in
`/Users/f/fl/bench/2026-11-13/waits/clone`, branch `021-29-test-waits`,
on main's 8815b6c2, to land. Tests only; no product code changed.

* The grep (`waitForEvent()` and `.join()` with no argument in `java/src`
  and `java/src-dev`) found 37 waits of a test on a thread or an event.
  Each now has a limit of 60 s (021-28: generous for a loaded machine),
  then an assertion whose message names the wait ("the rw thread did not
  end within 60 s"): `t.join(60_000)` and `Assert.assertFalse(msg,
  t.isAlive())`; `e.waitForEvent(60_000)` and `Assert.assertTrue(msg,
  e.didItHappen())`. `StorageContractTester` has no `Assert` import and
  throws `AssertionError`; `IndexHarness` uses its `check()`.
* The waits, by line of 8815b6c2:
  - `pubimp/PubTesterOutput.java` 190, 198, 201 (the entry's), 246;
  - `pubimp/PubTester.java` 788, 804, 808 (the entry's), 1652, 4245;
  - `pubimp/PubTesterJavadoc.java` 957; `pubimp/PubTesterThreads.java`
    507; `pubimp/PubTesterIndexJobs.java` 965;
  - `pubimp/IndexHarness.java` 1507, with 600 s: a thread runs one
    generated transaction, also in `harness-soak.sh`'s runs of chosen
    sizes, where 60 s could be too short; it still fails, not hangs;
  - `core/DbTesterMerge.java` 350, `core/EvictionAccountingTester.java`
    232 and `core/EvictionReaderTester.java` 566 (a one-line `for` of
    reader joins, now a block); `core/DbUtil.java` 470;
    `core/DbTesterDelete.java` 579; `core/DbTesterLongKeys.java` 222;
    `core/ReclaimReaderTester.java` 462; `core/ReclaimMaintainTester.java`
    200; `pub/Time.java` 541;
  - `storage/StorageManagerTester.java` 109;
    `storage/StorageContractTester.java` 129, 274;
    `storage/BufferedStream.java` 957 (a test's join of the stream's
    consumer thread after `stop()`), 1077, 1153, 1156, 1475;
  - `stream/StreamContractTester.java` 134, and 128, a latch's
    `entered.await()` in the test's own thread, now `await(60, SECONDS)`
    with an assertion (not a `join()`, but the same hang);
    `stream/FileStream.java` 3018, 3019, 3352, 3419;
  - `common/EventToWaitFor.java` 90 (its own `test2`);
  - `src-dev/bergdb/dev/NanotestForBergDB.java` 263 (its
    `testIndexThreadsChecked`).
* Left as they are:
  - every index build's `start().join()` and `Job.join()`
    (`job.join()`, `indexJob(name).join()`, `create(database).join()`):
    a build's job, not a test thread, as the entry says; none was seen
    to hang;
  - product code: `Eviction.endThread` (713), `Jmx`'s `stop()` (325),
    `BufferedStream.close()` (810);
  - `src-dev/bergdb/test/` (`Get`, `PerfGetMany`, `Concurrency2`,
    `GetThreaded`, `manual/TransThroughput`, ...): performance and
    manual programs, not unit tests or f-tests;
  - latch waits inside a worker thread (`ReclaimReaderTester` 213,
    `FileStream` 3341, `BufferedStream` 1944, `NanotestForBergDB` 246):
    the joins of those threads now bound them.
* A caution: `EventToWaitFor.waitForEvent(long)` waits once; a spurious
  wakeup returns early, and the assertion would then fail a test that
  would have passed. Rare in practice; a loop to a deadline in
  `EventToWaitFor` (in `bergdb.common`, used by tests only besides its
  own) would remove it, left out here as the brief allowed tests only.

Gate, in one slot (2026-11-13, 07:32 to 07:33), on this commit's Java:
`BEFORE COMMIT OK (64 s)` (unit 1700, f 89, demos 14); log
`/Users/f/fl/bench/2026-11-13/waits/gate.txt`.
