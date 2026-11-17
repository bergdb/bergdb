# 022-05 Java's Core tests in C

Created 2026-11-09 by Frans Lundberg. Status: done.

Frans, 2026-11-09, 17:09: "Are all units test successful? Have all of them
been converted to C? Those for Core, that is." And at 17:15: "If there are
valuable test to be written, write them, run them. If they fail, fix the
errors."

Every test method of Java's Core layer at `main` `e875a34` (the packages
`bergdb.core`, `bergdb.stream`, `bergdb.dag`, `bergdb.storage`,
`bergdb.common`, and the methods that nanotest runs without the name
`test*`) was read against C's tests and classed: P, C already has a test or
a harness that checks what it checks; W, written now in C; N, not for C (C
has no counterpart: threads, JMX, the storage thread, replication, Java's
test tools, the stream's Java API); L, left. Five workers did it in clones
of 022's integration repository, each landing gated on the 2026.4 branch
between 17:45 and 18:45 (shared brief: "Brief: Java's Core tests ported to
C", kept beside the clones). Each part's file has a table per Java class,
one row per method, with the C test or the reason.


# 1. The counts

| Part, in `05-java-tests-in-c/`  | Methods | P   | W   | N   | L |
|---|---|---|---|---|---|
| db-tester.md                    | 166 | 52  | 66  | 48  | 0 |
| restart-getmany-trans.md        | 185 | 131 | 38  | 16  | 0 |
| eviction-reclaim-harnesses.md   | 182 | 82  | 45  | 53  | 2 |
| dag-common.md                   | 193 | 126 | 2   | 65  | 0 |
| stream-storage.md               | 165 | 59  | 35  | 68  | 3 |
| In all                          | 891 | 450 | 186 | 250 | 5 |

The parts: [db-tester](05-java-tests-in-c/db-tester.md) (`DbTester`,
`DbTesterFailure`, `DbTesterJavadoc`, `DbTesterLongKeys`, `DbUtil`),
[restart-getmany-trans](05-java-tests-in-c/restart-getmany-trans.md)
(`DbTesterRestart`, `DbTesterGetMany`, `DbTesterStream`, the record, node
and clock classes), [eviction-reclaim-harnesses](05-java-tests-in-c/eviction-reclaim-harnesses.md)
(`Eviction`, `Reclaim`, `NodeCollection` and the fault harnesses 6.1 to
6.5), [dag-common](05-java-tests-in-c/dag-common.md) (`bergdb.dag`,
`bergdb.common`), [stream-storage](05-java-tests-in-c/stream-storage.md)
(`bergdb.stream`, `bergdb.storage`).

Of the 641 methods with a counterpart in C (P, W and L), 450 were covered
before tonight and 186 are covered now; 5 are left. C's unit tests grew
from 411 to 516 entries and its functional tests from 37 to 44 (C's gate,
`C BEFORE COMMIT OK`, at each landing).


# 2. What the new tests found

* **C, fixed:** a failed stream let a later `bergdb_sync` and `bergdb_close`
  return OK (`stream_flush` returned for an empty buffer before it checked
  the failure): a retried `F_FULLFSYNC` could report lost bytes as durable.
  Found by two workers on their own (stream-storage, eviction-reclaim);
  fixed in `stream.c`, with tests that fail without the fix.
* **C, fixed:** a database in memory never freed what reclaim cut; its
  memory stream now drops the cut 1 MB blocks, as Java's `MemoryStream`
  (stream-storage). A change of 012-11's memory stream: for Frans to
  review.
* **C, a departure kept (decision (a) by default; Frans may change it):**
  `bergdb_close` returns `BERGDB_IO` after a call has already reported the
  storage failure, where Java's `close()` returns normally since 019-09
  (db-tester, section 3.1; `bergdb.h` and `c/readme.md` section 11 say so).
* **Java:** no fault found. Dead code noted: `DbStarter.PrevMap`,
  `StoredTrans.getValueNode`.
* Every other new test passed on C as it was; negative controls (C broken
  on purpose in scratch copies) show the tests catch what they aim at.


# 3. What is left

* `MemoryStream.testCutPast2GB` (passes by hand in 0.5 s; holds 128 MB:
  a stress or functional home).
* `StorageContractTester.testWorkloadsLong` (more seeds: a stress step).
* `FileStreamPowerLossTester.testUnorderedUnforcedDeletionsAreDetected` (a
  `power.c` mode with deletes durable out of order, a few dozen lines).
* `CorruptStreamTester.testFull` (the corrupt set's full mode as a night
  step).
* `FileStream.testConstants` (low value).

The gate grew by about a minute under load: the new restart and
recovery tests wait on real forces (`F_FULLFSYNC`) in the test build where
they open directories many times.
