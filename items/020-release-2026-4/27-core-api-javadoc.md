# 020-27 The Core API's Javadoc checked against behaviour

Created 2026-11-09 by Frans Lundberg. Status: open.

The Javadoc of the Core API that release 2026.4 offers users, `bergdb.core.Db` and the types
of its signatures (`bergdb.pub`'s "The API and its jar"), checked against what the code does,
promise by promise, with tests, as 020-19 and 020-25 checked the Pub API's; with today's
section "Keys and the layers above" (020-22).


## 1. The request

coord-1109, 2026-11-09, 13:23 (Frans away): do for the Core API what 020-19 and 020-25 did for
the Pub API: `Db` and `DbBuilder`, and the public classes that their public methods take or
return (transactions, the reads, the start's results, the exceptions), with 020-22's "Keys
and the layers above". For each promise a test that shows it, existing or new, fast, in the
Core's tester style, or a mismatch: a code fault gets a fix with a failing test first (a Core
fix that is not small: the test, and a report), a Javadoc fault a Javadoc fix, an unclear one
a question for Frans with a recommendation; no change of meaning for 2026.4 (the stable
baseline). Gate under the lock, and `java/stress/level1.sh` if Core code changes; commits by
topic. Stop at 18:30 or when done.


## 2. The method

* The work is in the clone `/Users/f/fl/bench/2026-11-09/clone-j27`, from `main` at `82edabf`,
  rebased onto `cf287ad` (020-25's commits and 021-13's change of `Db.getTrans`). 020-19,
  020-22 and 020-25 were read, as the brief asked; the other hunts' findings were not.
* Each Javadoc text of the classes below was read sentence by sentence, with the code behind
  it, and each promise written down (section 3) with the test that shows it: an existing
  tester's, found by name and doc comment, or a new one.
* Small programs in the scratchpad probed the promises and the corners that no Javadoc gives:
  calls before `start()` and after `stop()`, null and out-of-range arguments, the stop
  conditions at their edges, a Db's threads, and writes through the Core into a database of
  the Pub API (the online `Db`, as the testers use it, and keys of every kind).
* The new tests are in two new testers, each listed in its `Pack`: `bergdb.core.DbTesterJavadoc`
  (the Core alone; `bergdb.core` may not depend on the Pub API) and
  `bergdb.pubimp.PubTesterCoreKeys` (the Keys section, which needs the Pub API). One test per
  promise or small group, each named after its class and promise in its doc comment. Fast:
  the two run in about 0.5 s together.

The scope. The definition, "`Db` with the types of its signatures", reaches far: `DbBuilder`
takes `AppendOnlyStream` and `Clock`, `Db.internal()` returns `Db.Internal`, which returns the
`Dag`, `NodeStream` and `Cache3`. Checked promise by promise: `Db`, `DbBuilder`, `Trans` and
`Trans.Builder`, `GetData`'s outputs, `GetMany` with its stop conditions and `Kvt`,
`StartInfo`, `StoredTrans` as `getTrans()` returns it, and the exceptions that their Javadoc
names. Read, not checked one by one: the members that their own Javadoc marks internal or for
tests (section 3.9), and the stream classes (`FileStream`, `MemoryStream`), `DatabaseId` and
`Eviction.Schedule`, which `DbBuilder` takes. Question Q1 (section 5) is about that extent.


## 3. The promises and their tests

Tests are named by class and method: `JC` is `DbTesterJavadoc` (new), `CK` `PubTesterCoreKeys`
(new), `DT` `DbTester`, `DF` `DbTesterFailure`, `DR` `DbTesterRestart`, `DS` `DbTesterStream`,
`GM` `DbTesterGetMany`, `CT` `CapacityTester`, `IT` `InterruptTester`, `TR` `Trans`'s own
tests, `RR` `ReclaimReaderTester`, `PT` `PubTester`, `PI` `PubTesterIndex`, `PIJ`
`PubTesterIndexJobs`, `PP` `PubTesterPrimary`, `IDT` `IndexDefinitionTester`, `U8`
`Utf8ReadTester`.

### 3.1. Db's class Javadoc (5 sections, 34 promises)

* The Core Data API: `getOne()`, `getMany()`, `getTrans()` and `execute()` read and write all
  data. Descriptive; the tests of 3.3 and 3.4.
* Keys and the layers above (020-22):
  * The Core takes any key: an empty key, `{0}`, `{ff}`, a key of 3,000 bytes (a probe), keys
    of every kind (CK, `PT.testTransactionInfoLeavesOutKeysWithNoUkey`).
  * Your keys, every key that does not start with 01 66, 01 2f or 01 25: BergDB never reads
    them for their meaning or changes them (K2). CK.testYourKeysNeverWritten (six such keys
    keep their value and their transaction through the Pub API's writes, an index's build
    and deletion; `usePrimary()` lists none).
  * The Pub API's keys: a write is allowed, the Pub API's reads check what they read.
    `U8.testStringValueNotWellFormed`, `U8.testScanPastKeysWithoutIkey`, a probe (bytes that
    are no object at an object key: a `byte[]` for `Object.class`).
  * A Core put at an object key of an indexed directory can leave the value out of the
    index's scans until the key is written again through the Pub API, a put of its own bytes
    too, or the index is made again; a put that keeps the indexed fields changes nothing (K1).
    CK.testCorePutAtAnIndexedObjectKey.
  * A delete there leaves an entry that scans skip. CK.testCoreDeleteAtAnIndexedObjectKey.
  * The other keys of `/d` and `/-` are reserved: left out by `transactionInfo()`, the scans
    and builds. `PT.testTransactionInfoLeavesOutKeysWithNoUkey`,
    `PI.testScanLeavesOutAKeyWithNoUkey`, `PP.testScanLeavesOutTheEmptyName`.
  * BergDB's keys: data that does not parse refused with `InternalDataException` at a start
    or at the read that meets it. `PIJ.testStartRefusesBadIndexData`,
    `PI.testCorruptEntryKey`, `IDT`'s `read()` test, `DR.testMalformedSettingsRefusedAtStart`,
    a probe (a malformed definition: `useIndex()` throws it).
  * A scan never returns a value that does not match its query, whatever was written through
    Db. CK.testCorePutAtAnIndexedObjectKey (every scan checks each value against its query).
  * Write while no Database runs; the online Db's writes of BergDB's keys are seen only in
    part until the next start (K3). CK.testOnlineWriteOfADefinitionSeenInPart.
* Errors: a failure on an I/O error, corrupt data, an unexpected exception of the stream, an
  Error (in a StopCondition too, or on a Db thread), or any exception after the go point; the
  call throws it (an Error as it is), later reads and transactions `DbFailedException` with
  the first failure as the cause, nothing more appended; synced transactions safe; `stop()`,
  `close()` and `sync()` still work; the next start recovers; everything else fails only the
  call. `DF.testErrorIsThrownAsItIs`, `testReadErrorInGetOne`, `testCorruptNodeInGetMany`,
  `testErrorInStopConditionFailsTheDatabase`, `testUncheckedReadFailsTheDatabase`,
  `testAppendErrorInStore`, `testBackgroundWriteFailureFailsReads`, `testSyncFails`,
  `testCloseOfFailedDatabaseReturnsNormally`, `testRefusedBeforeTheGoPoint`,
  `DT.testCrash1` to `testCrash8InCreation`.
* Db shutdown: `stop()` returns at once, `close()` waits; nothing else releases a Db's
  resources; a Db not stopped still writes what it committed, within the buffer time (50 ms
  by default, `StorageManager.DEFAULT_BUFFER_TIME`); its threads are daemon threads.
  JC.testOwnThreadsAreDaemons (the storage's writer and the evictor; commits written without
  `stop()` or `sync()`), `DT.testStopWritesAll`, `DT.testCloseWaits`.
* AutoCloseable: a try-with-resources block closes with `close()`, also when it throws.
  `DT.testTryWithResourcesCloses`, `DT.testCloseFailureSuppressedByBlockFailure`.

### 3.2. Db's start, stop and close (3 methods, 24 promises)

* `start()`, `start(params)`: once per Db; a second call, also after `stop()`, throws
  `IllegalDbStateException` and closes nothing (J1); `StreamFormatException` for another
  maximum node size or none; `DatabaseNotCreatedException` for an incomplete creation,
  nothing written; a start that throws closes the storage, later calls refused as after
  `stop()`. JC.testSecondStartRefused, `DR.testOtherNodeSizeRefused`,
  `DR.testNoNodeSizeRefused`, `DT.testCrash8InCreation`, `DF.testFailedStartClosesStorage`.
* `stop()`: no read or transaction after it (`DbStoppingException`); a running transaction
  completes and is written; a thread of its own closes, not a daemon; if it cannot be made,
  the calling thread closes and throws; several calls, any thread; a FileStream on the
  directory refused until `close()` returns. JC.testCallsBeforeStartAndAfterStop,
  `DT.testStopWithRunningTransaction`, `DT.testStopWritesAll`,
  `DT.testStopMultipleStopCalls`, `DF.testStopWhoseCloserCannotStart`,
  `DF.testCloseWaitsForTheFailedStreamsClose`, `PT.testStartWhileStoppingRefused`,
  `PT.testStopThenReturnFromMain`.
* `close()`: waits until closed, also after `stop()` or another `close()`; within a
  transaction it closes at once; a failed final flush or close, and an unreported earlier
  failure of the storage, throw `StreamIoException`; a failed database's close returns
  normally. `DT.testCloseWaits`, `DT.testCloseAfterStopAndTwice`,
  `DT.testCloseReportsFinalFlushFailure`, `DS.testFirstCloseFailureIsReported`,
  `DF.testCloseReportsBackgroundWriteFailure`,
  `DF.testCloseAfterStopReportsBackgroundWriteFailure`,
  `DF.testCloseOfFailedDatabaseReturnsNormally`.

### 3.3. Db's reads (5 methods and GetData, 30 promises)

* `getOne()`: null for a key without a value at the lookup time (J4); the array returned is
  the database's own while in memory, the array that was put; `Long.MAX_VALUE` the latest
  state; `GetData.tpos` the position of the writing transaction; `IllegalDbStateException`
  before `start()`, `DbStoppingException` after `stop()`; `DbFailedException` for a failed
  read, an Error as it is; `LookupTimeNotAvailableException` before the first available
  lookup time, also when a cut overtakes the read. JC.testGetOneAndTheTransaction,
  JC.testCallsBeforeStartAndAfterStop, `DF.testReadErrorInGetOne`,
  `DF.testCorruptNodeInGetOne`, `DF.testReadDuringStop`, `DF.testGetDuringClose`,
  `RR.testLatestReaderExpiresWhenCutOvertakesIt`, `DT.testStopGetException1`.
* `getMany()`: as `getOne()` for its states, failures and lookup times (J2); an Error of the
  StopCondition fails the database. JC.testCallsBeforeStartAndAfterStop, GM (31 tests),
  `DF.testReadErrorInGetMany`, `DF.testCorruptNodeInGetMany`,
  `DF.testErrorInStopConditionFailsTheDatabase`.
* `getTrans()`: the transaction at a get's position (`tt`, `tpos`, `lastPos`, its value
  nodes); `IllegalArgumentException` for a position that cannot start a transaction, nothing
  read; `DbFailedException` for a failed read, a checksum or a malformed record;
  `LookupTimeNotAvailableException` after reclaim removed it; waits for the writer for a
  record not yet appended (021-13). JC.testGetOneAndTheTransaction,
  `DT.testGetTransOfEveryValue`, `DT.testGetTransRefusesBadPositions`, `DF.testGetTrans`,
  `DF.testGetTransBelowTheCut`, `DF.testGetTransChecksum`, `DF.testGetTransMalformed`,
  `DF.testGetTransBadValueSize`, `DF.testGetTransOfARecordBeingAppended`.
* `newGetData()`, `newGetMany()`: refused before `start()` as a read is.
  JC.testCallsBeforeStartAndAfterStop.
* `printDag()`: refused when not active. JC.testCallsBeforeStartAndAfterStop.

### 3.4. Db's transactions, Trans and Trans.Builder (17 methods, 34 promises)

* `execute(Trans)`: nothing changes before the go point, a refusal leaves the database as it
  was; after it nothing is undone and an exception fails the database; `RerunException` for
  a key read and changed after the read time, and for a read time outside the STM's
  coverage, also before the last recovered commit; `DbException` for a transaction too large,
  dirty index nodes beyond one record, a clock out of range or in the last 1,024 times, the
  top node ordinals used; `IllegalDbStateException` before `start()` and after `stop()`;
  `InternalDataException` for corrupt internal data. `DF.testRefusedBeforeTheGoPoint`,
  `DF.testReadErrorInWarmup`, `DF.testValueTransformationThrows`, `DT.testRerun`,
  `DR.testStmAfterRestart`, `DT.testTransactionTooLarge`, `DT.testTooManyDirtyNodes`,
  `DT.testClockOutOfRange`, `DR.testEndOfOrdinals`, `DT.testStopExecute`,
  JC.testCallsBeforeStartAndAfterStop, `DR.testMalformedSettingsRefusedAtStart`.
* `execute(Trans.Builder)`: as `execute(b.build())`. Used by most testers.
* Trans: a Trans may be executed again; `tt`, `tpos`, `lastPos` and `nextPos` after
  `execute()`. `TR.testTransReuse`, JC.testGetOneAndTheTransaction.
* Trans.Builder: a value's array not copied; one operation a key, the last put, a delete only
  without a put, whatever their order; a null value refused, also with a String key; a lone
  surrogate refused in a String key or value; a negative lookup time and a negative hash
  refused. JC.testGetOneAndTheTransaction, JC.testTransBuilderOneOperationPerKey,
  JC.testBuilderRefusals, `TR.testLoneSurrogateRefused`, `TR.testNegativeHash`.
* RerunException: `getKeyHash()`. `RerunException.test1`.

### 3.5. Db's sync, settings and counters (19 methods, 46 promises)

* `sync(SyncLevel)`, `sync(pos, SyncLevel)`: durable through the commit byte; `NONE` returns
  at once; a null level refused (J3); `DbFailedException` when the storage failed;
  `StreamIoException` when interrupted. `DT.testSyncWaitsForTheCommitByte`,
  `DS.testSyncAfterOneCommitWaitsForOneForce`, `DF.testSyncFails`, `DF.testInterruptedSync`,
  `IT.testSync`, JC.testCallsBeforeStartAndAfterStop.
* `setStartupDistance()`: clamped to 400,000 to 10^9, set at once, kept in the stream by a
  commit of 200 kB, nothing written for the setting in force, a negative value refused, as a
  transaction refused when not active and then unchanged. `DT.testSetStartupDistanceClamped`,
  `DT.testSetStartupDistanceInForceOrRefused`, `DT.testDecreaseOfStartupDistance`,
  `DR.dbShouldRememberStartupDistance1`, JC.testCallsBeforeStartAndAfterStop.
* `getCacheSizeIndicator()`, `setCacheSizeIndicator()`: the budget, in force at return, for
  the run only; after `stop()` only the value set; below 1 refused (J3); an Error fails the
  database. `CT` (its budget tests), `DF.testErrorInSyncOrCacheSizeFailsTheDatabase`,
  JC.testCallsBeforeStartAndAfterStop.
* `getRetainDuration()`, `setRetainDuration()`, `setReclaimInternalFraction()`,
  `getInternalFraction()`: forever and 0.25 by default; kept in the stream, a restart keeps
  them; nothing written for the value in force; refused when not active, below a second, out
  of 0.001 to 0.90 or NaN, at the end of the ordinals, unchanged when refused; the fraction in
  units of 2^-16. `DR.testStreamWithoutSettingsHasDefaults`,
  `DR.testReclaimSettingsKeptOverRestarts`, `DR.testReclaimSettingInForceWritesNothing`,
  `DR.testRefusedReclaimSettingChangesNothing`, `DR.testReclaimSettingAtEndOfOrdinals`,
  `DT.testReclaimInternalFractionValidation`, JC.testCallsBeforeStartAndAfterStop.
* `getStreamLength()`, `getDurableLength()`, `getGetOpCount()`,
  `getLastTransPosOfLastValidMetaBlock()`, `getFirstAvailableLookupTime()`, `currentTime()`:
  `DT.testSetStartupDistanceInForceOrRefused`, `DT.testSyncWaitsForTheCommitByte`,
  `DT.testGetOp`, `GM.testGetOpCount`, `DR.testLastTransPosAfterRestart`, `Reclaim.Tester`'s
  and `RR`'s tests, `DbClock`'s tests. The others (`getStartupDistance()`,
  `getTransactionCount()`, `getKvCount()`, `getFirstAvailablePos()`,
  `getReclaimIterationCount()`) have no Javadoc and promise nothing.

### 3.6. DbBuilder (24 methods, 30 promises)

* `Db.builder()`: a new builder. `build()`: `IllegalStateException` without a stream,
  `IllegalArgumentException` for a null clock (J5); `start()`: as `build()` and `start()`
  (J5). JC.testBuilderRefusals.
* `stream()`, `mainStream()`: one stream, replaced by a stream of the same name, another name
  refused with `IllegalStateException`; null and negative arguments refused; a buffer size
  below 100 and a time below 10 taken as 100 and 10 (J5). `DT.testSecondStreamRefused`,
  JC.testBuilderRefusals.
* `maxNodeSize8()` to `maxNodeSize62()`: kept from the creation, another refused at a start.
  `DR.testOtherNodeSizeRefused`.
* `startupDistance()`: 50 MB by default, below 10 refused, a database keeps the one in its
  stream (J5). `DR.dbShouldRememberStartupDistance1` and `2`, JC.testBuilderRefusals.
* `cacheSizeIndicator()`: 200 MB by default, below 1 refused (C3).
  JC.testBuilderCacheSizeIndicatorBelowOneRefused.
* `id()` (null refused), `testId()`, `clock()`, `systemClock()`, `createdTxt()`,
  `reclaimStepReserve()` (below 1 refused), `evictionSchedule()`, `audit()`,
  `secondTopOrdinal()`, `noEvict()`, `testSetup()`: JC.testBuilderRefusals,
  `DS.testCreatedTxt`, `DR.testOrdinalsAcrossBoundaries`, and their use by every tester.

### 3.7. GetMany, its stop conditions and Kvt (22 members, 20 promises)

* The order and the start key: forward or backward, from the first or the last key or from
  `startKey`, inclusive or not (J6). `GM.testStartKeyRandom` (both directions, inclusive and
  exclusive, against a sorted list), `GM.test1` to `testStart5`.
* `StopCondition`: four answers (J6); `eod()` once at the end, `handleKvt()` never after it,
  also when the database has no state at the lookup time (C2); none after a stop.
  JC.testEodOnceAtTheEnd.
* `GetN`, `GetOne`, `PrefixN`: at most N, none for 0 (C1); `Prefix`, `PrefixN` and `Endpoint`
  keep their own key (C1 for `PrefixN`). JC.testGetManyAtMostN, `GM.testEndpoint1` to `3`,
  `GM.testEndpointBackward`.
* `Kvt`: the key, the value (the database's array), the time of the key node entry, the
  value node's position. GM's tests, `DT.testGetTransOfEveryValue`.

### 3.8. StartInfo, StoredTrans and the exceptions (12 classes, 14 promises)

* `StartInfo`: the effective startup distance. `DT.testStartInfoReportsEffectiveDistance`.
  Its other fields, the section's position, first time, transaction count and last
  position, are each a line of Javadoc that tools print; not checked here.
* `StoredTrans` as `getTrans()` gives it: `tt`, `tpos`, `lastPos`, its value nodes.
  JC.testGetOneAndTheTransaction, `DT.testGetTransOfEveryValue`.
* `DbStoppingException` (an `IllegalDbStateException`) after `stop()`;
  `InternalDataException` (a `DbException`) for BergDB's keys; `RerunException`;
  `StreamIoException` and `StreamFormatException` while the database stops or as the cause of
  a `DbFailedException`; the Pub API's exceptions of `bergdb.pub.util` (020-25, section 3.8).
  JC.testCallsBeforeStartAndAfterStop, the tests of 3.1 to 3.4.

### 3.9. Read, not checked one by one

Members whose Javadoc marks them internal or for tests: `Db.internal()` and `Db.Internal`,
`Db.ExecuteData`, `Db.Aux`, `Db.TestHooks` and `testHooks`, `Db.StartParams`,
`Db.StartListener`, `Db.PrintStartListener` and `SYSTEM_OUT_START_LISTENER`,
`Db.TransactionListener`, `Db.ReadSync`, `Db.WriteLock`, `Db.lookupTime()` ("Internal, not
part of public API"), `Db.checkNodes()` ("for testing only"), `Db.getAccessData()`,
`Trans.Listener` and `Trans`'s public working fields, `GetMany.Chain`. And the classes that
`DbBuilder` takes: `AppendOnlyStream`, `FileStream`, `MemoryStream`, `Clock` (020-25,
section 3.7), `DatabaseId`, `Eviction.Schedule`. See Q1.

### 3.10. The count

Promises written down and checked: about 230, in 3.1 to 3.8, each bullet a few of them. Every
public method of `Db` and `DbBuilder` but those of 3.9 has its promises checked, and so have
`Trans.Builder`, `GetMany`'s stop conditions, `StartInfo` and the exceptions. Tests added: 9
in `DbTesterJavadoc` and 4 in `PubTesterCoreKeys`, 3 of them for the code faults (each
failing before its fix), 10 of promises kept.


## 4. Findings

Severity: high (wrong data, a failed database), medium (a user is misled into a wrong
program), low (a wrong or missing sentence or message, no wrong data).

### 4.1. Code faults

* **C1** (low). `GetMany.GetN` and `GetMany.PrefixN` with a count of 0 gave every KV (of the
  prefix), against "Gets at most N kvs": the count passed 0 before it was compared
  (`GetMany.java`, `GetN.handleKvt`, line 499 at `82edabf`). And `PrefixN`'s constructor kept
  the caller's array, its copy assigned to the parameter (line 550), where `Prefix` and
  `Endpoint` copy theirs. Fix: a count that is reached stops the scan; `PrefixN` copies.
  Test: JC.testGetManyAtMostN, which failed before ("GetN(0), expected 0, got 5"). Commit
  `22178c1`.
* **C2** (low). `StopCondition.eod()` was not called when the database had no state at the
  lookup time (before its first transaction): `Dag.getMany` returned at once, though the
  interface promises the call at the end of the database (`Dag.java`, line 562 at
  `82edabf`). BergDB's own readers end on a short page too and did not depend on it. Fix:
  `eod()` then. Test: JC.testEodOnceAtTheEnd, which failed before ("eod at time 0, expected
  1, got 0"). Commit `713768c`.
* **C3** (low). `DbBuilder.cacheSizeIndicator()` took a value below 1, which
  `Db.setCacheSizeIndicator()` refuses: the start then threw an `AssertionError` from
  `Cache3.setSizeIndicator` (with `-ea`) or ran with a budget of 0 or less
  (`DbBuilder.java`, line 170 at `82edabf`). The Pub API clamps its value and never passed
  one. Fix: `IllegalArgumentException`, and a Javadoc for the method. Test:
  JC.testBuilderCacheSizeIndicatorBelowOneRefused, which failed before. Commit `2fb8b71`.

`releases/next.md` has an entry for each, under Core API.

### 4.2. Javadoc faults

Each fixed in the Javadoc alone; the code is unchanged. Commit `ef3f8b2` (J1 to J6) and
`1c666d9` (K1 to K3, with `key-encoding.md`, docs/levels.md, section 11, and 020-22's entry in
`releases/next.md`).

* **J1** (low). `Db.start()` and `start(params)`: "@throws IllegalStateException If start()
  has been called already"; it throws `IllegalDbStateException`, a `DbException`, not an
  `IllegalStateException`, and closes nothing. Test: JC.testSecondStartRefused.
* **J2** (low). `Db.getMany()`: `IllegalDbStateException` "If start() has not been called";
  also after `stop()` and `close()` (a `DbStoppingException`), as `getOne()` says. Test:
  JC.testCallsBeforeStartAndAfterStop.
* **J3** (low). `Db.setCacheSizeIndicator()` did not say that a value below 1 is refused, nor
  `sync(SyncLevel)` and `sync(pos, SyncLevel)` that a null level is
  (`IllegalArgumentException` each) and that `NONE` returns at once. Test:
  JC.testCallsBeforeStartAndAfterStop.
* **J4** (low). `Db.getOne()` had no `@return`: null for a key without a value at the lookup
  time. Test: JC.testGetOneAndTheTransaction.
* **J5** (low). `DbBuilder.start()`: "Same as calling done() and then start()"; there is no
  `done()`, it is `build()`. Unsaid: `startupDistance()` refuses a value below 10;
  `stream()` refuses null and negative arguments and takes a buffer size below 100 and a
  time below 10 as 100 and 10; `build()` throws `IllegalStateException` without a stream and
  `IllegalArgumentException` for a null clock. Test: JC.testBuilderRefusals.
* **J6** (low). `GetMany`'s class comment gave an interval "(key1, key2]" of two keys that
  the class does not have; `startKey` and `inclusive` gave only the forward order, and
  `StopCondition.handleKvt()` "three cases" of four. Tests: `GM.testStartKeyRandom`,
  JC.testEodOnceAtTheEnd.
* **K1** (low). Keys and the layers above: a Core put at an object key of an indexed
  directory "leaves the value out of the index's scans"; it can: a put that keeps what the
  index takes from the value (the fields of its levels) changes nothing in the index, as
  020-22's W7 says. Now "can leave the value out", and the W7 case said. Test:
  CK.testCorePutAtAnIndexedObjectKey.
* **K2** (low). "BergDB never reads or writes" the Core user's keys; reclaim copies their live
  values forward as it copies every value. Now "never reads them for their meaning or
  changes them", 020-22's wording of the rule, the Core keeping them as any key. Test:
  CK.testYourKeysNeverWritten.
* **K3** (low). "The Db under a running Database is not API, and its writes of BergDB's keys
  are not seen until the next start"; `useIndex()` reads a definition from the stream and
  sees a Core delete of it at once, while the index manager, which reads the definitions at
  a start, does not (020-22's W25). Now "seen only in part until the next start". Test:
  CK.testOnlineWriteOfADefinitionSeenInPart.

### 4.3. Tests of promises kept

In commit `ef3f8b2` (6 tests of `DbTesterJavadoc`) and `1c666d9` (`PubTesterCoreKeys`).
Promises that no test showed before, now shown (all kept): `getOne()`'s array, the one put;
`GetData.tpos` and `Trans.nextPos`; `Trans.Builder`'s one operation a key; every call before
`start()` and after `stop()`, with the settings unchanged; a Db's threads daemon threads and
its commits written without `stop()`; `DbBuilder`'s and `Trans.Builder`'s refusals; the Keys
section's rules for a Core put and delete at an indexed key and for the Core user's keys.


## 5. For Frans

* **Q1**. The extent of the Core API. `bergdb.pub`'s "The API and its jar" makes the API "the
  Core's bergdb.core.Db with the types of its signatures". By the letter that holds `Db`'s
  internals (`Db.internal()` returns `Db.Internal`, which returns the `Dag`, the
  `NodeStream`, `Cache3`, `Eviction` and `Reclaim`; `ExecuteData`, `TestHooks`,
  `StartParams`), members that their own Javadoc calls internal (`lookupTime()`: "Internal,
  not part of public API") or for tests (`checkNodes()`, `printDag()`), and through
  `DbBuilder` the stream classes, `DatabaseId` and `Eviction.Schedule`; through `GetMany`,
  `GetData`'s and `Trans`'s working fields. 020-22 already says that `Db.internal()` is not
  API. Recommendation: name the API's part of the Core in `Db`'s class Javadoc, "the Core
  API": `Db.builder()` and `DbBuilder`'s stream, clock, node size, startup distance and cache
  size; `start()`, `stop()`, `close()`; `getOne()`, `getMany()`, `getTrans()`, `execute()`,
  `trans()` and `Trans.Builder`; `sync()`; the settings and their getters; `GetData`,
  `GetMany` with its stop conditions, `Kvt`, `StoredTrans`'s fields that `getTrans()` gives,
  `StartInfo`; `FileStream` and `MemoryStream` as streams; and say that the rest is not API
  whatever is public, as the package page says of `pubimp`. A narrowing of the letter, not of
  the use that `ReleaseDemo` and the Keys section describe; for 2026.4 if Frans agrees, else
  after it. Not changed.
* **Q2**. Null keys in the Core. `Trans.Builder.put()` and `delete()` with a null key throw
  `NullPointerException`, and `put(String, String)` an `AssertionError` with `-ea`; the
  Javadoc says nothing. The Pub API refuses every null argument with
  `IllegalArgumentException` (020-21, 3, Frans's decision for the Pub API); the Core's
  `Trans.Builder` does so for a null value and for the key of `put(long[], kt, value, vt)`.
  Recommendation: `IllegalArgumentException` for a null key in each `put()` and `delete()`
  of `Trans.Builder`, about ten lines and a test, after the release unless Frans wants it in
  2026.4. Not changed.


## 6. Notes, not changed

* `Db.sync()` before `start()` returns normally; every other call refuses it.
* `Db.newGetData()` and `newGetMany()` after `stop()` give their object; the read with it is
  refused.
* `StopCondition.handleKvt()` returning a value other than the four: an `AssertionError`
  with `-ea`, else taken as CONTINUE.
* `Db.getStartupDistance()`, `getTransactionCount()`, `getKvCount()`,
  `getFirstAvailablePos()` and `getReclaimIterationCount()` have no Javadoc; the counters
  count since the start, internal transactions included.
* `Db.StartListener` is an empty interface that nothing calls; `PrintStartListener` too;
  `Db.TransactionListener` has no public way to register one. Dead API by the letter of Q1.
* `Db.Aux` is a public class whose fields are private: "Private auxiliary database state".
* The C clone (012, 022) has its own reads; whether it has C1's and C2's corners was not
  checked (022's port study lists the Java changes to port).


## 7. State

Done: every listed class has its promises checked (section 3); three code faults fixed (C1 to
C3), nine Javadoc faults fixed (J1 to J6, K1 to K3), 13 tests added, two questions for Frans
(Q1, Q2), notes in section 6. The commits are in the clone
`/Users/f/fl/bench/2026-11-09/clone-j27`, branch `main`, on `cf287ad`: `22178c1` (C1),
`713768c` (C2), `2fb8b71` (C3), `ef3f8b2` (J1 to J6 and the tests of promises kept),
`1c666d9` (K1 to K3 and `PubTesterCoreKeys`), `5cf84dd` (DbBuilder's streams in
`testBuilderRefusals`; the Documentation entry in `releases/next.md`). Not pushed; the
coordinator takes them to the main tree. `releases/next.md` has an entry for each code fault
(Core API) and one for the Javadoc faults (Documentation), as 020-19's.

Gates (`java/before-commit.sh`, under the shared lock, in the clone): `1c666d9`'s tree before
the rebase onto `cf287ad` (`868b165`, the first five commits): BEFORE COMMIT OK (160 s; unit
1539, f 86, DEMOS OK), 13:50; the tip, `5cf84dd`: BEFORE COMMIT OK (159 s; unit 1539, f 86,
DEMOS OK), then `java/stress/level1.sh` LEVEL 1 OK (MEM 129, SS 1.51), 13:59. JAVADOC PUB OK;
`Db`, `DbBuilder` and `GetMany` pass doclint (html, syntax). Outputs in
`/Users/f/fl/bench/2026-11-09/j27-gate1.txt` and `j27-gate2.txt`.

Left: Q1 and Q2 after Frans's word; section 6's notes, each a small entry if Frans wants it.


Log
===

2026-11-09. Created by coord-1109's agent j27, 13:23. Every listed class checked, C1 to C3,
J1 to J6 and K1 to K3 fixed in the clone with their tests, 6 commits on `cf287ad`, the tip
gated (BEFORE COMMIT OK and LEVEL 1 OK, 13:59). Stopped at 14:00: every listed class done.

2026-11-09. Q2 decided by Frans, 16:20: "Yes, as recommended. Absolutely." Done by
coord-1109's agent q27 in `/Users/f/fl/bench/2026-11-09/clone-q27`, commit "020-27, Q2": every
public method of `Db`, `DbBuilder`, `Trans.Builder` and `GetMany`'s stop conditions that takes
an object refuses null with `IllegalArgumentException` that names the parameter, with its
`@throws`; tests `DbTesterJavadoc.testDbNullArguments`, `testDbBuilderNullArguments`,
`testTransBuilderNullArguments` and `testGetManyNullArguments`, each failing before.

2026-11-09. Q1 decided by Frans, 16:27: "Yes to the Javadoc proposal. This has been
intentionally open. And still we expect Core API to change faster and be less well-defined.
The Pub API is the stable, default, and preferred API. The Core API is for when low-level
control and max performance is really needed. It is less stable, less safe, and can destroy
the data for pub layer. The Core layer is mostly an internal layer to develop Pub Layer on
top." Done by q27, commit "020-27, Q1": a paragraph "The Core API" at the top of `Db`'s
class Javadoc that names it, and a sentence in `DbBuilder`'s, in the Core's package page and
in `bergdb.pub`'s "The API and its jar"; Javadoc only.
