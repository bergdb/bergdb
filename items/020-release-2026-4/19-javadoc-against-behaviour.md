# 020-19 The public Javadoc checked against behaviour

Created 2026-11-09 by Frans Lundberg. Status: open.

The public Javadoc of release 2026.4's API, the packages bergdb.pub and bergdb.pub.util with
their package pages and the overview, checked against what the code does, promise by
promise, with tests; a bug hunt for 020.


## 1. The request

One of the bug hunts that coord-1109 started for release 2026.4 (020), at Frans's request
(2026-11-09, 09:21: "Start 1 to 4"; 09:22: "Use effort xhigh"). The task, from the
coordinator's brief: go through every public class, method and constructor of the release
jar's API; write each promise down as a checkable sentence; find the test that shows it, or
write one; judge each mismatch a fault of the code or of the Javadoc by the specs (020-07,
020-09, 020-10) and by what a user would expect; fix a code fault with a failing test first
and a Javadoc fault with a Javadoc fix; leave to Frans what is not clearly either. Priority:
the classes that 2026.4 changed most (DbObject and the DbValue family, IndexBuilder,
UseIndexBuilder, UsePrimaryBuilder, Job, JobStatus, IndexBuildException, Connection,
Database, Kv), then the rest.


## 2. The method

* The work is in the clone `/Users/f/fl/bench/2026-11-09/clone-j19`, from `main` at
  `a9e5488`. The other hunts' findings were not read.
* Each Javadoc text was read sentence by sentence, with the implementation behind it
  (`bergdb.pubimp`), and each promise written down (section 3) with the test that shows it:
  an existing tester's, found by name and doc comment, or a new one.
* The new tests are in a new tester, `bergdb.pubimp.PubTesterJavadoc`, one test per promise
  or small group, each named after the class and the promise in its doc comment; one more is
  in `PubTesterIndexJobs`. Fast: the class runs in about 0.5 s, its slowest test 66 ms.
* Behaviour that no Javadoc promises was probed with small programs on the release jar
  alone (the user's view), in the scratchpad; what they showed is in sections 5 and 6.
* The examples were run as written: the overview's `Demo` with `java -cp bergdb.jar
  Demo.java` (put, get, delete, get: the output as the page shows it), the package page's
  examples assembled into the one program that the page describes (they compile and print
  each comment's output), and the class comments' examples with data, in
  `PubTesterJavadoc.testPackageExamples` and `testClassExamples`.


## 3. The promises and their tests

Tests are named by class and method: `J` is `PubTesterJavadoc` (new), `T` `PubTester`, `IJ`
`PubTesterIndexJobs`, `IX` `PubTesterIndex`, `IR` `PubTesterIndexRaces`, `PR`
`PubTesterPrimary`, `DO` `DbObjectTester`, `DX` `DataObjectsTester`, `OUT`
`PubTesterOutput`, `U8` `Utf8ReadTester`, `PP` `PubPromiseTester` (harness 6.7 of 2026.3,
the Pub API's String and byte[] promises against a reference), `H2` `IndexHarness`, `H3`
`IndexJobsHarness`.

### 3.1. Connection (17 methods, 52 promises)

* Keys: a key starts with '/', has a second char, does not end with '/', has no "//" and no
  lone surrogate; every call that takes a key refuses another, and null, with
  IllegalArgumentException. J.testNullArgumentsRefused, PP, T.testKeyWithLoneSurrogateRefused.
* setEnableKeyReplace(), getEnableKeyReplace(): off by default; "${transactionTime}" in the
  key of a put replaced in a w() and an rw(), unique for each transaction and increasing; a
  delete's key taken as written. J.testKeyReplace, T.testKeyReplaceEveryOccurrence, PP.
* setLookupTime(): Time.MAX by default; a time after the last transaction reads the latest;
  it ends a freeze; a time before the first available lookup time throws
  LookupTimeNotAvailableException, also for a read that has started. J.testLookupTimeAndFreeze,
  PP, J.testIndexScanBehindCut, PR.testScanBehindCut.
* getLookupTime(): Time.MAX by default, t after setLookupTime(t); after freezeLookupTime(),
  Time.MAX until the next read, then the frozen time, which another connection can read at.
  J.testLookupTimeAndFreeze.
* freezeLookupTime(): the next read, a get(), exists(), useIndex() or usePrimary(), fixes
  the time; later reads read at it; each call freezes anew, also after setLookupTime(t).
  J.testLookupTimeAndFreeze, J.testFreezeByUseIndex, T.testFreezeThenExists,
  T.testFreezeAgainReadsNewState, PR.testScanFixesFrozenLookupTime.
* currentTime(): at or after the last completed transaction's time, before any later one's;
  after a restart with a test clock it may repeat. J.testCurrentTime, T.testCurrentTime.
* exists(): a read as get(); one that finds the key sets transactionInfo() as a get() does.
  J.testTransactionInfo, T.testFreezeThenExists, T.testExistsOfMalformedKeyThrows.
* get(): null for no entry; a String, a byte[] (the database's own array), a Data Object by
  its constructor, best effort; a primitive, a wrapper or an array for a value put as one;
  DbObject.class exactly; Object.class a DbObject at an object key, a String at ".txt", else
  bytes; DataFormatException for a String that is not well-formed UTF-8;
  ObjectCreationException for a class that is not a Data Object (also at a key without a
  value), a constructor that throws (the cause), a value that is not a stored object, an
  object of format 1; IllegalArgumentException for a null key or class.
  J.testGetAsObjectByKind, J.testGetOfPrimitivesAndArrays, J.testGetRefusesWhatIsNotAnObject,
  J.testNullArgumentsRefused, J.testPackageExamples, T.testFormat1ObjectRefused, U8, DX
  (G1 to G122), PP.
* transactionInfo(): IllegalStateException before a get() has retrieved a value, also after
  one that found no entry; the time and the user's KVs, a delete with value null, a delete
  of a key without an entry and an index's entries left out; LookupTimeNotAvailableException
  after reclaim rewrote the value. J.testTransactionInfo, T.testTransactionInfo1,
  T.testTransactionInfoWithIndex, T.testTransactionInfoAfterReclaim,
  T.testTransactionInfoAfterGetOfMissingKey, PP.
* put(): overwrites; a byte[] copied; a String and each string of an object well-formed
  UTF-8, a lone surrogate refused; an object only at an object key, "Bad key" at another;
  null refused; an object that cannot be stored exactly refused, nothing written;
  DbException for a transaction too large (J8); DataFormatException for a format-1 byte[] in
  an indexed directory (J5). J.testObjectKeys, J.testTooLargeRefused,
  J.testFormat1PutRefusedInEveryPath, T.testByteArrayCopiedAtPutNotAtGet,
  T.testValueWithLoneSurrogateRefused, T.testRefusedObjectWritesNothing, T.testHugeStringRefused,
  DX (W1 to W36), PP.
* delete(): nothing to delete is no error; null and bad keys refused.
  T.testDeleteOfNonExistantEntry, T.testDeleteWithNullNotPossible, PP.
* w(): see WBuilder below. rw(): its action may run more than once, its outputs those of the
  run that committed; a conflict reruns it; an interrupt in the wait after a conflict throws
  DbException, not run (J8). OUT.testRerun, J.testRwInterruptedAfterConflict, PP.
* useIndex(): the definition read at the connection's lookup time, resolved at the call;
  NoSuchIndexException if no index then, or building then; ObjectCreationException for a
  type that a get does not take, whatever the data; IllegalArgumentException for nulls; every
  iterator reads at t, also after the index was deleted, until the cut passes t; a read for
  the freeze; transactionInfo() unchanged. J.testGetRefusesWhatIsNotAnObject,
  J.testDeleteIndexKeepsEarlierScans, J.testIndexScanBehindCut, J.testFreezeByUseIndex,
  J.testJobStatus, IX.testScanKeepsTransactionInfo, IX.testScanLookupTime.
* usePrimary(): as useIndex() for its time, the freeze and transactionInfo();
  ObjectCreationException for a type whatever the data; IllegalArgumentException for null.
  J.testGetRefusesWhatIsNotAnObject, J.testNullArgumentsRefused, PR.
* sync(), sync(SyncLevel): wait for the connection's last transaction; an interrupt throws
  DbException, the transaction committed, the flag set (J6). J.testSyncInterrupted (on a
  stream that holds its appends, so that each sync waits), T.testSync1 to T.testSync6.

### 3.2. Database (18 methods, 38 promises)

* One database at a time has a directory. T.testStartWhileStoppingRefused.
* getStartupInfo(): the seconds that the start took. T.testStartupInfoTime.
* Errors: a failure fails the database, the call throwing it, later calls
  DbFailedException; refusals and a conversion's exceptions, an Error too, fail only the
  call. T.testErrorFailsTheDatabase, J.testConversionErrorFailsOnlyTheCall,
  T.testMalformedObjectRefused.
* Interrupts: sync(), Job.join() and an rw() waiting after a conflict end their wait; every
  other call ignores the interrupt; the flag is set after each. J.testInterruptFlagKept
  (every call of Connection and Database but those three, on a file database, close()
  included), J.testSyncInterrupted, J.testRwInterruptedAfterConflict,
  IJ.testJoinReturnsAfterAnInterrupt.
* AutoCloseable; the class example. J.testClassExamples, T.testTryWithResourcesCloses.
* stop(): no read or transaction after it (IllegalDbStateException); idempotent; the
  writes done in the background, also when main returns. J.testCallsAfterStop,
  T.testStopWritesAll, T.testStopThenReturnFromMain.
* close(): waits; several times, also after stop(); a failed flush throws.
  T.testCloseAfterStopAndTwice, T.testCloseReportsBackgroundWriteFailure.
* connection(): one per thread; Time.MAX at each call, a freeze ended; ended threads not
  kept. newConnection(): new, Time.MAX. J.testConnections,
  T.testConnectionOfEndedThreadNotKept, T.testNewConnectionLookupTime.
* sync(), sync(SyncLevel): J.testSyncInterrupted, T.testSync1 to T.testSync6.
* currentTime(): J.testCurrentTime.
* getRetainDuration(), setRetainDuration(): Duration.MAX until set; less than a second
  refused; kept in the stream; IllegalDbStateException after stop(), unchanged.
  J.testSettings, J.testCallsAfterStop, T.testSetRetainDurationKept, T.testRetainDuration1.
* getStartupDistanceInMb(), setStartupDistanceInMb(): clamped to 5 to 1000; kept in the
  stream; IllegalDbStateException after stop(), unchanged. J.testSettings,
  J.testCallsAfterStop, J.testInterruptFlagKept, T.testSetStartupDistanceInMb.
* getCacheSizeInMb(), setCacheSizeInMb(): clamped to 4 to 100,000; for the run; after
  stop() it only sets the value (J1). J.testSettings, J.testCallsAfterStop,
  T.testSetCacheSizeInMb.
* getFirstAvailableLookupTime(): moves forward with reclaim. T.testFirstAvailableLookupTime1,
  J.testIndexScanBehindCut.
* indexBuilder(): 1 to 255 UTF-8 bytes, no '/', whitespace or lone surrogate, else
  IllegalArgumentException; "primary" a name like any other; existence checked at start().
  J.testIndexNames, IJ.testIndexNamedPrimary.
* deleteIndex(): gone at every later time, the name free, a building job FAILED "deleted",
  earlier scans still work, also after a new index of the name; NoSuchIndexException for
  no index. J.testDeleteIndexKeepsEarlierScans,
  J.testIndexNames, IJ.testBuildDeletedBeforeItsStep, IJ.testDeleteTwice.
* indexJob(): the job of start() or of a resumed build; ACTIVE with count 0 for an index
  active at the start; a failed build's join() throws each time; NoSuchIndexException.
  J.testJobStatus, IJ.testJoinThrowsForAFailedBuild, IJ.testBuildOverAnObjectItCannotIndex.

### 3.3. IndexBuilder (6 methods, 24 promises)

* dir(): once, first; IllegalArgumentException for null or not a directory;
  IllegalStateException twice or spent. type(): one of four names; after dir() and a
  complete level; at most 8 levels. field(): 1 to 255 bytes, no lone surrogate, a '.' part
  of the name; once per level after type(). nestedField(String): split at '.', 1 to 16
  parts, none empty. nestedField(String[]): not null or empty, at most 16 parts. start():
  needs dir() and complete levels; IndexAlreadyExistsException for a name building or
  active; spent after start() whatever it threw. J.testIndexBuilderChecks,
  J.testFieldNameWithADot, J.testJobStatus, IJ.testDirTwice, IJ.testNestedFieldEmptyPart.
* The index function: a suffix other than ".obj" or a value that is not a stored object
  gives no entry; a byte[] that passes the check is an object; a String never is; format 1
  refused by a put (DataFormatException) and failing a build; a put over and a delete of it
  work; each kind taken by its level type only, no conversion; a boolean, an array, an object
  or an absent field no entry; NaN no entry; levels over 4,096 bytes no entry; a
  subdirectory's values no entry. J.testIndexFunction, J.testFormat1PutRefusedInEveryPath,
  IR.testFormat1InIndexedDirectory, IJ.testLargeValueNoEntry, IJ.testSubdirNotIndexed, H2.
* The order of each level: longs, doubles (-0.0 as 0.0, the infinities at the ends),
  strings by code points, bytes unsigned. J.testIndexOrder, IX.testNegLongs1,
  IX.collationUnicode1, H2.
* Every put and delete at an object key keeps the index; a String or byte[] over an object
  deletes its entry. IR.testStringOverObject, H2.
* start(): the build in the background; join() at once for an empty directory; a stop
  before the end, the next start builds again from the first key; a failed build throws
  from join(), the database goes on, the index stays and the next start builds it again.
  J.testReplaceWhatTheBuildCannotIndex, IJ.testStartResumesBuildsAndCleanups,
  IJ.testBuildOverAnObjectItCannotIndex, the class example in J.testClassExamples.

### 3.4. UseIndexBuilder (18 methods, 14 promises)

* The grammar: eq() level by level, then one from() and one to(), or one prefix(), on the
  next level; backward() once; IllegalStateException out of the grammar and after objects()
  or kvs(); IllegalArgumentException for an argument of another type than the level's, a
  null, a NaN, a lone surrogate; objects() and kvs() again from the beginning; a from()
  above the to() empty; -0.0 as 0.0. J.testUseIndexGrammar, J.testIndexOrder, IX.testGrammar.
* The result: the entries in the order of the levels, then the keys, ascending or
  descending; stale entries skipped before hasNext() says true; a conversion that throws
  throws from next(); LookupTimeNotAvailableException behind the cut. J.testIndexOrder,
  J.testClassExamples, J.testIndexScanBehindCut, J.testConversionErrorFailsOnlyTheCall,
  IX.testStaleLastEntries, IX.testExclusiveBounds, IX.testPrefix, H2.

### 3.5. UsePrimaryBuilder (6 methods, 14 promises)

* dir() first and once; inclusive(), backward(), startAt() each at most once, after dir();
  startAt() refuses null, empty, '/' and a lone surrogate; objects() and kvs() need dir(),
  may be called again, and spend the builder. J.testUsePrimaryGrammar,
  PR.testPrimaryNeedsDir, PR.testBuilderSpentAfterListing.
* What it lists, by type, in key order, at its time; internal keys never; the iterator goes
  on after a conversion that throws; LookupTimeNotAvailableException behind the cut.
  PR.testTypesListByKind, PR.sortOrder0, PR.testRootDir1, PR.testIteratorContract,
  PR.testScanBehindCut, J.testPackageExamples, U8.testScanPastKeysWithoutIkey.

### 3.6. Job, JobStatus, IndexBuildException (8 members, 16 promises)

* getStatus(): a snapshot, never throws; join(): waits, ACTIVE, or BUILDING after a stop or
  an interrupt; join(millis): BUILDING when the time is up, 0 as join(); a failed build
  throws IndexBuildException at every join(), its status FAILED and its cause; the reason
  null unless FAILED, "deleted" without a cause for a deletion; count the values read in
  this process; note() one line, and for a deletion no "next start" (F1).
  J.testJobStatus, IJ.testNoteOfADeletedBuild, IJ.testJoinThrowsForAFailedBuild,
  IJ.testJoinReturnsAfterAnInterrupt, IJ.testJoinFromAnotherThread,
  IJ.testStatusIsSnapshot, H3.
* IndexBuildException: a deleted index is gone; another stays and the next start builds it
  again; replace the values and restart. J.testReplaceWhatTheBuildCannotIndex,
  IJ.testBuildOverAnObjectItCannotIndex.

### 3.7. DbObject (31 members, 38 promises)

* new DbObject(bytes): the full check, BadFormatException with the condition's code first,
  "format-1" for format 1; a copy; null refused. J.testDbObjectBytes, DO.testBadFormatException,
  `ObjectFormatTester` (the 020-07 vectors).
* getBytes(): a new array each time, the header first; one byte string per object, the
  fields by their names' unsigned bytes. J.testDbObjectBytes, DbObject.testGetBytesGivesACopy.
* getFieldCount(), has(), getType(), getDbValue(), the typed getters with String and
  String[]: the value of its type, else false, 0, 0.0 or null, never a throw for the data;
  INT for an integer within int's range; LONG for every integer; a null name refused, an
  impossible name absent; a path part absent or not an object makes the field absent; the
  parts checked first. J.testDbObjectGetters, J.testDbObjectNames,
  DbObject.testNamePartsCheckedFirst, DO.testNestedField1 to 5.
* getObject() a view, getBytes() of it with the header; the other getters copies.
  J.testDbObjectBytes, J.testDbObjectGetters.
* getByteSize(), write(): the encoding without the header. J.testDbObjectBytes,
  J.testValues.
* toDbObject(): exact; a null field absent; an array in "array", a primitive in "p"; a
  DbObject as it is; the refusals named by place. toJavaObject(): best effort; "p" and
  "array"; null if absent; ObjectCreationException. J.testDataObjectConversions,
  J.testLoneSurrogateRefusals, DX, DO.testCycleRefused, DO.testDeepRefused.
* Builder: a later add of a name replaces; build() again; null, empty, long and
  lone-surrogate names, null values and a 32,768th field refused; more than 16 levels
  refused; the sizes refused before allocation. J.testBuilders, J.testViewsCopiedIn,
  DbObject.testLongFieldName, DbValue.testSizesRefused.
* A put of a DbObject checks its bytes and stores a copy. DbObject.testPutChecksTheBytes,
  T.testDbObjectPutStoresACopy.

### 3.8. DbValue and its six other classes (27 members, 18 promises)

* getType(); getByteSize() and write() agree, write() throws IndexOutOfBoundsException for
  a short array; DbLong in the fewest bytes; DbDouble one NaN, -0.0 kept; DbString and
  DbByteArray refuse null, DbString a lone surrogate; DbByteArray copies both ways.
  J.testValues, DbLong.testSerialize0, DbDouble.testSerialize0, DbByteArray.testImmutable.
* DbArray: getSize(), the iterator in order without remove(), NoSuchElementException past
  the end; toIntArray(), toLongArray(), toDoubleArray() new arrays, converted as a get
  converts; Builder.add() refuses null, build() more than 15 levels. J.testDbArray,
  J.testDbArrayConversions, J.testBuilders, J.testViewsCopiedIn.

### 3.9. Kv

* key() and value(), fixed. J.testPackageExamples, J.testClassExamples, PR.testKv.

### 3.10. The rest

WBuilder, RwEnvironment, ReadInterface, Action, Transaction, TransactionInfo, Factory,
DatabaseBuilder, StartupInfo, Time, Duration, TestClock, CryptoKey, the exceptions, Clock and
SyncLevel were read, and their promises checked against existing tests by name (PP, OUT,
T's start, crypto and creation tests, Time's and TimeResolver's own tests) and by the
probes; not each written down here. J3, J4, J6, J7 and J8 came from them, and section 5's
questions and section 6's notes. New tests of them: J.testBuilderSettings (DatabaseBuilder's
defaults and clamps; no test showed the cache size's), J.testTimeStrings (J7).

### 3.11. The count

Promises written down and checked for the priority classes: about 214, in 3.1 to 3.9, each
bullet a few of them. Every public method of the priority classes has its promises checked.
Tests added: 44 in `PubTesterJavadoc` and 1 in `PubTesterIndexJobs`.


## 4. Findings

Severity: high (wrong data, a failed database), medium (a user is misled into a wrong
program), low (a wrong or missing sentence or message, no wrong data).

### 4.1. Code faults

* **F1** (low). `JobStatus.note()` of a build that ended because its index was deleted
  said "The next start takes it again", which is false: the index is gone
  (`IndexBuilderImp.java`, `Status.note()`, line 282 at `a9e5488`); `JobStatus.State.FAILED`'s
  Javadoc said the same of every failure (`JobStatus.java`, line 21). Test:
  `PubTesterIndexJobs.testNoteOfADeletedBuild`, which failed before the fix. Fix: commit
  `dbd6630` in the clone.

### 4.2. Javadoc faults

Each fixed in the Javadoc alone; the code is unchanged. JAVADOC PUB OK after each.

* **J1** (low). `Database.setCacheSizeInMb()`: "After stop() the method has no effect"; it
  sets the value, which `getCacheSizeInMb()` then gives (`Database.java`, line 294). Test:
  `J.testCallsAfterStop`. Commit `cd25687`.
* **J2** (low). `DbObject`, "Strings": the messages of the Builder and of DbString were said
  to name the field and the array index; only `toDbObject()`'s does (`DbObject.java`, line
  85). Test: `J.testLoneSurrogateRefusals`. Commit `a60e177`.
* **J3** (low). `ReadInterface.get()` and `RwEnvironment.get()`: "A class other than String,
  byte[], DbObject and Object is a Data Object class"; primitives, wrappers and arrays are
  taken too, as `Connection.get()` says (`ReadInterface.java` line 35, `RwEnvironment.java`
  line 27). Test: `J.testGetOfPrimitivesAndArrays`. Commit `c1ce287`.
* **J4** (low). `DbException` gave as a refusal "a stored value that does not fit its Java
  field (DataFormatException)", 2026.3's rule; a get now converts best effort
  (`DbException.java`, line 9). Tests: `U8.testStringValueNotWellFormed`,
  `J.testFormat1PutRefusedInEveryPath`. Commit `ed3361f`.
* **J5** (low). A byte[] put of a format-1 object in an indexed directory throws
  DataFormatException from `Connection.put()`, `WBuilder.execute()` and `Connection.rw()`;
  none of them said so, and `DataFormatException` pointed to `WBuilder.put()`, which does not
  throw it. Test: `J.testFormat1PutRefusedInEveryPath`. Commit `7c6ec69`.
* **J6** (low). `Transaction.sync()`, `sync(SyncLevel)` and `Connection.sync(SyncLevel)` did
  not say that an interrupt in the wait throws DbException, as `Database`'s "Interrupts"
  says (`Transaction.java` lines 42 and 49, `Connection.java` line 381). Test:
  `J.testSyncInterrupted`. Commit `771534c`.
* **J7** (low). `Time`'s grammar of a time string omitted what the code takes and its own
  tests use: "T" before the time of day, "HH:MM:SS" without a fraction, and a minus time's
  time of day; and `units()`, `millis()`, `add()`, `utc()` and both `resolve()` throw
  IllegalArgumentException for a time outside Time's range, which none said (`Time.java`,
  lines 57 to 185). The message's typo "ouf of range" corrected. Test: `J.testTimeStrings`.
  Commit `8f86908`.
* **J8** (medium). `Connection.put()` and `delete()`: DbException "If the transaction could
  not be processed because the database is faulty"; `WBuilder.execute()` and
  `Connection.rw()` named none. A DbException there is a refusal, nothing written and the
  database going on: a transaction too large (more than 7/8 of 2^31 - 9 bytes, about 1.88
  GB, of values and keys in the stream), or a database stopping or stopped; for rw() also
  an interrupt after a conflict. No Javadoc gave the size limit of a transaction, and the
  package page's "Strings" gives 2^31 - 9 bytes for a String value, which a put cannot reach
  (`Connection.java` lines 255 and 281, `WBuilder.java` line 51). Tests:
  `J.testTooLargeRefused` (the record limit lowered by reflection, as the Core's tests lower
  it), `J.testRwInterruptedAfterConflict`, `J.testCallsAfterStop`. Commit `5409f8b`.

### 4.3. Tests of promises kept

Commits `8095816`, `3032209`, `a28687c`, `94bdd00`, `a25bca3`, `88eab79` and `90a7534` add
`PubTesterJavadoc`, 44 tests, the tests of J1 to J8 among them; `90a7534` made two of them
independent of timing (a sync on a file database could find its transaction durable
already, and a poll with the interrupt flag set did not wait). Promises that no test showed
before, now shown (all kept): the package page's examples as a whole; the interrupt flag
kept by every call that does not wait, and
the rw() interrupted after a conflict; useIndex() behind the cut and after a deletion
whose cleanup has ended; the freeze by useIndex(); IndexBuilder's checks in full and a
field name with a dot; the index function and the order of each level type; replacing the
values that a build cannot index; a conversion's Error failing only its call; the DbObject
getters with impossible names; DbArray's conversions; the values' write() bounds.


## 5. For Frans

* **Q1**. `Time.utc()` and `Time.resolve()` accept fields out of range and roll them over:
  "2013-13-01" is 2014-01-01, "2013-02-30" is 2013-03-02, "2013-00-10" is 2012-12-10,
  "25:00" the next day, "12:60" 13:00, "23:59:60" the next day. The Javadoc's grammar
  ("YYYY-MM-DD", "HH:MM") and its "@throws BadFormatException If the time string does not
  follow the format above" say otherwise; the code means it ("Let's allowed "overflow" for
  now", `TimeResolver.parseDate`), a test keeps it (`TimeResolver.testBadSeconds`: "00:00:75"
  is "00:01:15"), and 021-01 saw it and left it. A typo in a lookup time then reads another
  state silently. Recommendation: refuse with BadFormatException a month outside 1 to 12, a
  day outside its month, an hour above 23, a minute above 59 and a second of 60 or more,
  and change that test; else say in the Javadoc that the calendar rolls such fields over.
  Not changed.
* **Q2**. `WBuilder` after `execute()`: a second `execute()` runs the same writes again as a
  new transaction, and a `put()` after `execute()` adds to them; no Javadoc says whether a
  builder may be used again. Recommendation: say that execute() spends the builder, and
  throw IllegalStateException after it, as UsePrimaryBuilder and IndexBuilder do; or say
  that it may be executed again. Not changed.


## 6. Notes, not changed

Small things seen on the way, below the bar of a fix in this hunt:

* `Database.setRetainDuration(null)` throws NullPointerException; every other null
  argument of the API gives IllegalArgumentException.
* `Job.join(millis)` with a negative `millis` returns at once; `Thread.join()` refuses one.
* An absolute time string outside Time's range gives IllegalArgumentException (J7), a
  minus time before 1970 BadFormatException.
* `Duration.seconds(Double.NaN)` gives a duration of 0.
* `CryptoKey.NULL.serialize()` gives "null-null-", which `CryptoKey.parse()` refuses;
  `parse(null)` throws NullPointerException; `getKeyData()` gives the key's own array, so a
  caller can change the key.
* `Connection.delete()` of a key without an entry "does nothing", but commits a
  transaction with a time of its own.
* `Connection.java` line 104, in freezeLookupTime()'s Javadoc, is 154 chars long.


## 7. State

Done: every public method of the priority classes has its promises checked (section 3);
one code fault fixed (F1), eight Javadoc faults fixed (J1 to J8), 45 tests added, two
questions for Frans (Q1, Q2), notes in section 6. The commits are in the clone
`/Users/f/fl/bench/2026-11-09/clone-j19`, on `main` after `a9e5488`; the coordinator takes
them to the main tree.

Gate: `java/before-commit.sh` on `a28687c` (F1, J1 to J6, J8 and their tests): BEFORE
COMMIT OK (154 s; unit 1460, f 86, DEMOS OK), 09:57; on the tip, `90a7534` (all 16
commits): BEFORE COMMIT OK (152 s; unit 1462, f 86, DEMOS OK), 10:05.

Left: the rest (section 3.10) promise by promise, as for the priority classes; Q1 and Q2
after Frans's word; section 6's notes, each a small entry if Frans wants it.


Log
===

2026-11-09. Created by coord-1109's agent j19, 09:24.
The priority classes checked, F1 and J1 to J8 fixed in the clone, the tests added; 16
commits in the clone, `dbd6630` to `90a7534`, the tip gated (BEFORE COMMIT OK, 10:05).
Stopped at 10:06: every public method of the priority classes checked.
