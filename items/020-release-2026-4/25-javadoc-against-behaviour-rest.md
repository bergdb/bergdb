# 020-25 The public Javadoc checked against behaviour: the rest

Created 2026-11-09 by Frans Lundberg. Status: open.

The rest of release 2026.4's public API, after 020-19's priority classes: the classes of
bergdb.pub and bergdb.pub.util that 020-19 read but did not check promise by promise
(020-19, section 3.10), and the package pages' remaining claims, checked against what the
code does, with tests.


## 1. The request

coord-1109, 2026-11-09, 12:41, at Frans's word (12:40): do for the rest of the release jar's
public API what 020-19 did for the priority classes: WBuilder, RwEnvironment, ReadInterface,
Transaction, TransactionInfo, DatabaseBuilder, StartupInfo, Time, Duration, CryptoKey,
Factory, Action, Kv, TestClock, the exceptions of bergdb.pub.util and their documented
meanings, SyncLevel, Clock, and the package pages' remaining claims; today's changes too
(020-21: strict Time, WBuilder spent, the refusals; 020-22: the rules for Core writes). A code
fault gets a fix with a failing test first, a Javadoc fault a Javadoc fix (JAVADOC PUB OK),
listed apart; what is not clearly either goes to Frans with a recommendation. Tests fast
(under 100 ms each), one commit per class or so, gated. Stop when every listed class is
done, or at 17:00.


## 2. The method

* The work is in the clone `/Users/f/fl/bench/2026-11-09/clone-j25`, from `main` at
  `b7aa2a0`, rebased onto `b49606b` (with 020-23's Y1 and Y2 of `Time`) and then onto
  `82edabf` (items only). The other
  hunts' findings were not read; 020-19 and 020-21 were, as the brief asked.
* Each Javadoc text of the listed classes was read sentence by sentence, with the
  implementation behind it (`bergdb.pubimp`, and `bergdb.core`'s `DbClock` and `Db.sync`),
  and each promise written down (section 3) with the test that shows it: an existing
  tester's, found by name and doc comment, or a new one.
* Small programs on the release jar alone (`build/bergdb-release.jar`, the user's view), in
  the scratchpad, probed the promises and the corners that no Javadoc gives: null arguments,
  calls after a failure and after stop(), a clock out of range or going back, time zones and
  summer time, CryptoKey strings, foreign streams.
* The new tests are in a new tester, `bergdb.pubimp.PubTesterJavadocRest` (Pack lists it),
  one test per promise or small group, each named after its class and promise in its doc
  comment; 020-19's `PubTesterJavadoc` is changed in one line (C3). Fast: the class runs in
  about 0.2 s, its slowest test about 50 ms.
* Time's examples were run as its Javadoc writes them (`testTimeExamples`); the package
  pages' examples were run by 020-19 and are not repeated.


## 3. The promises and their tests

Tests are named by class and method: `R` is `PubTesterJavadocRest` (new), `J`
`PubTesterJavadoc` (020-19), `T` `PubTester`, `OUT` `PubTesterOutput`, `PP`
`PubPromiseTester`, `U8` `Utf8ReadTester`, `DX` `DataObjectsTester`, `PR`
`PubTesterPrimary`, `DBI` `DatabaseBuilderImp`'s own tests, `TI` `Time`'s own tests, `TR`
`TimeResolver`'s, `CK` `CryptoKey`'s, `DF` `bergdb.core.DbTesterFailure`.

### 3.1. WBuilder (3 methods, 16 promises)

* The class: get one with Connection.w(), execute it once; execute() spends it, whatever it
  threw (020-21, 2); of several puts and deletes of one key the last one counts (J1).
  J.testWBuilderSpentByExecute, R.testWBuilderOneTransaction, T.testWPutThenDelete.
* put(): a String as UTF-8, a byte[] as it is, copied at the put; a lone surrogate, a
  String over 2^31 - 9 bytes, an object at a key with another suffix than ".obj" ("Bad
  key"), a null value, a null or invalid key refused at once; an object that cannot be
  stored exactly refused, a null field left out; IllegalStateException when spent.
  R.testWBuilderOneTransaction, J.testObjectKeys, T.testValueWithLoneSurrogateRefused,
  T.testHugeStringRefused, T.testRefusedObjectWritesNothing, DX (W1 to W36), PP.
* delete(): no effect for a key without an entry; a null or invalid key refused.
  R.testWBuilderOneTransaction.
* execute(): one transaction, none of it before its time, returned when committed;
  DbException for a transaction too large or a database stopping; DbFailedException after a
  failure; DataFormatException for a format-1 byte[] in an indexed directory, nothing
  written. R.testWBuilderOneTransaction, J.testTooLargeRefused,
  J.testFormat1PutRefusedInEveryPath, T.testErrorFailsTheDatabase (and a probe: a w() after
  a failure, DbFailedException; after stop(), DbStoppingException).

### 3.2. RwEnvironment, ReadInterface and Action (8 methods, 24 promises)

* RwEnvironment: valid only while Action.run() runs, IllegalStateException after;
  the last call on a key counts (J1). OUT.testEnvironmentAfterRun, T.testRwPutThenDelete,
  T.testRwManyPutsOfOneKey.
* get() and exists(): one state, the latest as of the first read, whatever the
  connection's lookup time; the action's own puts and deletes not seen; a byte[] returned is
  the database's own; the classes of Connection.get(); ObjectCreationException and
  DataFormatException as the action's exception; IllegalArgumentException for a null or
  invalid key and a null class (J2). R.testRwEnvironmentReadsOneState,
  R.testActionExceptions, R.testRwEnvironmentRefusals, R.testTimeNullArguments,
  T.testRwFirstReadThatThrowsFixesTheReadTime, T.testRwKeepsFrozenLookupTime,
  T.testByteArrayCopiedAtPutNotAtGet, J.testGetOfPrimitivesAndArrays,
  U8.testStringValueNotWellFormed, T.testExistsOfMalformedKeyThrows.
* put() and delete(): a byte[] copied at the put; the refusals of WBuilder.put(), each
  ending the action. R.testRwEnvironmentReadsOneState, R.testRwEnvironmentRefusals,
  T.testRwStringPutThenDeleteOfObjectKey, PP.
* setOutput(): a null or empty name and a null value refused; a name set again replaced;
  the outputs of an earlier run cleared. R.testRwEnvironmentRefusals, OUT.testOutputs,
  OUT.testRefused, OUT.testRerun.
* ReadInterface: one method reads through a Connection and an RwEnvironment alike; exists()
  refuses a bad key in both. R.testRwEnvironmentReadsOneState,
  T.testExistsOfMalformedKeyThrows.
* Action.run(): may run more than once; reads the latest as of its first read; the outputs
  of the run that committed; a RuntimeException thrown by rw(), nothing written, the
  database going on; an Error fails the database. OUT.testRerun, R.testActionExceptions,
  T.testErrorFailsTheDatabase.

### 3.3. Transaction and TransactionInfo (6 methods, 16 promises)

* getOutput(): the committed run's output, null if none, null for every name of a
  w-transaction; a superclass, Long.class for a long; IllegalArgumentException for a null or
  empty name and a null class; ClassCastException for another class.
  R.testWBuilderOneTransaction, OUT.testOutputs, OUT.testMissingOutput, OUT.testWrongClass.
* getTime(): the time when it was executed, unique: the clock's when later than the last,
  else the next unit; a put, a delete, a w(), an empty w() and an rw() each a time of its
  own. R.testTransactionTimes, R.testClockOutOfRangeRefused.
* sync() and sync(SyncLevel): wait for this transaction's durability; an interrupt throws
  DbException, the flag set; null refused (J3). T.testWSyncLevelWaitsForItsOwn,
  T.testSync1 to T.testSync6, J.testSyncInterrupted, R.testTransactionTimes.
* TransactionInfo: the time of the transaction that wrote the value got; its KVs the
  user's, a delete with value null, a delete of a key without an entry, an index's entries
  and (020-22) a key that is no Pub key left out. J.testTransactionInfo,
  T.testTransactionInfo1, T.testTransactionInfoWithIndex,
  T.testTransactionInfoLeavesOutKeysWithNoUkey.

### 3.4. Factory, DatabaseBuilder and StartupInfo (11 methods, 34 promises)

* Factory.database(): a new builder at each call. R.testDatabaseBuilderRules.
* create(): records the directory; start() opens it, creating it and its parents; a
  directory without created.txt, missing, empty or with other files only, gets a new
  database; created.txt and no stream byte refused (DatabaseMissingException); null
  refused. T.testBuilderOpensInStart, T.testCreateMissingAndEmpty, T.testCreatedTxt1,
  T.testCreatedTxt2, T.testStreamFilesRemoved, T.testOnlyStreamFileEmptied,
  T.testMissingStreamRemedy, R.testDatabaseBuilderRules.
* open(): never creates; a missing directory, a file, a directory without a stream byte
  refused, nothing created; null refused. T.testOpenRefusesMissingDirectory,
  T.testOpenRefusesFile, T.testOpenRefusesDirectoryWithoutStream,
  T.testOpenRefusesCreatedTxtWithoutStream, T.testOpenExisting, R.testDatabaseBuilderRules.
* cryptoKey(): null refused; NULL after a key means no encryption. DBI.testCryptoKeyNullRefused,
  DBI.testCryptoKeyNullAfterKey, R.testDatabaseBuilderRules.
* clock(): null refused; a TestClock gives deterministic times. DBI.testClockNullRefused,
  R.testTransactionTimes.
* startupDistanceInMb(): 50 by default, clamped to 5 to 1000; a database keeps the one
  stored in its stream. J.testBuilderSettings, T.testSetStartupDistanceInMb,
  R.testDatabaseBuilderRules.
* cacheSizeInMb(): a fifth of the maximum heap by default, clamped (C3), 100 without a
  maximum; a value clamped to 4 to 100,000; the budget in long; eviction to three quarters.
  R.testDefaultCacheSizeClamped, J.testBuilderSettings, DBI.testCacheSizeAbove2GB, the
  Eviction tests.
* start(): a failed start closes what it opened; one database at a time on a directory and
  on a stream of memory(); IllegalStateException without a database and for an algorithm
  other than salsa, nothing created; a StreamIoException for a directory that cannot be
  listed; BadCryptoKey for a wrong, missing or needless key and, without a key, a foreign or
  damaged stream (J7), nothing written; DatabaseNotCreatedException for an incomplete
  creation. T.testFailedStartsLeaveNothing, T.testExceptionAfterStartClosesDb,
  DF.testFailedStartClosesStorage, T.testStartWhileStoppingRefused,
  T.testSecondStartOfOneBuilder, T.testSecondStartOfMemoryBuilder,
  R.testDatabaseBuilderRules, T.testUnknownCryptoAlgorithmClosesFile,
  T.testRefusedStartCreatesNothing, T.testUnlistableDirectory, T.testEncrypted1 to
  T.testEncrypted3, T.testOpenEncrypted, R.testBadCryptoKeyForAForeignStream,
  T.testCrashInCreation, T.testCrashedCreationBeforeFirstWrite.
* StartupInfo.getStartupDuration(): the start's seconds. T.testStartupInfoTime.

### 3.5. Time and Duration (19 members, 40 promises)

* Time: 100 ns units from 1970, 0 to 2^56 - 1; MAX is 2198-05-04 23:50:03.7927935; units()
  and millis() refuse a time outside it; immutable, any thread. R.testTimeInTheZone,
  J.testTimeStrings, TI.testEquals1, TI.testMillis, TI.testToUtcStringFromThreads.
* resolve(zone, now, s): the examples as written; the grammar with each field in its range,
  strict (020-21, 1); a minus time exact (020-23, Y1) and a year and a month with a time of
  day (020-23, Y2); a time of day today in the zone; a minus day 24 hours across summer time;
  a fraction rounded half up; BadFormatException for a time outside the range;
  IllegalArgumentException for nulls. R.testTimeExamples, R.testTimeInTheZone,
  TI.testStrictTimeStrings, TI.testResolveThrows, TI.testResolveUsesTheTimeZone, TR's
  tests.
* utc() and resolve(zone, s): an absolute time only. R.testTimeInTheZone.
* add(), isBetween(): past MAX refused; both ends included; a null refused (C2).
  R.testTimeInTheZone, R.testTimeNullArguments, TI.testAdd, TI.testIsBetween.
* equals(), hashCode(), toUtcString(): seven digits of the fraction, no leap second.
  R.testTimeInTheZone, TI.testToUtcString, TI.testToUtcStringRoundUp.
* Duration: non-negative; units() refuses a negative (J4); seconds() rounds to the nearest
  unit, MAX above it and for infinity, refuses NaN and a negative result; MAX is
  Long.MAX_VALUE units; equals() and hashCode(). R.testDurationRules, J.testJavadocCorners.

### 3.6. CryptoKey (11 members, 16 promises)

* generate(): a 'salsa' key of 40 bytes, getKeyData() a copy each time; serialize() and
  parse() round-trip, equal with equal hash codes; toString() masked; NULL null, without
  key data, getAlgo() null (C1's Javadoc), round-tripping; parse() refuses a string not in
  serialize()'s format (C1: three parts exactly), null with IllegalArgumentException.
  R.testCryptoKeyRules, R.testCryptoKeyParseExact, CK.testSerializeAndParse,
  CK.testHashCode, CK.testGetKeyDataGivesACopy, CK.testNullRoundTrip.

### 3.7. TestClock, Clock and SyncLevel (6 members, 12 promises)

* TestClock: 0 until setTime(); the same time again taken; an earlier time and null
  refused, unchanged (J4); thread-safe. R.testTestClock, T.testTestClockSetTimeEqual,
  T.testTestClockTimeIsVolatile.
* Clock: 10^7 units a second; a time outside 0 to 2^56 - 1 refuses the transaction and the
  start, a DbException, the database going on; the last 1024 units kept for the database's
  own transactions; a clock that goes back (J5). R.testTestClock,
  R.testClockOutOfRangeRefused, DbClock's tests (015-55).
* SyncLevel: NONE does nothing, also with the flag set; ORDINARY forces a file storage.
  J.testSyncInterrupted, T.testSync1 to T.testSync6.

### 3.8. The exceptions (13 classes, 26 promises)

* The kinds: BadCryptoKey, DatabaseMissingException, DatabaseNotCreatedException,
  DataFormatException and IllegalDbStateException are DbExceptions, DbFailedException an
  IllegalDbStateException, LookupTimeNotAvailableException an IllegalArgumentException;
  IndexBuildException, ObjectCreationException, NoSuchIndexException,
  IndexAlreadyExistsException, BadFormatException and CryptoKey.FormatException are not
  DbExceptions. R.testExceptionKinds.
* DbException: a refusal changes nothing and the database goes on (a transaction too large,
  a clock out of range, DataFormatException's data); a failure fails the database, an I/O
  error or corrupt data the cause of a DbFailedException, an Error thrown as it is.
  J.testTooLargeRefused, R.testClockOutOfRangeRefused, U8, DF.testReadErrorInGetOne,
  DF.testCorruptNodeInGetOne, DF.testSyncFails, T.testErrorFailsTheDatabase.
* DbFailedException: every later transaction and read refused with the first failure as the
  cause; sync() of the transactions before it, stop() and close() still work; the next start
  recovers; an expired lookup time and a read during a stop fail nothing.
  R.testFailedDatabaseSyncsAndCloses, T.testErrorFailsTheDatabase,
  DF.testCloseOfFailedDatabaseReturnsNormally, DF.testReadDuringStop,
  J.testIndexScanBehindCut (and a probe: every read, transaction and index call after a
  failure throws it).
* IllegalDbStateException: after stop(). J.testCallsAfterStop.
* DatabaseMissingException, DatabaseNotCreatedException, BadCryptoKey: section 3.4.
* BadFormatException: a time string, a DbObject's bytes. TI.testStrictTimeStrings,
  `DbObjectTester.testBadFormatException`.
* LookupTimeNotAvailableException, DataFormatException, ObjectCreationException,
  NoSuchIndexException, IndexAlreadyExistsException, IndexBuildException: 020-19, section 3.

### 3.9. Kv

020-19, section 3.9: done there.

### 3.10. The package pages and the overview

* bergdb.pub: the examples run as written (020-19, J.testPackageExamples); "Text and
  bytes", "Objects", "Null and absent fields" (J.testGetAsObjectByKind, J.testObjectKeys,
  T.testStoreArray, T.testStorePrimitive, DX); "Strings" (021-04's tests); "The API and its
  jar" (build.sh's check of the release jar, ReleaseDemo; 020-22's rules in Db's Javadoc,
  its tests); "Good to know" (T.testStopWritesAll, T.testSync1, J.testConnections,
  T.testRetainDuration1, T.testErrorFailsTheDatabase, J.testJobStatus); its dependencies
  (deps.py: true).
* bergdb.pub.util: its dependencies, false (J6).
* The overview: its program run as written (020-19).

### 3.11. The count

Promises written down and checked: about 185, in 3.1 to 3.10, each bullet a few of them.
Every public method and constructor of the listed classes has its promises checked. Tests
added: 18 in `PubTesterJavadocRest`, 3 of them for the code faults (each failing before its
fix), 15 of promises kept, those of J1 to J7 among them.


## 4. Findings

Severity: high (wrong data, a failed database), medium (a user is misled into a wrong
program), low (a wrong or missing sentence or message, no wrong data).

### 4.1. Code faults

* **C1** (low). `CryptoKey.parse()` took a string with more parts than `serialize()`'s three:
  "NAME-salsa-HEX-x", "NAME-salsa-HEX-" and "a-salsa-HEX-HEX" gave the key, as `split("-")`
  without a limit dropped a trailing empty part and the parts after the third were ignored;
  the Javadoc promised a `FormatException` for a string not in `serialize()`'s format
  (`CryptoKey.java`, `parse()`, line 109 at `b7aa2a0`). Fix: exactly three parts; the
  Javadoc gives the format, and `getAlgo()` null for NULL. Test:
  `R.testCryptoKeyParseExact`, which failed before. Commit `6cbd931`.
* **C2** (low). `Time.add(null)` and `Time.isBetween()` with a null threw
  `NullPointerException`, where every null argument of the API throws
  `IllegalArgumentException` (020-21, 3, Frans's decision of 10:30); no Javadoc said
  either (`Time.java`, lines 207 and 214 at `b7aa2a0`). And `RwEnvironment.get(key,
  null)`'s message named a parameter "c" (`KvToObjectImp.java`, line 44). Fix:
  `IllegalArgumentException` with its `@throws`; the message "clazz == null not allowed".
  Test: `R.testTimeNullArguments`, which failed before. Commit `2e95f39`.
* **C3** (low). The default cache size was not clamped: `DatabaseBuilder.cacheSizeInMb()`
  gives a fifth of the maximum heap as the default and clamps a value to 4 to 100,000, but
  the default was at least 2 with no upper bound, so a heap under 20 MB gave 2 or 3 MB and
  one over 500 GB more than 100,000 (`DatabaseBuilderImp.java`, the constructor, line 62
  at `b7aa2a0`). Fix: `defaultCacheSizeInMb()` clamps; 100 for a JVM without a maximum, as
  before, now in the Javadoc; J.testBuilderSettings computes the default with the clamp.
  Test: `R.testDefaultCacheSizeClamped`, which failed before ("Expected 4, got 3"). Commit
  `21e87d2`.

### 4.2. Javadoc faults

Each fixed in the Javadoc alone; the code is unchanged. JAVADOC PUB OK after each.

* **J1** (low). `WBuilder` and `RwEnvironment` did not say what several puts and deletes of
  one key in one transaction do: the last one counts (015-40). Tests:
  `R.testWBuilderOneTransaction`, `T.testWPutThenDelete`, `T.testRwPutThenDelete`. Commit
  `312f857`.
* **J2** (low). `ReadInterface.get()` and `RwEnvironment.get()` listed only
  `ObjectCreationException`; they also throw `IllegalArgumentException` (a null or invalid
  key, a null class) and `DataFormatException` (a String value not well-formed UTF-8), as
  `Connection.get()` says. Tests: `R.testRwEnvironmentRefusals`, `R.testTimeNullArguments`,
  `U8.testStringValueNotWellFormed`. Commit `312f857`.
* **J3** (low). `sync(SyncLevel)` of `Transaction`, `Connection` and `Database` refuses null
  with `IllegalArgumentException`; none said so. Test: `R.testTransactionTimes`. Commit
  `8e651de`.
* **J4** (low). `Duration.units()` refuses a negative value, and `TestClock.setTime()` null
  and an earlier time, with `IllegalArgumentException`; neither said so. Tests:
  `R.testDurationRules`, `R.testTestClock`. Commit `8cfb428`.
* **J5** (low). `Clock.getTime()` gave the range 0 to 2^56 - 1 and not what a time
  outside it does (the transaction, or the start, refused with a `DbException`, the
  database going on; 005-18), nor that the last 1024 units are kept for the database's own
  transactions, so that a user transaction needs a time of 2^56 - 1025 or less (015-55),
  nor that the clock may go back (the next unit is taken). A test with a `TestClock` near
  `Time.MAX` meets a refusal that no Javadoc of the Pub API explains. Test:
  `R.testClockOutOfRangeRefused`. Commit `8cfb428`.
* **J6** (low). `bergdb.pub.util`'s package page said "Depends on: common."; it uses no
  other package of BergDB (deps.py). Now "Depends on: nothing.", which deps.py then holds
  it to. Commit `05ded17`.
* **J7** (low). `BadCryptoKey` and `DatabaseBuilder.start()` gave a missing or wrong key
  only; without a key, a start also throws it for a stream that is not a BergDB stream, or
  is damaged at its beginning (its message says so since 005-33). Test:
  `R.testBadCryptoKeyForAForeignStream`. Commit `769df35`.

### 4.3. Tests of promises kept

Commits `4512291` (the tester, 12 tests), `9195bdd` (Time's examples) and `dd881ed`
(RwEnvironment's refusals). Promises that no test showed before, now shown (all kept):
WBuilder's transaction as a whole, none of it before its time; Transaction.getTime() with a
TestClock, for every kind of transaction; the action's reads not seeing its own writes, and
reading the latest whatever the connection's lookup time; an action's RuntimeException
thrown as the same object; a clock out of range a refusal, not a failure, and a clock that
goes back; DbFailedException's sync of earlier transactions, stop() and close(); the
exceptions' kinds; Factory's new builders; a stored startup distance kept over the
builder's; a time of day in its zone, a minus day across summer time, absolute only for
utc(); Time's examples; Duration's rules; CryptoKey's rules.


## 5. For Frans

* **Q1**. A local time that summer time skips or repeats: `Time.resolve(zone, ...)` takes
  "2013-03-31 02:30" in Europe/Stockholm, a time that does not exist there, as 03:30 summer
  time (01:30 UTC: moved forward by the gap), and "2013-10-27 02:30", which happens twice,
  as the later one, 02:30 standard time (01:30 UTC); a time of day today and a minus time
  with a time of day the same. The Javadoc says nothing of either, and since 020-21 says
  that the parse is strict, "with each field in its range", which both are. java.time takes
  the gap the same way, but the overlap as the earlier time (00:30 UTC). Recommendation:
  say it in `Time.resolve()`'s Javadoc, as the code does it (the gap moved forward by its
  length, the overlap the later time), with a test; refusing a skipped time would make a
  time of day fail one hour a year in a zone with summer time, for no typo. Not changed.


## 6. Notes, not changed

* A `WBuilder` takes the connection's key replace setting when `w()` makes it: a
  `setEnableKeyReplace(true)` after `w()` does not apply to its puts. No Javadoc says when
  the setting is read.
* `RwEnvironment` is closed when `rw()` ends, not when `Action.run()` returns: a call from
  another thread between the end of a run and the commit, or between runs, is not refused,
  though "a call to it after that throws IllegalStateException". Only a misuse meets it.
* `IllegalDbStateException` says "before it has been started"; no `Database` exists before
  its start, so the Pub API never throws it so.
* `Transaction.sync()` and `Connection.sync()` after `stop()` throw a `StreamIoException`
  ("Storage is closing"); `Database.stop()` says to call only `close()` after it.
* `WBuilder.put()`'s `@throws` does not name the key replace refusal in a directory
  (020-14, X1); `Connection.setEnableKeyReplace()` gives it.
* A stream of one byte is taken as an incomplete creation (`DatabaseNotCreatedException`)
  when its byte is the magic's first, 1 in 256 for a random byte read with a crypto key;
  otherwise a `StreamIoException`. By design (005-33): one byte cannot be told apart.
* `Factory`'s trailing comment says that pub refers to pubimp in two places only; since
  020-08 `DbObject` and the value classes do too (the package page says so). A comment, not
  Javadoc.
* `bergdb.core.Db`, part of the API by "The API and its jar", was not in this item's list;
  its Javadoc was not checked here.


## 7. State

Done: every listed class has its promises checked (section 3); three code faults fixed (C1
to C3), seven Javadoc faults fixed (J1 to J7), 18 tests added, one question for Frans (Q1),
notes in section 6. The commits are in the clone `/Users/f/fl/bench/2026-11-09/clone-j25`,
branch `main`, on `82edabf`: `4512291` (the tester), `6cbd931` (C1), `2e95f39` (C2),
`21e87d2` (C3), `312f857` (J1, J2), `8e651de` (J3), `8cfb428` (J4, J5), `05ded17` (J6),
`9195bdd` (Time's examples), `769df35` (J7), `dd881ed` (RwEnvironment's refusals). Not
pushed; the coordinator takes them to the main tree. `releases/next.md` has an entry for
each code fault; the Javadoc faults have no entry.

Gates (`java/before-commit.sh`, under the shared lock, in clones of their own): the first
ten commits, then `4f53a8b`, now `769df35` (the same tree in java/): BEFORE COMMIT OK
(197 s; unit 1523, f 86, DEMOS OK), 13:14; the tip, `dd881ed`: BEFORE COMMIT OK (185 s;
unit 1524, f 86, DEMOS OK), JAVADOC PUB OK, 13:21. Outputs in
`/Users/f/fl/bench/2026-11-09/j25-gate1.txt` and `j25-gate2.txt`.

Left: Q1 after Frans's word; section 6's notes, each a small entry if Frans wants it; the
Javadoc of the Core's `Db`, part of the API, which neither 020-19 nor this item checked.


Log
===

2026-11-09. Created by coord-1109's agent j25, 12:55. Every listed class checked, C1 to C3
and J1 to J7 fixed in the clone with their tests, 11 commits on `82edabf`, the tip gated
(BEFORE COMMIT OK, 13:21). Stopped at 13:25: every listed class done.
